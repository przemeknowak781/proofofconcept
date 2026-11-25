"""Independent checks for Zenodo 24523144. Python 3, standard library.

python reproduce.py                 # independent graph counts and finite bound
python reproduce.py path/to/bin     # also run geng, multig and count_trees
"""
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from itertools import combinations
from math import comb, factorial, prod
from pathlib import Path
import os
import re
import subprocess
import sys

LIMIT = 14


def partitions(total, minimum=1):
    if total == 0:
        yield ()
    for first in range(minimum, total + 1):
        for rest in partitions(total - first, first):
            yield (first,) + rest


def fixed_multigraphs(cycles):
    """Multisets of pairs fixed by a vertex permutation of this cycle type."""
    permutation = []
    for length in cycles:
        start = len(permutation)
        permutation.extend([*range(start + 1, start + length), start])
    pairs = set(combinations(range(len(permutation)), 2))
    coefficients = [1] + [0] * LIMIT
    while pairs:
        pair = next(iter(pairs))
        length = 0
        while pair in pairs:
            pairs.remove(pair)
            u, v = pair
            pair = tuple(sorted((permutation[u], permutation[v])))
            length += 1
        for m in range(length, LIMIT + 1):
            coefficients[m] += coefficients[m - length]
    return coefficients


def connected_counts():
    """Burnside counts all isomorphism classes, then removes disconnected ones."""
    predicted = [[0] * (LIMIT + 1) for _ in range(LIMIT + 1)]
    predicted[0][0] = 1
    connected = {}
    for n in range(1, LIMIT + 1):
        group_size = factorial(n)
        total = [0] * (LIMIT + 1)
        for cycles in partitions(n):
            centralizer = prod(k**v * factorial(v) for k, v in Counter(cycles).items())
            for m, count in enumerate(fixed_multigraphs(cycles)):
                total[m] += count * (group_size // centralizer)
        for m, numerator in enumerate(total):
            assert numerator % group_size == 0
            count = numerator // group_size - predicted[n][m]
            assert count >= 0
            connected[n, m] = count
            if count == 0:
                continue
            # Add multisets built from these count component types of size (n,m).
            for v in range(LIMIT - n, -1, -1):
                for e, previous in enumerate(predicted[v]):
                    if previous == 0:
                        continue
                    for k in range(1, (LIMIT - v) // n + 1):
                        if e + k * m > LIMIT:
                            break
                        predicted[v + k * n][e + k * m] += previous * comb(count + k - 1, k)
    return connected


def executable(directory, name):
    return str((directory / (name + ('.exe' if os.name == 'nt' else ''))).resolve())


def run_for_n(directory, n):
    # Each program is started directly. Reap and verify all three children.
    with subprocess.Popen([executable(directory, 'geng'), '-cq', str(n), f'{n-1}:{LIMIT}'],
                          stdout=subprocess.PIPE) as supports:
        with subprocess.Popen([executable(directory, 'multig'), '-q', '-T', f'-e{n}:{LIMIT}'],
                              stdin=supports.stdout, stdout=subprocess.PIPE) as graphs:
            supports.stdout.close()
            counted = subprocess.run([executable(directory, 'count_trees'), str(n)],
                                     stdin=graphs.stdout, capture_output=True)
            graphs.stdout.close()
            if graphs.wait() or supports.wait() or counted.returncode:
                raise RuntimeError(f'n={n}, return codes {supports.returncode}, '
                                   f'{graphs.returncode}, {counted.returncode}')
    return n, [tuple(map(int, line.split())) for line in counted.stdout.splitlines()]


def spectral_check():
    # Kirchhoff and AM-GM give tau <= (2m/(n-1))^(n-1) / n.
    # Loops only reduce the Laplacian trace relative to 2m.
    for m in range(1, LIMIT + 1):
        for n in range(2, m + 2):
            numerator = (2 * m)**(n - 1)
            denominator = n * (n - 1)**(n - 1)
            assert numerator**2 * 8**m < denominator**2 * 27**m


def table_check():
    """Exponentiate each log inequality to compare rationals without rounding."""
    base = Fraction(27, 8)**4
    def exp16d(d, r):
        return (1+r)**(9*d) * r**d / (r+Fraction(1, d))**(2*d+16)
    for d in range(3, 120):
        critical = min(Fraction(1, 8), Fraction(1, d-2))
        right = Fraction(9*d-1, d*(3*d+1))
        relaxed_right = Fraction(3, d)
        assert exp16d(d, critical) <= base**d
        assert exp16d(d, right) < base**d
        assert exp16d(d, relaxed_right) < (2*base)**d
        if d != 5:
            assert exp16d(d, relaxed_right) <= base**d
    assert exp16d(2, Fraction(1, 8)) < (base/2)**2
    assert exp16d(4, Fraction(1, 8)) == base**4
    assert exp16d(5, Fraction(3, 5)) > base**5


def main():
    connected = connected_counts()
    spectral_check()
    table_check()
    print('468 rational table entries passed; d=4 equality and d=5 negative control passed.')
    print('Kirchhoff + AM-GM: strict bound for every m=1..14 and n=2..m+1.', flush=True)
    reference = Path(__file__).resolve().parents[1] / 'spanning-trees-per-edge/verify/exhaustive_m14.out'
    rows = re.findall(r'm=\s*(\d+):\s*(\d+) multigraphs, violations (\d+),.*?\(tau = (\d+)\)',
                      reference.read_text(encoding='utf8'))
    assert len(rows) == LIMIT - 1
    enumerated = {}
    if len(sys.argv) == 2:
        directory = Path(sys.argv[1])
        with ThreadPoolExecutor(max_workers=3) as workers:
            for n, entries in workers.map(lambda k: run_for_n(directory, k), range(2, LIMIT + 1)):
                for m, count, maximum in entries:
                    assert (n, m) not in enumerated
                    enumerated[n, m] = (count, maximum)
    print('m  Burnside  generated  max_tau')
    for m, published, violations, published_max in map(lambda row: map(int, row), rows):
        count = sum(connected[n, m] for n in range(2, m + 1))
        assert count == published
        if len(sys.argv) == 1:
            print(m, count, '-', '-')
            continue
        maxima = []
        for n in range(2, m + 1):
            found, maximum = enumerated.get((n, m), (0, 0))
            assert found == connected[n, m], (n, m, found, connected[n, m])
            maxima.append(maximum)
        maximum = max(maxima)
        assert maximum == published_max
        assert maximum**2 * 8**m < 27**m and violations == 0
        print(m, count, count, maximum)
    total = sum(c for (n, m), c in connected.items() if 2 <= n <= m)
    print('Total:', total)


if __name__ == '__main__':
    main()
