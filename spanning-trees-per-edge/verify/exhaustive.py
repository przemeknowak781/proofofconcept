"""Exhaustive check of the theorem  tau(G)^2 * 8^m < 27^m  (exact integers) over all connected loopless multigraphs
with at most M edges that are not trees, generated with nauty (geng + multig).  Trees have tau = 1, loops do not
change tau, and disconnected graphs have tau = 0, so these cases are trivial and are not enumerated.
Usage: python3 exhaustive.py M [PROCESSES]        (M = 11 takes about a minute)
Requires the nauty programs `geng` and `multig` (on Debian/Ubuntu they are called nauty-geng and nauty-multig)."""
import math, shutil, subprocess, sys
from multiprocessing import Pool

GENG = shutil.which('nauty-geng') or shutil.which('geng')
MULTIG = shutil.which('nauty-multig') or shutil.which('multig')


def tau_exact(n, edges):
    """Number of spanning trees: fraction-free (Bareiss) elimination on the reduced Laplacian, Python integers."""
    if n == 1: return 1
    Lp = [[0] * n for _ in range(n)]
    for u, v in edges:
        Lp[u][u] += 1; Lp[v][v] += 1; Lp[u][v] -= 1; Lp[v][u] -= 1
    M = [row[1:] for row in Lp[1:]]; k = n - 1; sign = 1; prev = 1
    for i in range(k - 1):
        if M[i][i] == 0:
            sw = next((r for r in range(i + 1, k) if M[r][i] != 0), None)
            if sw is None: return 0
            M[i], M[sw] = M[sw], M[i]; sign = -sign
        for r in range(i + 1, k):
            for c in range(i + 1, k):
                M[r][c] = (M[r][c] * M[i][i] - M[r][i] * M[i][c]) // prev
        prev = M[i][i]
    return sign * M[k - 1][k - 1]


def job(args):
    m, n = args
    cmd = f"{GENG} -c -q {n} {n-1}:{m} | {MULTIG} -q -T -e{m}"
    p = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, text=True)
    cnt = viol = 0; best = (-1.0, None, None); p27 = 27 ** m; p8 = 8 ** m
    for line in p.stdout:
        t = line.split(); nv, ne = int(t[0]), int(t[1]); edges = []
        for i in range(ne):
            u, v, mult = int(t[2 + 3 * i]), int(t[3 + 3 * i]), int(t[4 + 3 * i]); edges += [(u, v)] * mult
        assert len(edges) == m
        tau = tau_exact(nv, edges); cnt += 1
        if tau * tau * p8 >= p27: viol += 1
        val = math.log(tau) / m
        if val > best[0]: best = (val, tau, line.strip())
    p.wait()
    return m, n, cnt, viol, best


if __name__ == '__main__':
    assert GENG and MULTIG, 'nauty (geng, multig) not found'
    M = int(sys.argv[1]); procs = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    # a connected graph with m edges has at most m + 1 vertices; with exactly m + 1 it is a tree (tau = 1), skipped
    jobs = sorted([(m, n) for m in range(2, M + 1) for n in range(2, m + 1)], key=lambda j: -j[0])
    res = {}
    with Pool(procs) as pool:
        for m, n, cnt, viol, best in pool.imap_unordered(job, jobs): res.setdefault(m, []).append((cnt, viol, best))
    total = violations = 0
    for m in sorted(res):
        c = sum(r[0] for r in res[m]); v = sum(r[1] for r in res[m]); b = max(r[2] for r in res[m]); total += c; violations += v
        print(f"m={m:2d}: {c:9d} multigraphs, violations {v}, max tau^(1/m) = {math.exp(b[0]):.6f} (tau = {b[1]})")
    print('total', total, 'connected loopless multigraphs that are not trees; violations', violations,
          '; bound sqrt(27/8) =', math.sqrt(27 / 8))
