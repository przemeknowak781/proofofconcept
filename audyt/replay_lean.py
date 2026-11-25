"""Run under 'lake env python -I -X utf8 ../replay_lean.py' after fetching Mathlib.
The working directory must be the lean-kenyon package (or its audit copy).
"""
from graphlib import TopologicalSorter
from pathlib import Path
import re
import subprocess
import tempfile
import time


def run(args):
    return subprocess.run(args, capture_output=True, encoding='utf8', errors='replace')


def main():
    sources = {'.'.join(f.with_suffix('').parts): f
               for f in [*Path('.').glob('*.lean'), *Path('Kenyon').glob('*.lean'),
                         *Path('TreeEntropy').glob('*.lean')]}
    imports = {m: set(re.findall(r'^import\s+(\S+)', f.read_text(encoding='utf8'), re.M))
               & sources.keys() for m, f in sources.items()}
    assert len(sources) == 31
    for module in TopologicalSorter(imports).static_order():
        src = sources[module]
        target = Path('.lake/build/lib/lean') / src.with_suffix('.olean')
        target.parent.mkdir(exist_ok=True, parents=True)
        start = time.monotonic()
        result = run(['lean', '-j2', '-R', '.', '-o', str(target), str(src)])
        if result.returncode:
            print(result.stdout, result.stderr, flush=True)
            result.check_returncode()
        print(f'source OK {module} ({time.monotonic() - start:.1f} s)', flush=True)
    file = Path('scripts/PrintAxioms.lean')
    expected = re.findall(r'^#print axioms (\S+)', file.read_text(encoding='utf8'), re.M)
    axioms = run(['lean', str(file)])
    output = axioms.stdout + axioms.stderr
    print(output, flush=True)
    axioms.check_returncode()
    observed = re.findall(r"^'(\S+)' depends on axioms: \[([^\]]*)\]\s*$", output, re.M)
    assert [name for name, _ in observed] == expected
    allowed = {'Classical.choice', 'propext', 'Quot.sound'}
    for name, words in observed:
        assert set(words.split(', ')) <= allowed, (name, words)
    modules = [f'{folder}.{f.stem}' for folder in ['TreeEntropy', 'Kenyon']
               for f in sorted(Path(folder).glob('*.lean'))]
    assert len(modules) == 29
    for module in modules:
        start = time.monotonic()
        result = run(['leanchecker', module])
        if result.returncode:
            print(result.stdout, result.stderr, flush=True)
            result.check_returncode()
        print(f'kernel OK {module} ({time.monotonic() - start:.1f} s)', flush=True)

    with tempfile.TemporaryDirectory(dir='.') as tmp:
        false_statement = Path(tmp) / 'MustReject.lean'
        false_statement.write_text('theorem mustReject : (1 : Nat) = 2 := by decide\n',
                                   encoding='utf8')
        rejected = run(['lean', str(false_statement)])
        assert rejected.returncode and 'is false' in rejected.stdout + rejected.stderr, rejected
    print(f'PASS: {len(expected)} axiom reports, {len(modules)} kernel replays, false theorem rejected.')


if __name__ == '__main__':
    main()
