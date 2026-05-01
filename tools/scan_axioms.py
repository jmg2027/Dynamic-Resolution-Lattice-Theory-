#!/usr/bin/env python3
"""Scan a Lean module's per-theorem axiom status.

Usage:
    tools/scan_axioms.py E213.Math.IntHelpers
    tools/scan_axioms.py E213.Math.Pigeonhole E213.Math.IntHelpers ...

Generates a temporary probe file appending #print axioms for every
top-level theorem/lemma/def in each module, builds it, and reports.

Produces output like:
    [PURE]  E213.Math.X.thm1
    [DIRTY] E213.Math.X.thm2  [propext, Quot.sound]
"""
import subprocess, sys, re, pathlib, tempfile

LEAN_ROOT = pathlib.Path('lean/E213')
DECL_RX = re.compile(
    r'^(?:protected\s+)?(?:theorem|lemma|def)\s+([A-Za-z_][\w\']*)',
    re.MULTILINE,
)
NAMESPACE_RX = re.compile(r'^namespace\s+(\S+)', re.MULTILINE)
PROBE_PATH = LEAN_ROOT / '_AxiomScanProbe.lean'
LINE_RX = re.compile(
    r"info: [^']*'([^']+)' "
    r"(does not depend on any axioms|"
    r"depends on axioms: \[([^\]]+)\])"
)


def find_decls(module: str):
    rel = pathlib.Path(*module.split('.')[1:]).with_suffix('.lean')
    path = pathlib.Path('lean') / 'E213' / rel
    if not path.exists():
        return []
    src = path.read_text()
    namespaces = NAMESPACE_RX.findall(src)
    ns = namespaces[-1] if namespaces else module
    if not ns.startswith('E213'):
        ns = module
    decls = DECL_RX.findall(src)
    return [f'{ns}.{n}' for n in decls if not n.startswith('_')]


def scan(modules):
    lines = [f'import {m}' for m in modules]
    decls = []
    for m in modules:
        decls.extend(find_decls(m))
    lines.extend(f'#print axioms {d}' for d in decls)
    PROBE_PATH.write_text('\n'.join(lines) + '\n')
    cmd = ['lake', 'build', 'E213._AxiomScanProbe']
    r = subprocess.run(cmd, cwd='lean', capture_output=True, text=True)
    out = r.stdout + r.stderr
    PROBE_PATH.unlink(missing_ok=True)
    pure, dirty, errors = [], [], []
    for m in LINE_RX.finditer(out):
        name = m.group(1)
        if 'does not depend' in m.group(2):
            pure.append(name)
        else:
            dirty.append((name, m.group(3)))
    if 'error' in out.lower():
        errors = [l for l in out.splitlines() if 'error' in l.lower()][:5]
    return pure, dirty, errors


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(__doc__); sys.exit(2)
    pure, dirty, errors = scan(sys.argv[1:])
    for n in pure: print(f'[PURE]  {n}')
    for n, ax in dirty: print(f'[DIRTY] {n}  [{ax}]')
    if errors:
        print('# build errors:', file=sys.stderr)
        for e in errors: print(f'  {e}', file=sys.stderr)
    print(f'# {len(pure)} pure / {len(dirty)} dirty')
    sys.exit(1 if errors else 0)
