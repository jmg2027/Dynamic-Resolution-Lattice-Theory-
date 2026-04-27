#!/usr/bin/env python3
"""213 axiom audit.

Run `lake build`, parse `#print axioms` output, classify each theorem
as pure (0 axioms) or dirty (depends on propext/Quot.sound/etc).

Usage:
    python3 tools/audit_axioms.py                # all kernel + audited
    python3 tools/audit_axioms.py --filter Kernel  # only E213.Kernel.*

Run from repo root.
"""
import subprocess, re, sys, argparse
from collections import Counter

LINE = re.compile(
    r"info: [^']*'([^']+)' "
    r"(does not depend on any axioms|"
    r"depends on axioms: \[([^\]]+)\])"
)


KERNEL_MODULES = [
    'E213.Kernel.Term', 'E213.Kernel.Compare', 'E213.Kernel.Pair',
    'E213.Kernel.Rat', 'E213.Kernel.Decide', 'E213.Kernel.Sound',
    'E213.Kernel.Demo', 'E213.Kernel.Cap_PeriodicTable',
    'E213.Kernel.Cap_PhysicsBrackets',
    'E213.Kernel.Cap_PhysicsObservables',
    'E213.Kernel.Cap_PhysicsFalsifiers',
]


def run_audit(targets=None):
    targets = targets or KERNEL_MODULES
    cmd = ['lake', 'build', '--rehash'] + targets
    r = subprocess.run(cmd, cwd='lean', capture_output=True, text=True)
    out = r.stdout + r.stderr
    pure, dirty = [], []
    for m in LINE.finditer(out):
        name = m.group(1)
        if 'does not depend' in m.group(2):
            pure.append(name)
        else:
            dirty.append((name, m.group(3)))
    return pure, dirty


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--filter', default='', help='substring filter on names')
    args = ap.parse_args()

    pure, dirty = run_audit()
    if args.filter:
        pure = [n for n in pure if args.filter in n]
        dirty = [(n, a) for n, a in dirty if args.filter in n]

    print(f"== 213 Axiom Audit ==")
    print(f"Pure (0 axioms):      {len(pure)}")
    print(f"With axiom deps:      {len(dirty)}")

    if dirty:
        ax_count = Counter()
        for _, axs in dirty:
            for a in axs.split(','):
                ax_count[a.strip()] += 1
        print(f"\n== Axioms used ==")
        for ax, n in ax_count.most_common():
            print(f"  {ax}  ({n} thms)")
        print(f"\n== Dirty theorems ==")
        for name, axs in dirty[:40]:
            print(f"  {name}  [{axs}]")
        if len(dirty) > 40:
            print(f"  ... +{len(dirty) - 40} more")

    print(f"\n== Pure theorems (sample) ==")
    for n in pure[:20]:
        print(f"  ✓ {n}")
    if len(pure) > 20:
        print(f"  ... +{len(pure) - 20} more")

    sys.exit(0 if not dirty or not args.filter.startswith('Kernel') else 1)


if __name__ == '__main__':
    main()
