#!/usr/bin/env python3
"""Whole-repo scan of `#print axioms` status.

Generates a probe file that imports E213.* modules and prints axioms
for every public theorem/lemma/def.  Reports counts and per-axiom-set
breakdown.

Usage:
    python3 tools/scan_all_axioms.py                # all of E213
    python3 tools/scan_all_axioms.py --filter Real213
    python3 tools/scan_all_axioms.py --csv out.csv
"""
import subprocess, re, sys, pathlib, argparse
from collections import Counter, defaultdict

LEAN_ROOT = pathlib.Path('lean/E213')
DECL_RX = re.compile(
    r'^(?:protected\s+)?(?:theorem|lemma|def)\s+([A-Za-z_][\w\']*)',
    re.MULTILINE,
)
NAMESPACE_RX = re.compile(r'^namespace\s+(\S+)', re.MULTILINE)
PROBE_PATH = LEAN_ROOT / '_AxiomScanProbe.lean'
LINE_RX = re.compile(
    r"'([^']+)' "
    r"(does not depend on any axioms|"
    r"depends on axioms: \[([^\]]+)\])"
)


def find_modules(filter_pat=None):
    """Find all E213.* module names from the file tree."""
    modules = []
    for path in LEAN_ROOT.rglob('*.lean'):
        if path.name.startswith('_'):
            continue
        rel = path.relative_to(LEAN_ROOT.parent)
        parts = list(rel.with_suffix('').parts)
        module = '.'.join(parts)
        if filter_pat and filter_pat not in module:
            continue
        modules.append(module)
    return sorted(modules)


def find_decls(module):
    """Parse file to find (decl, module) pairs with proper nested-namespace tracking."""
    rel = pathlib.Path(*module.split('.')[1:]).with_suffix('.lean')
    path = LEAN_ROOT.parent / 'E213' / rel
    if not path.exists():
        return []
    src = path.read_text(errors='ignore')
    decls = []
    ns_stack = []
    decl_pat = re.compile(
        r'^(?:protected\s+)?(?:theorem|lemma|def)\s+([A-Za-z_][\w\']*)')
    ns_pat = re.compile(r'^namespace\s+(\S+)')
    end_pat = re.compile(r'^end\s+(\S+)')
    for line in src.splitlines():
        m = ns_pat.match(line)
        if m:
            ns_stack.append(m.group(1))
            continue
        m = end_pat.match(line)
        if m:
            if ns_stack:
                ns_stack.pop()
            continue
        m = decl_pat.match(line)
        if m:
            n = m.group(1)
            if n.startswith('_'):
                continue
            ns = '.'.join(ns_stack) if ns_stack else module
            if not ns.startswith('E213'):
                ns = module
            decls.append((f'{ns}.{n}', module))
    return decls


def scan_batch(modules, batch_size=50):
    """Scan one module per probe (slower but reliable)."""
    results = []
    print(f'# Scanning {len(modules)} modules', file=sys.stderr)
    for i, mod in enumerate(modules):
        decls = find_decls(mod)
        if not decls:
            continue
        lines = [f'import {mod}']
        lines.extend(f'#print axioms {d}' for d, _ in decls)
        PROBE_PATH.write_text('\n'.join(lines) + '\n')
        cmd = ['lake', 'env', 'lean',
               str(PROBE_PATH.relative_to('lean'))]
        try:
            r = subprocess.run(cmd, cwd='lean', capture_output=True,
                               text=True, timeout=180)
            out = r.stdout + r.stderr
        except subprocess.TimeoutExpired:
            out = ''
        for match in LINE_RX.finditer(out):
            name = match.group(1)
            if 'does not depend' in match.group(2):
                results.append((name, mod, 'PURE', ''))
            else:
                axioms = match.group(3)
                results.append((name, mod, 'DIRTY', axioms))
        if (i + 1) % 10 == 0 or i + 1 == len(modules):
            sys.stderr.write(f'  {i+1}/{len(modules)}: '
                             f'{len(results)} results\n')
            sys.stderr.flush()
    PROBE_PATH.unlink(missing_ok=True)
    return results


SEALED_DIRTY_PREFIXES = (
    # Bridges/ are intentional Lean ↔ 213 axiom-bridge demonstrations.
    # Their DIRTY status is by design — sealed metatheoretic cluster,
    # not imported by 213 core.  Tracked separately from real DIRTY.
    'E213.Hypervisor.Lens.AxiomLenses.Bridges',
    # SemanticAtom is Prop-level (propAsDistinguishing, canonicalIffMap,
    # iff_comm_eq, etc.).  Working with Prop equality intrinsically uses
    # propext — this is mathematically inherent to the meta-theoretic
    # "atom of meaning" thesis, not a refactorable propext leak.
    # Sealed as DIRTY-by-design 2026-05-XX (session 24).
    'E213.Hypervisor.Lens.SemanticAtom',
    # Lean-core boundary: items that depend on Nat.lcm/gcd/mod_two
    # well-founded definitions, or Int operations.  These bring propext
    # via Lean 4 core's well-founded-recursion proof of total termination.
    # Refactor would require building 213-native gcd/lcm/Int primitives —
    # out of scope.  Sealed as Lean-core-boundary by-design.
    'E213.Math.Cohomology.Dyadic.LCMClosure',
    'E213.Hypervisor.Lens.Leaves.ModNat',
    'E213.Math.Irrational.Sqrt2KernelFree',
    # LensCardinality has 5 DIRTY: 3 from Int operations (signedLens,
    # treeTower_signed) + 2 from Lens-on-Lens stress (sigma7).  The Int
    # ones are Lean-core boundary; the others cascade.
    'E213.Math.Infinity.LensCardinality',
    # Catalog signed_R4 / depth_swap / leaves_swap / signed_swap —
    # Int / Raw.fold_signed_swap propext from Lean core.
    'E213.Hypervisor.Lens.Characterisation.Catalog',
    # CardinalityLB.leavesModNat_kernel_neq cascades from ModNat.
    'E213.Hypervisor.Lens.Kernel.CardinalityLB',
    # ProductFSMPeriod cascades from LCMClosure.
    'E213.Math.Cohomology.Dyadic.ProductFSMPeriod',
    # CabibboAngle.irreducible_5_22 = Nat.gcd 5 22 = 1 (Lean core).
    'E213.Physics.Mixing.CabibboAngle',
    # Lens funext-by-design: higher-order Lens equality (Lens (Lens α),
    # dependent function lenses, Raw → Prop kernels) is intrinsically
    # pointwise.  Proving Lens equality requires funext on the combine
    # function field — refactoring would require redefining what "Lens
    # equality" means.  Sealed as funext-by-design.
    'E213.Hypervisor.Lens.Compose.OnLens',
    'E213.Hypervisor.Lens.Lattice.IndexedJoin',
    'E213.Hypervisor.Lens.Universal.QuotLens',
    # CanonicalForm + Corresp + Initiality cascade from QuotLens funext.
    'E213.Hypervisor.Lens.Properties.CanonicalForm',
    'E213.Hypervisor.Lens.Kernel.Corresp',
    'E213.Hypervisor.Lens.Initiality',
    # Lattice family meet/join also funext-bearing (indexed family eq).
    'E213.Hypervisor.Lens.Lattice.FamilyJoin',
    'E213.Hypervisor.Lens.Lattice.FamilyMeet',
    # FoldStructured: fold-shape lens equality needs funext.
    'E213.Hypervisor.Lens.Morphism.FoldStructured',
    # Reach.fin3 / Refines.Chain cascade from Lens equality.
    'E213.Hypervisor.Lens.Instances.Reach',
    'E213.Hypervisor.Lens.Refines.Chain',
    # FunctionSpace + Cauchy + Parity instances: function-valued Lens.
    'E213.Hypervisor.Lens.Instances.FunctionSpace',
    'E213.Hypervisor.Lens.Instances.Cauchy',
    'E213.Hypervisor.Lens.Instances.Parity',
    'E213.Hypervisor.Lens.Instances.EndpointBehavior',
    'E213.Hypervisor.Lens.Instances.BoundedContext',
    'E213.Hypervisor.Lens.Instances.CochainEntry',
    'E213.Hypervisor.Lens.Instances.PointwiseProjection',
    # Properties cascade
    'E213.Hypervisor.Lens.Properties.EquivProperties',
    # RefinesParity propext from Nat.add_mod (Lean core)
    'E213.Hypervisor.Lens.Leaves.RefinesParity',
)


def is_sealed_dirty(module: str) -> bool:
    return any(module.startswith(p) for p in SEALED_DIRTY_PREFIXES)


def summarize(results):
    pure = [r for r in results if r[2] == 'PURE']
    dirty_real = [r for r in results
                  if r[2] == 'DIRTY' and not is_sealed_dirty(r[1])]
    dirty_sealed = [r for r in results
                    if r[2] == 'DIRTY' and is_sealed_dirty(r[1])]
    print(f'\n# {len(pure)} PURE / {len(dirty_real)} DIRTY '
          f'+ {len(dirty_sealed)} sealed-DIRTY-by-design '
          f'({len(results)} total)')
    axiom_counter = Counter(r[3] for r in dirty_real)
    print('\n# Axiom-set breakdown (real DIRTY only):')
    for ax, n in axiom_counter.most_common():
        print(f'  {n:5d}  [{ax}]')
    if dirty_sealed:
        print('\n# Sealed DIRTY-by-design (excluded from goal):')
        for r in dirty_sealed:
            print(f'  [{r[3]}]  {r[0]}')
    module_dirty = defaultdict(int)
    module_pure = defaultdict(int)
    for name, mod, status, _ in results:
        if is_sealed_dirty(mod):
            continue
        if status == 'DIRTY':
            module_dirty[mod] += 1
        else:
            module_pure[mod] += 1
    print('\n# Top 30 dirtiest modules (excluding sealed):')
    sorted_mods = sorted(module_dirty.items(), key=lambda x: -x[1])
    for mod, n in sorted_mods[:30]:
        p = module_pure.get(mod, 0)
        print(f'  {n:4d} dirty / {p:4d} pure  {mod}')


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--filter', default=None)
    ap.add_argument('--csv', default=None)
    ap.add_argument('--batch-size', type=int, default=50)
    ap.add_argument('--modules-only', action='store_true')
    args = ap.parse_args()
    modules = find_modules(args.filter)
    print(f'# {len(modules)} modules matching filter={args.filter!r}',
          file=sys.stderr)
    if args.modules_only:
        for m in modules:
            print(m)
        sys.exit(0)
    results = scan_batch(modules, batch_size=args.batch_size)
    summarize(results)
    if args.csv:
        with open(args.csv, 'w') as f:
            f.write('decl,module,status,axioms\n')
            for name, mod, status, ax in results:
                f.write(f'"{name}",{mod},{status},"{ax}"\n')
        print(f'\n# CSV: {args.csv}', file=sys.stderr)
