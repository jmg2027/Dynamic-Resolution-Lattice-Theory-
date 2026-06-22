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


# Sealed-DIRTY-by-design modules.  Each entry's justification is
# documented in STRICT_ZERO_AXIOM.md §"Sealed-by-design categories"
# (which is the single source of truth — keep this list in sync).
#
# Policy: only modules with a *structural* reason to use a Lean-core
# axiom (propext / Quot.sound / Classical.choice) are waived.  Any
# DIRTY outside this list is a real regression that violates the
# 0-axiom standard.
SEALED_DIRTY_PREFIXES = (
    # (a) Prop-as-distinguishing thesis.  `HasDistinguishing` for `Prop`
    #     has a `combine_sym : combine P Q = combine Q P` field at type
    #     `Prop = Prop` — provable only via `propext`.
    "E213.Lens.Foundations.SemanticAtom",
    "E213.Lens.Properties.Morphism.BoolProp",
    # (b) Lens funext-by-design.  `Lens.combine` for the universal /
    #     indexed / Cauchy Lens family is function-valued (e.g.
    #     `(Raw → Prop) → (Raw → Prop) → (Raw → Prop)`), and
    #     `Lens.combine_sym` is therefore a function-equality
    #     statement that demands `funext` (= `Quot.sound` in the
    #     kernel).  `DepthJoin` also lands here: its `tier`-classifier
    #     theorems pass through `Lens.equiv` (Prop-valued Lens.view
    #     equality) and `Lens.refines` (function-shape kernel
    #     equality), both of which need propext + Quot.sound to close.
    "E213.Lens.Universal.QuotLens",
    "E213.Lens.Lattice.IndexedJoin",
    "E213.Lens.Instances.Cauchy",
    "E213.Lens.Instances.Leaves.DepthJoin",
    # (a) cont. — command-elaborator plumbing.  Each module's only DIRTY
    #     declaration is a `def elab… : CommandElab` that inherits
    #     `Classical.choice` (+ propext, Quot.sound) via the
    #     `Lean.Elab.Command` monad.  Not 213-math content (no theorem about
    #     Raw / Lens / observables); cannot be PURE (lives in the Elab monad).
    "E213.Lib.Math.Tactic.QuadExtension",
    "E213.Meta.Tactic.DeriveConjugationCodomain",
    "E213.Meta.Tactic.VerifyConjugation",
    "E213.Meta.Tactic.NativeGuard",          # 213-native *vocabulary* guard
                                             #   metaprogram; CommandElab-class
                                             #   plumbing (same as the elab defs
                                             #   above), not math content.
    # (c) axiom-exhibiting bridge lenses.  Each file's only DIRTY decl
    #     *deliberately applies* the named axiom to demonstrate "the axiom
    #     IS a lens application" (documented "DIRTY BY DESIGN" in-file).
    #     Their DIRTY status is the content, not a leak.
    "E213.Lens.AxiomLenses.Bridges.Funext",     # funextLens_inhabited := funext
    "E213.Lens.AxiomLenses.Bridges.QuotSound",  # sound_lens := Quot.sound
    # (a) cont. — Prop-as-distinguishing (same justification as
    #     `SemanticAtom`/`BoolProp` above): the `propext` decls are the
    #     Prop-side statement; the Bool-lens `view` equalities are the PURE
    #     213-native content.
    "E213.Lib.Math.Foundations.Choice.CanonicalTruthChar",
    # (b) cont. — funext toll on a *cochain* function-equality.  The PURE
    #     mathematical content is the pointwise `cup_symm_pointwise`; the
    #     lone DIRTY decl `cup_symm` is the `funext` wrapper restating it as
    #     a function-`=` (same class as the Lens funext family above).
    "E213.Lib.Math.Cohomology.Surfaces.T2Minimal.CupPairing",
)


def is_sealed_dirty(module: str) -> bool:
    return any(module.startswith(p) for p in SEALED_DIRTY_PREFIXES)


# Sealed-by-design DECL prefixes (checked on the declaration name, not the
# module).  The command-elaborator defs (`elabVerifyConjugation`,
# `elabDeriveConjugation`, …) live in `E213.Tactic.*` but get *attributed to the
# module that invokes the command macro* (e.g. a `Cauchy.*` file using
# `derive_conjugation`), so module-based sealing misses them and they show up as
# false "real DIRTY".  They are the same CommandElab plumbing as the
# `Meta.Tactic.*` entries above (category (a)); seal them by decl name.
SEALED_DIRTY_DECLS = (
    "E213.Tactic.elab",
)


def is_sealed_decl(decl: str) -> bool:
    return any(decl.startswith(p) for p in SEALED_DIRTY_DECLS)


def summarize(results):
    pure = [r for r in results if r[2] == 'PURE']
    dirty_real = [r for r in results
                  if r[2] == 'DIRTY' and not is_sealed_dirty(r[1])
                     and not is_sealed_decl(r[0])]
    dirty_sealed = [r for r in results
                    if r[2] == 'DIRTY' and (is_sealed_dirty(r[1])
                       or is_sealed_decl(r[0]))]
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
