#!/usr/bin/env python3
"""Measure a theorem's CIC kernel-feature footprint (the *fragment* it uses).

Usage:
    tools/cic_footprint.py E213.Theory.Raw.Lambek.isPart_wf
    tools/cic_footprint.py --import E213.Theory.Raw.Lambek \
        E213.Theory.Raw.Lambek.isPart_wf E213.Theory.Raw.slash E213.Theory.Raw.rec

What it does — and what it does NOT do (read this):

  This walks the FULL transitive constant-closure of a fully-elaborated proof
  term (`getUsedConstants`, including `private`/`_`-prefixed/`recAux` helpers
  that `scan_axioms.py`'s source-regex misses) and reports a feature vector:
    - axioms            : the axiom closure (Lean.collectAxioms-equivalent)
    - quot              : any `Quot.*` (quotient) constant present?
    - classical         : any `Classical.*` present?
    - wf_fix_nonstruct  : non-structural `WellFounded.fix/.fixF/.rec` present?
    - nat_consts        : count of `Nat.*` constants (the Round-5 metric)
    - inductives        : the set of `inductive` types in the closure
    - recursors         : the set of recursors (`.rec`) used (Acc.rec / Tree.rec
                          are large-elimination — flagged)
    - closure_size      : total constants in the closure

  HONEST SCOPE (per the genesis-seam Round-6 debate; do not overstate):
    * This is a MEASUREMENT of the syntactic CIC fragment, exterior-judgeable
      (anyone can re-run it).  It does NOT *reduce* CIC dependence: the tool
      runs inside Lean and trusts the elaborator + kernel that produced the
      term — its own trusted base is LARGER than what it certifies.
    * The vector does NOT bound LOGICAL STRENGTH.  The kernel's definitional
      equality (ι/β reduction + proof irrelevance) and `Acc.rec` large
      elimination already exceed PRA regardless of these flags.  "universe-0 /
      structural / Nat-free" is a syntactic restriction, not a strength claim.
    * The de Bruijn floor stands: a trusted checker is irreducible.  This tool
      sharpens the *bracket* on the fragment; it never reaches a zero-kernel.

  The single §5.1-legal use: a mechanically re-checkable certificate that the
  audited cone restricts to {no axioms, no Quot, no Classical, structural +
  Acc recursion, listed inductives, Nat-count} — axiom-base-minimization +
  fragment-restriction, nothing more.
"""
import subprocess, sys, pathlib

LEAN_DIR = 'lean'
PROBE = pathlib.Path('lean/E213/_CicFootprintProbe.lean')

LEAN_TEMPLATE = r'''import @IMP@
import Lean
open Lean

partial def usedClosure (env : Environment) (n : Name) (seen : NameSet) : NameSet :=
  if seen.contains n then seen
  else Id.run do
    let mut seen := seen.insert n
    match env.find? n with
    | some ci =>
      let mut deps := ci.type.getUsedConstants
      match ci.value? with
      | some v => deps := deps ++ v.getUsedConstants
      | none => pure ()
      for d in deps do
        seen := usedClosure env d seen
      return seen
    | none => return seen

def report (env : Environment) (target : Name) : IO Unit := do
  let cl := (usedClosure env target {}).toList
  let mut axioms : Array Name := #[]
  let mut inducts : Array Name := #[]
  let mut recs : Array Name := #[]
  let mut quot := false
  let mut classical := false
  let mut wffix := false
  let mut natCount := 0
  for n in cl do
    if (`Nat).isPrefixOf n then natCount := natCount + 1
    if (`Quot).isPrefixOf n then quot := true
    if (`Classical).isPrefixOf n then classical := true
    if n == `WellFounded.fix || n == `WellFounded.fixF || n == `WellFounded.rec
       || n == `Acc.rec then
      wffix := true
    match env.find? n with
    | some (.axiomInfo _) => axioms := axioms.push n
    | some (.inductInfo _) => inducts := inducts.push n
    | some (.recInfo _) => recs := recs.push n
    | _ => pure ()
  IO.println s!"TARGET {target}"
  IO.println s!"  closure_size {cl.length}"
  IO.println s!"  axioms {axioms.qsort (·.toString < ·.toString) |>.toList}"
  IO.println s!"  quot {quot}"
  IO.println s!"  classical {classical}"
  IO.println s!"  wf_fix_nonstruct {wffix}"
  IO.println s!"  nat_consts {natCount}"
  IO.println s!"  inductives {inducts.qsort (·.toString < ·.toString) |>.toList}"
  IO.println s!"  recursors {recs.qsort (·.toString < ·.toString) |>.toList}"
  let minimal := axioms.isEmpty && !quot && !classical && !wffix && natCount == 0
  IO.println s!"  verdict {if minimal then "MINIMAL-STRUCTURAL (axiom-free, no Quot, no Classical, no non-structural/Acc WF-recursion, Nat-free)" else "EXTENDED-FRAGMENT"}"

run_cmd do
  let env ← getEnv
  @BODY@
'''


def run(imp, targets):
    body = '\n  '.join(f'liftM (report env `{t})' for t in targets)
    PROBE.write_text(LEAN_TEMPLATE.replace("@IMP@", imp).replace("@BODY@", body))
    try:
        r = subprocess.run(['lake', 'env', 'lean', str(PROBE.relative_to(LEAN_DIR))],
                           cwd=LEAN_DIR, capture_output=True, text=True, timeout=600)
        return r.stdout + r.stderr
    finally:
        PROBE.unlink(missing_ok=True)


if __name__ == '__main__':
    args = sys.argv[1:]
    imp = 'E213.Theory.Raw.Lambek'
    if args and args[0] == '--import':
        imp = args[1]; args = args[2:]
    if not args:
        print(__doc__); sys.exit(2)
    out = run(imp, args)
    # surface the report lines + any errors
    for line in out.splitlines():
        if line.startswith('TARGET') or line.startswith('  ') or 'error' in line.lower():
            print(line)
    sys.exit(0 if 'error' not in out.lower() else 1)
