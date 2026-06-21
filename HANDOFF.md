# Session Handoff — 2026-06-21

## Branch
`claude/multi-agent-research-pxzpls` (tracks `origin/`). This session reorients the
research direction; read `research-notes/frontiers/the_substance_test.md` first.

## What this session was (the convening)
A multi-agent investigation + adversarial debate to infer the originator's ultimate
purpose and start the research that serves it (directive: "not peripheral theorems —
the true intent"). Six agents: four evidence (repo trajectory, physics centrality,
Proof-ISA depth, math breadth) + three personas (Foundationalist, Engineer, Skeptic).
Full synthesis: `research-notes/frontiers/the_substance_test.md`.

## The inferred purpose (진의)
The repo is a machine for determining whether "everything is the residue under a Lens"
(primacy / no-exterior) is **substance or wordplay** — and for making that
determination *without self-deception* (hence the large anti-over-claim apparatus:
CLAUDE.md failure modes, `scan_all_axioms.py`, the publishability audit).

Key findings carried forward (evidence in the frontier note):
- Breadth is genuine (~26k thms, spot-PURE); **novelty is not** — the publishability
  audit finds "no new mathematics" anywhere; the one artifact is the ∅-axiom corpus.
- The **Proof-ISA is a classification scaffold, not an engine** (lifts are post-hoc
  relabels; only original demo is Euclid; "geometrization" = `8−3=5`).
- Physics is a **test surface**, not the goal.

## The reorientation (what counts as progress now)
Stop adding isolated ∅-axiom re-derivations of classical theorems (novelty ≈ 0, and
type-mismatched to the primacy claim). Two lines instead:
- **Line A — genuine cross-domain unifications**: a unification counts only when it
  carries a *proven map / shared engine* (never a value-coincidence, never prose).
  This is the only artifact that tests *unity across domains*, not constructivity per
  domain — the operational content of no-exterior.
- **Line B — exposure**: the no-exterior claim cannot be falsified from inside; ship
  the formalization paper (already scoped in the publishability audit) and run one
  pre-registered, time-boxed ISA attack on a recognized open problem.

## Closed this session (Line A, first deposit)
**COUNT-duality** — `lean/E213/Lib/Math/Combinatorics/CountDuality.lean` (7/7 PURE).
The Erdős union bound (Ramsey, row read) and the LYM inequality (Sperner, column
read) are **proven** to be the two marginals of one incidence double-count
(`incidence_balance` = `Sperner.sumOver_swap`). The union bound is re-derived
*through* the swap it previously bypassed (`union_bound_via_balance`); `count_duality`
carries both faces. Converts the corpus's narrated "two faces, one matrix"
(`PROOF_ISA.md`, `counting_as_cardinality.md`) into a theorem.
- Essay: `theory/essays/proof_isa/count_duality.md` (+ INDEX entry).
- Wired into `lean/E213/Lib/Math/Combinatorics.lean`; umbrella build green.
- `tools/scan_axioms.py E213.Lib.Math.Combinatorics.CountDuality` → 7 pure / 0 dirty.

## Next (priority order, Line A)
1. **Two-cut antipode**: binomial inversion ↔ Möbius inversion as one antipode under
   `Δ_+`/`Δ_×` — both sides PURE, only the bridge unwritten
   (`research-notes/frontiers/convolution_comultiplication_crossdomain.md`).
2. **`e`'s two homes** (factorial `Σ1/k!` and `lcm(1..N)~eᴺ`) as one prime-power
   identity — `NumberTheory.FactorialLcmIdentity.vp_factorial_eq_sum_vp_lcm` exists;
   state it as the cross-domain identity it is.
3. **A cross-domain `LensIso` + transport** via `lensIso_iff_kernel_eq`
   (`Lens/Unified.lean`) between two independently-built domains, a theorem
   transported across. Guard: avoid the tautology (same `Raw`) and the
   genius-requiring extreme — aim at provable-but-not-definitional kernel coincidence
   (COUNT-duality is the template: two enumerations, one swap).

## Line B (parallel, when ready)
- The ITP/CPP/JAR formalization paper, residue-metaphysics stripped (audit §"the one
  publishable kernel").
- One time-boxed, pre-registered ISA attack on a recognized open problem.

## Verify
```
cd lean && lake build E213.Lib.Math.Combinatorics   # green
python3 tools/scan_axioms.py E213.Lib.Math.Combinatorics.CountDuality   # 7 pure / 0 dirty
```

## File map
```
lean/E213/Lib/Math/Combinatorics/CountDuality.lean         ← NEW (7 PURE): the unification
lean/E213/Lib/Math/Combinatorics.lean                      ← import + docstring
theory/essays/proof_isa/count_duality.md                   ← NEW essay
theory/essays/proof_isa/INDEX.md                           ← entry
research-notes/frontiers/the_substance_test.md             ← NEW: convening synthesis + 진의 + reorientation
```
