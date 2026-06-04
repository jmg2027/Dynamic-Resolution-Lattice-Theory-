# Session Handoff — 2026-06-04 (G167 Eisenstein/elliptic + split-converse marathon)

## Branch
`claude/eisenstein-elliptic-conjecture-Vvzcx` — pushed, clean.
`cd lean && lake build E213` ✓.  All new modules ∅-axiom (PURE).

## What Was Done This Session

### 1. G167 capstone — the cross-determinant's number field IS the modular trace field
`Real213/CrossDetTraceField` (20 PURE): the fixed-point form `fixForm M = (c, d−a, −b)` of a
Möbius map has discriminant `tr²−4` identically (`fixForm_disc_eq_traceDisc`); on the three
`SL(2,ℤ)` faces it recovers the signature reference forms (golden `+5` / cusp `0` / Eisenstein
`−3`), unifying the number-field and trace-field trichotomies; `fixForm_automorph` (monodromy
preserves its form); `disc_sign_is_line_cusp_curve` (the elliptic conjecture, exact).

### 2. The Eisenstein period's arithmetic (promoted to `theory/`)
`EisensteinFormCharacter` (χ₋₃ fingerprint), `EisensteinSplitting` (local split/ramified/inert
Euler factors + Brahmagupta multiplicativity), `EisensteinClassNumber` (`h(−3)=1`),
`EisensteinEuclidean` (`covering_bound`).  Promoted to
`theory/math/numbertheory/eisenstein_period_arithmetic.md` (gate H1–H4 satisfied).

### 3. The Eisenstein split-converse marathon — the ℤ[ω]-side COMPLETE (∅-axiom)
The disc-`−3` Fermat representation `p ∣ x²+x+1 ⟹ p = a²−ab+b²` — **45 PURE theorems**:
- `Int213/OrderMul` (9) — pure Int mul-order / sign / cast lemmas (core ones are propext-dirty).
- `ModArith/CenteredDivision` (4) — balanced integer division.
- `Integer/EisensteinEuclidean` (1) — `covering_bound` (covering radius² ≤ 3/4 < 1).
- `Integer/EisensteinDivStep` (6) — `zomega_div_step`: **ℤ[ω] is norm-Euclidean**.
- `Integer/EisensteinDvd` (6) — divisibility↔norm bridge + `unit ⟺ ‖·‖²=1`.
- `Integer/EisensteinGcd` (10) — `gcd_bezout`: the Euclidean gcd + Bezout (fuel-induction).
- `ModArith/PrimeSquareFactor` (1) — `p²=a·b, a,b≥2 ⟹ a=p`.
- `Integer/EisensteinSplit` (9) — Euclid's lemma + `split_norm`/`split_form`: the disc-`−3`
  representation, given `∃ x, p ∣ x²+x+1` and `¬(p:ℤ)∣1`.

## Open Problems (Priority Order)

### 1. Phase 3 of the split-converse marathon (the one remaining gate)
`p ≡ 1 mod 3 ⟹ ∃ x, p ∣ x²+x+1` — the primitive-cube-root input.  Reduces (non-circularly)
to **Lagrange's root bound** ("degree-`d` poly over `ℤ/p` has ≤ d roots") + FLT (have FLT,
`UniversalFLT.universal_flt_main`).  Needs a polynomial-root library mod `p` (evaluation,
factor theorem, degree induction) not in the repo — a major independent sub-marathon.  Plan +
exact argument in `research-notes/frontiers/eisenstein_split_converse_marathon.md`.

### 2. `¬ (p:ℤ) ∣ 1` for primes (trivial, deferred)
A pure proof was blocked by `ring_intZ`'s constant-folding limit (`1 + −1 ≠ C 0`); currently a
hypothesis of `split_form`.  Reachable via a pure `Int.natAbs_mul` (4-sign-case build).

### 3. (carried) the orbit-realizability kernel `H`, continuant program E2–E5 — see prior notes.

## Current Precision Results (0 free parameters)
Unchanged this session (math-frontier work, no physics-constant edits).  Canonical table:
`catalogs/physics-constants.md`.

## Three-tier state
- **Promotion this session**: `theory/math/numbertheory/eisenstein_period_arithmetic.md`
  (the G167 capstone + Eisenstein-period arithmetic).
- **Active scratchpad**: `research-notes/frontiers/eisenstein_split_converse_marathon.md`
  (split-converse marathon — ℤ[ω]-side done, Phase 3 open),
  `research-notes/frontiers/G167_crossdet_number_field_eisenstein_conjecture.md`.

## Next
Phase 3 (Lagrange's root bound mod `p`) is the single classical input gating the full split
converse.  It is a self-contained sub-marathon (polynomial-root theory over `ℤ/p`); start from
the FLT foothold and the exact reduction recorded in the marathon note.
