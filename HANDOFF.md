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

### 4. Phase 3 + full assembly — the split converse is CLOSED (∅-axiom)
`p ≡ 1 (mod 3) ⟹ ∃ a b : Int, ↑p = a² − ab + b²`, end to end, no `propext`/Classical/
`native_decide`.  Pillar I (the primitive-cube-root input) built bottom-up:
- `PolyRoot/FactorTheorem` (3) — polynomials as coeff lists, synthetic division, `factor_eval`.
- `PolyRoot/IntEuclid` (8) — `int_euclid` (Euclid's lemma over ℤ via natAbs).
- `PolyRoot/RootBound` (2) — ★`eval_zero`: **Lagrange's root bound** (eval-vanishing form).
- `PolyRoot/CyclotomicPoly` (7) — the polynomials `Xᵐ` and `Tᵐ − 1` (constant coeff `−1`).
- `PolyRoot/ResidueList` (7) — the nonzero residues `[1, p)` as a distinct-mod-`p` root list.
- `ModArith/EisensteinCubeRoot` (1) — `p ∣ z(z²+3z+3), p∤z ⟹ ∃ x, p∣x²+x+1`.
- `ModArith/CubeFromFLT` (6) — FLT bridge: a non-cube-fixed `aᵐ` ⟹ `∃ x, p∣x²+x+1`.
- `ModArith/NonFixedExists` (7) — ★`exists_nonfixed`: a non-cube-fixed element exists,
  produced by a **constructive bounded search** refuted in its `none`-branch by `eval_zero`.
- `Integer/EisensteinConverse` (9) — ★`eisenstein_split_converse`, assembling both pillars
  (FLT primality bridged from divisor-dichotomy via `prime_coprime`/`modBezout_gcd_one`);
  plus the **necessity** direction (`form_mod3`: `a²−ab+b² ≢ 2 mod 3` over ℤ via
  `4·form = (2a−b)²+3b²`) and the full ★`eisenstein_iff`:
  for a prime `p ≠ 3`, `p ≡ 1 (mod 3) ⟺ ∃ a b : Int, ↑p = a²−ab+b²`.

## Open Problems (Priority Order)

### 1. `¬ (p:ℤ) ∣ 1` for primes — RESOLVED inside `eisenstein_split_converse`
Now discharged purely via `int_dvd_to_nat` + `le_of_dvd_pos` (`(p:ℤ)∣1 ⟹ p ≤ 1`), no longer a
loose hypothesis at the converse's top level.  (`split_form` still carries it as a parameter;
the converse supplies it.)

### 2. (carried) the orbit-realizability kernel `H`, continuant program E2–E5 — see prior notes.

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
The split iff is fully closed (both directions, ∅-axiom).  Natural follow-ons: (a) promote the
closed PolyRoot + Eisenstein-converse sub-tree to `theory/` per `PROMOTION_CRITERIA`;
(b) generalise Lagrange's bound + the cyclotomic-existence pattern to the disc-`−4` (Gaussian,
`p ≡ 1 mod 4` ⟺ `p = a²+b²`) and other class-number-one imaginary quadratic fields — the
`PolyRoot` library + `centered_div` balanced-residue tooling are field-agnostic and ready.

## (archived) Phase 3 plan
Phase 3 (Lagrange's root bound mod `p`) was the single classical input gating the full split
converse.  It is a self-contained sub-marathon (polynomial-root theory over `ℤ/p`); start from
the FLT foothold and the exact reduction recorded in the marathon note.
