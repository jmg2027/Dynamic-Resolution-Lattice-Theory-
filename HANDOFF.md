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

### 5. Gaussian disc-`−4` arc — Fermat's two-square theorem CLOSED (∅-axiom)
`p ≡ 1 (mod 4) ⟹ p = a² + b²`, end to end, no `propext`/Classical/`native_decide`.  Built by
generalising the disc-`−3` engine (the `PolyRoot` Lagrange machinery is field-agnostic):
- `ModArith/NonFixedExists.exists_nonfixed_gen` — exponent-generic non-residue existence.
- `ModArith/QRNegOne.qr_neg_one` — Pillar I: `p ≡ 1 mod 4 ⟹ ∃ x, p ∣ x²+1` (`−1` a QR), via
  a non-`(p−1)/2`-fixed element + FLT + Euclid.
- `Integer/GaussianDivStep.zi_div_step` — `ℤ[i]` is norm-Euclidean (covering radius² = 1/2).
- `Integer/GaussianDvd` — divisibility↔norm bridge in `ℤ[i]`.
- `Integer/GaussianGcd.gcd_bezout` — Euclidean gcd + Bezout in `ℤ[i]` (fuel induction).
- `Integer/GaussianSplit.split_form` — Pillar II: `p ∣ x²+1 ⟹ p = a²+b²`.
- `Integer/GaussianTwoSquare` — ★ `two_square_of_mod4` (Fermat's theorem) + the necessity
  direction (`form4_residue`: `a²+b² ≢ 3 mod 4`) and ★ `two_square_iff`:
  for an odd prime `p`, `p ≡ 1 (mod 4) ⟺ p = a²+b²` (axiom-free).

### 6. Parametric `ℤ[√−D]` descent — the disc generalised over the radicand (∅-axiom)
The Gaussian descent lifted to a single parametric family `ZSqrt D` (norm `re² + D·im²`),
norm-Euclidean exactly for `D ∈ {1,2}` (covering radius² `(1+D)/4 < 1`):
- `Integer/ZSqrtNegDivStep.zsqrt_div_step` — `1 ≤ D ≤ 2` ⟹ `ℤ[√−D]` norm-Euclidean (one proof,
  `ring_intZ` with `D` a free variable).
- `Integer/ZSqrtNegSplit.split_form` — `1 ≤ D ≤ 2`, `p ∣ x²+D`, `¬(p:ℤ)∣1` ⟹ `p = a²+D·b²`;
  `split_form_two` instantiates `D = 2` (`p = a²+2b²`, disc-`−8`), `D = 1` recovers Gaussian.
- **Open boundary** (made precise): the descent form reaches `ℤ[√−D]` only for `D ≤ 2`
  (`D = 3` needs the half-integer ring `ℤ[ω]`); the Pillar-I residue input (which primes have
  `−D` a QR) is unconditional only for `D = 1,3` (single order argument) — `D = 2` (`p ≡ 1,3
  mod 8`) needs the quadratic character of `2`, so the `D = 2` arc is the conditional split
  `p ∣ x²+2 ⟹ p = a²+2b²`, not yet the congruence iff.

### 7. Sharpness — the `ℤ[√−D]` descent bound `D ≤ 2` is optimal (∅-axiom, a NEGATIVE result)
`Integer/ZSqrtNegSharp.descent_false_at_three`: no universal `p ∣ x²+3 ⟹ p = a²+3b²` holds —
witness `2 ∣ 1²+3` yet `2 ≠ a²+3b²` (`form_a2_3b2_mod4`: `a²+3b² ∈ {0,1,3} mod 4`, never `2`).
The same finite engine that *constructs* representations (`D≤2`) here *constructs the
counterexample* at `D=3`, where the covering radius `(1+D)/4` crosses `1` (`ℤ[√−3] ⊊ ℤ[ω]` not
integrally closed).

### 8. Lagrange's four-square theorem — CLOSED (∅-axiom)
`NumberTheory/FourSquare.nat_isSum4 : ∀ n, isSum4 ↑n` is axiom-free — the first repo result
needing an **additive** pigeonhole + an **all-`n`** descent, reached by neither the
multiplicative counting-bound nor the commutative CD machinery.  35 PURE / 0 dirty.
- `NumberTheory/FourSquareSeed.four_square_seed` (★ Pillar I, axiom-free, **constructive**):
  odd prime `p = 2m+1` ⟹ `∃ x y ≤ m, p ∣ x²+y²+1`.  The repo's first additive pigeonhole
  (`no_inj_lt` on `gval`); witness via a bounded 2-D search refuted in its `none`-branch (no
  Classical).  Dodges two propext traps (`Decidable (p∣a)` via `a%p`; the `Int.natAbs` triangle
  by staying in ℕ).  16 PURE incl. `sq_distinct`, `nat_prime_dvd_mul`.
- `NumberTheory/FourSquare` (Pillar II, Euler-descent route — over ℤ, no quaternion gcd):
  `four_sq_id` (Euler's identity), `isSum4_mul`, `descent_core` (`m·p=Σaᵢ², m·r=ΣAᵢ² ⟹
  p·r=Σdⱼ²`); the parity-split descent (`halve_step` even-`m`, `odd_descent` strict `r<m`,
  avoiding the `r=m` mod-8 crux); `descent_rec` (fuel recursion); `seed_multiple`
  (`k·p = x²+y²+1²+0²`, `1≤k<p`); `dvd_dec`/`searchDiv`/`exists_prime_factor` (constructive
  least-divisor prime factorization); `prime_isSum4`; ★`nat_isSum4` (all `n`).
- **Follow-on**: promote the closed `FourSquare`/`FourSquareSeed` sub-tree to `theory/` per
  `PROMOTION_CRITERIA`.

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
Lagrange's four-square theorem is **CLOSED** (`FourSquare.nat_isSum4`, ∅-axiom).  `E213.Lib.Math`
aggregator builds clean (fixed a pre-existing misplaced-import break in `Analysis/ODE.lean`).

Follow-ons: promote the closed `FourSquare`/`FourSquareSeed` + PolyRoot / Eisenstein-converse /
Gaussian / ℤ[√−D] sub-trees to `theory/` per `PROMOTION_CRITERIA`; the disc-`−8` congruence iff
(needs the quadratic character of `2`).

## (archived) Phase 3 plan
Phase 3 (Lagrange's root bound mod `p`) was the single classical input gating the full split
converse.  It is a self-contained sub-marathon (polynomial-root theory over `ℤ/p`); start from
the FLT foothold and the exact reduction recorded in the marathon note.
