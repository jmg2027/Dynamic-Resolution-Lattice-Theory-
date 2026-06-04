# Marathon — the Eisenstein split converse (`p ≡ 1 mod 3 ⟹ p = a²−ab+b²`)

**Date**: 2026-06-04.  **Status**: open marathon (multi-session).  **Tier**: 1.

The capstone arc (`theory/math/numbertheory/eisenstein_period_arithmetic.md`) closed the
*necessary* side of the disc-`−3` representation (the χ₋₃ fingerprint) and the structural
foundations (class number one, the Euclidean covering bound).  This marathon targets the
*sufficient* side — the split converse — the disc-`−3` Fermat theorem:

> Every prime `p ≡ 1 (mod 3)` is a value of `a² − ab + b²` (`= N(π)` for a prime `π ∈ ℤ[ω]`).

## Two pillars

**Pillar I — quadratic-residue input.**  `p ≡ 1 (mod 3) ⟹ ∃ x, p ∣ x² + x + 1` (a
primitive cube root of unity mod `p`, i.e. an order-3 element of `(ℤ/p)ˣ`).  Needs the
cyclic structure of `(ℤ/p)ˣ` (primitive-root theorem) or a counting substitute.  The repo's
`ModArith` carries Fermat's little theorem universal in `p` (`UniversalFLT`) — a starting
foothold.

**Pillar II — Euclidean descent.**  `p ∣ x²+x+1` and `p ∤ (x − ω)` in `ℤ[ω]` ⟹ `p` is not
prime in `ℤ[ω]` ⟹ `p = N(π)`.  Rests on `ℤ[ω]` being norm-Euclidean (hence gcd / UFD).

## Phased plan

  - **Phase 1 — norm-Euclidean property of `ℤ[ω]`.**
    - 1a — centered integer division: `∀ A (N>0), ∃ q r, A = qN + r ∧ 2|r| ≤ N`.
    - 1b — the division step: `∀ α β, β ≠ 0 → ∃ γ ρ, α = βγ + ρ ∧ ‖ρ‖² < ‖β‖²`
      (round each coordinate of `α·conj β` by `‖β‖²`, then `covering_bound`).
  - **Phase 2 — gcd / divisibility in `ℤ[ω]`.**  Euclidean algorithm (well-founded on
    `‖·‖²`), gcd existence, the "non-prime ⟹ proper norm factor" descent.
  - **Phase 3 — Pillar I (the remaining wall).**  `p ≡ 1 mod 3 ⟹ ∃ x, p ∣ x²+x+1`.  An
    order-3 element of `(ℤ/p)ˣ`, equivalently `−3` a QR mod `p` (`4(x²+x+1) = (2x+1)²+3`).
    **All non-circular routes reduce to Lagrange's root bound** ("degree-`d` poly over `ℤ/p`
    has `≤ d` roots"): with FLT (`universal_flt_main`, available), every nonzero `a` has
    `(aᵐ)³ = a^(p−1) = 1` (`m = (p−1)/3`); if every `aᵐ = 1` then `Tᵐ−1` has all `p−1` nonzero
    roots, impossible as `m < p−1`, so some `aᵐ ≠ 1` is a primitive cube root.  The power-sum
    (`Σ aᵐ ≡ 0`) and cubing-map kernel-counting routes circle back to the same bound.
    Lagrange's bound needs a **polynomial-root library mod `p`** (evaluation, factor theorem,
    degree induction) — **not in the repo**; a major independent sub-marathon.
  - **Phase 4 — assembly (DONE for the ℤ[ω]-side).**  `split_form` (`EisensteinSplit`) closes
    `p ∣ x²+x+1 ⟹ p = a²−ab+b²`; Phase 3 supplies the `x`.

## Phase 3-core sub-marathon (Lagrange's root bound) — started

Goal: `∃ a ∈ [1,p), aᵐ ≢ 1 mod p` (then `cube_root_of_order3` finishes Phase 3).  Reduces to
Lagrange: `Tᵐ−1` (degree `m < p−1`) cannot have all `p−1` nonzero residues as roots.

  - **Factor theorem (DONE)** — `PolyRoot/FactorTheorem` (3 PURE): polynomials as coeff lists
    (`eval` Horner), synthetic-division `quot r` (only `+`,`×`), and ★`factor_eval`:
    `eval f x − eval f r = (x−r)·eval (quot r f) x` over `ℤ`.  So a root `r` peels a factor
    `(X−r)`, and (mod `p`, `p` prime, via Euclid) the other roots are roots of `quot r f`.
  - **Root bound (next)** — by induction: distinct roots `rs` of `f` ⟹ `rs.length ≤ deg f`.
    Design caveat: this `quot` keeps the list length (spurious trailing `0`); the induction
    needs an *effective degree* — either redefine `quot` to drop the trailing `0` (3-clause,
    re-prove `factor_eval`) or prove `eval (quot r f) = eval (quot r f).dropLast`.  Then the
    distinct-roots peel: `s ≠ r mod p`, both roots ⟹ `p ∣ eval (quot r f) s`.
  - **Existence + FLT connection (next)** — `Tᵐ−1` has leading coeff `1 ≢ 0`, so `≤ m` roots;
    `p−1 > m` residues ⟹ some `a` with `aᵐ ≢ 1`; `z = aᵐ−1`, `p ∣ (aᵐ)³−1 = z(z²+3z+3)` via
    `universal_flt_main` ⟹ `cube_root_of_order3`.

## Status — the ℤ[ω]-side is complete (∅-axiom)

Phases 0–2 and Phase 4 are closed: **45 PURE theorems, 0 dirty** across `OrderMul`,
`CenteredDivision`, `EisensteinEuclidean`, `EisensteinDivStep`, `EisensteinDvd`,
`EisensteinGcd`, `EisensteinSplit`, `PrimeSquareFactor`.  `split_form` gives the disc-`−3`
representation given the primitive-cube-root input.

**Phase 3 reduction also closed**: `ModArith.EisensteinCubeRoot.cube_root_of_order3` (1 PURE) —
`p ∣ z·(z²+3z+3)`, `p ∤ z` ⟹ `∃ x, p ∣ x²+x+1` (`x = z+1`), the Euclid step.  So Phase 3 now
reduces to exactly: (a) the **FLT-modular connection** (`z+1 = aᵐ`, `p ∣ (aᵐ)³−1` via
`universal_flt_main` — mechanical modular arithmetic, reachable), and (b) the **existence of a
non-cube-fixed element** (`∃ a, aᵐ ≢ 1 mod p`) — the lone genuine wall, equivalent to
Lagrange's root bound (a polynomial-root library mod `p`, a separate sub-marathon).

## Honest scope

Phase 1–2 are reachable with the pure `ℕ`/`ℤ` infrastructure (`div_add_mod`, `mod_lt`,
`covering_bound`, ZOmega `conj`/`normSq_mul`).  Phase 3 (primitive roots) is the deep pillar
and may not close from inside the reflection provers without a substantial cyclicity proof.
The transcendental period value remains separately out of reach (cubic AGM / `L(1,χ₋₃)`).

## Progress

  - **Phase 0 (done)** — `covering_bound` (`EisensteinEuclidean`): covering radius² ≤ 3/4 < 1.
  - **Phase 1a (DONE)** — `ModArith.CenteredDivision.centered_div` (2 PURE): centered division
    `∀ A (N>0), ∃ q r, A = qN + r ∧ 2|r| ≤ N`, built exactly per the scouting below.
  - **Phase 1b-infra (DONE)** — `Meta.Int213.OrderMul` (4 PURE): the pure `Int` multiplicative
    order lemmas the descent's final inequality needs (`mul_le_mul_right_nonneg`,
    `mul_le_mul_left_nonneg`, `int_sign` trichotomy, `mul_nonpos_of_nonneg_of_nonpos`).
  - **Phase 1b-foundation (DONE)** — `Integer.EisensteinDivStep` (3 PURE): the ZOmega-side
    helpers `normSq_pos` (`β≠0 → 0<‖β‖²`), `mul_conj_self` (`β·conjβ = ofInt‖β‖²`),
    `normSq_conj` (`‖conju‖²=‖u‖²`).  Note: `ring_intZ` cannot close `expr = 0` directly
    (reflection normalizer mismatch on `PE.C 0`) — route via `= q*q − q*q` + `sub_self_zero`.
  - **Phase 1b atomic pieces (ALL DONE, PURE)** — every brick the assembly needs is built and
    ∅-axiom: `CenteredDivision.centered_div_int` / `centered_div_int_sq` (`4r²≤N²`);
    `EisensteinEuclidean.covering_bound`; `EisensteinDivStep.{normSq_pos, mul_conj_self,
    normSq_conj}`; `ZOmega.{normSq_mul, conj_mul}`; `Int213.OrderMul.{mul_le_mul_*_nonneg,
    int_sign, mul_nonpos_*, ofNat_le_of_le, natAbs_cast_of_nonneg, mul_pos, int_lt_irrefl}`.
    Remaining is pure glue (`zomega_div_step`), blocked only on a Lean-engineering snag:
    `ring_intZ` does not see through ZOmega `.re`/`.im` projections of `mk` (gives
    `application type mismatch` in the reflection prover).  Two routes: (a) explicit `show`
    with the sub/neg-unfolded component forms (`u - v = u + -v`), then `ring_intZ`; (b)
    abstract `CommRing213 ZOmega` manipulation `ρ·conjβ = α·conjβ − γ·(β·conjβ) = α·conjβ −
    γ·ofInt N` via `mul_conj_self` + a `sub_mul`/`mul_comm`/`mul_assoc` chain.  The math is
    settled: `‖ρ‖²·N = rre²−rre·rim+rim²`, then `covering_bound` ⇒ `8‖ρ‖²N ≤ 6N²`, then the
    `int_sign` contradiction (`N ≤ ‖ρ‖² ⇒ 8N² ≤ 6N²` vs `0 < 2N²` by `mul_pos`/`int_lt_irrefl`).
  - **Phase 1b-assembly (DONE)** — `EisensteinDivStep.zomega_div_step` (6 PURE):
    `β≠0 → ∃ γ ρ, α = βγ + ρ ∧ ‖ρ‖² < ‖β‖²`.  **Phase 1 complete: `ℤ[ω]` is norm-Euclidean,
    ∅-axiom.**  Glue snag resolved: `rho_conj_eq` proved by explicit `show` with the
    sub/neg-unfolded components (`u−v = u+−v`) + `ring_intZ`; the final inequality extracted
    as `div_step_ineq` (no `set` — that tactic is Mathlib-only); `ring_intZ` leading-`0`
    limitation (`0−(P−N)`) routed through `zero_sub` + `-(P−N)=N−P`.
  - **Phase 2a (DONE)** — `Integer.EisensteinDvd` (3 PURE): the divisibility↔norm bridge.
    `normSq_dvd_of_dvd` (`a ∣ b ⟹ ‖a‖² ∣ ‖b‖²`, the workhorse turning a proper `ℤ[ω]`-factor
    of `p` into a proper `ℤ`-factor of `p²`); `unit_of_normSq_one` + `normSq_one_of_unit`
    (the full `unit ⟺ ‖·‖² = 1` — so a norm-`p` element is never a unit).
  - **Phase 2b (DONE)** — `EisensteinDvd` §2 (3 PURE): the descent setup.
    `dvd_components_of_dvd` (`ofInt p ∣ θ ⟹ p ∣ θ.re ∧ p ∣ θ.im`); `normSq_x_sub_omega`
    (`‖x−ω‖² = x²+x+1`); `not_dvd_x_sub_omega` (`p` non-unit ⟹ `p ∤ (x−ω)`, since its
    imaginary part is the unit `−1`).  So when `p ∣ x²+x+1`: `p ∣ ‖x−ω‖²` yet `p ∤ (x−ω)` —
    `p` is reducible in `ℤ[ω]`.
  - **Phase 2c-arith (DONE)** — `ModArith.PrimeSquareFactor.eq_p_of_mul_eq_psq` (1 PURE):
    `p` prime, `a·b = p²`, `2 ≤ a, b` ⟹ `a = p`.  The descent's conclusion-arithmetic: once
    `p = d·e` (non-units) is in hand, `p² = ‖d‖²·‖e‖²` with both `≥ 2` gives `‖d‖² = p`.
    Built on the `MarkovPrimeFactor` prime-power library (`dvd_prime_pow_cases`).
  - **Phase 2c-gcd-dvd (DONE)** — `EisensteinGcd` (2 PURE): `Dvd ZOmega` instance + the
    closure lemmas `zdvd_add` and ★`zdvd_combo` (`d∣β → d∣ρ → α=βγ+ρ → d∣α`, the Euclidean-step
    transfer carrying a common divisor up the recursion).
  - **Phase 2c-gcd-helpers (DONE)** — `Int213.OrderMul.natAbs_lt_of_lt` (`0≤a`, `a<b` ⟹
    `a.natAbs < b.natAbs`, the fuel-decrease, PURE).  Confirmed available + ∅-axiom: ZOmega
    `ofInt_one_mul`/`mul_ofInt_one` (hand-proved rw chains, tested), Ring213
    `add_zero`/`zero_mul`/`mul_zero` apply to ZOmega, `ofInt 0 = (0:ZOmega)` by rfl,
    `normSq_eq_zero_iff` for `‖β‖².natAbs=0 ⟹ β=0`.
  - **Phase 2c-gcd-main (DONE)** — `EisensteinGcd.gcd_bezout` (10 PURE): the `ℤ[ω]`
    Euclidean gcd + Bezout, `∀ n α β, ‖β‖².natAbs ≤ n → ∃ d s t, d = s·α + t·β ∧ d∣α ∧ d∣β`,
    by fuel-induction.  Snag resolved exactly as predicted: `bezout_rearrange` via a manual
    `Ring213` calc (`rearrange_helper` + `cassini_ring`-style steps), `ofInt`-unit algebra
    hand-proved (`ofInt_one_mul`/`mul_ofInt_one`), `Dvd ZOmega` instance + `zdvd_refl`/`zero`/
    `combo`, `normSq_natAbs_zero`.  **Phase 2c (gcd) complete.**
  - **Phase 2c-euclid (DONE)** — `EisensteinSplit.split_norm` (8 PURE): `p` prime,
    `p ∣ x²+x+1`, `¬(p:ℤ)∣1` ⟹ `∃ d, ‖d‖² = p` (= `a²−ab+b²`).  The gcd `d = gcd(ofInt p, x−ω)`
    is a proper non-unit divisor: non-unit (else `unit_bezout_dvd_conj` ⟹ `p∣conj(x−ω)`,
    impossible by `not_dvd_unit_im`), cofactor non-unit (else `p∣(x−ω)`); so `ofInt p = d·e`
    reducible, `norm_factor_eq_p` ⟹ `‖d‖²=p`.  **The entire ℤ[ω]-side is ∅-axiom.**
    Remaining: `¬(p:ℤ)∣1` (trivial for primes, deferred), Phase 3 (the `x`), Phase 4 (assemble).
  - **(ref) Phase 2c-euclid plan** — Euclid's lemma from `gcd_bezout`: `p ∤ (x−ω)` ⟹
    `gcd(p, x−ω)` is a unit ⟹ Bezout `1 = s·p + t·(x−ω)` ⟹ (multiplying by `conj(x−ω)`,
    using `p ∣ ‖x−ω‖²`) `p ∣ conj(x−ω)` — contradiction (also a non-unit imaginary part), so
    `gcd(p, x−ω)` is a non-unit proper divisor `d` of `p`; then `p = d·e` reducible and
    `eq_p_of_mul_eq_psq` ⟹ `‖d‖² = p`.  (Earlier fuel-induction plan retained below for ref.)
  - **(ref) Phase 2c-gcd-main plan** — `gcd_bezout` by **fuel-induction** on
    `‖β‖².natAbs` (avoids constructive-function refactor + Classical): `∀ n α β,
    ‖β‖².natAbs ≤ n → ∃ d s t, d = s·α + t·β ∧ d∣α ∧ d∣β`.  Base `β=0`: `d=α` (`s=ofInt 1,
    t=ofInt 0`).  Step: `zomega_div_step α β → α=βγ+ρ, ‖ρ‖²<‖β‖²`; recurse on `(β,ρ)`; `d∣α`
    by `zdvd_combo`; Bezout rearranges `s·β+t·(α−βγ) = t·α+(s−tγ)·β`.  Needs: a `One`-free
    base (ZOmega has no Lean `One` instance — use `ofInt 1`), the `0≤x<y ⟹ x.natAbs<y.natAbs`
    fuel-decrease (pure), and `normSq.natAbs=0 ⟹ β=0`.  Then Euclid's lemma + the reducibility
    `p = d·e`, closing with `PrimeSquareFactor.eq_p_of_mul_eq_psq` ⟹ `‖d‖² = p`.
    **Snag**: the 5-var Bezout identity `s·β+t·ρ = t·(βγ+ρ)+(s−tγ)·β` is NOT closeable by
    `ring_intZ` (`application type mismatch` — the reflection prover can't see through ZOmega
    `.re`/`.im` projections on an expression that large).  Prove it by a manual
    `Ring213`/`CommRing213` calc à la `EisensteinCrossDet.cassini_ring` (`mul_add`, `sub_mul`,
    `mul_assoc`, `mul_comm`, then the `cancel_lemma` add/neg pattern).
    Path: `centered_div_int` wrapper (β.normSq : Int>0 from `normSq_pos`); `γ = ⟨qre,qim⟩` from
    `centered_div` on `(α·conjβ).re/.im`; prove `ρ·conjβ = ⟨rre,rim⟩` (ext + ring_intZ, with
    `mul_conj_self`); `‖ρ‖²·N = eisForm rre rim` (`normSq_mul` + `normSq_conj`); `covering_bound`
    (needs `4r²≤N²` from `2|r|≤N` via a pure `ofNat_le` cast); then `‖ρ‖² < N` by the
    `int_sign` contradiction (`N ≤ ‖ρ‖² ⟹ 8N² ≤ 6N² ⟹ 2N² ≤ 0` vs `0 < N²`).
  - **Phase 1a (scouting record)** — centered division `∀ A (N>0), ∃ q r, A = qN + r ∧ 2|r| ≤ N`.
    Toolkit: pure Nat `AddMod213.div_add_mod` + `Nat.mod_lt` (both PURE) for the ordinary
    remainder, then center (subtract `N` when `2·(a%N) > N`).  **Purity caveat**: the core
    subtraction lemmas `Nat.sub_add_cancel`, `Nat.add_sub_cancel`, `Int.ofNat_sub` are
    `propext`-dirty — must route through the repo's pure replacements
    `NatRing213.nat_sub_add_cancel`, `NatRing213.nat_add_sub_self_right`,
    `Int213.Order.ofNat_sub_ofNat` (`ofNat b − ofNat a = subNatNat b a`).  Bound argument
    (`2(N−m) ≤ N` from `N < 2m`): `N−m ≤ m` via `Nat.sub_le_sub_right` (PURE) on `N ≤ 2m`,
    then `2(N−m) = (N−m)+(N−m) ≤ (N−m)+m = N`.  The negative-`A` case reduces by negation.
    Next increment: assemble this, then Phase 1b (the `ℤ[ω]` division step via `conj` +
    `normSq_mul` + `covering_bound`).
