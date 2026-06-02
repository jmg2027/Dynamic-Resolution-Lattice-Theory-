# G171 — the Apéry zeta coefficient-degree statistic: ζ(2) degree 2, ζ(3) degree 3 (∅-axiom)

**Date**: 2026-06-02.  **Status**: 32 PURE theorems landed (`DepthAperyCubic` 23 +
`DepthQuadraticGeneric` 7 + `CasoratianStep` 2) + honest re-positioning + conjectures.
**Source of truth**: `lean/E213/Lib/Math/Cauchy/{DepthAperyCubic, DepthQuadraticGeneric,
CasoratianStep}.lean`.
**Anchors**: `G171_modular_tower_axes.md` (the e→π→ζ(3) row-3 "buildable next rung"),
`DivergenceDepth` (e depth 3), `DepthPiQuartic`/`DepthPRecursiveInstances` (π depth 6).

## What `G171_modular_tower_axes` asked for, and what actually closed

The earlier note proposed completing the depth tower **e = 3 → π = 6 → ζ(3) = ?** via the
Apéry recurrence
`n³aₙ = (34n³−51n²+27n−5)aₙ₋₁ − (n−1)³aₙ₋₂`, "the `DepthPiQuartic` analog (π depth 6) for
the 3-axis."  Three research agents (literature, repo-infra, red-team) sharpened this into
a **corrected, defensible** result.

### The correction: the honest tower is e → ζ(2) → ζ(3), by COEFFICIENT DEGREE

The literature agent's key findings (verified, sources below):

1. **The Casoratian (discrete Wronskian) of the Apéry recurrence** `Cₙ = aₙbₙ₋₁ − aₙ₋₁bₙ`
   satisfies `c₂(n)Cₙ = −c₀(n)Cₙ₋₁`, telescoping to `Cₙ = ±6/n³` for ζ(3) and `±5/n²` for
   ζ(2).  The constants `6`, `5` are **initial-condition artifacts** (`a₁b₀−a₀b₁`), NOT
   invariants — the invariant content is the **denominator exponent** `n³`, `n²`.

2. **The leading/middle coefficient `34n³−51n²+27n−5` plays NO role in the Casoratian** —
   it is `c₁`, which cancels identically in the Abel/Liouville derivation.  So it is *not*
   "the cross-determinant"; that role is the outer coefficients `c₂ = n³`, `c₀ = (n−1)³`.

3. **The "3, 6, 9" or "depth = 2 + degree → 9" pattern is numerology** — it requires the
   inconsistent degree-6 "product `n³(n−1)³`" reading and silently swaps the order-1
   Wallis-π for order-2 ζ(2).  The principled ζ(3) divergence depth is **5** (= 2 + 3,
   the Casoratian denominator `n³` of degree 3), if one insists on the "2 + degree" rule.

4. **The clean, citable invariant is the coefficient degree 1 → 2 → 3** for the minimal
   holonomic recurrences of **e, ζ(2), ζ(3)** — recurrence orders 1, 2, 2; Casoratian
   denominators `1`, `n²`, `n³`; matching the Rhin–Viola irrationality-measure records
   μ(ζ(2)) ≤ 5.4412, μ(ζ(3)) ≤ 5.5139.

So **π-via-Wallis (depth 6) and ζ(2)=π²/6-via-Apéry (degree 2) are two different
presentations of π-related constants** — depth is presentation-dependent (as HANDOFF
already flagged for the μ-thread).  The presentation-STABLE invariant is the minimal
holonomic recurrence's coefficient degree.

## The ∅-axiom result (20 PURE)

### `DepthAperyCubic` (18 PURE) — coefficient-degree tower

Every minimal-holonomic recurrence coefficient is a discrete polynomial whose
finite-difference depth equals its degree (concrete instances of `newton_polyDepth`'s
"degree d ⟹ depth d", pinned with the reflection prover `Meta.Nat.PolyNat`):

| constant | recurrence (order) | coefficients | `polyDepth` | floor = lead·(deg)! |
|---|---|---|---|---|
| ζ(2) | `(n+1)²uₙ₊₁=(11n²+11n+3)uₙ+n²uₙ₋₁` (2) | `(n+1)²`, `11n²+11n+3`, `n²` | **2** | `2=1·2!`, `22=11·2!`, `2` |
| ζ(3) | `n³aₙ=(34n³−51n²+27n−5)aₙ₋₁−(n−1)³aₙ₋₂` (2) | `n³`, `34n³−51n²+27n−5`, `(n−1)³` | **3** | `6=1·3!`, `204=34·3!`, `6` |

ζ(3)'s cubic coefficients are reindexed to the recurrence's domain `n = m+2`, clearing
truncation: `34n³−51n²+27n−5 ↦ 34m³+153m²+231m+117`, `n³ ↦ (m+2)³`, `(n−1)³ ↦ (m+1)³`.

Headline theorems: `zeta2_to_zeta3_degree_step` (`polyDepth 2 zeta2Top ∧ polyDepth 3
aperyTop`), `apery_cubic_rung`, `zeta2_quadratic_rung`.  **Exactness** (§5): the depths are
pinned *exactly* — `aperyTop_depth_exact` (`polyDepth 3 ∧ ¬ polyDepth 2`, the 2nd
difference `6m+18` still non-constant), `zeta2Top_depth_exact` (`polyDepth 2 ∧ ¬ polyDepth
1`).  So the degrees `2`, `3` are not just upper bounds.

### `CasoratianStep` (2 PURE) — why the degree is what the Wronskian sees

`casoratian_step`: for any `ℕ`-coefficients `c₂,c₁,c₀` and any two solution triples of
`c₂x₂=c₁x₁+c₀x₀`,

    c₂·(a₂·b₁) + c₀·(a₁·b₀) = c₂·(a₁·b₂) + c₀·(a₀·b₁)

— the subtraction-free form of `c₂Cₙ = −c₀Cₙ₋₁` (both sides reduce to
`c₁a₁b₁ + c₀a₀b₁ + c₀a₁b₀`).  The middle `c₁` cancels, so the Casoratian propagates by the
**outer** coefficients `c₂ = aperyTop`, `c₀ = aperyBot` alone.  This is the abstract reason
the tower invariant is `deg c₂ = deg c₀` (`= 3` for ζ(3), `2` for ζ(2)) and not the middle
coefficient, even though all three share a degree.

## What kills the "infinite tower" (the decisive falsifiers)

The degree coincidence `1 → 2 → 3` does **not** continue, and degree does **not** cause
irrationality.  Three web-confirmed exhibits:

| constant | min recurrence order | irrationality status |
|---|---|---|
| ζ(4) = π⁴/90 | **2** (Sorokin/Zudilin) | recurrence does **not** prove it (computation only) |
| ζ(5) | **3** (Zudilin) | recurrence does **not** prove it |
| Catalan β(2) | **2** (Zudilin 2003) | **OPEN** |

So an order-2 recurrence with polynomial coefficients is *neither sufficient for
irrationality* (Catalan) *nor unique to one degree* (ζ(4) is order 2, ζ(5) order 3).
Irrationality runs on growth rates + the `lcm(1..n)` bound, orthogonal to coefficient
degree.  **Conclusion:** ζ(3)'s degree-3 is the exception above the order-2, degree-2
Apéry-like (Zagier sporadic) family — not "rung 3 of a ladder."

## Conjectures (ranked, for the next rungs)

- **C-A — DONE this marathon (`DepthQuadraticGeneric`, 7 PURE).**  The Zagier/Almkvist–
  Zudilin "sporadic" Apéry-like family is uniformly order-2 with degree-2 coefficients
  (ζ(2)-Apéry, Domb, Almkvist–Zudilin, Catalan-β(2), … all `(an²+bn+c)`).
  `quadratic_polyDepth : ∀ A B C, polyDepth 2 (fun n => A·n²+B·n+C)` (floor `2A`) caps the
  entire family in one ∅-axiom statement, zero coefficient-transcription risk.  The
  multivariate-`Nat` obstruction (no `ring`/`omega` for nonlinear `Nat`; `poly_id` is
  univariate-in-`X`) was dissolved by the **Newton-form transfer**: `A·n²+B·n+C = newton
  (C, A+B, 2A) 2` (via `binom n 1 = n` and `n² = 2·binom n 2 + n`, both proved here for the
  local `binom`) carried along `polyDepth_congr` (a new reusable transfer lemma) +
  `newton_polyDepth`; only two small additive-AC reorder lemmas + the reflection prover's
  `(n+1)² = n²+2n+1` were needed by hand.

- **C-B: ζ(5)/ζ(4) and the degree-4/5 continuation.**  Zudilin's order-3 Apéry-like
  recursion for ζ(5) and the (conjectural) ζ(4) recurrence raise the **order** to 3 while
  the coefficient degree need not be 4 — so the "degree = zeta argument" tower may BREAK at
  ζ(4).  Conjecture (to falsify): the coefficient degree of the minimal recurrence for
  ζ(k) is `k` only for `k ∈ {2,3}`; at `k ≥ 4` the order grows and the clean degree-tower
  ends.  Worth checking the exact Zudilin recurrence degrees before claiming a tower beyond
  ζ(3).  **Do not extend the tower past ζ(3) without the explicit recurrence.**

- **C-C: Casoratian telescoping ⟹ `Cₙ·n³` constant (the 1/n³ floor) ∅-axiom.**  Iterate
  `casoratian_step` with `c₂ = aperyTop`, `c₀ = aperyBot` over a concrete ℕ-rescaled
  solution pair to prove `n³·Cₙ = (n−1)³·Cₙ₋₁` telescopes to a constant numerator — the
  ∅-axiom "Casoratian denominator is exactly `n³`" capstone.  Needs a ℕ-model of two
  Apéry solutions (or an abstract telescoping lemma over the step law).  Medium difficulty;
  the abstract telescoping lemma `∀n, c₂(n)Cₙ = c₀(n)Cₙ₋₁ ⟹ (∏c₂)Cₙ = (∏c₀)C₀` is itself
  a clean reusable result.

- **C-D (speculative, flagged): does the coefficient degree predict the irrationality
  measure?**  μ(ζ(2)) ≈ 5.44, μ(ζ(3)) ≈ 5.51 both sit just above 5 — NOT obviously tracking
  the degree 2 vs 3.  Conjecture is most likely **false** as stated (the agent flagged the
  rate modulus / divergence depth as orthogonal to μ, presentation-dependent).  Record as a
  caution, not a target.

## Red-team caveats to keep attached to any write-up

- "finite-difference depth = polynomial degree" is, for a single polynomial, the trivial
  fact `Δ^d(deg-d) = lead·d!`.  The **non-triviality** is (a) doing it ∅-axiom over ℕ with a
  truncating `diff` (the reflection prover + reindexing earn it), and (b) the *uniformity*
  across the recurrence coefficients + the Casoratian-cancellation that selects the outer
  coefficients.  Don't sell the per-polynomial depth as deep; sell the tower + the
  Wronskian grounding.
- e (order 1) in the same tower as ζ(2),ζ(3) (order 2) is a mild stretch — honest framing:
  it is the **degree-1 / order-1 base case**, the tower being indexed by coefficient degree,
  with the order jumping 1→2 between e and ζ(2).

## Sources

- van der Poorten, *A proof that Euler missed… Apéry's proof of the irrationality of ζ(3)*
  (Math. Intelligencer 1979) — the recurrences + the `±6/n³` Casoratian.
- Beukers (1979), Legendre/integral form.  Rhin–Viola (2001), *The group structure for
  ζ(3)*, Acta Arith. — μ(ζ(3)) ≤ 5.5139, μ(ζ(2)) ≤ 5.4412.
- Zudilin, *A third-order Apéry-like recursion for ζ(5)* (arXiv:math/0206178).
- Zagier, *Integral solutions of Apéry-like recurrence equations* — the sporadic family.
