import E213.Lib.Math.Algebra.Mobius213.Px.PnFibonacciUniversal
import E213.Lib.Math.Algebra.Mobius213OneAsGlue
import E213.Meta.Tactic.NatHelper

/-!
# RatioLensFounding — `ℚ` is the ratio rung, and its coprimality is `det P = NS − NT = 1`

`seed/AXIOM/06_lens_readings.md` §6.7 founds `ℚ` by *"taking ratios of chain readings, with the
coprimality condition that §3.5's `det P = 1` already encodes algebraically."*  The distinctive
213 content is not the generic field-of-fractions construction; it is that **the ratio's
lowest-terms (coprimality) condition is exactly the unimodular determinant `det P = NS − NT = 1`.**

This file makes that a theorem.  The convergent matrix `Pⁿ = [[Q00, Q01],[Q01, Q11]]` reads the
self-pointing as a ratio `Q01/Q00` (or `Q00/Q01`), and its determinant is the unit:
`Q00·Q11 − Q01² = NS − NT = 1` (`PnFibonacciUniversal.det_pn_universal`,
`Mobius213OneAsGlue.ns_minus_nt_is_one`).  A unimodular determinant is exactly the
coprimality / lowest-terms condition `ℚ` requires, so the ratio is automatically in lowest terms.

The coupling to `ℤ` is by *identity of the unit*, not by construction-dependency.  This file's
content is `Nat`-level — `Q00, Q01, Q11 : Nat → Nat`, `NS − NT` a `Nat` value (`= 1` by
`ns_minus_nt_is_one`) — and it imports neither `ℤ` (`Int213`) nor `DifferenceLensFounding`.  The
value `NS − NT = 1` is the *same unit* the difference-Lens carries as its `det P`
(`SharedUnitAcrossReadings.the_unit_is_one_across_readings`): the ratio rung does not *build on*
the `ℤ` rung, it *shares its unit*.  So `ℚ` and `ℤ` are sibling readings of the count, coupled at
the unit `1`, not stacked.  The ratio's own identity is cross-multiplication (`ratioEquiv`,
reflexive and symmetric below).
-/

namespace E213.Lens.Number.RatioLensFounding

open E213.Lib.Math.Algebra.Mobius213.Px.PnFibonacciUniversal (Q00 Q01 Q11 det_pn_universal)
open E213.Lib.Math.Algebra.Mobius213OneAsGlue (ns_minus_nt_is_one)
open E213.Lib.Physics.Simplex.Counts (NS NT)
open E213.Tactic.NatHelper (mul_assoc)

/-- The ratio identity: `p₁/p₂ = q₁/q₂` is cross-multiplication `p₁·q₂ = q₁·p₂`. -/
def ratioEquiv (p q : Nat × Nat) : Prop := p.1 * q.2 = q.1 * p.2

theorem ratioEquiv_refl (p : Nat × Nat) : ratioEquiv p p := rfl

theorem ratioEquiv_symm {p q : Nat × Nat} (h : ratioEquiv p q) : ratioEquiv q p := h.symm

/-! ## The ratio rung runs the same sandwich, transported by ×

Comparison is primitive only on the chain.  Each rung compares its
objects by transporting both into one chain frame via *its own fold's
action*, then running the chain's one sandwich.  The difference-Lens
transports by co-translation (`Int213.subNatNat_add_add`); the
ratio-Lens transports by co-scaling (`ratioEquiv_scale`) and compares
crossed readings `p₁·q₂` vs `q₁·p₂` — the join frame (common
denominator).  The sandwich itself is unchanged: ratio identity is its
collapse on the crossed readings (`ratioEquiv_of_cross_sandwich`,
mirroring `Int213.eq_of_sandwich`), and the coherence of the transport
is exactly transitivity, which holds by cancelling the middle reading —
possible only at positive resolution (`ratioEquiv_trans`). -/

/-- Co-scaling is the ratio fiber: `(a, b) ~ (k·a, k·b)`.  The ×-action
    analog of the difference-Lens fiber `(a,b) ~ (a+c, b+c)`.  (For
    `k = 0` the readout degenerates; the live fiber is `0 < k`,
    cf. `ratioEquiv_trans`'s positivity.) -/
theorem ratioEquiv_scale (a b k : Nat) :
    ratioEquiv (a, b) (k * a, k * b) := by
  show a * (k * b) = (k * a) * b
  rw [← mul_assoc a k b, Nat.mul_comm a k]

/-- Ratio identity is the chain sandwich collapsed on the *crossed*
    readings: same strict-inequality pair as `Int213.eq_of_sandwich`,
    transported into the join frame by ×. -/
theorem ratioEquiv_of_cross_sandwich {p q : Nat × Nat}
    (h1 : p.1 * q.2 < q.1 * p.2 + 1) (h2 : q.1 * p.2 < p.1 * q.2 + 1) :
    ratioEquiv p q :=
  Nat.le_antisymm (Nat.le_of_lt_succ h1) (Nat.le_of_lt_succ h2)

/-- ★★★ **The ratio layer is ×-witness-closed**: `(a/b)·x = c/d`
    always has the ratio-pair witness `x = (b·c, a·d)` — the
    componentwise product `(a·(b·c), b·(a·d))` cross-relates to
    `(c,d)`.  Slot-layer reading: ×-questions with ratio-pair slots
    mint no new numbers (each layer is closed under its own
    operation's slot-questions); the ^-question over the same slots
    is what mints the radicals. -/
theorem ratio_mul_witness (a b c d : Nat) :
    ratioEquiv (a * (b * c), b * (a * d)) (c, d) := by
  show (a * (b * c)) * d = c * (b * (a * d))
  rw [← mul_assoc a b c, ← mul_assoc b a d, Nat.mul_comm b a,
      ← mul_assoc c (a * b) d, Nat.mul_comm c (a * b)]

/-- ★★★ Transitivity of the ratio identity — the coherence of the
    ×-transport.  Cancelling the middle reading `q.2` needs `0 < q.2`:
    two transports compose only at positive resolution. -/
theorem ratioEquiv_trans {p q r : Nat × Nat} (hq : 0 < q.2)
    (h1 : ratioEquiv p q) (h2 : ratioEquiv q r) : ratioEquiv p r := by
  obtain ⟨p1, p2⟩ := p
  obtain ⟨q1, q2⟩ := q
  obtain ⟨r1, r2⟩ := r
  have hc1 : p1 * q2 = q1 * p2 := h1
  have hc2 : q1 * r2 = r1 * q2 := h2
  show p1 * r2 = r1 * p2
  have key : q2 * (p1 * r2) = q2 * (r1 * p2) := by
    calc q2 * (p1 * r2)
        = (q2 * p1) * r2 := (mul_assoc q2 p1 r2).symm
      _ = (p1 * q2) * r2 := by rw [Nat.mul_comm q2 p1]
      _ = (q1 * p2) * r2 := by rw [hc1]
      _ = q1 * (p2 * r2) := mul_assoc q1 p2 r2
      _ = q1 * (r2 * p2) := by rw [Nat.mul_comm p2 r2]
      _ = (q1 * r2) * p2 := (mul_assoc q1 r2 p2).symm
      _ = (r1 * q2) * p2 := by rw [hc2]
      _ = r1 * (q2 * p2) := mul_assoc r1 q2 p2
      _ = r1 * (p2 * q2) := by rw [Nat.mul_comm q2 p2]
      _ = (r1 * p2) * q2 := (mul_assoc r1 p2 q2).symm
      _ = q2 * (r1 * p2) := Nat.mul_comm (r1 * p2) q2
  have hle1 : q2 * (p1 * r2) ≤ q2 * (r1 * p2) := by
    rw [key]; exact Nat.le_refl _
  have hle2 : q2 * (r1 * p2) ≤ q2 * (p1 * r2) := by
    rw [key]; exact Nat.le_refl _
  exact Nat.le_antisymm
    (Nat.le_of_mul_le_mul_left hle1 hq)
    (Nat.le_of_mul_le_mul_left hle2 hq)

/-- ★★★ **The convergent's lowest-terms condition is the difference-Lens unit `det P = NS − NT`.**
    The convergent matrix `Pⁿ = [[Q00, Q01],[Q01, Q11]]` has determinant `Q00·Q11 − Q01² = NS − NT`,
    written additively `Q00·Q11 = Q01² + (NS − NT)` (`det_pn_universal` with the glue
    `ns_minus_nt_is_one`).  A unimodular determinant is exactly the coprimality / lowest-terms
    condition `ℚ` requires (`06_lens_readings §6.7` / `§3.5`: *the coprimality that `det P = 1`
    already encodes algebraically*).  So the ratio `Q01/Q00` is automatically in lowest terms,
    because the cross-determinant of its readings is the difference-Lens unit. -/
theorem convergent_lowest_terms_is_det (n : Nat) :
    Q00 n * Q11 n = Q01 n * Q01 n + (NS - NT) := by
  rw [ns_minus_nt_is_one]; exact det_pn_universal n

/-- ★★★ **`ℚ` is the ratio rung whose lowest-terms condition is the difference-Lens unit.**
    Bundle: the ratio identity is cross-multiplication (`ratioEquiv`, reflexive/symmetric); the
    convergent's lowest-terms condition is the matrix determinant `Q00·Q11 = Q01² + (NS − NT)`
    (`convergent_lowest_terms_is_det`), the unimodular/coprimality datum §6.7 says `det P` encodes;
    and `NS − NT = 1` is the difference-Lens unit.  So the `ℚ`-rung's defining coprimality is
    *derived from* the `ℤ`-rung's unit `det P = NS − NT`, not imposed — `ℚ` is the ratio reading
    whose well-definedness is the difference-Lens unit. -/
theorem ratio_lens_founds_on_difference :
    (∀ p : Nat × Nat, ratioEquiv p p)
    ∧ (∀ n, Q00 n * Q11 n = Q01 n * Q01 n + (NS - NT))
    ∧ (NS - NT = 1) :=
  ⟨ratioEquiv_refl, convergent_lowest_terms_is_det, ns_minus_nt_is_one⟩

end E213.Lens.Number.RatioLensFounding
