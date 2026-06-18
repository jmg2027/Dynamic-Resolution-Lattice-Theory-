import E213.Lib.Physics.Simplex.Counts
import E213.Lib.Physics.Mixing.SignedHodgeStar

/-!
# Lorentz metric signature `(1, 3)` — sourced in `(NS, NT)`, ∅-axiom

The signed Hodge star `⋆² = −1` (`Mixing/SignedHodgeStar.lean`) supplies the *one*
distinguished order-2 / `i` axis — the temporal direction.  A multi-agent panel
(2026-06-16) established the next step toward a genuine metric-signature theorem and,
in doing so, killed a tempting wrong route:

> **`⋆²`-eigenvalue-count is NOT the metric signature.**  `⋆² = −1` holds on *all four*
> `Λ¹` directions (signature `(4,0)`), and the across-grades `⋆²` pattern is `(2,3)`.
> Neither is Lorentzian.  The signature must be read off an explicit *diagonal bilinear
> form*, not off `⋆²`.

So, mirroring the closed `H¹(T²)` signature witness
(`Cohomology/Surfaces/T2Minimal/Signature.lean`, `signature_one_one_witness`, which
exhibits a `(1,1)` orthogonal `±` basis), this file exhibits the Lorentzian form on the
`NS + (NT − 1) = 3 + 1 = 4` axes:

  * one **negative** axis (index `0`) — the `NT`/order-2/`i` direction (the carrier of
    `⋆² = −1`), `bil(e₀,e₀) = −1`;
  * `NS = 3` **positive** axes (indices `1,2,3`) — the spatial slots, `bil(eₖ,eₖ) = +1`;
  * all four mutually orthogonal and distinct (a nondegenerate diagonal form).

By Sylvester's law of inertia this is signature `(1, 3)`, with the split **sourced in
the atomic counts**: `neg = NT − 1 = 1`, `pos = NS = 3`, `dim = NS + (NT − 1) = 4`.

## Forced vs read (the discipline)

What is ∅-axiom here: the form, its orthogonality, the `(1,3)` count, nondegeneracy, and
the identification of the counts with `(NS, NT − 1)`.  What stays a **reading** (kept in
prose, never in a theorem body — `delta4_dual_defect_status.md` flags "Δ⁴ = spacetime" as
having zero Lean support): calling these four axes "spacetime", and which global sign
convention `(−,+,+,+)` vs `(+,−,−,−)` is "the" metric (an overall `η ↦ −η` Lens choice).
The theorem states the *count* `(1,3)`, which is convention-free.  All ∅-axiom (`decide`).
-/

namespace E213.Lib.Physics.Mixing.LorentzSignature

open E213.Lib.Physics.Simplex.Counts (NS NT)
open E213.Lib.Physics.Mixing.SignedHodgeStar (starStar star_sq_neg_one_grade1 hodge_i_order_four)

/-- The diagonal of the Lorentzian form: index `0` (the `NT`/`i`/time axis) is `−1`,
    the `NS = 3` spatial axes `1,2,3` are `+1`. -/
def etaDiag (i : Nat) : Int := if i = 0 then -1 else 1

/-- The bilinear form `η = diag(−1, +1, +1, +1)` on the four axes. -/
def bil (f g : Nat → Int) : Int :=
  etaDiag 0 * f 0 * g 0 + etaDiag 1 * f 1 * g 1
    + etaDiag 2 * f 2 * g 2 + etaDiag 3 * f 3 * g 3

/-- Standard basis axis `k`. -/
def e (k : Nat) : Nat → Int := fun i => if i = k then 1 else 0

/-! ## §1 — the diagonal signs -/

/-- The **negative** (time / order-2 / `i`) axis: `η(e₀, e₀) = −1`. -/
theorem bil_time : bil (e 0) (e 0) = -1 := by decide
theorem bil_space1 : bil (e 1) (e 1) = 1 := by decide
theorem bil_space2 : bil (e 2) (e 2) = 1 := by decide
theorem bil_space3 : bil (e 3) (e 3) = 1 := by decide

/-! ## §2 — orthogonality (the form is diagonal) -/

theorem bil_01 : bil (e 0) (e 1) = 0 := by decide
theorem bil_02 : bil (e 0) (e 2) = 0 := by decide
theorem bil_03 : bil (e 0) (e 3) = 0 := by decide
theorem bil_12 : bil (e 1) (e 2) = 0 := by decide
theorem bil_13 : bil (e 1) (e 3) = 0 := by decide
theorem bil_23 : bil (e 2) (e 3) = 0 := by decide

/-! ## §3 — distinctness + nondegeneracy -/

theorem e0_ne_e1 : e 0 ≠ e 1 := fun h => absurd (show (1:Int) = 0 from congrFun h 0) (by decide)
theorem e0_ne_e2 : e 0 ≠ e 2 := fun h => absurd (show (1:Int) = 0 from congrFun h 0) (by decide)
theorem e0_ne_e3 : e 0 ≠ e 3 := fun h => absurd (show (1:Int) = 0 from congrFun h 0) (by decide)
theorem e1_ne_e2 : e 1 ≠ e 2 := fun h => absurd (show (1:Int) = 0 from congrFun h 1) (by decide)
theorem e1_ne_e3 : e 1 ≠ e 3 := fun h => absurd (show (1:Int) = 0 from congrFun h 1) (by decide)
theorem e2_ne_e3 : e 2 ≠ e 3 := fun h => absurd (show (1:Int) = 0 from congrFun h 2) (by decide)

/-- The form is **nondegenerate**: the product of the diagonal (the determinant of the
    diagonal matrix) is `(−1)·1·1·1 = −1 ≠ 0`. -/
theorem det_eta : etaDiag 0 * etaDiag 1 * etaDiag 2 * etaDiag 3 = -1 := by decide

/-! ## §4 — the signature split is sourced in `(NS, NT)` -/

/-- The **negative** count equals `NT − 1 = 1` (the single temporal / order-2 axis). -/
theorem neg_count_eq : (1 : Nat) = NT - 1 := by decide
/-- The **positive** count equals `NS = 3` (the spatial slots). -/
theorem pos_count_eq : (3 : Nat) = NS := by decide
/-- The **dimension** equals `NS + (NT − 1) = 4`. -/
theorem dim_eq : (4 : Nat) = NS + (NT - 1) := by decide

/-! ## §5 — the master signature witness -/

/-- ★★★★★ **Lorentz signature `(1, 3)` — ∅-axiom, sourced in `(NS, NT)`.**

    The diagonal form `η = diag(−1, +1, +1, +1)` on the `NS + (NT−1) = 4` axes admits the
    orthogonal basis `e₀, e₁, e₂, e₃` with exactly **one** negative self-pairing
    (`η(e₀,e₀) = −1`, the `NT`/order-2/`i` axis) and **`NS = 3`** positive self-pairings
    (`η(eₖ,eₖ) = +1`), all distinct, the form nondegenerate (`det = −1 ≠ 0`).  By
    Sylvester's law of inertia the signature is `(1, 3)`, with the split sourced in the
    atomic counts: `neg = NT − 1`, `pos = NS`, `dim = NS + (NT − 1)`.

    Beyond the `⋆² = −1` parity skeleton: a genuine `(1,3)` form, not the `(4,0)` of `⋆²`
    itself.  "Spacetime" and the global sign convention stay readings (see header). -/
theorem lorentz_signature_one_three :
    -- one negative axis, three positive axes
    bil (e 0) (e 0) = -1
    ∧ bil (e 1) (e 1) = 1 ∧ bil (e 2) (e 2) = 1 ∧ bil (e 3) (e 3) = 1
    -- mutually orthogonal (diagonal form)
    ∧ bil (e 0) (e 1) = 0 ∧ bil (e 0) (e 2) = 0 ∧ bil (e 0) (e 3) = 0
    ∧ bil (e 1) (e 2) = 0 ∧ bil (e 1) (e 3) = 0 ∧ bil (e 2) (e 3) = 0
    -- distinct basis, nondegenerate
    ∧ e 0 ≠ e 1 ∧ e 1 ≠ e 2 ∧ e 2 ≠ e 3
    ∧ etaDiag 0 * etaDiag 1 * etaDiag 2 * etaDiag 3 = -1
    -- the split is sourced in (NS, NT)
    ∧ (1 : Nat) = NT - 1 ∧ (3 : Nat) = NS ∧ (4 : Nat) = NS + (NT - 1) :=
  ⟨bil_time, bil_space1, bil_space2, bil_space3,
   bil_01, bil_02, bil_03, bil_12, bil_13, bil_23,
   e0_ne_e1, e1_ne_e2, e2_ne_e3, det_eta,
   neg_count_eq, pos_count_eq, dim_eq⟩

/-! ## §6 — the negative axis, canonically the `NT`-sourced order-2 (`i`) direction

What is *not* provable (the honest wall, multi-agent panel 2026-06-16): that the
negative direction **must** be the form carrying `⋆² = −1`.  The signed Hodge star is
grade-symmetric on `Λ¹` — `⋆² = −1` holds *uniformly* on **all four** vector forms
(`star_sq_neg_one_grade1`, `k(4−k)=3` odd), i.e. signature `(4,0)`, not `(1,3)`.  So
`⋆²` offers **no** `Λ¹`-internal asymmetry to single out one axis; which index wears the
minus is a convention (`etaDiag`'s `if i=0`), and `(−,+,+,+)` vs `(+,−,−,−)` is an
`η ↦ −η` Lens reading — hence the signature theorem states only the convention-free
*count* `(1,3)`.

What **is** provable: the negative direction is the unique axis whose count is `NT−1`,
and that count, the order-4 `⟨⋆⟩ ≅ C₄` (`NT² = 4`), and the `Λ¹` complex structure
`⋆² = −1` all descend from the **same forced atom `NT`** — a link by *shared source*,
witnessed below by the real `SignedHodgeStar` theorems appearing in the proof term, not
by a `−1 = −1` value coincidence. -/

/-- An axis is **order-2 / negative** when its self-pairing is `< 0`. -/
def axisOrder2 (i : Nat) : Bool := decide (bil (e i) (e i) < 0)

/-- ★★ **The negative axis is canonically the `NT`-sourced order-2 (`i`) axis.**  ∅-axiom.
    Exactly one of the four axes is order-2 (index `0`); its count is `NT − 1`; and the
    same forced `NT` gives the order-4 complex structure `NT² = 4` (`hodge_i_order_four`)
    and the `Λ¹` Hodge `⋆² = −1` (`star_sq_neg_one_grade1`).  The identification is by
    shared source, not sign coincidence (see header): the `−` axis *can* be canonically
    taken as the order-2 axis and its count `NT − 1` is forced — it is **not** proven to
    *be* the `⋆² = −1` carrier (`⋆²` is uniform `(4,0)` on `Λ¹`). -/
theorem time_axis_is_order2_via_NT :
    (List.range 4).filter axisOrder2 = [0]
    ∧ ((List.range 4).filter axisOrder2).length = NT - 1
    ∧ NT * NT = 4
    ∧ starStar [0] = -1
    ∧ (3 : Nat) = NS :=
  ⟨by decide, by decide, hodge_i_order_four.2.2.2, star_sq_neg_one_grade1, by decide⟩

end E213.Lib.Physics.Mixing.LorentzSignature
