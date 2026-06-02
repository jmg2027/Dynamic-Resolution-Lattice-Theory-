import E213.Lens.Bool213.Raw
import E213.Theory.Raw.API

/-!
# SelfReferenceForms — the two structural forms of Raw self-reference

The residue's self-reference admits two structurally distinct realisations, and the
distinction is what each Lens reads off the *same* underlying Raw self-pointing
(`seed/AXIOM/05_no_exterior.md` §5.2):

  * **Bool-style** (liar-like).  The negation `not = swap` is its own inverse —
    `not (not r) = r`, an involution of period `2` — yet it has **no fixed point on the
    Bool values**: `not r ≠ r` for `r ∈ {T, F}`.  The self-reference loops without
    grounding: oscillation, never settling at period `1`.
  * **Nat-style** (Lambek-like).  Every Raw *is* its own constructor readout
    (`decompose`: atom or slash of two distinct Raws) — a period-`1` self-fixed-point,
    the loop closing at the identity — and the slash descent is strictly well-founded
    (`depth_drops`), so the self-reference terminates at the atomic floor.  The loop is
    also a fixed point: it converges.

Both are readings of one Raw-level self-reference; the Bool-Lens extracts the
oscillatory aspect (every distinguishing is a binary choice that does not stand still),
the Nat-Lens the cumulative aspect (every distinguishing leaves a residue the next uses
as input).  `self_reference_two_forms` states the dichotomy as one ∅-axiom theorem: the
Bool form is involutive (period 2) and fixed-point-free on its values, the Nat form is a
period-1 self-fixed-point with well-founded descent.

The contentful new result is `bool_not_no_fixed_point` — that the Bool negation genuinely
has no fixed point on its values (the liar's "never settles"), which the involution
`not_not` alone does not give.  The Nat-style side reuses the Lambek closure.

All zero-axiom.
-/

namespace E213.Lens.Bool213.SelfReferenceForms

open E213.Theory (Raw)
open E213.Lens.Bool213.Raw (not isBool T F not_T not_F not_not T_ne_F)
open E213.Theory.Raw.Lambek (decompose depth_drops)

/-! ## §1 — the Bool-style liar: no fixed point on the Bool values -/

/-- ★★ **The Bool negation has no fixed point on its values.**  For every Bool213 value
    `r` (`isBool r`), `not r ≠ r`: `not T = F ≠ T` and `not F = T ≠ F`.  Together with
    the involution `not_not`, this is the liar structure — period `2`, never period `1`:
    the self-reference oscillates and never settles. -/
theorem bool_not_no_fixed_point (r : Raw) (h : isBool r = true) : not r ≠ r := by
  by_cases hT : r = T
  · subst hT; rw [not_T]; exact Ne.symm T_ne_F
  · by_cases hF : r = F
    · subst hF; rw [not_F]; exact T_ne_F
    · exfalso
      unfold isBool at h
      rw [decide_eq_false hT, decide_eq_false hF] at h
      exact absurd h (by decide)

/-! ## §2 — the dichotomy -/

/-- ★★★ **The two structural forms of Raw self-reference.**  One ∅-axiom statement of
    `05_no_exterior.md` §5.2:

    1. **Bool-style** (liar / oscillation): `not` is an involution (`not_not`, period 2)
       with **no** fixed point on the Bool values (`bool_not_no_fixed_point`, never
       period 1) — the loop never settles;
    2. **Nat-style** (Lambek / convergence): every Raw is its own constructor readout
       (`decompose`, a period-1 self-fixed-point), and the slash descent is strictly
       well-founded (`depth_drops`) — the loop closes at the identity and terminates at
       the atomic floor.

    Both read the *same* Raw self-pointing; the difference is which aspect the Lens
    extracts.  The Bool loop oscillates (period 2, no period-1 fixed point); the Nat loop
    converges (period-1 fixed point, well-founded). -/
theorem self_reference_two_forms :
    ((∀ r : Raw, not (not r) = r)
      ∧ (∀ r : Raw, isBool r = true → not r ≠ r))
    ∧ ((∀ r : Raw, r = Raw.a ∨ r = Raw.b ∨ ∃ (x y : Raw) (h : x ≠ y), r = Raw.slash x y h)
      ∧ (∀ (x y : Raw) (h : x ≠ y),
          x.depth < (Raw.slash x y h).depth ∧ y.depth < (Raw.slash x y h).depth)) :=
  ⟨⟨not_not, bool_not_no_fixed_point⟩, ⟨decompose, depth_drops⟩⟩

end E213.Lens.Bool213.SelfReferenceForms
