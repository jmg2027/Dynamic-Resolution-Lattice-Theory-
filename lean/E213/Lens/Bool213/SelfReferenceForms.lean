import E213.Lens.Bool213.Raw
import E213.Theory.Raw.API
import E213.Meta.Nat.PureNat

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

§3 makes the oscillation *quantitative*: the `not`-orbit of a Bool value returns to its
start at exactly the even iterates (`bool_notIter_eq_self_iff`: `notIter k r = r ↔ even k`),
so the minimal period is exactly `2` (`bool_min_period_two`) — never period `1`, the liar
made precise.  This is the oscillation-side analog of the convergence-side quantitative
bound (`Lambek.descent_chain_drops`) and the escape-side concrete witness
(`ResidueReentry.reentry_undifferentiated_nonfixed`).

§4 pins the *exact boundary*: the same `not = swap` is fixed-point-free **only** on the
Bool values.  Off them it settles — the symmetric between `a / b` is swap-invariant
(`not_fixes_between`, period `1`, `between_not_bool`).  So "the Bool-Lens reads exactly the
period-2 region" is the theorem `oscillation_region_is_bool`.

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

/-! ## §3 — quantitative oscillation: the Bool orbit has period *exactly* 2

`bool_not_no_fixed_point` says the period is not `1`; `not_not` says it divides `2`.  Here
the two combine into the precise statement: the `not`-orbit of a Bool value returns to its
start at **exactly** the even iterates — period exactly `2`, never settling, the liar's
oscillation made quantitative.  This is the oscillation-side analog of the convergence-side
`Lambek.descent_chain_drops` (the unit step accumulates) and the escape-side
`ResidueReentry.reentry_undifferentiated_nonfixed` (the named non-fixed-point): each of the
three outcomes of the one self-pointing now has its quantitative / concrete form. -/

/-- `notIter k` = `not` applied `k` times.  The orbit of one self-referential turn under
    the Bool negation. -/
def notIter : Nat → Raw → Raw
  | 0,     r => r
  | k + 1, r => not (notIter k r)

/-- An **even** number of `not`s is the identity (on every Raw — `not` is involutive):
    `notIter (2k) r = r`.  The orbit closes at every even iterate. -/
theorem notIter_even (k : Nat) (r : Raw) : notIter (2 * k) r = r := by
  induction k with
  | zero => rfl
  | succ n ih =>
      show notIter (2 * (n + 1)) r = r
      rw [Nat.mul_succ]
      show not (not (notIter (2 * n) r)) = r
      rw [not_not, ih]

/-- An **odd** number of `not`s is one `not`: `notIter (2k+1) r = not r`. -/
theorem notIter_odd (k : Nat) (r : Raw) : notIter (2 * k + 1) r = not r := by
  show not (notIter (2 * k) r) = not r
  rw [notIter_even]

/-- The orbit has only **two** points: every iterate is either `r` or `not r`. -/
theorem notIter_orbit (k : Nat) (r : Raw) : notIter k r = r ∨ notIter k r = not r := by
  rcases E213.Meta.Nat.PureNat.nat_dichotomy k with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact Or.inl (hj ▸ notIter_even j r)
  · exact Or.inr (hj ▸ notIter_odd j r)

/-- ★★ **Period exactly 2 on the Bool values.**  For a Bool value `r` (`isBool r`), the
    `not`-orbit returns to `r` **iff** the iterate count is even: `notIter k r = r ↔
    isEven k`.  The forward direction uses `not r ≠ r` (`bool_not_no_fixed_point`) to rule
    out the odd iterates; so the orbit never settles at an odd step — period exactly `2`. -/
theorem bool_notIter_eq_self_iff (r : Raw) (h : isBool r = true) (k : Nat) :
    notIter k r = r ↔ E213.Meta.Nat.PureNat.isEven k = true := by
  rcases E213.Meta.Nat.PureNat.nat_dichotomy k with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst hj
    exact ⟨fun _ => E213.Meta.Nat.PureNat.isEven_two_mul j, fun _ => notIter_even j r⟩
  · subst hj
    constructor
    · intro he
      rw [notIter_odd j r] at he
      exact absurd he (bool_not_no_fixed_point r h)
    · intro he
      rw [E213.Meta.Nat.PureNat.isEven_two_mul_succ j] at he
      exact Bool.noConfusion he

/-- ★★ **The minimal period is exactly 2.**  On a Bool value: the orbit does **not** close
    at `1` (`notIter 1 r ≠ r`) but **does** close at `2` (`notIter 2 r = r`).  The liar
    oscillates with period `2` — period `1` (settling) is excluded, period `2` is attained. -/
theorem bool_min_period_two (r : Raw) (h : isBool r = true) :
    notIter 1 r ≠ r ∧ notIter 2 r = r :=
  -- `notIter 1 r` reduces to `not r`; `notIter 2 r` to `notIter (2*1) r` (defeq).
  ⟨bool_not_no_fixed_point r h, notIter_even 1 r⟩

/-! ## §4 — the exact boundary: `not` is fixed-point-free *exactly* on the Bool values

The oscillation is the Bool-Lens reading.  Off the Bool values, the same `not = swap` is
not fixed-point-free: the symmetric "between" of the two atoms, `a / b`, is swap-invariant
(period `1`, settled).  So the period-2 region is *exactly* the Bool image — fixed-point-free
on `{T, F}`, with a concrete fixed point `a / b` outside it. -/

/-- The atoms differ — propext-free (`Tree.noConfusion`). -/
private theorem a_ne_b : Raw.a ≠ Raw.b :=
  fun e => E213.Term.Internal.Tree.noConfusion (congrArg Subtype.val e)

/-- ★★ **`not` fixes the symmetric between `a / b`.**  `not = swap` swaps the two atoms, so
    it sends `a / b` to `b / a = a / b` (canonical): a period-`1` fixed point of `not`,
    *outside* the Bool values.  The settled (convergent) outcome of the same turn, on the
    undifferentiated-between rather than on a Bool value. -/
theorem not_fixes_between : not (Raw.slash Raw.a Raw.b a_ne_b) = Raw.slash Raw.a Raw.b a_ne_b := by
  show Raw.swap (Raw.slash Raw.a Raw.b a_ne_b) = _
  rw [Raw.swap_slash]
  -- `swap a ≡ b`, `swap b ≡ a` (both `rfl`); the proof arg is irrelevant, so the goal is
  -- defeq to `slash b a _ = slash a b _`, closed by `slash_comm`.
  exact (Raw.slash_comm Raw.a Raw.b a_ne_b).symm

/-- The between `a / b` is not a Bool value: `isBool (a / b) = false` (a slash is neither
    atom). -/
theorem between_not_bool : isBool (Raw.slash Raw.a Raw.b a_ne_b) = false := by
  unfold isBool T F
  rw [decide_eq_false (Raw.slash_ne_a Raw.a Raw.b a_ne_b),
      decide_eq_false (Raw.slash_ne_b Raw.a Raw.b a_ne_b)]
  rfl

/-- ★★★ **The period-2 region is exactly the Bool values.**  `not` is fixed-point-free on
    every Bool value (`bool_not_no_fixed_point`, period 2), and has a concrete fixed point
    off them — the symmetric between `a / b` (`not_fixes_between`, period 1, `between_not_bool`).
    So "the Bool-Lens reads exactly the period-2 region" is a theorem: the oscillation is the
    Bool-Lens facet, the settling its complement. -/
theorem oscillation_region_is_bool :
    (∀ r : Raw, isBool r = true → not r ≠ r)
    ∧ (∃ r : Raw, isBool r = false ∧ not r = r) :=
  ⟨bool_not_no_fixed_point,
   Raw.slash Raw.a Raw.b a_ne_b, between_not_bool, not_fixes_between⟩

end E213.Lens.Bool213.SelfReferenceForms
