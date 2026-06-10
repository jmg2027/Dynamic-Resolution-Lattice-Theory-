import E213.Meta.Nat.Gcd213
import E213.Meta.Int213.OrderMul

/-!
# Rat213 — the signed lowest-terms normal form of a ratio pair

The signed composite of the two obstruction readouts
(`research-notes/frontiers/signed_rationals_normal_form.md`, brick 3):

```
  ratio pair  =  ( numerator : Int — sign carried by the difference-Lens )
              ×  ( denominator : Nat, positive — the ∣-order magnitude )
```

A nonpositive factor reverses `≤` (`OrderMul.mul_le_mul_right_nonpos`),
so cross-`≤` does not descend through the sign quotient; the ∣-order
data is orientation-blind.  Hence the normal form reads the sign off
the numerator (`Int` constructor = the swap readout) and keeps the
lowest-terms condition (`gcd213 a.natAbs b = 1`) on magnitudes.

Contents: `ratioEqZ` (the signed cross-equation, extending
`RatioLensFounding.ratioEquiv` to `Int` numerators), `IsLowest`,
and the two halves of exactness —

* `lowest_exists` : every positive-denominator pair normalizes
  (`Gcd213.gcd_strip_coprime`);
* `lowest_unique` : the normal form is unique
  (`Gcd213.coprime_repr_unique` on magnitudes; the mixed-sign cases
  die by constructor clash — the sign readout is rigid).

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Rat213

open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213
  (gcd213_dvd_left gcd213_dvd_right gcd_strip_coprime coprime_repr_unique
   mul_assoc_213)
open E213.Meta.Int213 (mul_mul_mul_comm mul_comm)
open E213.Meta.Int213.Order (sub_zero ofNat_succ_sub_one lt_of_sub_one_nonneg)
open E213.Meta.Int213.OrderMul (mul_le_mul_right_nonneg le_of_mul_le_mul_right_pos)

/-- The signed cross-equation: `a₁/b₁ = a₂/b₂` as
    `a₁ · b₂ = a₂ · b₁` over `Int` (denominators cast). -/
def ratioEqZ (a₁ : Int) (b₁ : Nat) (a₂ : Int) (b₂ : Nat) : Prop :=
  a₁ * Int.ofNat b₂ = a₂ * Int.ofNat b₁

/-- Lowest terms: coprime magnitudes, positive denominator. -/
def IsLowest (a : Int) (b : Nat) : Prop :=
  gcd213 a.natAbs b = 1 ∧ 0 < b

/-- `negOfNat x · ofNat y = negOfNat (x·y)`. -/
theorem negOfNat_mul_ofNat (x y : Nat) :
    Int.negOfNat x * Int.ofNat y = Int.negOfNat (x * y) := by
  cases x with
  | zero =>
    show Int.ofNat (0 * y) = Int.negOfNat (0 * y)
    rw [Nat.zero_mul]
    exact rfl
  | succ k => rfl

/-- `natAbs (negOfNat x) = x`. -/
theorem natAbs_negOfNat : ∀ (x : Nat), (Int.negOfNat x).natAbs = x
  | 0 => rfl
  | _+1 => rfl

/-- ★★★★ **Existence**: every positive-denominator signed pair has a
    lowest-terms representative, by stripping the gcd off the
    magnitude (`gcd_strip_coprime`) and carrying the sign across. -/
theorem lowest_exists (a : Int) (b : Nat) (hb : 0 < b) :
    ∃ a' b', IsLowest a' b' ∧ ratioEqZ a b a' b' := by
  obtain ⟨m', hm'⟩ := gcd213_dvd_left a.natAbs b
  obtain ⟨b', hb'⟩ := gcd213_dvd_right a.natAbs b
  have hg_pos : 0 < gcd213 a.natAbs b := by
    cases hgz : gcd213 a.natAbs b with
    | zero =>
      rw [hgz, Nat.zero_mul] at hb'
      exact absurd (hb' ▸ hb) (Nat.lt_irrefl 0)
    | succ g' => exact Nat.succ_pos g'
  have hb'_pos : 0 < b' := by
    cases b' with
    | zero =>
      rw [Nat.mul_zero] at hb'
      exact absurd (hb' ▸ hb) (Nat.lt_irrefl 0)
    | succ k => exact Nat.succ_pos k
  have hcop : gcd213 m' b' = 1 := gcd_strip_coprime rfl hg_pos hm' hb'
  cases a with
  | ofNat m =>
    refine ⟨Int.ofNat m', b', ⟨hcop, hb'_pos⟩, ?_⟩
    show Int.ofNat (m * b') = Int.ofNat (m' * b)
    have hm2 : m = gcd213 (Int.ofNat m).natAbs b * m' := hm'
    have key : m * b' = m' * b :=
      calc m * b'
          = (gcd213 (Int.ofNat m).natAbs b * m') * b' :=
            congrArg (· * b') hm2
        _ = (m' * gcd213 (Int.ofNat m).natAbs b) * b' := by
            rw [Nat.mul_comm (gcd213 (Int.ofNat m).natAbs b) m']
        _ = m' * (gcd213 (Int.ofNat m).natAbs b * b') :=
            mul_assoc_213 _ _ _
        _ = m' * b := congrArg (m' * ·) hb'.symm
    exact congrArg Int.ofNat key
  | negSucc n =>
    refine ⟨Int.negOfNat m', b', ⟨?_, hb'_pos⟩, ?_⟩
    · rw [natAbs_negOfNat]; exact hcop
    · show Int.negOfNat ((n + 1) * b') = Int.negOfNat m' * Int.ofNat b
      rw [negOfNat_mul_ofNat]
      have hm2 : n + 1 = gcd213 (Int.negSucc n).natAbs b * m' := hm'
      have key : (n + 1) * b' = m' * b :=
        calc (n + 1) * b'
            = (gcd213 (Int.negSucc n).natAbs b * m') * b' :=
              congrArg (· * b') hm2
          _ = (m' * gcd213 (Int.negSucc n).natAbs b) * b' := by
              rw [Nat.mul_comm (gcd213 (Int.negSucc n).natAbs b) m']
          _ = m' * (gcd213 (Int.negSucc n).natAbs b * b') :=
              mul_assoc_213 _ _ _
          _ = m' * b := congrArg (m' * ·) hb'.symm
      exact congrArg Int.negOfNat key

/-- ★★★★★ **Uniqueness**: two lowest-terms signed pairs naming the
    same ratio are equal.  Same-sign cases reduce to the magnitude
    statement `coprime_repr_unique`; mixed-sign cases are constructor
    clashes — with positive denominators the sign of the cross-product
    is the sign of the numerator, so the sign readout is rigid. -/
theorem lowest_unique {a₁ a₂ : Int} {b₁ b₂ : Nat}
    (h : ratioEqZ a₁ b₁ a₂ b₂)
    (h₁ : IsLowest a₁ b₁) (h₂ : IsLowest a₂ b₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  obtain ⟨hco₁, hb₁⟩ := h₁
  obtain ⟨hco₂, hb₂⟩ := h₂
  cases a₁ with
  | ofNat m₁ =>
    cases a₂ with
    | ofNat m₂ =>
      have h' : Int.ofNat (m₁ * b₂) = Int.ofNat (m₂ * b₁) := h
      have hnat : m₁ * b₂ = m₂ * b₁ := Int.ofNat.inj h'
      obtain ⟨hm, hb⟩ := coprime_repr_unique hnat hco₁ hco₂ hb₁
      exact ⟨congrArg Int.ofNat hm, hb⟩
    | negSucc n₂ =>
      exfalso
      cases b₁ with
      | zero => exact absurd hb₁ (Nat.lt_irrefl 0)
      | succ b₁' =>
        have h' : Int.ofNat (m₁ * b₂)
            = Int.negSucc ((n₂ + 1) * b₁' + n₂) := h
        exact Int.noConfusion h'
  | negSucc n₁ =>
    cases a₂ with
    | ofNat m₂ =>
      exfalso
      cases b₂ with
      | zero => exact absurd hb₂ (Nat.lt_irrefl 0)
      | succ b₂' =>
        have h' : Int.negSucc ((n₁ + 1) * b₂' + n₁)
            = Int.ofNat (m₂ * b₁) := h
        exact Int.noConfusion h'
    | negSucc n₂ =>
      cases b₁ with
      | zero => exact absurd hb₁ (Nat.lt_irrefl 0)
      | succ b₁' =>
        cases b₂ with
        | zero => exact absurd hb₂ (Nat.lt_irrefl 0)
        | succ b₂' =>
          have h' : Int.negSucc ((n₁ + 1) * b₂' + n₁)
              = Int.negSucc ((n₂ + 1) * b₁' + n₂) := h
          have hinj : (n₁ + 1) * b₂' + n₁ = (n₂ + 1) * b₁' + n₂ :=
            Int.negSucc.inj h'
          have hnat : (n₁ + 1) * (b₂' + 1) = (n₂ + 1) * (b₁' + 1) :=
            congrArg Nat.succ hinj
          obtain ⟨hm, hb⟩ := coprime_repr_unique hnat hco₁ hco₂ hb₁
          exact ⟨congrArg Int.negSucc (Nat.succ.inj hm), hb⟩

/-! ## The derived order and its descent through `ratioEqZ`

Cross-`≤` is only ×-equivariant on the positive cone
(`OrderMul.mul_le_mul_right_nonpos` is the reversal witness), so the
order below is stated with `Nat` (positive) denominators — the sign
already read off into the numerator — and *then* it descends through
the cross-equation. -/

/-- The signed cross-order: `a₁/b₁ ≤ a₂/b₂` as `a₁·b₂ ≤ a₂·b₁`. -/
def ratioLeZ (a₁ : Int) (b₁ : Nat) (a₂ : Int) (b₂ : Nat) : Prop :=
  a₁ * Int.ofNat b₂ ≤ a₂ * Int.ofNat b₁

/-- `0 < n → 0 < ofNat n` over `Int`. -/
theorem ofNat_pos : ∀ {n : Nat}, 0 < n → (0 : Int) < Int.ofNat n
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | n + 1, _ => by
    apply lt_of_sub_one_nonneg
    have hval : Int.ofNat (n + 1) - 0 - 1 = Int.ofNat n := by
      rw [sub_zero]; exact ofNat_succ_sub_one n
    rw [hval]
    exact ⟨n⟩

/-- ★★★★★ **The cross-order descends through the cross-equation** (one
    direction; `ratioLeZ_iff` for both).  Multiply into the join frame
    `B·D`, transport along the two cross-equations (`mul_mul_mul_comm`
    shuffles), cancel the positive frame
    (`le_of_mul_le_mul_right_pos`).  This is the well-definedness that
    fails outside the positive cone: sign-major first, cross-`≤` on
    magnitudes after. -/
theorem ratioLeZ_descends {a c a' c' : Int} {b d b' d' : Nat}
    (hb : 0 < b) (hd : 0 < d)
    (ha : ratioEqZ a b a' b') (hc : ratioEqZ c d c' d')
    (h : ratioLeZ a b c d) : ratioLeZ a' b' c' d' := by
  have hK : (0 : Int) ≤ Int.ofNat b' * Int.ofNat d' := by
    show (0 : Int) ≤ Int.ofNat (b' * d')
    exact Int.ofNat_nonneg _
  have step1 : (a * Int.ofNat d) * (Int.ofNat b' * Int.ofNat d')
             ≤ (c * Int.ofNat b) * (Int.ofNat b' * Int.ofNat d') :=
    mul_le_mul_right_nonneg h _ hK
  have hL : (a * Int.ofNat d) * (Int.ofNat b' * Int.ofNat d')
          = (a' * Int.ofNat d') * (Int.ofNat b * Int.ofNat d) :=
    calc (a * Int.ofNat d) * (Int.ofNat b' * Int.ofNat d')
        = (a * Int.ofNat b') * (Int.ofNat d * Int.ofNat d') :=
          mul_mul_mul_comm a (Int.ofNat d) (Int.ofNat b') (Int.ofNat d')
      _ = (a' * Int.ofNat b) * (Int.ofNat d * Int.ofNat d') :=
          congrArg (· * (Int.ofNat d * Int.ofNat d')) ha
      _ = (a' * Int.ofNat b) * (Int.ofNat d' * Int.ofNat d) := by
          rw [mul_comm (Int.ofNat d) (Int.ofNat d')]
      _ = (a' * Int.ofNat d') * (Int.ofNat b * Int.ofNat d) :=
          mul_mul_mul_comm a' (Int.ofNat b) (Int.ofNat d') (Int.ofNat d)
  have hR : (c * Int.ofNat b) * (Int.ofNat b' * Int.ofNat d')
          = (c' * Int.ofNat b') * (Int.ofNat b * Int.ofNat d) :=
    calc (c * Int.ofNat b) * (Int.ofNat b' * Int.ofNat d')
        = (c * Int.ofNat b) * (Int.ofNat d' * Int.ofNat b') := by
          rw [mul_comm (Int.ofNat b') (Int.ofNat d')]
      _ = (c * Int.ofNat d') * (Int.ofNat b * Int.ofNat b') :=
          mul_mul_mul_comm c (Int.ofNat b) (Int.ofNat d') (Int.ofNat b')
      _ = (c' * Int.ofNat d) * (Int.ofNat b * Int.ofNat b') :=
          congrArg (· * (Int.ofNat b * Int.ofNat b')) hc
      _ = (c' * Int.ofNat d) * (Int.ofNat b' * Int.ofNat b) := by
          rw [mul_comm (Int.ofNat b) (Int.ofNat b')]
      _ = (c' * Int.ofNat b') * (Int.ofNat d * Int.ofNat b) :=
          mul_mul_mul_comm c' (Int.ofNat d) (Int.ofNat b') (Int.ofNat b)
      _ = (c' * Int.ofNat b') * (Int.ofNat b * Int.ofNat d) := by
          rw [mul_comm (Int.ofNat d) (Int.ofNat b)]
  rw [hL, hR] at step1
  have hBD : (0 : Int) < Int.ofNat b * Int.ofNat d := by
    show (0 : Int) < Int.ofNat (b * d)
    exact ofNat_pos (Nat.mul_pos hb hd)
  exact le_of_mul_le_mul_right_pos step1 hBD

/-- Both ways: equivalent positive-denominator presentations agree on
    the cross-order — the derived order is well-defined on the
    quotient. -/
theorem ratioLeZ_iff {a c a' c' : Int} {b d b' d' : Nat}
    (hb : 0 < b) (hd : 0 < d) (hb' : 0 < b') (hd' : 0 < d')
    (ha : ratioEqZ a b a' b') (hc : ratioEqZ c d c' d') :
    ratioLeZ a b c d ↔ ratioLeZ a' b' c' d' :=
  ⟨ratioLeZ_descends hb hd ha hc,
   ratioLeZ_descends hb' hd' ha.symm hc.symm⟩

end E213.Lib.Math.NumberSystems.Rat213
