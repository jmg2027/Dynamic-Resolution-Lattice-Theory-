import E213.Meta.UniversalLens.Core.Nat2
import E213.Meta.BitPatternUniqueness

/-!
# expSumLens.view injectivity (full universality of `Lens (ℕ × ℕ)`)

Closes the open question from `UniversalLensNat2`: the exp-sum
encoding `view : Raw → ℕ × ℕ` is INJECTIVE (universal).

Strategy: project to first component (`expSumNat r := view r .1`)
and prove `expSumNat` injective by structural induction on Raw,
using the bit-pattern uniqueness lemma at the slash case.

Once first-component injectivity is established, full view injectivity
follows trivially (Prod.mk_injective.left).
-/

namespace E213.Meta.UniversalLens.Nat2Inj

open E213.Firmware E213.Hypervisor E213.Meta.BitPattern

/-- First-component encoding: `expSumNat = (expSumLens.view _).1`. -/
def expSumNat (r : Raw) : Nat := (expSumLens.view r).1

/-- Concrete: expSumNat a = 1. -/
theorem expSumNat_a : expSumNat Raw.a = 1 := rfl

/-- Concrete: expSumNat b = 2. -/
theorem expSumNat_b : expSumNat Raw.b = 2 := rfl

/-- ★ Slash encodes as 2^x + 2^y. -/
theorem expSumNat_slash (x y : Raw) (h : x ≠ y) :
    expSumNat (Raw.slash x y h) = 2 ^ (expSumNat x) + 2 ^ (expSumNat y) := by
  show (expSumLens.view (Raw.slash x y h)).1 = _
  have hfs : expSumLens.view (Raw.slash x y h)
              = expSumLens.combine (expSumLens.view x) (expSumLens.view y) :=
    Raw.fold_slash _ _ _ expSumLens_symmetric x y h
  rw [hfs]
  rfl

/-- ★★ Lower bound: expSumNat r ≥ 1 for all r. -/
theorem expSumNat_pos (r : Raw) : 1 ≤ expSumNat r := by
  induction r using Raw.rec with
  | a => show 1 ≤ 1; omega
  | b => show 1 ≤ 2; omega
  | slash x y h _ _ =>
    rw [expSumNat_slash]
    have h1 : 0 < 2 ^ (expSumNat x) := Nat.pos_pow_of_pos _ (by decide)
    have h2 : 0 < 2 ^ (expSumNat y) := Nat.pos_pow_of_pos _ (by decide)
    omega

/-- ★★ Slash trees have expSumNat ≥ 4 (since 2^a + 2^b ≥ 2 + 2 = 4 for a, b ≥ 1). -/
theorem expSumNat_slash_ge (x y : Raw) (h : x ≠ y) :
    4 ≤ expSumNat (Raw.slash x y h) := by
  rw [expSumNat_slash]
  have hx : 1 ≤ expSumNat x := expSumNat_pos x
  have hy : 1 ≤ expSumNat y := expSumNat_pos y
  have h2x : 2 ≤ 2 ^ (expSumNat x) := by
    obtain ⟨k, hk⟩ : ∃ k, expSumNat x = k + 1 := ⟨expSumNat x - 1, by omega⟩
    rw [hk, Nat.pow_succ]
    have : 0 < 2^k := Nat.pos_pow_of_pos _ (by decide)
    omega
  have h2y : 2 ≤ 2 ^ (expSumNat y) := by
    obtain ⟨k, hk⟩ : ∃ k, expSumNat y = k + 1 := ⟨expSumNat y - 1, by omega⟩
    rw [hk, Nat.pow_succ]
    have : 0 < 2^k := Nat.pos_pow_of_pos _ (by decide)
    omega
  omega

/-- Auxiliary explicit injectivity statement. -/
theorem expSumNat_inj_aux : ∀ r s : Raw, expSumNat r = expSumNat s → r = s := by
  intro r
  induction r using Raw.rec with
  | a =>
    intro s hs
    induction s using Raw.rec with
    | a => rfl
    | b => rw [expSumNat_a, expSumNat_b] at hs; omega
    | slash x' y' h' _ _ =>
      have := expSumNat_slash_ge x' y' h'
      rw [expSumNat_a] at hs; omega
  | b =>
    intro s hs
    induction s using Raw.rec with
    | a => rw [expSumNat_a, expSumNat_b] at hs; omega
    | b => rfl
    | slash x' y' h' _ _ =>
      have := expSumNat_slash_ge x' y' h'
      rw [expSumNat_b] at hs; omega
  | slash x y h ihx ihy =>
    intro s hs
    induction s using Raw.rec with
    | a =>
      have := expSumNat_slash_ge x y h
      rw [expSumNat_a] at hs; omega
    | b =>
      have := expSumNat_slash_ge x y h
      rw [expSumNat_b] at hs; omega
    | slash x' y' h' _ _ =>
      rw [expSumNat_slash, expSumNat_slash] at hs
      have hxy_distinct : expSumNat x ≠ expSumNat y :=
        fun heq => h (ihx y heq)
      rcases E213.Meta.BitPattern.two_pow_sum_inj_full
              (expSumNat x) (expSumNat y) (expSumNat x') (expSumNat y')
              hxy_distinct hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hxx : x = x' := ihx x' h1
        have hyy : y = y' := ihy y' h2
        subst hxx; subst hyy; rfl
      · have hxy' : x = y' := ihx y' h1
        have hyx' : y = x' := ihy x' h2
        subst hxy'; subst hyx'
        exact Raw.slash_comm _ _ _

/-- ★★★★★★★★ FULL injectivity of expSumNat. -/
theorem expSumNat_inj : Function.Injective expSumNat :=
  fun _ _ h => expSumNat_inj_aux _ _ h

/-- ★★★★★★★★ expSumLens.view is injective — full universality. -/
theorem expSumLens_view_inj : Function.Injective expSumLens.view := by
  intro r s hrs
  apply expSumNat_inj
  show (expSumLens.view r).1 = (expSumLens.view s).1
  rw [hrs]

/-- ★★★★★★★★★ expSumLens is a Universal Lens (in the sense of
    `E213.Meta.UniversalLens.IsUniversal`).  This is the first
    non-trivial universal lens — codomain ℕ × ℕ rather than Raw. -/
theorem expSumLens_is_universal :
    E213.Meta.UniversalLens.IsUniversal expSumLens :=
  expSumLens_view_inj

end E213.Meta.UniversalLens.Nat2Inj
