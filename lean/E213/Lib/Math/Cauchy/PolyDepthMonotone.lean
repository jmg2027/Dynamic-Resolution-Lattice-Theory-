import E213.Lib.Math.Cauchy.NewtonGregory
import E213.Meta.Int213.Order

/-!
# Finite difference-depth ⟹ eventually monotone (∅-axiom)

The constructive bridge missing from `PositiveFloorUnbounded` (which only handled the
positive-top-difference branch over `ℕ`): **every finite-`Δ`-depth integer sequence is eventually
monotone** — non-decreasing (`MonoFromZ`) or non-increasing (`AntiFromZ`).

The proof inducts on the depth `d` via the sign trichotomy of the *constant* top difference
`c = liftKZ d s 0` (`Int213.Order.pos_zero_or_neg`):
  * `c > 0` ⟹ `s` eventually *strictly increasing* (`posTop_evStrictMonoZ`, the `Int` port of the
    `PositiveFloorUnbounded` descent) ⟹ non-decreasing;
  * `c < 0` ⟹ negate and reuse the `c > 0` branch ⟹ non-increasing;
  * `c = 0` ⟹ `liftKZ d s` is genuinely constant (faithful `Int` difference, no `ℕ` truncation)
    ⟹ `polyDepthZ (d-1) s`, recurse.

LPO-free: each nonzero branch yields *strict* monotonicity (no bounded-monotone stabilisation),
and the `c = 0` branch reduces the depth.
-/

namespace E213.Lib.Math.Cauchy.PolyDepthMonotone

open E213.Lib.Math.Cauchy.NewtonGregory (diffZ liftKZ isConstZ polyDepthZ)
open E213.Meta.Int213.Order

/-- Eventually strictly increasing (over `Int`). -/
def EvStrictMonoZ (N : Nat) (s : Nat → Int) : Prop := ∀ n, N ≤ n → s n < s (n + 1)

/-- Eventually non-decreasing. -/
def MonoFromZ (N : Nat) (s : Nat → Int) : Prop := ∀ m n, N ≤ m → m ≤ n → s m ≤ s n

/-- Eventually non-increasing. -/
def AntiFromZ (N : Nat) (s : Nat → Int) : Prop := ∀ m n, N ≤ m → m ≤ n → s n ≤ s m

/-! ## Strict ⟹ monotone, and the eventual-positivity telescope -/

theorem mono_of_evStrictMonoZ {N : Nat} {s : Nat → Int} (h : EvStrictMonoZ N s) : MonoFromZ N s := by
  intro m n hNm hmn
  induction hmn with
  | refl => exact le_refl (s m)
  | @step k hk ih => exact le_trans ih (le_of_lt (h k (Nat.le_trans hNm hk)))

theorem evStrictMonoZ_ge {M : Nat} {s : Nat → Int} (h : EvStrictMonoZ M s) :
    ∀ i, s M + Int.ofNat i ≤ s (M + i) := by
  intro i
  induction i with
  | zero =>
    show s M + Int.ofNat 0 ≤ s (M + 0)
    rw [show s M + Int.ofNat 0 = s M from Int.add_zero (s M)]
    exact le_refl (s M)
  | succ i ih =>
    have hstrict : s (M + i) + 1 ≤ s (M + i + 1) := h (M + i) (Nat.le_add_right M i)
    rw [show s M + Int.ofNat (i + 1) = (s M + Int.ofNat i) + 1 by
          rw [show Int.ofNat (i + 1) = Int.ofNat i + 1 from rfl, ← E213.Meta.Int213.add_assoc]]
    exact le_trans (add_le_add_right ih 1) hstrict

theorem evStrictMonoZ_eventually_pos {M : Nat} {s : Nat → Int} (h : EvStrictMonoZ M s) :
    ∃ N, ∀ n, N ≤ n → (0 : Int) < s n := by
  refine ⟨M + ((s M).natAbs + 1), fun n hn => ?_⟩
  have htel : s M + Int.ofNat ((s M).natAbs + 1) ≤ s (M + ((s M).natAbs + 1)) :=
    evStrictMonoZ_ge h ((s M).natAbs + 1)
  have e2 : s M + Int.ofNat ((s M).natAbs + 1) = (s M + Int.ofNat (s M).natAbs) + 1 := by
    rw [show Int.ofNat ((s M).natAbs + 1) = Int.ofNat (s M).natAbs + 1 from rfl,
        ← E213.Meta.Int213.add_assoc]
  have h1 : (1 : Int) ≤ (s M + Int.ofNat (s M).natAbs) + 1 := by
    have hz := add_le_add_right (nonneg_add_natAbs (s M)) 1
    rw [E213.Meta.Int213.zero_add] at hz
    exact hz
  have h1A : (1 : Int) ≤ s M + Int.ofNat ((s M).natAbs + 1) := e2 ▸ h1
  have hposM' : (0 : Int) < s (M + ((s M).natAbs + 1)) := le_trans h1A htel
  exact lt_of_lt_of_le hposM'
    (mono_of_evStrictMonoZ h (M + ((s M).natAbs + 1)) n (Nat.le_add_right M _) hn)

/-! ## `diffZ`/negation commute with `liftKZ`; positive top ⟹ eventually strictly increasing -/

theorem liftKZ_diffZ (k : Nat) (s : Nat → Int) : liftKZ k (diffZ s) = diffZ (liftKZ k s) := by
  induction k with
  | zero => rfl
  | succ k ih => show diffZ (liftKZ k (diffZ s)) = diffZ (liftKZ (k + 1) s); rw [ih]; rfl

theorem posTop_evStrictMonoZ : ∀ (e : Nat) (s : Nat → Int), polyDepthZ (e + 1) s →
    (0 : Int) < liftKZ (e + 1) s 0 → ∃ N, EvStrictMonoZ N s := by
  intro e
  induction e with
  | zero =>
    intro s hpd hpos
    refine ⟨0, fun n _ => ?_⟩
    apply lt_of_sub_pos
    show (0 : Int) < s (n + 1) - s n
    have hc : liftKZ 1 s n = liftKZ 1 s 0 := hpd n
    have hdef : liftKZ 1 s n = s (n + 1) - s n := rfl
    rw [← hdef, hc]; exact hpos
  | succ e ih =>
    intro s hpd hpos
    have hcomm : liftKZ (e + 1) (diffZ s) = liftKZ (e + 2) s := by rw [liftKZ_diffZ]; rfl
    have hg_pd : polyDepthZ (e + 1) (diffZ s) := by
      intro n
      show liftKZ (e + 1) (diffZ s) n = liftKZ (e + 1) (diffZ s) 0
      rw [hcomm]; exact hpd n
    have hg_pos : (0 : Int) < liftKZ (e + 1) (diffZ s) 0 := by rw [hcomm]; exact hpos
    obtain ⟨M, hM⟩ := ih (diffZ s) hg_pd hg_pos
    obtain ⟨M', hM'⟩ := evStrictMonoZ_eventually_pos hM
    refine ⟨M', fun n hn => ?_⟩
    apply lt_of_sub_pos
    show (0 : Int) < s (n + 1) - s n
    exact hM' n hn

/-- Pointwise negation. -/
def negS (s : Nat → Int) : Nat → Int := fun n => -(s n)

/-- Negation commutes with iterated differences — stated **pointwise** to avoid `funext`
    (which leaks `Quot.sound`). -/
theorem liftKZ_negS_apply (k : Nat) (s : Nat → Int) :
    ∀ n, liftKZ k (negS s) n = -(liftKZ k s n) := by
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    show liftKZ k (negS s) (n + 1) - liftKZ k (negS s) n = -(liftKZ k s (n + 1) - liftKZ k s n)
    rw [ih (n + 1), ih n]; ring_intZ

/-! ## The bridge: finite depth ⟹ eventually monotone -/

theorem polyDepthZ_evMono : ∀ (d : Nat) (s : Nat → Int), polyDepthZ d s →
    (∃ N, MonoFromZ N s) ∨ (∃ N, AntiFromZ N s) := by
  intro d
  induction d with
  | zero =>
    intro s hpd
    refine Or.inl ⟨0, fun m n _ _ => ?_⟩
    have hm : s m = s 0 := hpd m
    have hn : s n = s 0 := hpd n
    rw [hm, ← hn]; exact le_refl (s n)
  | succ d ih =>
    intro s hpd
    rcases pos_zero_or_neg (liftKZ (d + 1) s 0) with hp | hz | hn
    · obtain ⟨N, hN⟩ := posTop_evStrictMonoZ d s hpd hp
      exact Or.inl ⟨N, mono_of_evStrictMonoZ hN⟩
    · -- c = 0: `liftKZ d s` is genuinely constant ⟹ depth drops
      have hstep : ∀ n, liftKZ d s (n + 1) = liftKZ d s n := by
        intro n
        have h0 : liftKZ (d + 1) s n = 0 := (hpd n).trans hz
        have hdef : liftKZ (d + 1) s n = liftKZ d s (n + 1) - liftKZ d s n := rfl
        rw [hdef] at h0
        exact eq_of_sub_eq_zero h0
      have hpd' : polyDepthZ d s := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih2 => rw [hstep n, ih2]
      exact ih s hpd'
    · -- c < 0: negate, reuse the positive branch, flip
      have hneg_pd : polyDepthZ (d + 1) (negS s) := by
        intro n
        show liftKZ (d + 1) (negS s) n = liftKZ (d + 1) (negS s) 0
        rw [liftKZ_negS_apply (d + 1) s n, liftKZ_negS_apply (d + 1) s 0, hpd n]
      have hneg_pos : (0 : Int) < liftKZ (d + 1) (negS s) 0 := by
        rw [liftKZ_negS_apply (d + 1) s 0]; exact neg_pos_of_neg hn
      obtain ⟨N, hN⟩ := posTop_evStrictMonoZ d (negS s) hneg_pd hneg_pos
      refine Or.inr ⟨N, fun m n hNm hmn => ?_⟩
      have hmono : -(s m) ≤ -(s n) := mono_of_evStrictMonoZ hN m n hNm hmn
      exact le_of_neg_le_neg hmono

end E213.Lib.Math.Cauchy.PolyDepthMonotone
