import E213.Theory.Internal.Int213
import E213.Meta.Tactic.Nat213
import E213.Theory.Tower.NatPairToInt

/-!
# Theory.Tower.NatTripleToZ2 — 3-orthogonal-axis projection

**Exploratory.**  3-axis analog of G62's NatPairToInt.

Projection `ℕ³ → ℤ²` via `(a, b, c) ↦ (a - c, b - c)`:
- diagonal-translation invariant
- surjective onto ℤ²
- 3 unit axes → `{(1,0), (0,1), (-1,-1)}` summing to 0 = Eisenstein
  basis `{1, ω, ω²}` (since `1 + ω + ω² = 0`)

So 3-axis ℕ³ / diagonal ≅ ℤ², and the three axes realize cube-roots
of unity.  Exploratory closure — user's 3-axis intuition was held
in suspense.
-/

namespace E213.Theory.Tower.NatTripleToZ2

/-- Triple of naturals: three orthogonal ℕ-axes. -/
abbrev NTriple : Type := Nat × Nat × Nat

/-- Project ℕ³ → ℤ² via `(a, b, c) ↦ (a - c, b - c)`. -/
def ntripleToZ2 (t : NTriple) : Int × Int :=
  (Int.subNatNat t.1 t.2.2, Int.subNatNat t.2.1 t.2.2)

/-- Origin. -/
theorem ntripleToZ2_origin : ntripleToZ2 (0, 0, 0) = (0, 0) := rfl

/-- ★ First axis = `1` in Eisenstein: `(n, 0, 0) ↦ (n, 0)`. -/
theorem ntripleToZ2_axis_1 (n : Nat) :
    ntripleToZ2 (n, 0, 0) = (Int.ofNat n, 0) := by
  show (Int.subNatNat n 0, Int.subNatNat 0 0) = (Int.ofNat n, 0)
  cases n with
  | zero => rfl
  | succ k =>
      show (match 0 - (k+1) with
            | 0 => Int.ofNat ((k+1) - 0)
            | j+1 => Int.negSucc j, 0) = (Int.ofNat (k+1), 0)
      rw [Nat.zero_sub]; rfl

/-- ★ Second axis = `ω` in Eisenstein: `(0, n, 0) ↦ (0, n)`. -/
theorem ntripleToZ2_axis_2 (n : Nat) :
    ntripleToZ2 (0, n, 0) = (0, Int.ofNat n) := by
  show (Int.subNatNat 0 0, Int.subNatNat n 0) = (0, Int.ofNat n)
  cases n with
  | zero => rfl
  | succ k =>
      show (0, match 0 - (k+1) with
              | 0 => Int.ofNat ((k+1) - 0)
              | j+1 => Int.negSucc j) = (0, Int.ofNat (k+1))
      rw [Nat.zero_sub]; rfl

/-- ★ Third axis = `ω²` in Eisenstein: `(0, 0, n) ↦ (-n, -n)`.
    Since `1 + ω + ω² = 0`, the third basis vector is `-1 - ω`,
    which has Eisenstein-coords `(-1, -1)` per unit. -/
theorem ntripleToZ2_axis_3 (n : Nat) :
    ntripleToZ2 (0, 0, n) = (-(Int.ofNat n), -(Int.ofNat n)) := by
  show (Int.subNatNat 0 n, Int.subNatNat 0 n)
     = (-(Int.ofNat n), -(Int.ofNat n))
  cases n with
  | zero => rfl
  | succ k => rfl

/-- ★★★ Eisenstein equilibrium: the three axis-unit vectors sum
    to **zero** in ℤ².  This is the structural signature of the
    cube-root-of-unity relation `1 + ω + ω² = 0`. -/
theorem three_axes_sum_to_zero :
    let v1 := ntripleToZ2 (1, 0, 0)
    let v2 := ntripleToZ2 (0, 1, 0)
    let v3 := ntripleToZ2 (0, 0, 1)
    (v1.1 + v2.1 + v3.1, v1.2 + v2.2 + v3.2) = (0, 0) := by
  simp only [ntripleToZ2_axis_1, ntripleToZ2_axis_2, ntripleToZ2_axis_3]
  rfl

/-- ★ Diagonal-translation invariance: shifting all three axes
    by the same `k` doesn't change the projection. -/
theorem ntripleToZ2_diag_invariant (a b c k : Nat) :
    ntripleToZ2 (a + k, b + k, c + k) = ntripleToZ2 (a, b, c) := by
  show (Int.subNatNat (a + k) (c + k), Int.subNatNat (b + k) (c + k))
     = (Int.subNatNat a c, Int.subNatNat b c)
  rw [show Int.subNatNat (a + k) (c + k) = Int.subNatNat a c from
        E213.Theory.Tower.NatPairToInt.npairToInt_translation_invariant a c k,
      show Int.subNatNat (b + k) (c + k) = Int.subNatNat b c from
        E213.Theory.Tower.NatPairToInt.npairToInt_translation_invariant b c k]

end E213.Theory.Tower.NatTripleToZ2
