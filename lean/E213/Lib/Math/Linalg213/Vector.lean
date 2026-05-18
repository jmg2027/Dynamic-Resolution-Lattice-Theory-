import E213.Lib.Physics.Simplex.Counts

/-!
# 213 Linear Algebra — Vector type (foundation)

**Strict 213-internal principle:** we do NOT borrow classical
linear algebra (no real/complex vector spaces, no Mathlib).  We
build *all* of linear algebra from Raw + atomicity.

A `Vec d` is a function from atomic indices `Fin d` to ℕ — a
non-negative integer-valued vector.  Why ℕ and not Bool?
  * Bool gives GF(2) algebra which is degenerate
    (⟨v,v⟩ can be 0 for v ≠ 0).
  * ℕ is the simplest non-degenerate option in 213-internal
    (ℕ is forced by atomicity counting; no ℝ/ℂ needed).
  * Inner product ⟨v, w⟩ = Σ vᵢ · wᵢ ≥ 0 (non-degenerate cone).

This is the *first* foundational file for 213 linear algebra.
The target: paper 1's chiral compression theorem
  "any N atomic relations have Gram rank ≤ d = 5"
which (combined with the bipartite chirality of paper 2) forces
the universe shape to K_{3,2}^{(2)} as formalized cohomologically.
-/

namespace E213.Lib.Math.Linalg213.Vector

open E213.Lib.Physics.Simplex.Counts (d NS NT)

/-- A 213-native vector at dimension `n`. -/
def Vec (n : Nat) : Type := Fin n → Nat

/-- Zero vector. -/
def Vec.zero (n : Nat) : Vec n := fun _ => 0

/-- Standard basis vector at index i. -/
def Vec.basis {n : Nat} (i : Fin n) : Vec n :=
  fun j => if i.val == j.val then 1 else 0

/-- Pointwise addition. -/
def Vec.add {n : Nat} (v w : Vec n) : Vec n := fun i => v i + w i

/-- Scalar multiplication by ℕ. -/
def Vec.smul {n : Nat} (c : Nat) (v : Vec n) : Vec n := fun i => c * v i

/-- Smoke: zero + zero at n=5 (atomic). -/
theorem zero_add_zero : ∀ i : Fin 5, Vec.add (Vec.zero 5) (Vec.zero 5) i = 0 := by
  decide

/-- e_0, e_1 ∈ Vec 5. -/
def e0_5 : Vec 5 := Vec.basis ⟨0, by decide⟩
def e1_5 : Vec 5 := Vec.basis ⟨1, by decide⟩

/-- Smoke: e_0 + e_1 in Vec 5 has values (1, 1, 0, 0, 0). -/
theorem basis_add_d5 :
    Vec.add e0_5 e1_5 ⟨0, by decide⟩ = 1
    ∧ Vec.add e0_5 e1_5 ⟨1, by decide⟩ = 1
    ∧ Vec.add e0_5 e1_5 ⟨2, by decide⟩ = 0 := by
  decide

/-- 213's atomic dimension is d = 5 (`Theory.Atomicity` theorem). -/
theorem atomic_d_eq_5 : E213.Lib.Physics.Simplex.Counts.d = 5 := by decide

/-- The chiral split of d = 5 into (NS, NT) = (3, 2). -/
theorem atomic_chiral_split :
    E213.Lib.Physics.Simplex.Counts.d = E213.Lib.Physics.Simplex.Counts.NS + E213.Lib.Physics.Simplex.Counts.NT
    ∧ E213.Lib.Physics.Simplex.Counts.NS = 3
    ∧ E213.Lib.Physics.Simplex.Counts.NT = 2 := by decide

end E213.Lib.Math.Linalg213.Vector
