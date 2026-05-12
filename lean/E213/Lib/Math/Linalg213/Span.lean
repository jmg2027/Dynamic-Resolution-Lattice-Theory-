import E213.Lib.Math.Linalg213.Rank

/-!
# 213 Linear Algebra — basis span (3)

Proves that any `v : Vec 5` decomposes as a ℕ-linear combination
of the 5 standard basis vectors e_0, ..., e_4.  This is the
**213-internal "rank ≤ 5"** in its constructive form:
  ∀ v ∈ Vec 5, v = Σ_{k=0}^4 v(k) · e_k

We state this *pointwise* (avoiding funext / Quot.sound) at each
index k via direct arithmetic identity:
  v(k) = v(0)·e_0(k) + v(1)·e_1(k) + ... + v(4)·e_4(k)

For each fixed k, exactly one e_i(k) = 1 (when i = k) and the
rest = 0, so the identity reduces to v(k) · 1 + 0 + ... = v(k).
Proven by `omega` (Nat linear arithmetic).
-/

namespace E213.Lib.Math.Linalg213.Span

open E213.Lib.Math.Linalg213.Vector

/-- Standard basis vectors at d=5. -/
def e2_5 : Vec 5 := Vec.basis ⟨2, by decide⟩
def e3_5 : Vec 5 := Vec.basis ⟨3, by decide⟩
def e4_5 : Vec 5 := Vec.basis ⟨4, by decide⟩

/-- Basis decomposition at index k: v(k) equals the sum of
    v(i)·e_i(k) over i = 0..4.  Each e_i(k) ∈ {0, 1} concretely. -/
def basisDecompAt (v : Vec 5) (k : Fin 5) : Nat :=
  v ⟨0, by decide⟩ * (e0_5 k) +
  v ⟨1, by decide⟩ * (e1_5 k) +
  v ⟨2, by decide⟩ * (e2_5 k) +
  v ⟨3, by decide⟩ * (e3_5 k) +
  v ⟨4, by decide⟩ * (e4_5 k)

/-- ★ Pointwise decomposition at k=0: v(0) equals
    v(0)·1 + v(1)·0 + v(2)·0 + v(3)·0 + v(4)·0. -/
theorem decomp_at_0 (v : Vec 5) :
    basisDecompAt v ⟨0, by decide⟩ = v ⟨0, by decide⟩ := by
  show v ⟨0, _⟩ * 1 + v ⟨1, _⟩ * 0 + v ⟨2, _⟩ * 0
       + v ⟨3, _⟩ * 0 + v ⟨4, _⟩ * 0 = v ⟨0, _⟩
  rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero, Nat.mul_zero, Nat.mul_one]
  rfl

theorem decomp_at_1 (v : Vec 5) :
    basisDecompAt v ⟨1, by decide⟩ = v ⟨1, by decide⟩ := by
  show v ⟨0, _⟩ * 0 + v ⟨1, _⟩ * 1 + v ⟨2, _⟩ * 0
       + v ⟨3, _⟩ * 0 + v ⟨4, _⟩ * 0 = v ⟨1, _⟩
  rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero, Nat.mul_zero,
      Nat.mul_one, Nat.zero_add]
  rfl

theorem decomp_at_2 (v : Vec 5) :
    basisDecompAt v ⟨2, by decide⟩ = v ⟨2, by decide⟩ := by
  show v ⟨0, _⟩ * 0 + v ⟨1, _⟩ * 0 + v ⟨2, _⟩ * 1
       + v ⟨3, _⟩ * 0 + v ⟨4, _⟩ * 0 = v ⟨2, _⟩
  rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero, Nat.mul_zero,
      Nat.mul_one, Nat.zero_add]
  rfl

theorem decomp_at_3 (v : Vec 5) :
    basisDecompAt v ⟨3, by decide⟩ = v ⟨3, by decide⟩ := by
  show v ⟨0, _⟩ * 0 + v ⟨1, _⟩ * 0 + v ⟨2, _⟩ * 0
       + v ⟨3, _⟩ * 1 + v ⟨4, _⟩ * 0 = v ⟨3, _⟩
  rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero, Nat.mul_zero,
      Nat.mul_one, Nat.zero_add]
  rfl

theorem decomp_at_4 (v : Vec 5) :
    basisDecompAt v ⟨4, by decide⟩ = v ⟨4, by decide⟩ := by
  show v ⟨0, _⟩ * 0 + v ⟨1, _⟩ * 0 + v ⟨2, _⟩ * 0
       + v ⟨3, _⟩ * 0 + v ⟨4, _⟩ * 1 = v ⟨4, _⟩
  rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero, Nat.mul_zero,
      Nat.mul_one, Nat.zero_add]

/-- ★ 3 capstone: every `v : Vec 5` admits the basis
    decomposition `v = Σ_{k=0}^{4} v(k) · e_k` pointwise.
    Constructive form of "Vec 5 is rank-5 over ℕ". -/
theorem vec5_basis_span (v : Vec 5) :
    basisDecompAt v ⟨0, by decide⟩ = v ⟨0, by decide⟩
    ∧ basisDecompAt v ⟨1, by decide⟩ = v ⟨1, by decide⟩
    ∧ basisDecompAt v ⟨2, by decide⟩ = v ⟨2, by decide⟩
    ∧ basisDecompAt v ⟨3, by decide⟩ = v ⟨3, by decide⟩
    ∧ basisDecompAt v ⟨4, by decide⟩ = v ⟨4, by decide⟩ :=
  ⟨decomp_at_0 v, decomp_at_1 v, decomp_at_2 v, decomp_at_3 v, decomp_at_4 v⟩

end E213.Lib.Math.Linalg213.Span
