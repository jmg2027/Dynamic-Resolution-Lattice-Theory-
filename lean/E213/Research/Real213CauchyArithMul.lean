import E213.Research.Real213CauchyComplete
import E213.Research.Real213CutMulComm
import E213.Research.Real213CutMulDetermined

/-!
# Research.Real213CauchyArithMul: cutMul on Cauchy sequences

cutMul of two CauchyCutSeqs is Cauchy.  Modulus uses the max over
the search range j ∈ [0, B] of a.N j k where B = (m+1)*(k+1).
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- max of a.N j k for j ∈ [0, M] (no precision doubling). -/
def maxNAt (a_N : Nat → Nat → Nat) (kPrec : Nat) : Nat → Nat
  | 0 => a_N 0 kPrec
  | M+1 => Nat.max (a_N (M+1) kPrec) (maxNAt a_N kPrec M)

/-- maxNAt dominates each individual modulus in [0, M]. -/
theorem maxNAt_ge (a_N : Nat → Nat → Nat) (kPrec : Nat) :
    ∀ M j, j ≤ M → a_N j kPrec ≤ maxNAt a_N kPrec M
  | 0, j, hj => by
    have : j = 0 := Nat.le_zero.mp hj
    rw [this]
    show a_N 0 kPrec ≤ a_N 0 kPrec
    exact Nat.le_refl _
  | M+1, j, hj => by
    cases Nat.lt_or_ge j (M+1) with
    | inl hjlt =>
      have hjle : j ≤ M := Nat.le_of_lt_succ hjlt
      exact Nat.le_trans (maxNAt_ge a_N kPrec M j hjle)
                         (Nat.le_max_right _ _)
    | inr hjge =>
      have heq : j = M+1 := Nat.le_antisymm hj hjge
      rw [heq]
      exact Nat.le_max_left _ _

/-- Pointwise cutMul of two CauchyCutSeqs is Cauchy.
    Modulus: max over the search range j ∈ [0, B]
    where B = (m+1)*(k+1) is cutMul's bound. -/
def CauchyCutSeq.cutMul (a b : CauchyCutSeq) : CauchyCutSeq where
  cs := fun i => Real213CutSum.cutMul (a.cs i) (b.cs i)
  N := fun m k => Nat.max (maxNAt a.N k ((m+1)*(k+1)))
                          (maxNAt b.N k ((m+1)*(k+1)))
  cauchy := by
    intro m k i j hi hj
    show Real213CutSum.cutMul (a.cs i) (b.cs i) m k
       = Real213CutSum.cutMul (a.cs j) (b.cs j) m k
    show cutMulOuter (a.cs i) (b.cs i) k m ((m+1)*(k+1)) ((m+1)*(k+1))
       = cutMulOuter (a.cs j) (b.cs j) k m ((m+1)*(k+1)) ((m+1)*(k+1))
    apply cutMulOuter_congr
    · intro m' hm'
      have hia : i ≥ a.N m' k :=
        Nat.le_trans (Nat.le_trans
          (maxNAt_ge a.N k ((m+1)*(k+1)) m' hm')
          (Nat.le_max_left _ _)) hi
      have hja : j ≥ a.N m' k :=
        Nat.le_trans (Nat.le_trans
          (maxNAt_ge a.N k ((m+1)*(k+1)) m' hm')
          (Nat.le_max_left _ _)) hj
      exact a.cauchy m' k i j hia hja
    · intro m' hm'
      have hib : i ≥ b.N m' k :=
        Nat.le_trans (Nat.le_trans
          (maxNAt_ge b.N k ((m+1)*(k+1)) m' hm')
          (Nat.le_max_right _ _)) hi
      have hjb : j ≥ b.N m' k :=
        Nat.le_trans (Nat.le_trans
          (maxNAt_ge b.N k ((m+1)*(k+1)) m' hm')
          (Nat.le_max_right _ _)) hj
      exact b.cauchy m' k i j hib hjb
    · exact Nat.le_refl _

/-- Limit of cutMul of two Cauchy seqs = cutMul of limits. -/
theorem CauchyCutSeq.cutMul_limit (a b : CauchyCutSeq) :
    (a.cutMul b).limit = Real213CutSum.cutMul a.limit b.limit := by
  funext m k
  let Nmax := Nat.max (maxNAt a.N k ((m+1)*(k+1)))
                      (maxNAt b.N k ((m+1)*(k+1)))
  show cutMulOuter (a.cs Nmax) (b.cs Nmax) k m ((m+1)*(k+1)) ((m+1)*(k+1))
     = cutMulOuter a.limit b.limit k m ((m+1)*(k+1)) ((m+1)*(k+1))
  apply cutMulOuter_congr
  · intro m' hm'
    show a.cs Nmax m' k = a.cs (a.N m' k) m' k
    have hbig : Nmax ≥ a.N m' k :=
      Nat.le_trans (maxNAt_ge a.N k ((m+1)*(k+1)) m' hm')
                   (Nat.le_max_left _ _)
    exact a.cauchy m' k Nmax (a.N m' k) hbig (Nat.le_refl _)
  · intro m' hm'
    show b.cs Nmax m' k = b.cs (b.N m' k) m' k
    have hbig : Nmax ≥ b.N m' k :=
      Nat.le_trans (maxNAt_ge b.N k ((m+1)*(k+1)) m' hm')
                   (Nat.le_max_right _ _)
    exact b.cauchy m' k Nmax (b.N m' k) hbig (Nat.le_refl _)
  · exact Nat.le_refl _

/-- cutMul is commutative at the Cauchy limit. -/
theorem CauchyCutSeq.cutMul_comm_limit (a b : CauchyCutSeq) :
    (a.cutMul b).limit = (b.cutMul a).limit := by
  rw [cutMul_limit, cutMul_limit]
  funext m k
  exact cutMul_comm a.limit b.limit m k

end E213.Research.Real213CutSum
