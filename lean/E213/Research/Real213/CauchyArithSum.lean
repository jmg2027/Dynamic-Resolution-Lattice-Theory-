import E213.Research.Real213.CauchyComplete
import E213.Research.Real213.CutSumComm
import E213.Research.Real213.CutSumDetermined

/-!
# Research.Real213CauchyArithSum: cutSum on Cauchy sequences

cutSum of two CauchyCutSeqs is Cauchy.  Modulus uses the max over
the search range j ∈ [0, 2m] of a.N j (2k) and b.N j (2k).

Key lemma: cutSumAux_congr (existing in Real213CutSumDetermined).
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- max of a.N j (2*k) for j ∈ [0, M]. -/
def maxModulus (a_N : Nat → Nat → Nat) (k : Nat) : Nat → Nat
  | 0 => a_N 0 (2*k)
  | M+1 => Nat.max (a_N (M+1) (2*k)) (maxModulus a_N k M)

/-- maxModulus dominates each individual modulus in [0, M]. -/
theorem maxModulus_ge (a_N : Nat → Nat → Nat) (k : Nat) :
    ∀ M j, j ≤ M → a_N j (2*k) ≤ maxModulus a_N k M
  | 0, j, hj => by
    have : j = 0 := Nat.le_zero.mp hj
    rw [this]
    show a_N 0 (2*k) ≤ a_N 0 (2*k)
    exact Nat.le_refl _
  | M+1, j, hj => by
    cases Nat.lt_or_ge j (M+1) with
    | inl hjlt =>
      have hjle : j ≤ M := Nat.le_of_lt_succ hjlt
      exact Nat.le_trans (maxModulus_ge a_N k M j hjle)
                         (Nat.le_max_right _ _)
    | inr hjge =>
      have heq : j = M+1 := Nat.le_antisymm hj hjge
      rw [heq]
      exact Nat.le_max_left _ _

/-- Pointwise cutSum of two CauchyCutSeqs is Cauchy.
    Modulus: max over the search range j ∈ [0, 2m]. -/
def CauchyCutSeq.cutSum (a b : CauchyCutSeq) : CauchyCutSeq where
  cs := fun i => E213.Research.Real213.CutSum.cutSum (a.cs i) (b.cs i)
  N := fun m k => Nat.max (maxModulus a.N k (2*m))
                          (maxModulus b.N k (2*m))
  cauchy := by
    intro m k i j hi hj
    show E213.Research.Real213.CutSum.cutSum (a.cs i) (b.cs i) m k
       = E213.Research.Real213.CutSum.cutSum (a.cs j) (b.cs j) m k
    show cutSumAux (a.cs i) (b.cs i) k (2*m) (2*m)
       = cutSumAux (a.cs j) (b.cs j) k (2*m) (2*m)
    apply cutSumAux_congr
    · intro m' hm'
      have hia : i ≥ a.N m' (2*k) :=
        Nat.le_trans (Nat.le_trans (maxModulus_ge a.N k (2*m) m' hm')
                                   (Nat.le_max_left _ _)) hi
      have hja : j ≥ a.N m' (2*k) :=
        Nat.le_trans (Nat.le_trans (maxModulus_ge a.N k (2*m) m' hm')
                                   (Nat.le_max_left _ _)) hj
      exact a.cauchy m' (2*k) i j hia hja
    · intro m' hm'
      have hib : i ≥ b.N m' (2*k) :=
        Nat.le_trans (Nat.le_trans (maxModulus_ge b.N k (2*m) m' hm')
                                   (Nat.le_max_right _ _)) hi
      have hjb : j ≥ b.N m' (2*k) :=
        Nat.le_trans (Nat.le_trans (maxModulus_ge b.N k (2*m) m' hm')
                                   (Nat.le_max_right _ _)) hj
      exact b.cauchy m' (2*k) i j hib hjb
    · exact Nat.le_refl _

/-- Limit of cutSum of two Cauchy seqs = cutSum of limits. -/
theorem CauchyCutSeq.cutSum_limit (a b : CauchyCutSeq) :
    (a.cutSum b).limit = E213.Research.Real213.CutSum.cutSum a.limit b.limit := by
  funext m k
  let Nmax := Nat.max (maxModulus a.N k (2*m)) (maxModulus b.N k (2*m))
  show cutSumAux (a.cs Nmax) (b.cs Nmax) k (2*m) (2*m)
     = cutSumAux a.limit b.limit k (2*m) (2*m)
  apply cutSumAux_congr
  · intro m' hm'
    show a.cs Nmax m' (2*k) = a.cs (a.N m' (2*k)) m' (2*k)
    have hbig : Nmax ≥ a.N m' (2*k) :=
      Nat.le_trans (maxModulus_ge a.N k (2*m) m' hm')
                   (Nat.le_max_left _ _)
    exact a.cauchy m' (2*k) Nmax (a.N m' (2*k)) hbig (Nat.le_refl _)
  · intro m' hm'
    show b.cs Nmax m' (2*k) = b.cs (b.N m' (2*k)) m' (2*k)
    have hbig : Nmax ≥ b.N m' (2*k) :=
      Nat.le_trans (maxModulus_ge b.N k (2*m) m' hm')
                   (Nat.le_max_right _ _)
    exact b.cauchy m' (2*k) Nmax (b.N m' (2*k)) hbig (Nat.le_refl _)
  · exact Nat.le_refl _

/-- cutSum is commutative at the Cauchy limit. -/
theorem CauchyCutSeq.cutSum_comm_limit (a b : CauchyCutSeq) :
    (a.cutSum b).limit = (b.cutSum a).limit := by
  rw [cutSum_limit, cutSum_limit]
  funext m k
  exact cutSum_comm a.limit b.limit m k

end E213.Research.Real213.CutSum
