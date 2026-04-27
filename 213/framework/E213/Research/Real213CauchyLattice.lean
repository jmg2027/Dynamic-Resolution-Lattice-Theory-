import E213.Research.Real213CauchyComplete
import E213.Research.Real213CutMaxMin

/-!
# Research.Real213CauchyLattice: lattice ops on Cauchy sequences

cutMax / cutMin of two CauchyCutSeqs is Cauchy.

The modulus is max of the input moduli, and the joint Cauchy property
follows from the input Cauchy properties evaluated pointwise on Bool.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- Pointwise cutMax of two CauchyCutSeqs is Cauchy. -/
def CauchyCutSeq.cutMax (a b : CauchyCutSeq) : CauchyCutSeq where
  cs := fun i => Real213CutSum.cutMax (a.cs i) (b.cs i)
  N := fun m k => Nat.max (a.N m k) (b.N m k)
  cauchy := by
    intro m k i j hi hj
    show (a.cs i m k && b.cs i m k) = (a.cs j m k && b.cs j m k)
    have hia : i ≥ a.N m k := Nat.le_trans (Nat.le_max_left _ _) hi
    have hib : i ≥ b.N m k := Nat.le_trans (Nat.le_max_right _ _) hi
    have hja : j ≥ a.N m k := Nat.le_trans (Nat.le_max_left _ _) hj
    have hjb : j ≥ b.N m k := Nat.le_trans (Nat.le_max_right _ _) hj
    rw [a.cauchy m k i j hia hja, b.cauchy m k i j hib hjb]

/-- Pointwise cutMin of two CauchyCutSeqs is Cauchy. -/
def CauchyCutSeq.cutMin (a b : CauchyCutSeq) : CauchyCutSeq where
  cs := fun i => Real213CutSum.cutMin (a.cs i) (b.cs i)
  N := fun m k => Nat.max (a.N m k) (b.N m k)
  cauchy := by
    intro m k i j hi hj
    show (a.cs i m k || b.cs i m k) = (a.cs j m k || b.cs j m k)
    have hia : i ≥ a.N m k := Nat.le_trans (Nat.le_max_left _ _) hi
    have hib : i ≥ b.N m k := Nat.le_trans (Nat.le_max_right _ _) hi
    have hja : j ≥ a.N m k := Nat.le_trans (Nat.le_max_left _ _) hj
    have hjb : j ≥ b.N m k := Nat.le_trans (Nat.le_max_right _ _) hj
    rw [a.cauchy m k i j hia hja, b.cauchy m k i j hib hjb]

/-- Limit of cutMax of two Cauchy seqs = cutMax of limits. -/
theorem CauchyCutSeq.cutMax_limit (a b : CauchyCutSeq) :
    (a.cutMax b).limit = Real213CutSum.cutMax a.limit b.limit := by
  funext m k
  show (a.cs (Nat.max (a.N m k) (b.N m k)) m k
        && b.cs (Nat.max (a.N m k) (b.N m k)) m k)
       = (a.cs (a.N m k) m k && b.cs (b.N m k) m k)
  rw [a.cauchy m k _ _ (Nat.le_max_left _ _) (Nat.le_refl _)]
  rw [b.cauchy m k _ _ (Nat.le_max_right _ _) (Nat.le_refl _)]

/-- Limit of cutMin of two Cauchy seqs = cutMin of limits. -/
theorem CauchyCutSeq.cutMin_limit (a b : CauchyCutSeq) :
    (a.cutMin b).limit = Real213CutSum.cutMin a.limit b.limit := by
  funext m k
  show (a.cs (Nat.max (a.N m k) (b.N m k)) m k
        || b.cs (Nat.max (a.N m k) (b.N m k)) m k)
       = (a.cs (a.N m k) m k || b.cs (b.N m k) m k)
  rw [a.cauchy m k _ _ (Nat.le_max_left _ _) (Nat.le_refl _)]
  rw [b.cauchy m k _ _ (Nat.le_max_right _ _) (Nat.le_refl _)]

end E213.Research.Real213CutSum
