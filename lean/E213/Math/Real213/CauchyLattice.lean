import E213.Math.Max213
import E213.Math.Real213.CauchyComplete
import E213.Math.Real213.CutMaxMin
import E213.Math.Real213.CutDouble
import E213.Math.Real213.CutBisection
import E213.Math.Real213.CutAlgebraic

/-!
# Research.Real213CauchyLattice: lattice ops on Cauchy sequences

cutMax / cutMin of two CauchyCutSeqs is Cauchy.

The modulus is max of the input moduli, and the joint Cauchy property
follows from the input Cauchy properties evaluated pointwise on Bool.
-/

namespace E213.Math.Real213.CauchyLattice

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutBisection (cutHalf)
open E213.Math.Real213.CutMaxMin (cutMax cutMin)
open E213.Math.Real213.CauchyComplete (CauchyCutSeq)
open E213.Math.Real213.CutDouble (cutDouble)

/-- Pointwise cutMax of two CauchyCutSeqs is Cauchy. -/
def CauchyCutSeq.cutMax (a b : CauchyCutSeq) : CauchyCutSeq where
  cs := fun i => E213.Math.Real213.CutSum.cutMax (a.cs i) (b.cs i)
  N := fun m k => Nat.max (a.N m k) (b.N m k)
  cauchy := by
    intro m k i j hi hj
    show (a.cs i m k && b.cs i m k) = (a.cs j m k && b.cs j m k)
    have hia : i ≥ a.N m k := Nat.le_trans (E213.Math.Max213.le_max_left _ _) hi
    have hib : i ≥ b.N m k := Nat.le_trans (E213.Math.Max213.le_max_right _ _) hi
    have hja : j ≥ a.N m k := Nat.le_trans (E213.Math.Max213.le_max_left _ _) hj
    have hjb : j ≥ b.N m k := Nat.le_trans (E213.Math.Max213.le_max_right _ _) hj
    rw [a.cauchy m k i j hia hja, b.cauchy m k i j hib hjb]

/-- Pointwise cutMin of two CauchyCutSeqs is Cauchy. -/
def CauchyCutSeq.cutMin (a b : CauchyCutSeq) : CauchyCutSeq where
  cs := fun i => E213.Math.Real213.CutSum.cutMin (a.cs i) (b.cs i)
  N := fun m k => Nat.max (a.N m k) (b.N m k)
  cauchy := by
    intro m k i j hi hj
    show (a.cs i m k || b.cs i m k) = (a.cs j m k || b.cs j m k)
    have hia : i ≥ a.N m k := Nat.le_trans (E213.Math.Max213.le_max_left _ _) hi
    have hib : i ≥ b.N m k := Nat.le_trans (E213.Math.Max213.le_max_right _ _) hi
    have hja : j ≥ a.N m k := Nat.le_trans (E213.Math.Max213.le_max_left _ _) hj
    have hjb : j ≥ b.N m k := Nat.le_trans (E213.Math.Max213.le_max_right _ _) hj
    rw [a.cauchy m k i j hia hja, b.cauchy m k i j hib hjb]

/-- Limit of cutMax of two Cauchy seqs = cutMax of limits. -/
theorem CauchyCutSeq.cutMax_limit (a b : CauchyCutSeq) :
    (a.cutMax b).limit = E213.Math.Real213.CutSum.cutMax a.limit b.limit := by
  funext m k
  show (a.cs (Nat.max (a.N m k) (b.N m k)) m k
        && b.cs (Nat.max (a.N m k) (b.N m k)) m k)
       = (a.cs (a.N m k) m k && b.cs (b.N m k) m k)
  rw [a.cauchy m k _ _ (E213.Math.Max213.le_max_left _ _) (Nat.le_refl _)]
  rw [b.cauchy m k _ _ (E213.Math.Max213.le_max_right _ _) (Nat.le_refl _)]

/-- Limit of cutMin of two Cauchy seqs = cutMin of limits. -/
theorem CauchyCutSeq.cutMin_limit (a b : CauchyCutSeq) :
    (a.cutMin b).limit = E213.Math.Real213.CutSum.cutMin a.limit b.limit := by
  funext m k
  show (a.cs (Nat.max (a.N m k) (b.N m k)) m k
        || b.cs (Nat.max (a.N m k) (b.N m k)) m k)
       = (a.cs (a.N m k) m k || b.cs (b.N m k) m k)
  rw [a.cauchy m k _ _ (E213.Math.Max213.le_max_left _ _) (Nat.le_refl _)]
  rw [b.cauchy m k _ _ (E213.Math.Max213.le_max_right _ _) (Nat.le_refl _)]

/-- Pointwise cutDouble of a Cauchy seq is Cauchy.
    Modulus shifts: N (m, k) := a.N m (2k). -/
def CauchyCutSeq.cutDouble (a : CauchyCutSeq) : CauchyCutSeq where
  cs := fun i => E213.Math.Real213.CutSum.cutDouble (a.cs i)
  N := fun m k => a.N m (2*k)
  cauchy := by
    intro m k i j hi hj
    show a.cs i m (2*k) = a.cs j m (2*k)
    exact a.cauchy m (2*k) i j hi hj

/-- Limit of cutDouble of a Cauchy seq = cutDouble of limit. -/
theorem CauchyCutSeq.cutDouble_limit (a : CauchyCutSeq) :
    a.cutDouble.limit = E213.Math.Real213.CutSum.cutDouble a.limit := by
  funext m k
  show a.cs (a.N m (2*k)) m (2*k) = a.cs (a.N m (2*k)) m (2*k)
  rfl

/-- Pointwise cutHalf of a Cauchy seq is Cauchy.
    Modulus: N (m, k) := a.N (2m) k. -/
def CauchyCutSeq.cutHalf (a : CauchyCutSeq) : CauchyCutSeq where
  cs := fun i => E213.Math.Real213.CutSum.cutHalf (a.cs i)
  N := fun m k => a.N (2*m) k
  cauchy := by
    intro m k i j hi hj
    show a.cs i (2*m) k = a.cs j (2*m) k
    exact a.cauchy (2*m) k i j hi hj

/-- Limit of cutHalf of a Cauchy seq = cutHalf of limit. -/
theorem CauchyCutSeq.cutHalf_limit (a : CauchyCutSeq) :
    a.cutHalf.limit = E213.Math.Real213.CutSum.cutHalf a.limit := by
  funext m k
  show a.cs (a.N (2*m) k) (2*m) k = a.cs (a.N (2*m) k) (2*m) k
  rfl

/-- Idempotence at limit: (a.cutMax a).limit = a.limit. -/
theorem CauchyCutSeq.cutMax_self_limit (a : CauchyCutSeq) :
    (a.cutMax a).limit = a.limit := by
  rw [cutMax_limit, E213.Math.Real213.CutSum.cutMax_idempotent]

/-- Idempotence at limit: (a.cutMin a).limit = a.limit. -/
theorem CauchyCutSeq.cutMin_self_limit (a : CauchyCutSeq) :
    (a.cutMin a).limit = a.limit := by
  rw [cutMin_limit, E213.Math.Real213.CutSum.cutMin_idempotent]

/-- cutDouble and cutHalf commute at the limit on Cauchy sequences. -/
theorem CauchyCutSeq.cutDouble_cutHalf_comm_limit (a : CauchyCutSeq) :
    a.cutDouble.cutHalf.limit = a.cutHalf.cutDouble.limit := by
  rw [cutHalf_limit, cutDouble_limit, cutDouble_limit, cutHalf_limit]
  exact (E213.Math.Real213.CutSum.cutDouble_cutHalf_comm _).symm

/-- Lattice distributivity at the Cauchy limit:
    a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c). -/
theorem CauchyCutSeq.cutMin_distrib_cutMax_limit
    (a b c : CauchyCutSeq) :
    (a.cutMin (b.cutMax c)).limit
    = ((a.cutMin b).cutMax (a.cutMin c)).limit := by
  rw [cutMin_limit, cutMax_limit, cutMax_limit, cutMin_limit, cutMin_limit]
  exact E213.Math.Real213.CutSum.cutMin_distrib_cutMax _ _ _

/-- Lattice distributivity at the Cauchy limit:
    a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c). -/
theorem CauchyCutSeq.cutMax_distrib_cutMin_limit
    (a b c : CauchyCutSeq) :
    (a.cutMax (b.cutMin c)).limit
    = ((a.cutMax b).cutMin (a.cutMax c)).limit := by
  rw [cutMax_limit, cutMin_limit, cutMin_limit, cutMax_limit, cutMax_limit]
  exact E213.Math.Real213.CutSum.cutMax_distrib_cutMin _ _ _

/-- cutMax is commutative at the Cauchy limit. -/
theorem CauchyCutSeq.cutMax_comm_limit (a b : CauchyCutSeq) :
    (a.cutMax b).limit = (b.cutMax a).limit := by
  rw [cutMax_limit, cutMax_limit]
  exact E213.Math.Real213.CutSum.cutMax_comm _ _

/-- cutMin is commutative at the Cauchy limit. -/
theorem CauchyCutSeq.cutMin_comm_limit (a b : CauchyCutSeq) :
    (a.cutMin b).limit = (b.cutMin a).limit := by
  rw [cutMin_limit, cutMin_limit]
  exact E213.Math.Real213.CutSum.cutMin_comm _ _

/-- cutMax is associative at the Cauchy limit. -/
theorem CauchyCutSeq.cutMax_assoc_limit (a b c : CauchyCutSeq) :
    ((a.cutMax b).cutMax c).limit
    = (a.cutMax (b.cutMax c)).limit := by
  rw [cutMax_limit, cutMax_limit, cutMax_limit, cutMax_limit]
  exact E213.Math.Real213.CutSum.cutMax_assoc _ _ _

/-- cutMin is associative at the Cauchy limit. -/
theorem CauchyCutSeq.cutMin_assoc_limit (a b c : CauchyCutSeq) :
    ((a.cutMin b).cutMin c).limit
    = (a.cutMin (b.cutMin c)).limit := by
  rw [cutMin_limit, cutMin_limit, cutMin_limit, cutMin_limit]
  exact E213.Math.Real213.CutSum.cutMin_assoc _ _ _

end E213.Math.Real213.CauchyLattice
