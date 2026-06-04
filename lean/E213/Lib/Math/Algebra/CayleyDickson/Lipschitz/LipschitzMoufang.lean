import E213.Lib.Math.Algebra.CayleyDickson.Lipschitz.LipschitzAlgebra213
import E213.Meta.Algebra213.AlternativeNormed

/-!
# `Lipschitz` as a `MoufangIntegerNormed213` instance

Lipschitz (= integer quaternions, Type A L2) is the Type A
counterpart to ZOmegaDouble's Phase 4 registration.  Both are
associative quaternion-analog CD layers (over commutative star
integer ring bases), and both satisfy the Moufang norm-collapse
identity trivially via `Ring213.mul_assoc`.

Generic `MoufangIntegerNormed213.normSq_mul` then provides
`Lipschitz.moufang_normSq_mul` via typeclass projection — same
result as the existing typeclass-derived
`LipschitzHeavy.normSq_mul` (via `IntegerNormed213.normSq_mul`),
arrived at through a parallel calc chain.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz

open E213.Meta.Algebra213
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI

private theorem lip_moufang_norm (u v : Lipschitz) :
    (u * v) * (Lipschitz.conj v * Lipschitz.conj u)
      = u * (v * Lipschitz.conj v) * Lipschitz.conj u := by
  rw [← Ring213.mul_assoc (u * v) (Lipschitz.conj v)
                          (Lipschitz.conj u),
      Ring213.mul_assoc u v (Lipschitz.conj v)]

private theorem lip_ofInt_paren_central (z : Int) (u : Lipschitz) :
    u * ofInt z * Lipschitz.conj u
      = ofInt z * (u * Lipschitz.conj u) := by
  rw [show u * ofInt z = ofInt z * u from
        (@IntegerNormed213.ofInt_central Lipschitz _ z u).symm,
      Ring213.mul_assoc (ofInt z) u (Lipschitz.conj u)]

/-- ★ MoufangIntegerNormed213 Lipschitz — Type A L2.  Moufang
    trivially via mul_assoc (associative).  Parallel to
    ZOmegaDouble's Phase 4 instance (Type C L3 base layer). -/
instance : MoufangIntegerNormed213 Lipschitz where
  ofInt               := ofInt
  normSq              := normSq
  self_mul_conj       := IntegerNormed213.self_mul_conj
  ofInt_mul           := IntegerNormed213.ofInt_mul
  ofInt_central       := IntegerNormed213.ofInt_central
  ofInt_inj           := IntegerNormed213.ofInt_inj
  moufang_norm        := lip_moufang_norm
  ofInt_paren_central := lip_ofInt_paren_central

/-- ★ Witness: Lipschitz's `normSq_mul` derived via the generic
    `MoufangIntegerNormed213.normSq_mul`.  Same value as the existing
    `LipschitzHeavy.normSq_mul` (via `IntegerNormed213.normSq_mul`),
    obtained through a parallel calc chain using the Moufang field
    + ofInt_paren_central. -/
theorem moufang_normSq_mul (u v : Lipschitz) :
    normSq (u * v) = normSq u * normSq v :=
  MoufangIntegerNormed213.normSq_mul u v

end E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz
