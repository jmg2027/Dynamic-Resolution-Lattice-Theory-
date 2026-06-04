import E213.Lib.Math.Algebra.CayleyDickson.Levels.CayleyAlgebra213
import E213.Lib.Math.Algebra.CayleyDickson.Levels.CayleyHeavy
import E213.Meta.Algebra213.CDDoubleMoufang

/-!
# `MoufangIntegerNormed213 Cayley` (Type A L3) via the polarization bridge

Cayley (integer octonions, `CDDouble Lipschitz`, 240 unit octonions)
doubles the **non-commutative** associative base Lipschitz, so the
Moufang norm-collapse is the genuine degree-4 Hurwitz identity.  We
supply `TraceNormed213 Lipschitz` (quaternion trace `2·re` on the inner
ZI real axis), which makes the abstract `instMoufangIntegerNormed213CDDouble`
fire on `CDDouble Lipschitz`; the concrete instance then bridges through
`toCDDouble`.

This replaces `CayleyHeavy.normSq_mul`'s `hurwitz_ring` brute force
(`maxHeartbeats 4000000`, 32-Int-var expansion) with the structural
polarization derivation.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Levels.Cayley

open E213.Meta.Algebra213
open E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble
open E213.Lib.Math.Algebra.CayleyDickson.Tower.CDDouble.Lipschitz
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI

-- `TraceNormed213 Lipschitz` (the polarization condition) now lives in
-- `LipschitzAlgebra213` so `CayleyHeavy` can reuse it without a cycle.

/-- Real-axis integer embed for Cayley. -/
def ofInt (n : Int) : Cayley := ⟨Lipschitz.ofInt n, 0⟩

theorem toCDDouble_ofInt (n : Int) :
    toCDDouble (ofInt n) = cdm_ofInt n := by
  apply CDDouble.ext
  · show Lipschitz.ofInt n = IntegerNormed213.ofInt n; rfl
  · show (0 : Lipschitz) = 0; rfl

private theorem cay_self_mul_conj (u : Cayley) :
    u * Cayley.conj u = ofInt (E213.Lib.Math.Algebra.CayleyDickson.Levels.CayleyHeavy.normSq u) := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_conj, toCDDouble_ofInt]
  exact cd_self_mul_conj (toCDDouble u)

private theorem cay_ofInt_mul (a b : Int) :
    ofInt a * ofInt b = ofInt (a * b) := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_ofInt, toCDDouble_ofInt, toCDDouble_ofInt]
  exact cd_ofInt_mul a b

private theorem cay_ofInt_central (z : Int) (u : Cayley) :
    ofInt z * u = u * ofInt z := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_mul, toCDDouble_ofInt]
  exact cd_ofInt_central z (toCDDouble u)

private theorem cay_ofInt_inj {a b : Int}
    (h : (ofInt a : Cayley) = ofInt b) : a = b := by
  apply @cd_ofInt_inj Lipschitz _ a b
  rw [← toCDDouble_ofInt, ← toCDDouble_ofInt, h]

private theorem cay_moufang_norm (u v : Cayley) :
    (u * v) * (Cayley.conj v * Cayley.conj u)
      = u * (v * Cayley.conj v) * Cayley.conj u := by
  apply toCDDouble_inj
  repeat rw [toCDDouble_mul]
  repeat rw [toCDDouble_conj]
  exact cd_moufang_norm (toCDDouble u) (toCDDouble v)

private theorem cay_ofInt_paren_central (z : Int) (u : Cayley) :
    u * ofInt z * Cayley.conj u = ofInt z * (u * Cayley.conj u) := by
  apply toCDDouble_inj
  repeat rw [toCDDouble_mul]
  repeat rw [toCDDouble_conj]
  repeat rw [toCDDouble_ofInt]
  exact cd_ofInt_paren_central z (toCDDouble u)

/-- ★ MoufangIntegerNormed213 Cayley — Type A L3 (integer octonions).
    The Moufang norm-collapse is the polarization-cancelled Hurwitz
    identity bridged from `cd_moufang_norm`. -/
instance : MoufangIntegerNormed213 Cayley where
  ofInt               := ofInt
  normSq              := E213.Lib.Math.Algebra.CayleyDickson.Levels.CayleyHeavy.normSq
  self_mul_conj       := cay_self_mul_conj
  ofInt_mul           := cay_ofInt_mul
  ofInt_central       := cay_ofInt_central
  ofInt_inj           := cay_ofInt_inj
  moufang_norm        := cay_moufang_norm
  ofInt_paren_central := cay_ofInt_paren_central

/-- ★ Witness: octonion Hurwitz norm composition via the generic
    `MoufangIntegerNormed213.normSq_mul` — strict ∅-axiom, replacing the
    `hurwitz_ring` brute force in `CayleyHeavy`. -/
theorem moufang_normSq_mul (u v : Cayley) :
    E213.Lib.Math.Algebra.CayleyDickson.Levels.CayleyHeavy.normSq (u * v) = E213.Lib.Math.Algebra.CayleyDickson.Levels.CayleyHeavy.normSq u * E213.Lib.Math.Algebra.CayleyDickson.Levels.CayleyHeavy.normSq v :=
  MoufangIntegerNormed213.normSq_mul u v

end E213.Lib.Math.Algebra.CayleyDickson.Levels.Cayley
