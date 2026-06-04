import E213.Lib.Math.Analysis.Functional.Norm
import E213.Lib.Math.Analysis.Functional.InnerProduct
import E213.Lib.Math.Analysis.Functional.LinearOperator
import E213.Lib.Math.Analysis.Functional.Spectrum

/-!
# Functional Analysis 213 — Capstone synthesis

5 cluster witnesses + total bundle.  All ∅-axiom.

213-native paradigm: Hahn-Banach / open mapping rejected (Choice
needed).  Constructive content (norm, inner product, operator,
spectrum on finite grid) preserved without any axiom-bloat.
-/

namespace E213.Lib.Math.Analysis.Functional.Capstone

open E213.Lib.Math.Analysis.Functional.Norm
  (lInfNorm l1Norm constFn lInf_zero l1_zero l1_const lInf_one)
open E213.Lib.Math.Analysis.Functional.InnerProduct
  (innerNum addFn inner_zero inner_comm inner_left_additive)
open E213.Lib.Math.Analysis.Functional.LinearOperator
  (LinOp idOp zeroOp scaleOp composeOp id_at zero_at scale_const
   compose_id_left)
open E213.Lib.Math.Analysis.Functional.Spectrum
  (IsEigenpair id_eigen scale_eigen zero_eigen compose_scale_eigen)

/-- ★ **Norm witness** — finite-grid norms behave correctly. -/
theorem norm_witness (n c : Nat) (f : Nat → Nat) :
    lInfNorm 0 f = 0
    ∧ l1Norm 0 f = 0
    ∧ l1Norm n (constFn c) = n * c
    ∧ lInfNorm 1 f = f 0 :=
  ⟨lInf_zero f, l1_zero f, l1_const n c, lInf_one f⟩

/-- ★ **Inner-product witness** — empty / symmetry / left-bilinear. -/
theorem inner_witness (n : Nat) (f h g : Nat → Nat) :
    innerNum 0 f g = 0
    ∧ innerNum n f g = innerNum n g f
    ∧ innerNum n (addFn f h) g = innerNum n f g + innerNum n h g :=
  ⟨inner_zero f g, inner_comm n f g, inner_left_additive n f h g⟩

/-- ★ **Operator witness** — id / zero / scale / compose-with-id. -/
theorem operator_witness (c : Nat) (T : LinOp) (f : Nat → Nat)
    (i : Nat) :
    idOp f = f
    ∧ zeroOp f i = 0
    ∧ scaleOp c (constFn c) i = c * c
    ∧ composeOp idOp T f = T f :=
  ⟨id_at f, zero_at f i, scale_const c c i, compose_id_left T f⟩

/-- ★ **Spectrum witness** — id / scale / zero eigenvalues. -/
theorem spectrum_witness (c : Nat) (v : Nat → Nat) :
    IsEigenpair idOp 1 v
    ∧ IsEigenpair (scaleOp c) c v
    ∧ IsEigenpair zeroOp 0 v :=
  ⟨id_eigen v, scale_eigen c v, zero_eigen v⟩

/-- ★★★ **Total witness** ★★★ — 5-fact bundle covering norm,
    inner product, operator, spectrum. -/
theorem total_witness (c : Nat) (f g v : Nat → Nat)
    (n i : Nat) :
    l1Norm n (constFn c) = n * c
    ∧ innerNum n f g = innerNum n g f
    ∧ idOp f = f
    ∧ scaleOp c (constFn c) i = c * c
    ∧ IsEigenpair (scaleOp c) c v :=
  ⟨l1_const n c, inner_comm n f g, id_at f,
   scale_const c c i, scale_eigen c v⟩

end E213.Lib.Math.Analysis.Functional.Capstone
