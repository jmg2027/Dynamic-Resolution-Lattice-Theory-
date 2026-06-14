import E213.Lib.Math.NumberSystems.SignedCut.Core.Core
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSum
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest

/-!
# SignedCut — Cancellation equivalence (∅-axiom)

213-native paradigm: the difference-Lens readout (`(m,n) ↦ m−n`),
of which the classical Grothendieck ℤ-from-ℕ quotient is the
flattened image (`06_lens_readings.md` §6.7;
`theory/essays/analysis/integers_as_difference_lens.md`).  Two
signed cuts `(p, n)` and `(p', n')` are identified by the
difference-Lens iff they are **cross-additive equal**:

  `(p, n) ~ (p', n')`  ⟺  `cutSum p n' = cutSum p' n` (pointwise)

This captures cancellation: `(a+c, b+c) ~ (a, b)` because
`cutSum (a+c) b = cutSum (b+c) a` (sum is commutative).

The equivalence is an *internal structural relation* among pairs,
not a quotient — no `Quot.sound` leak, and no exterior value-layer
at which representatives secretly coincide (`05_no_exterior.md`
§5.1; the tuple is the number).  Interchangeability **is** this
relation; at the cut layer the pairs remain distinct types.
-/

namespace E213.Lib.Math.NumberSystems.SignedCut.Core.Equivalence

open E213.Lib.Math.NumberSystems.SignedCut.Core.Core (SignedCut pos neg ofPos)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-- Pointwise cross-additive equality on a single (m, k) pair. -/
def signedEqAt (s t : SignedCut) (m k : Nat) : Prop :=
  cutSum (pos s) (neg t) m k = cutSum (pos t) (neg s) m k

/-- ★ Pointwise reflexivity (rfl). -/
theorem signedEqAt_refl (s : SignedCut) (m k : Nat) :
    signedEqAt s s m k := rfl

/-- ★ Pointwise symmetry. -/
theorem signedEqAt_symm (s t : SignedCut) (m k : Nat) :
    signedEqAt s t m k → signedEqAt t s m k :=
  fun h => h.symm

/-- ★ Self-equivalence at every (m, k). -/
theorem signedEq_refl (s : SignedCut) :
    ∀ m k, signedEqAt s s m k := fun _ _ => rfl

end E213.Lib.Math.NumberSystems.SignedCut.Core.Equivalence
