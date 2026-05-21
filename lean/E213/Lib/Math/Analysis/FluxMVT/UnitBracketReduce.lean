import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Mul.CutMul
import E213.Lib.Math.Real213.Mul.CutMulDetermined
import E213.Lib.Math.Real213.Mul.CutMulOne
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Real213.Sum.CutSumZero
/-!
# unitBracket cutMulOuter reduction template — G110 FLUX-1

Extracts the recurring 6-line `cutMulOuter_congr` block from
forward/backward MVT/fluxAlong proofs at the unit bracket.  The block
appears ~10× in `FluxMVTPolynomial.lean` (square/cube/quartic + cutPow,
each ×2 for forward/backward) and 4× in `FluxMVTPassthrough.lean`
(the `_pure` variants).

`cutMulOuter_unitBracket_reduce_at` encapsulates the call to
`cutMulOuter_congr` with the canonical bound `(m+1)*(k+1)`.  Caller
supplies the per-instance pointwise reductions `hL` and `hR`; then a
short `rw [...] ; exact <closer>` finishes the proof.
-/

namespace E213.Lib.Math.Analysis.FluxMVT.UnitBracketReduce

open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Mul.CutMul (cutMulOuter)
open E213.Lib.Math.Real213.Mul.CutMulDetermined (cutMulOuter_congr)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-- ★ Generic ∅-axiom reduction (constCut s 1 targets): rewrite
    `cutMulOuter f g k m ((m+1)*(k+1)) ((m+1)*(k+1))`
    to
    `cutMulOuter (constCut sL 1) (constCut sR 1) k m …`
    using `cutMulOuter_congr` + pointwise reductions.  PURE. -/
theorem cutMulOuter_unitBracket_reduce_at
    (f g : Nat → Nat → Bool) (sL sR : Nat) (m k : Nat)
    (hL : ∀ m', m' ≤ (m+1)*(k+1) → f m' k = constCut sL 1 m' k)
    (hR : ∀ m', m' ≤ (m+1)*(k+1) → g m' k = constCut sR 1 m' k) :
    cutMulOuter f g k m ((m+1)*(k+1)) ((m+1)*(k+1))
      = cutMulOuter (constCut sL 1) (constCut sR 1) k m ((m+1)*(k+1)) ((m+1)*(k+1)) :=
  cutMulOuter_congr k m ((m+1)*(k+1)) ((m+1)*(k+1))
    f (constCut sL 1) g (constCut sR 1) hL hR
    ((m+1)*(k+1)) (Nat.le_refl _)

/-- ★ Generic ∅-axiom reduction (arbitrary targets): mirror of
    `cutSumAux_unitBracket_reduce_at`.  Caller specifies arbitrary
    target cuts `gL`, `gR`.  Includes the cutMul-locality bound `bound`
    as an explicit parameter (`(m+1)*(k+1)` for cutMul, but the helper
    works for any bound). -/
theorem cutMulOuter_reduce_at
    (f g gL gR : Nat → Nat → Bool) (m k bound : Nat)
    (hL : ∀ m', m' ≤ bound → f m' k = gL m' k)
    (hR : ∀ m', m' ≤ bound → g m' k = gR m' k) :
    cutMulOuter f g k m bound bound = cutMulOuter gL gR k m bound bound :=
  cutMulOuter_congr k m bound bound f gL g gR hL hR bound (Nat.le_refl _)

end E213.Lib.Math.Analysis.FluxMVT.UnitBracketReduce
