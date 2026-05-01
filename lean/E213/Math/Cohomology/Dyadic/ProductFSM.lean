import E213.Math.Cohomology.Dyadic.ProductHelpers

/-!
# BitFSM.product — universal lens composition at FSM level

Given two BitFSMs `f1 : BitFSM n` and `f2 : BitFSM m` and a
combination function `g : Bool → Bool → Bool`, produces a single
`BitFSM (n * m)` whose state is the pair-encoding of (f1 state, f2 state)
and whose bit stream is `λ k => g (f1.bits k) (f2.bits k)`.

The "lens composition" structure: combine via product state space,
read out via g.  Universal — no coprimality needed.
-/

namespace E213.Math.Cohomology.Dyadic.ProductFSM

/-- ★★★ Generic product BitFSM via pair-encoding. -/
def BitFSM.product {n m : Nat} (hm : 0 < m)
    (f1 : BitFSM n) (f2 : BitFSM m) (g : Bool → Bool → Bool)
    : BitFSM (n * m) where
  init := encodeFinPair f1.init f2.init
  step v := encodeFinPair
    (f1.step (decodeFinFirst hm v))
    (f2.step (decodeFinSecond hm v))
  out v := g
    (f1.out (decodeFinFirst hm v))
    (f2.out (decodeFinSecond hm v))

end E213.Math.Cohomology.Dyadic.ProductFSM
