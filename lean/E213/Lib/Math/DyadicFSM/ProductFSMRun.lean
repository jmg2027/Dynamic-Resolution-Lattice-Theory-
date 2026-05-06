import E213.Lib.Math.DyadicFSM.ProductFSM

import E213.Lib.Math.DyadicFSM.BitFSM
import E213.Lib.Math.DyadicFSM.ProductHelpers
/-!
# Product FSM run/bit decomposition

Proves that decoding the product FSM's run gives back the
component runs:
  decodeFinFirst  ((product f1 f2).run k) = f1.run k
  decodeFinSecond ((product f1 f2).run k) = f2.run k

And consequently:
  (product f1 f2).bits k = g (f1.bits k) (f2.bits k)
-/

namespace E213.Lib.Math.DyadicFSM.ProductFSMRun

open E213.Lib.Math.DyadicFSM.BitFSM (BitFSM)
open E213.Lib.Math.DyadicFSM.ProductHelpers (decodeFinFirst decodeFinSecond encodeFinPair decode_encode_first decode_encode_second)


/-- ★★★★ Product FSM run decodes to component runs. -/
theorem product_run_decode {n m : Nat} (hm : 0 < m)
    (f1 : BitFSM n) (f2 : BitFSM m) (g : Bool → Bool → Bool) (k : Nat) :
    decodeFinFirst hm ((E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).run k) = f1.run k
    ∧ decodeFinSecond hm ((E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).run k) = f2.run k := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · exact decode_encode_first hm f1.init f2.init
    · exact decode_encode_second hm f1.init f2.init
  | succ k' ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨?_, ?_⟩
    · show decodeFinFirst hm
        ((E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).step
          ((E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).run k')) = f1.step (f1.run k')
      show decodeFinFirst hm
        (encodeFinPair
          (f1.step (decodeFinFirst hm ((E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).run k')))
          (f2.step (decodeFinSecond hm ((E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).run k'))))
        = f1.step (f1.run k')
      rw [decode_encode_first, ih1]
    · show decodeFinSecond hm
        ((E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).step
          ((E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).run k')) = f2.step (f2.run k')
      show decodeFinSecond hm
        (encodeFinPair
          (f1.step (decodeFinFirst hm ((E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).run k')))
          (f2.step (decodeFinSecond hm ((E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).run k'))))
        = f2.step (f2.run k')
      rw [decode_encode_second, ih2]

/-- ★★★★★ Product FSM bit stream = g applied componentwise. -/
theorem product_bits_eq {n m : Nat} (hm : 0 < m)
    (f1 : BitFSM n) (f2 : BitFSM m) (g : Bool → Bool → Bool) (k : Nat) :
    (E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).bits k = g (f1.bits k) (f2.bits k) := by
  show (E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).out
        ((E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).run k)
      = g (f1.out (f1.run k)) (f2.out (f2.run k))
  show g
        (f1.out (decodeFinFirst hm ((E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).run k)))
        (f2.out (decodeFinSecond hm ((E213.Lib.Math.DyadicFSM.ProductFSM.BitFSM.product hm f1 f2 g).run k)))
      = g (f1.out (f1.run k)) (f2.out (f2.run k))
  rw [(product_run_decode hm f1 f2 g k).1, (product_run_decode hm f1 f2 g k).2]

end E213.Lib.Math.DyadicFSM.ProductFSMRun
