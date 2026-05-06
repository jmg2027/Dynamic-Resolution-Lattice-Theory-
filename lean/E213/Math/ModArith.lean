import E213.Math.ModArith.JoinBezout
import E213.Math.ModArith.JoinCoprime
import E213.Math.ModArith.JoinEquivGCD
import E213.Math.ModArith.JoinEuclidean
import E213.Math.ModArith.JoinExample
import E213.Math.ModArith.JoinGCD
import E213.Math.ModArith.LensCRT
import E213.Math.ModArith.PureNatMod3
import E213.Math.ModArith.PureNatMod5

/-! Spec-as-code entry point for `E213.Math.ModArith`.

  213-native modular arithmetic on Nat.

  ## Join family (Lens-join derivations of standard results)

    * `JoinGCD`      — GCD via Lens-join
    * `JoinBezout`   — Bézout's identity
    * `JoinEuclidean` — Euclidean algorithm
    * `JoinCoprime`  — coprimality witness
    * `JoinEquivGCD` — GCD-equivalence Lens
    * `JoinExample`  — worked example consolidating the above

  ## Lens-CRT

    * `LensCRT`      — Chinese remainder theorem as Lens
                       composition

  ## Concrete instances

    * `PureNatMod3`  — pure-Nat mod-3 arithmetic
    * `PureNatMod5`  — pure-Nat mod-5 arithmetic
-/
