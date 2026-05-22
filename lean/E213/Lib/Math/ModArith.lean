import E213.Lib.Math.ModArith.JoinBezout
import E213.Lib.Math.ModArith.JoinCoprime
import E213.Lib.Math.ModArith.JoinEquivGCD
import E213.Lib.Math.ModArith.JoinEuclidean
import E213.Lib.Math.ModArith.JoinExample
import E213.Lib.Math.ModArith.JoinGCD
import E213.Lib.Math.ModArith.LensCRT
import E213.Lib.Math.ModArith.PureNatMod3
import E213.Lib.Math.ModArith.PureNatMod5
import E213.Lib.Math.ModArith.ModBezout
import E213.Lib.Math.ModArith.ModBezoutInvariant
import E213.Lib.Math.ModArith.UniversalFLT
import E213.Lib.Math.ModArith.FP2Sqrt5

/-! Spec-as-code entry point for `E213.Lib.Math.ModArith`.

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

  ## G119 marathon additions (Bezout / FLT / F_{p²})

    * `ModBezout`           — Bezout coefficients via Nat xgcd
    * `ModBezoutInvariant`  — universal modular inverse via Bezout
    * `UniversalFLT`        — Fermat's Little Theorem, universal in
                              prime p (Binomial / FreshmanDream /
                              FLTPrimary / FLTMain chain)
    * `FP2Sqrt5`            — F_{p²} = F_p[√5]: quadratic extension
                              of F_p adjoining √5, with Frobenius
                              x ↦ x^p as a ring endomorphism
-/
