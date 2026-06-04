import E213.Lib.Math.NumberTheory.ModArith.JoinBezout
import E213.Lib.Math.NumberTheory.ModArith.JoinCoprime
import E213.Lib.Math.NumberTheory.ModArith.JoinEquivGCD
import E213.Lib.Math.NumberTheory.ModArith.JoinEuclidean
import E213.Lib.Math.NumberTheory.ModArith.JoinExample
import E213.Lib.Math.NumberTheory.ModArith.JoinGCD
import E213.Lib.Math.NumberTheory.ModArith.LensCRT
import E213.Lib.Math.NumberTheory.ModArith.PureNatMod3
import E213.Lib.Math.NumberTheory.ModArith.PureNatMod5
import E213.Lib.Math.NumberTheory.ModArith.EisensteinFormCharacter
import E213.Lib.Math.NumberTheory.ModArith.ModBezout
import E213.Lib.Math.NumberTheory.ModArith.ModBezoutInvariant
import E213.Lib.Math.NumberTheory.ModArith.UniversalFLT
import E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor
import E213.Lib.Math.NumberTheory.ModArith.FP2Sqrt5
import E213.Lib.Math.NumberTheory.ModArith.FP2SqrtD

/-! Spec-as-code entry point for `E213.Lib.Math.NumberTheory.ModArith`.

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
    * `EisensteinFormCharacter` — `mod3` ring-hom + the χ₋₃ fingerprint of the disc-`−3`
      Eisenstein form `a²+ab+b²` (never `≡ 2 mod 3`), the Epstein-zeta / period skeleton

  ## Companion identities (Bezout / FLT / F_{p²})

    * `ModBezout`           — Bezout coefficients via Nat xgcd
    * `ModBezoutInvariant`  — universal modular inverse via Bezout
    * `UniversalFLT`        — Fermat's Little Theorem, universal in
                              prime p (Binomial / FreshmanDream /
                              FLTPrimary / FLTMain chain)
    * `FP2Sqrt5`            — F_{p²} = F_p[√5]: quadratic extension
                              of F_p adjoining √5, with Frobenius
                              x ↦ x^p as a ring endomorphism
    * `FP2SqrtD`            — F_{p²} = F_p[√D]: same construction
                              parametric in D (generalises FP2Sqrt5)
-/
