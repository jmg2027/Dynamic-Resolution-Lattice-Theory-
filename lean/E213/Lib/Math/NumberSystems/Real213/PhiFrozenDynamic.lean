import E213.Lib.Math.NumberSystems.Real213.PhiCauchyLimit
import E213.Lib.Math.NumberSystems.Real213.FibCassiniNat
import E213.Lib.Math.Mobius213.Px.CharPolySelf

/-!
# PhiFrozenDynamic — φ frozen = dynamic, identified (the §5.7 synthesis)

`seed/AXIOM/05_no_exterior.md` §5.7 names two readings of the golden ratio φ:

  * **frozen** — φ as `P`'s *algebraic fixed point*: the static eigen/fixed-point datum of the
    Möbius matrix `P = [[2,1],[1,1]]` (trace `NS = 3`, det `1`), whose characteristic
    discriminant is `(L 1)² − 4 = 5`;
  * **dynamic** — φ as the *limit of the Pell iteration*: the Cauchy limit of the rational
    Fibonacci convergents `fib(2n+2)/fib(2n+1)`, which are exactly `P`'s Möbius orbit
    (`MobiusSelfForm.mobius_iteration_master`).

These are **the same object**, and the identification is ∅-axiom — it does not need a foreign
real-number theory, because the 213 real layer (`Analysis/CauchyComplete`, `PhiAsCut`) builds φ
two ways and proves them the *same cut* (`PhiCauchyLimit.phiCauchy_limit_eq_phiCut`).  This file
makes the §5.7 statement explicit as one theorem, anchoring the **frozen** side to `P`'s
characteristic discriminant and exhibiting the **residue** between the readings: the `Nat` orbit
stays exactly the unit `1` off the frozen relation and never reaches it.

So §5.7 is *closed*: frozen and dynamic φ are identified, with the residue unit `1` between them
(the convergent never lands on the fixed-point relation — `convergent_never_frozen`).
-/

namespace E213.Lib.Math.NumberSystems.Real213.PhiFrozenDynamic

open E213.Lib.Math.NumberSystems.Real213.PhiCauchyLimit (phiConvergentSeq phiCauchy_limit_eq_phiCut)
open E213.Lib.Math.NumberSystems.Real213.FibCassiniNat (fib_cassini_norm convergent_never_frozen)
open E213.Lib.Math.Mobius213.Px.POrbitClosure (L)
open E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock (fib)

/-- ★★ **The frozen cut's discriminant is `P`'s characteristic discriminant.**  `phiCut`'s
    defining `5` (the cut `5k² ≤ (2m−k)²`) is exactly `P`'s char-poly discriminant
    `(L 1)² − 4` (`L 1 = NS = trace P = 3`).  So the *frozen* φ is `P`'s algebraic fixed-point
    datum, not an independent constant. -/
theorem phi_discriminant_is_P_charpoly : ((L 1) ^ 2 - 4 : Int) = 5 := by decide

/-- ★★★ **φ frozen = dynamic, identified (§5.7), with the residue unit between.**  For all
    `m k n`:

    1. **frozen, algebraic** — the cut φ's discriminant is `P`'s characteristic discriminant
       `(L 1)² − 4 = 5` (`phi_discriminant_is_P_charpoly`): the frozen φ is `P`'s fixed-point
       datum;
    2. **dynamic = frozen** — the Pell-convergent Cauchy limit *is* the closed-form φ cut,
       pointwise (`phiCauchy_limit_eq_phiCut`): the limit of `P`'s Möbius orbit lands on the
       *same* 213-native cut as the algebraic φ;
    3. **the residue between** — the `Nat` orbit stays exactly the unit `1` off the frozen
       fixed-point relation (`fib_cassini_norm`: `a² + 1 = a·b + b²`) and therefore *never*
       satisfies it (`convergent_never_frozen`): the dynamic approaches but never reaches the
       frozen, the gap being the irreducible unit `1`.

    Frozen and dynamic φ are one object; the residue is the unit `1` between the approach and
    the limit.  ∅-axiom (the identification (2) is the 213 real layer's, not a foreign reals'). -/
theorem frozen_eq_dynamic_phi (m k n : Nat) :
    ((L 1) ^ 2 - 4 : Int) = 5
    ∧ phiConvergentSeq.limit m k = E213.Lib.Math.NumberSystems.Real213.PhiAsCut.phiCut m k
    ∧ (fib (2 * n + 2) * fib (2 * n + 2) + 1
          = fib (2 * n + 2) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 1)
        ∧ fib (2 * n + 2) * fib (2 * n + 2)
          ≠ fib (2 * n + 2) * fib (2 * n + 1) + fib (2 * n + 1) * fib (2 * n + 1)) :=
  ⟨phi_discriminant_is_P_charpoly,
   phiCauchy_limit_eq_phiCut m k,
   ⟨fib_cassini_norm n, convergent_never_frozen n⟩⟩

end E213.Lib.Math.NumberSystems.Real213.PhiFrozenDynamic
