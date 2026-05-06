import E213.Math.DyadicFSM.ArithFSM.Mod5
import E213.Math.DyadicFSM.ForwardEventual

import E213.Math.DyadicFSM.ArithFSM
import E213.Math.DyadicFSM.Signature
/-!
# ArithFSM ⇒ K_{3,2}^{(2)} signature eventually periodic

Direct corollaries chaining the Pell-style ArithFSM family
(mod 2, mod 3, mod 5) into the K_{3,2}^{(2)} signature lens
via `signature_eventually_periodic_of_eventually_periodic_bits`.

Pell mod-N bit streams are universally periodic from step 0,
so the eventual-period theorem applies with N₀ = 0.
-/

namespace E213.Math.DyadicFSM.ArithFSM.Signature

open E213.Math.DyadicFSM.ForwardEventual (signature_eventually_periodic_of_eventually_periodic_bits)
open E213.Math.DyadicFSM.Signature (signature)
open E213.Math.DyadicFSM.ArithFSM (pellFSMmod2 pellFSMmod3)
open E213.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)


/-- ★★★ Pell mod-2 signature is eventually (in fact: from step 0)
    periodic. -/
theorem pellFSMmod2_signature_eventually_periodic :
    ∃ N P, 0 < P ∧ ∀ n, n ≥ N →
      signature pellFSMmod2.bits (n + P) = signature pellFSMmod2.bits n :=
  signature_eventually_periodic_of_eventually_periodic_bits
    pellFSMmod2.bits 3 0 (by decide)
    (fun n _ => pellFSMmod2_bits_period_3 n)

/-- ★★★ Pell mod-3 signature is eventually periodic. -/
theorem pellFSMmod3_signature_eventually_periodic :
    ∃ N P, 0 < P ∧ ∀ n, n ≥ N →
      signature pellFSMmod3.bits (n + P) = signature pellFSMmod3.bits n :=
  signature_eventually_periodic_of_eventually_periodic_bits
    pellFSMmod3.bits 4 0 (by decide)
    (fun n _ => pellFSMmod3_bits_period_4 n)

/-- ★★★ Pell mod-5 signature is eventually periodic. -/
theorem pellFSMmod5_signature_eventually_periodic :
    ∃ N P, 0 < P ∧ ∀ n, n ≥ N →
      signature pellFSMmod5.bits (n + P) = signature pellFSMmod5.bits n :=
  signature_eventually_periodic_of_eventually_periodic_bits
    pellFSMmod5.bits 10 0 (by decide)
    (fun n _ => pellFSMmod5_bits_period_10 n)

/-- ★★★★★ All three Pell ArithFSM streams (mod 2, 3, 5) yield
    eventually periodic K_{3,2}^{(2)} signatures.  Tier 1 is captured
    inside the eventually-periodic class — no transcendental escape. -/
theorem pell_family_signatures_eventually_periodic :
    (∃ N P, 0 < P ∧ ∀ n, n ≥ N →
      signature pellFSMmod2.bits (n + P) = signature pellFSMmod2.bits n)
    ∧ (∃ N P, 0 < P ∧ ∀ n, n ≥ N →
      signature pellFSMmod3.bits (n + P) = signature pellFSMmod3.bits n)
    ∧ (∃ N P, 0 < P ∧ ∀ n, n ≥ N →
      signature pellFSMmod5.bits (n + P) = signature pellFSMmod5.bits n) :=
  ⟨pellFSMmod2_signature_eventually_periodic,
   pellFSMmod3_signature_eventually_periodic,
   pellFSMmod5_signature_eventually_periodic⟩

end E213.Math.DyadicFSM.ArithFSM.Signature
