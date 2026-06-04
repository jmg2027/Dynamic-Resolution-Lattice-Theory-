import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FLTMain
import E213.Lib.Math.NumberTheory.DyadicFSM.PhiMod5
/-!
# FLT applied to φ (golden ratio mod p) at split primes

For split primes p (where 5 is QR mod p, so sqrt5 exists), the
golden ratio `phi p s = (1 + s) · inv2 p` is a nonzero element of
F_p and hence by FLT main satisfies `phi^(p-1) ≡ 1 (mod p)`.

This is the **FLT application** that's directly relevant to the
Phase 3.2 Fibonacci-Pisano condition (`F_{p-1} ≡ 0 mod p` via
Binet's φ^k - ψ^k formula).

Per-prime demonstrations at split primes 11 and 19, each requiring:
  · A `ModInverse p phi` witness (decidable, derivable from
    `phi · (phi - 1) ≡ 1 mod p` rearrangement).
  · The middle-binomial vanishing hypothesis (decidable per p).

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.PhiFLT

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FLTMain (flt_main)
open E213.Lib.Math.NumberTheory.DyadicFSM.PhiMod5
  (phi phi11_modInv phi19_modInv)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FreshmanDream
  (middle_vanish_5 middle_vanish_7)
open E213.Lib.Math.NumberTheory.DyadicFSM.MulOrderPigeonhole (ModInverse)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)

/-- Middle-binomial vanishing at p = 11 (decidable). -/
theorem middle_vanish_11 :
    ∀ k, k < 10 → (choose 11 (k + 1)) % 11 = 0 := by decide

/-- ★ **FLT for φ at p = 11**: `(phi 11 4)^10 ≡ 1 (mod 11)`.

    `phi 11 4 = 8`, `phi11_modInv.inv = 7` (from Part 12).
    By FLT main, `8^10 ≡ 1 mod 11`.

    This is the FLT instance directly used in Phase 3.2's
    Fibonacci-Pisano derivation: `F_10 ≡ 0 mod 11` follows from
    `phi^10 - ψ^10 ≡ 0 mod 11` (Binet form). -/
theorem phi_flt_11 : ((phi 11 4)^10) % 11 = 1 % 11 :=
  flt_main (phi 11 4) 10 (by decide) middle_vanish_11 phi11_modInv

/-- Middle-binomial vanishing at p = 19 (decidable). -/
theorem middle_vanish_19 :
    ∀ k, k < 18 → (choose 19 (k + 1)) % 19 = 0 := by decide

/-- ★ **FLT for φ at p = 19**: `(phi 19 9)^18 ≡ 1 (mod 19)`. -/
theorem phi_flt_19 : ((phi 19 9)^18) % 19 = 1 % 19 :=
  flt_main (phi 19 9) 18 (by decide) middle_vanish_19 phi19_modInv

/-! ## Direct demonstration without FLT (via decide)

For each specific split prime, `phi^(p-1) ≡ 1 mod p` is decidable
directly (since phi is concrete).  The FLT route above DERIVES
this from the abstract framework; the route below VERIFIES it
directly.  Both produce PURE proofs but with different abstraction
levels — FLT is the structural derivation, decide is the
computational verification. -/

theorem phi_flt_11_decide : ((phi 11 4)^10) % 11 = 1 % 11 := by decide

theorem phi_flt_19_decide : ((phi 19 9)^18) % 19 = 1 % 19 := by decide

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.PhiFLT
