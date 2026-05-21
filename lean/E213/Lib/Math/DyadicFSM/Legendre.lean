import E213.Lib.Math.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.DyadicFSM.ArithFSM
import E213.Lib.Math.DyadicFSM.ArithFSM.V1
import E213.Lib.Math.DyadicFSM.Pell.Family

/-!
# DyadicFSM.Legendre — Legendre-symbol Pisano variants

Consolidated single-file home for the 5 Legendre-symbol-based
Pisano-period variants:

  * `Legendre.V213`     — 213-tight Legendre-FSM package (∅-axiom)
  * `Legendre.Small`    — small-modulus direct verification
  * `Legendre.V13_19`   — mod-13 / mod-19 specialisation
  * `Legendre.Pisano`   — core Legendre-shifted Pisano period
  * `Legendre.PisanoExt` — extended-precision variant

Per-variant namespaces preserved as sub-namespaces of `Legendre`.
Pisano.Predictor consumes Legendre.
-/

namespace E213.Lib.Math.DyadicFSM.Legendre.V213

open E213.Lib.Math.DyadicFSM.ArithFSM.V1 (ArithFSM1)

/-- Legendre FSM: walk x ↦ D·x mod p, starting from 1. -/
def legendreFSM (D p : Nat) (hp : 0 < p) : ArithFSM1 p where
  init := ⟨1 % p, Nat.mod_lt _ hp⟩
  step x := ⟨(D * x.val) % p, Nat.mod_lt _ hp⟩
  out x := decide (x.val = 1)

/-- 213-native Legendre symbol: walk the FSM (p-1)/2 steps and read
    the trajectory's terminal state.  Returned as Fin 3:
      0 = ramified (D ≡ 0 mod p)
      1 = QR (split, terminal = 1)
      2 = NQR (inert, terminal = p-1) -/
def legendre213 (D p : Nat) (hp : 1 < p) : Fin 3 :=
  let v := ((legendreFSM D p (Nat.zero_lt_of_lt hp)).run ((p - 1) / 2)).val
  if v = 0 then ⟨0, by decide⟩
  else if v = 1 then ⟨1, by decide⟩
  else ⟨2, by decide⟩

end E213.Lib.Math.DyadicFSM.Legendre.V213

namespace E213.Lib.Math.DyadicFSM.Legendre.Small

open E213.Lib.Math.DyadicFSM.Legendre.V213 (legendreFSM legendre213)

/-- ★★★★★ Pell discriminant 5 is NQR mod 3 (inert). -/
theorem legendre_5_mod_3 : legendre213 5 3 (by decide) = ⟨2, by decide⟩ := by
  decide

/-- ★★★★★ Pell discriminant 5 is ramified mod 5 (Δ = 0). -/
theorem legendre_5_mod_5 : legendre213 5 5 (by decide) = ⟨0, by decide⟩ := by
  decide

/-- ★★★★★ Pell discriminant 5 is NQR mod 7 (inert). -/
theorem legendre_5_mod_7 : legendre213 5 7 (by decide) = ⟨2, by decide⟩ := by
  decide

/-- ★★★★★ Pell discriminant 5 is QR mod 11 (split). -/
theorem legendre_5_mod_11 : legendre213 5 11 (by decide) = ⟨1, by decide⟩ := by
  decide

/-- ★★★★★★ The Legendre lens reveals the Pell discriminant pattern:
    primes 3, 7 are inert (NQR), prime 11 is split (QR), prime 5
    is ramified.  All four cases decided by trajectory walking. -/
theorem pell_discriminant_legendre_table :
    legendre213 5 3 (by decide) = ⟨2, by decide⟩
    ∧ legendre213 5 5 (by decide) = ⟨0, by decide⟩
    ∧ legendre213 5 7 (by decide) = ⟨2, by decide⟩
    ∧ legendre213 5 11 (by decide) = ⟨1, by decide⟩ :=
  ⟨legendre_5_mod_3, legendre_5_mod_5, legendre_5_mod_7, legendre_5_mod_11⟩

end E213.Lib.Math.DyadicFSM.Legendre.Small

namespace E213.Lib.Math.DyadicFSM.Legendre.V13_19

open E213.Lib.Math.DyadicFSM.Legendre.V213 (legendre213)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3 pellFSMmod3_bits_period_4 pellFSMmod2 pellFSMmod2_bits_period_3)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod7 (pellFSMmod7 pellFSMmod7_bits_period_8)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod11 (pellFSMmod11 pellFSMmod11_bits_period_5 pellFSMmod11_bits_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod13 (pellFSMmod13 pellFSMmod13_bits_period_14)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod17 (pellFSMmod17 pellFSMmod17_bits_period_18)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod19 (pellFSMmod19 pellFSMmod19_bits_period_9)
open E213.Lib.Math.DyadicFSM.Legendre.Small (legendre_5_mod_3 legendre_5_mod_5 legendre_5_mod_7 legendre_5_mod_11)


/-- ★★★★★ Pell discriminant 5 is NQR mod 13 (inert). -/
theorem legendre_5_mod_13 :
    legendre213 5 13 (by decide) = ⟨2, by decide⟩ := by decide

/-- ★★★★★ Pell discriminant 5 is QR mod 19 (split). -/
theorem legendre_5_mod_19 :
    legendre213 5 19 (by decide) = ⟨1, by decide⟩ := by decide

/-- ★★★★★★★ Extended Legendre-Pisano bridge — 6 primes verified. -/
theorem legendre_pisano_6prime_bridge :
    -- p = 3: NQR/inert, period p+1 = 4
    (legendre213 5 3 (by decide) = ⟨2, by decide⟩
      ∧ ∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k)
    -- p = 5: ramified, period 2p = 10
    ∧ (legendre213 5 5 (by decide) = ⟨0, by decide⟩
        ∧ ∀ k, pellFSMmod5.bits (k + 10) = pellFSMmod5.bits k)
    -- p = 7: NQR/inert, period p+1 = 8
    ∧ (legendre213 5 7 (by decide) = ⟨2, by decide⟩
        ∧ ∀ k, pellFSMmod7.bits (k + 8) = pellFSMmod7.bits k)
    -- p = 11: QR/split, period (p-1)/2 = 5
    ∧ (legendre213 5 11 (by decide) = ⟨1, by decide⟩
        ∧ ∀ k, pellFSMmod11.bits (k + 5) = pellFSMmod11.bits k)
    -- p = 13: NQR/inert, period p+1 = 14  (NEW)
    ∧ (legendre213 5 13 (by decide) = ⟨2, by decide⟩
        ∧ ∀ k, pellFSMmod13.bits (k + 14) = pellFSMmod13.bits k)
    -- p = 19: QR/split, period (p-1)/2 = 9  (NEW)
    ∧ (legendre213 5 19 (by decide) = ⟨1, by decide⟩
        ∧ ∀ k, pellFSMmod19.bits (k + 9) = pellFSMmod19.bits k) :=
  ⟨⟨legendre_5_mod_3, pellFSMmod3_bits_period_4⟩,
   ⟨legendre_5_mod_5, pellFSMmod5_bits_period_10⟩,
   ⟨legendre_5_mod_7, pellFSMmod7_bits_period_8⟩,
   ⟨legendre_5_mod_11, pellFSMmod11_bits_period_5⟩,
   ⟨legendre_5_mod_13, pellFSMmod13_bits_period_14⟩,
   ⟨legendre_5_mod_19, pellFSMmod19_bits_period_9⟩⟩

end E213.Lib.Math.DyadicFSM.Legendre.V13_19

namespace E213.Lib.Math.DyadicFSM.Legendre.Pisano

open E213.Lib.Math.DyadicFSM.Legendre.V213 (legendre213)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3 pellFSMmod3_bits_period_4 pellFSMmod2 pellFSMmod2_bits_period_3)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod7 (pellFSMmod7 pellFSMmod7_bits_period_8)
open E213.Lib.Math.DyadicFSM.Legendre.Small (legendre_5_mod_3 legendre_5_mod_5 legendre_5_mod_7)


/-- ★★★★★★ Bridge: at p ∈ {3, 7} (NQR, inert), the Pell period
    matches the inert formula p + 1.  At p = 5 (ramified), the
    period matches 2p.  The Legendre lens computes the Pell
    period via trajectory branch law. -/
theorem legendre_pisano_bridge_table :
    -- p = 3: NQR + inert, period = p+1 = 4
    (legendre213 5 3 (by decide) = ⟨2, by decide⟩
      ∧ ∀ k, pellFSMmod3.bits (k + (3 + 1)) = pellFSMmod3.bits k)
    -- p = 5: ramified, period = 2p = 10
    ∧ (legendre213 5 5 (by decide) = ⟨0, by decide⟩
        ∧ ∀ k, pellFSMmod5.bits (k + (2 * 5)) = pellFSMmod5.bits k)
    -- p = 7: NQR + inert, period = p+1 = 8
    ∧ (legendre213 5 7 (by decide) = ⟨2, by decide⟩
        ∧ ∀ k, pellFSMmod7.bits (k + (7 + 1)) = pellFSMmod7.bits k) := by
  refine ⟨⟨legendre_5_mod_3, ?_⟩, ⟨legendre_5_mod_5, ?_⟩,
          ⟨legendre_5_mod_7, ?_⟩⟩
  · intro k
    have h : (3 : Nat) + 1 = 4 := by decide
    rw [h]; exact pellFSMmod3_bits_period_4 k
  · intro k
    have h : (2 : Nat) * 5 = 10 := by decide
    rw [h]; exact pellFSMmod5_bits_period_10 k
  · intro k
    have h : (7 : Nat) + 1 = 8 := by decide
    rw [h]; exact pellFSMmod7_bits_period_8 k

end E213.Lib.Math.DyadicFSM.Legendre.Pisano

namespace E213.Lib.Math.DyadicFSM.Legendre.PisanoExt

open E213.Lib.Math.DyadicFSM.Legendre.V213 (legendre213)
open E213.Lib.Math.DyadicFSM.ArithFSM (pellFSMmod3 pellFSMmod3_bits_period_4 pellFSMmod2 pellFSMmod2_bits_period_3)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod5 (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod7 (pellFSMmod7 pellFSMmod7_bits_period_8)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod11 (pellFSMmod11 pellFSMmod11_bits_period_5 pellFSMmod11_bits_period_10)
open E213.Lib.Math.DyadicFSM.ArithFSM.Mod13 (pellFSMmod13 pellFSMmod13_bits_period_14)
open E213.Lib.Math.DyadicFSM.Legendre.Small (legendre_5_mod_3 legendre_5_mod_5 legendre_5_mod_7 legendre_5_mod_11)


/-- ★★★★★★★ Extended bridge: Legendre lens predicts Pell period
    across all four branch types {inert, ramified, split, ...}. -/
theorem legendre_pisano_extended_bridge :
    -- p = 3: NQR + inert, period = p+1 = 4
    (legendre213 5 3 (by decide) = ⟨2, by decide⟩
      ∧ ∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k)
    -- p = 5: ramified, period = 2p = 10
    ∧ (legendre213 5 5 (by decide) = ⟨0, by decide⟩
        ∧ ∀ k, pellFSMmod5.bits (k + 10) = pellFSMmod5.bits k)
    -- p = 7: NQR + inert, period = p+1 = 8
    ∧ (legendre213 5 7 (by decide) = ⟨2, by decide⟩
        ∧ ∀ k, pellFSMmod7.bits (k + 8) = pellFSMmod7.bits k)
    -- p = 11: QR + split, period = (p-1)/2 = 5  (NEW)
    ∧ (legendre213 5 11 (by decide) = ⟨1, by decide⟩
        ∧ ∀ k, pellFSMmod11.bits (k + 5) = pellFSMmod11.bits k) :=
  ⟨⟨legendre_5_mod_3, pellFSMmod3_bits_period_4⟩,
   ⟨legendre_5_mod_5, pellFSMmod5_bits_period_10⟩,
   ⟨legendre_5_mod_7, pellFSMmod7_bits_period_8⟩,
   ⟨legendre_5_mod_11, pellFSMmod11_bits_period_5⟩⟩

end E213.Lib.Math.DyadicFSM.Legendre.PisanoExt
