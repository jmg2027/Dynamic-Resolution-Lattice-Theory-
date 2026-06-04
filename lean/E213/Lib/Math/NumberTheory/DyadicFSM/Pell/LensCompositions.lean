import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ModSmall
import E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSMPeriod
import E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSMPeriodDvd
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.BitFSM
import E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSM

/-!
# Pell lens compositions — pairwise + triple CRT closures

Compose `Pell` ArithFSM2 instances via
`E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSM.BitFSM.product`.  For
`Pell mod a × Pell mod b` with the XOR readout, the product
BitFSM has period dividing `lcm(period(a), period(b))` by
`lens_composition_period_dvd`.

Concrete instances established here:
  · `pellMod{3,5,7}_BitFSM_bits_period_*` — BitFSM-form lifts
    of the ArithFSM2 period theorems
  · `pellLens_3x5_period_20` — mod 3 × mod 5: period | 20
  · `pellLens_3x7_period_8`  — mod 3 × mod 7: period | 8
  · `pellLens_5x7_period_40` — mod 5 × mod 7: period | 40
  · `pellLens_3x5x7_period_40` — stacked triple: period | 40

This is the full Pell-CRT closure at the FSM level, not just
the stream level.

Standard: 0 sorry, ∅-axiom (PURE).
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.Pell.LensCompositions

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM
  (pellFSMmod3 pellFSMmod3_bits_period_4 pellFSMmod2 pellFSMmod2_bits_period_3)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod5
  (pellFSMmod5 pellFSMmod5_bits_period_10)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.Mod7
  (pellFSMmod7 pellFSMmod7_bits_period_8)
open E213.Lib.Math.NumberTheory.DyadicFSM.BitFSM (BitFSM)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSM
open E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSMPeriod
  (lens_composition_period)
open E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSMPeriodDvd
  (lens_composition_period_dvd)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.ToBitFSM
  (toBitFSM_bits_eq toBitFSM_bits_period_lift)

/-! ### §1 — BitFSM-form period lifts for the base Pell mods -/

/-- Lifted bit periodicity for Pell mod 3 (BitFSM form). -/
theorem pellMod3_BitFSM_bits_period_4 :
    ∀ k, (pellFSMmod3.toBitFSM (by decide : (0:Nat) < 3)).bits (k + 4)
        = (pellFSMmod3.toBitFSM (by decide : (0:Nat) < 3)).bits k :=
  toBitFSM_bits_period_lift _ _ pellFSMmod3_bits_period_4

/-- Lifted bit periodicity for Pell mod 5. -/
theorem pellMod5_BitFSM_bits_period_10 :
    ∀ k, (pellFSMmod5.toBitFSM (by decide : (0:Nat) < 5)).bits (k + 10)
        = (pellFSMmod5.toBitFSM (by decide : (0:Nat) < 5)).bits k :=
  toBitFSM_bits_period_lift _ _ pellFSMmod5_bits_period_10

/-- Lifted bit periodicity for Pell mod 7. -/
theorem pellMod7_BitFSM_bits_period_8 :
    ∀ k, (pellFSMmod7.toBitFSM (by decide : (0:Nat) < 7)).bits (k + 8)
        = (pellFSMmod7.toBitFSM (by decide : (0:Nat) < 7)).bits k :=
  toBitFSM_bits_period_lift _ _ pellFSMmod7_bits_period_8

/-! ### §2 — Pairwise CRT closures -/

/-- Pell mod 3 × mod 5 (XOR readout): period | 20.  Tactic-free
    ∅-axiom. -/
theorem pellLens_3x5_period_20 :
    ∀ k, (E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSM.BitFSM.product
            (n := 9) (m := 25) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
            xor).bits (k + 20)
        = (E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSM.BitFSM.product
            (n := 9) (m := 25) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
            xor).bits k := fun k =>
  lens_composition_period_dvd (n := 9) (m := 25) (by decide)
    (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
    (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
    xor 4 10 20 (by decide) (by decide) ⟨5, rfl⟩ ⟨2, rfl⟩
    (fun k => (toBitFSM_bits_eq _ _ (k + 4)).trans
        ((pellFSMmod3_bits_period_4 k).trans (toBitFSM_bits_eq _ _ k).symm))
    (fun k => (toBitFSM_bits_eq _ _ (k + 10)).trans
        ((pellFSMmod5_bits_period_10 k).trans (toBitFSM_bits_eq _ _ k).symm))
    k

/-- Pell mod 3 × mod 7 (XOR): period | 8.  Tactic-free ∅-axiom. -/
theorem pellLens_3x7_period_8 :
    ∀ k, (E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSM.BitFSM.product
            (n := 9) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits (k + 8)
        = (E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSM.BitFSM.product
            (n := 9) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits k := fun k =>
  lens_composition_period_dvd (n := 9) (m := 49) (by decide)
    (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
    (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
    xor 4 8 8 (by decide) (by decide) ⟨2, rfl⟩ ⟨1, rfl⟩
    pellMod3_BitFSM_bits_period_4 pellMod7_BitFSM_bits_period_8 k

/-- Pell mod 5 × mod 7 (XOR): period | 40.  Tactic-free ∅-axiom. -/
theorem pellLens_5x7_period_40 :
    ∀ k, (E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSM.BitFSM.product
            (n := 25) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits (k + 40)
        = (E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSM.BitFSM.product
            (n := 25) (m := 49) (by decide)
            (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits k := fun k =>
  lens_composition_period_dvd (n := 25) (m := 49) (by decide)
    (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
    (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
    xor 10 8 40 (by decide) (by decide) ⟨4, rfl⟩ ⟨5, rfl⟩
    pellMod5_BitFSM_bits_period_10 pellMod7_BitFSM_bits_period_8 k

/-! ### §3 — Triple stacked composition

`((mod 3 × mod 5) × mod 7)`, encoded into `BitFSM(9·25·49) =
BitFSM(11025)`, inheriting period | `lcm(4, 10, 8) = 40`.
-/

/-- Inner product `(mod 3 × mod 5)`. -/
def pellInner35 : BitFSM (9 * 25) :=
  E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSM.BitFSM.product
    (by decide : (0:Nat) < 25)
    (ArithFSM2.toBitFSM (by decide : 0 < 3) pellFSMmod3)
    (ArithFSM2.toBitFSM (by decide : 0 < 5) pellFSMmod5)
    xor

/-- Inner product has period | 20. -/
theorem pellInner35_period_20 :
    ∀ k, pellInner35.bits (k + 20) = pellInner35.bits k :=
  pellLens_3x5_period_20

/-- Pell mod 3 × 5 × 7 (stacked XOR): period | 40.
    Tactic-free ∅-axiom. -/
theorem pellLens_3x5x7_period_40 :
    ∀ k, (E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSM.BitFSM.product
            (n := 9 * 25) (m := 49) (by decide)
            pellInner35
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits (k + 40)
        = (E213.Lib.Math.NumberTheory.DyadicFSM.Product.ProductFSM.BitFSM.product
            (n := 9 * 25) (m := 49) (by decide)
            pellInner35
            (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
            xor).bits k := fun k =>
  lens_composition_period_dvd
    (n := 9 * 25) (m := 49) (by decide)
    pellInner35
    (ArithFSM2.toBitFSM (by decide : 0 < 7) pellFSMmod7)
    xor 20 8 40 (by decide) (by decide) ⟨2, rfl⟩ ⟨5, rfl⟩
    pellInner35_period_20 pellMod7_BitFSM_bits_period_8 k

end E213.Lib.Math.NumberTheory.DyadicFSM.Pell.LensCompositions
