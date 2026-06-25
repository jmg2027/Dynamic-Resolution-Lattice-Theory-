import E213.Lens.Number.Nat213.LegendreReadout
import E213.Lib.Math.NumberTheory.ModArith.ZolotarevMuBridge

/-!
# Lens.Number.Nat213.ZolotarevReadout — the permutation-sign / determinant face of the character (∅-axiom)

The **descent leg**, leg-2 — **Zolotarev's lemma** over `Nat213`: the Legendre symbol `(a/p)` is the
**sign of the multiply-by-`a` permutation** of the residues, and equally its **permutation-matrix
determinant**.  The quadratic character, read in `LegendreReadout` as "`a` is a square" and in
`DiscreteLogReadout` as "the discrete log is even", thus has two more faces — closing the
*one-permutation, four-readouts* identity (square / orbit-parity / inversion-sign / determinant).

* `psign213 a p := psign (mulPermMod a.toNat p.toNat)` — the inversion-sign of `x ↦ a·x (mod p)`;
* `det213 a p := det p.toNat (permMatrix (mulPermMod a.toNat p.toNat))` — its permutation-matrix
  determinant.

Both equal `1` exactly when `a` is a quadratic residue (`zolotarev`, `zolotarev_det`, via the native
`zolotarev_mu` / `det_permMatrix_mulPermMod` and `LegendreReadout.QR_iff_native`).  Native source:
`Lib/.../ModArith/ZolotarevMuBridge` + the `Linalg213` permutation/determinant machinery.
Transported, not re-derived.  ∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.ZolotarevReadout

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213 (toNat toNat_ge_one)
open E213.Lens.Number.Nat213.LegendreReadout (QR QR_iff_native)
open E213.Lib.Math.Algebra.Linalg213.Permutation (psign)
open E213.Lib.Math.Algebra.Linalg213.DetN (det)
open E213.Lib.Math.Algebra.Linalg213.PermMatrixDet (permMatrix)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevSign (mulPermMod)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevMuBridge (zolotarev_mu det_permMatrix_mulPermMod)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-- **The permutation-sign of multiply-by-`a`** mod `p`, over `Nat213` — the inversion-sign (in `Int`,
    `{±1}`) of the residue permutation `x ↦ a·x (mod p)`, read OUT from native `mulPermMod`/`psign`. -/
abbrev psign213 (a p : Nat213) : Int := psign (mulPermMod a.toNat p.toNat)

/-- **The permutation-matrix determinant of multiply-by-`a`** mod `p`, over `Nat213`. -/
abbrev det213 (a p : Nat213) : Int := det p.toNat (permMatrix (mulPermMod a.toNat p.toNat))

/-- The QR bridge specialised to a unit `a < p` (`a % p = a`), shared by both faces. -/
private theorem qr_unit_native {p a : Nat213} (hp : 1 < p.toNat) (halt : a.toNat < p.toNat) :
    QR p a ↔ ∃ z : Nat, 1 ≤ z ∧ z < p.toNat ∧ z ^ 2 % p.toNat = a.toNat := by
  have hua : ¬ p.toNat ∣ a.toNat :=
    fun h => absurd (le_of_dvd_pos p.toNat a.toNat (toNat_ge_one a) h) (Nat.not_le.mpr halt)
  have b := QR_iff_native hp hua; rw [Nat.mod_eq_of_lt halt] at b; exact b

/-- ★★★★★ **Zolotarev's lemma over `Nat213` (sign face)** — the Legendre symbol is the permutation
    sign: for a prime `p` (`2m = p − 1`) and a unit `a < p`, multiply-by-`a` is an **even** permutation
    of the residues **iff `a` is a quadratic residue**: `psign213 a p = 1 ⟺ QR p a`.  Native
    `zolotarev_mu` welded to `QR p a` through `QR_iff_native`.  ∅-axiom. -/
theorem zolotarev {p a : Nat213} (m : Nat) (hp : 1 < p.toNat)
    (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) (h2m : 2 * m = p.toNat - 1) (hm1 : 1 ≤ m)
    (halt : a.toNat < p.toNat) :
    psign213 a p = 1 ↔ QR p a :=
  (zolotarev_mu a.toNat p.toNat m hp hpr h2m hm1 (toNat_ge_one a) halt).trans
    (qr_unit_native hp halt).symm

/-- ★★★★★ **Zolotarev as a determinant over `Nat213`** — the same Legendre symbol read as the
    permutation-matrix determinant: `det213 a p = 1 ⟺ QR p a`.  Closes the one-permutation,
    four-readouts identity (square / orbit-parity / inversion-sign / determinant) on the carrier.
    Native `det_permMatrix_mulPermMod` welded through `QR_iff_native`.  ∅-axiom. -/
theorem zolotarev_det {p a : Nat213} (m : Nat) (hp : 1 < p.toNat)
    (hpr : ∀ d, d ∣ p.toNat → d = 1 ∨ d = p.toNat) (h2m : 2 * m = p.toNat - 1) (hm1 : 1 ≤ m)
    (halt : a.toNat < p.toNat) :
    det213 a p = 1 ↔ QR p a :=
  (det_permMatrix_mulPermMod a.toNat p.toNat m hp hpr h2m hm1 (toNat_ge_one a) halt).trans
    (qr_unit_native hp halt).symm

end E213.Lens.Number.Nat213.ZolotarevReadout
