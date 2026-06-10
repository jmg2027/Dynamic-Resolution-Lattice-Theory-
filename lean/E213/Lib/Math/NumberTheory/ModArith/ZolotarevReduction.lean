import E213.Lib.Math.NumberTheory.ModArith.Zolotarev
import E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative

/-!
# ZolotarevReduction — non-residue ⟹ odd permutation, and the full Legendre/sign iff

The residue direction `psign (mulPerm a p) = 1` for a quadratic residue `a` is
`Zolotarev.psign_mulPerm_qr_pred`.  This file closes the **converse** (a non-residue's
multiplication-permutation is *odd*) and assembles the full Zolotarev iff

  `psign (mulPerm a p) = 1  ⟺  a is a quadratic residue mod p`.

The whole converse rests on **one** witness: a single non-residue `a₀` whose permutation is odd
(`psign (mulPerm a₀ p) = −1`).  Given it, the multiplicativity of the Legendre character does the
rest: for any non-residue `a`, the product `a·a₀` is a *residue* (non·non = residue), so

  `1 = psign (mulPerm (a·a₀)) = psign (mulPerm a) · psign (mulPerm a₀) = psign (mulPerm a) · (−1)`,

forcing `psign (mulPerm a) = −1`.  The single witness (`a₀` a primitive root, its permutation a
`(p−1)`-cycle of sign `(−1)^(p−2) = −1`) is the remaining input, supplied by the primitive-root
machinery (`PrimitiveRoot.exists_primitive_root`).

  * `qr_dec` — quadratic-residue membership is decidable (bounded `firstSqrt` search).
  * ★★★ `nonqr_psign_neg` — a non-residue's permutation is odd, *given* the odd-witness `a₀`.
  * ★★★★★ `zolotarev_iff` — the full Legendre/sign equivalence, *given* the odd-witness `a₀`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.ZolotarevReduction

open E213.Lib.Math.Algebra.Linalg213.Permutation (psign)
open E213.Lib.Math.NumberTheory.ModArith.Zolotarev (mulPerm psign_mulPerm_hom psign_mulPerm_qr_pred)
open E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative (legendre_mul)
open E213.Lib.Math.NumberTheory.ModArith.EulerConverse (firstSqrt firstSqrt_some firstSqrt_none)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-- Pure `x · (−1) = −x` over `ℤ` (core `Int.mul_neg_one` carries `propext`). -/
theorem mul_neg_one_int (x : Int) : x * (-1) = -x := by
  cases x with
  | ofNat n => show Int.negOfNat (n * 1) = Int.negOfNat n; rw [Nat.mul_one]
  | negSucc n => show Int.ofNat (n.succ * 1) = Int.ofNat n.succ; rw [Nat.mul_one]

/-- A quadratic-residue predicate is decidable on a unit range: either there is a root
    `1 ≤ x < p` with `x² ≡ a`, or there is none.  (Bounded `firstSqrt` search; the `none`
    branch refutes any claimed root via `firstSqrt_none`.) -/
theorem qr_dec (p a : Nat) (hp : 1 < p) :
    (∃ x, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = a) ∨ ¬ (∃ x, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = a) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have hp1lt : p - 1 < p := Nat.sub_lt hppos Nat.zero_lt_one
  cases hfn : firstSqrt p a (p - 1) with
  | some x =>
    obtain ⟨h1, h2, h3⟩ := firstSqrt_some p a (p - 1) x hfn
    exact Or.inl ⟨x, h1, Nat.lt_of_le_of_lt h2 hp1lt, h3⟩
  | none =>
    refine Or.inr (fun h => ?_)
    obtain ⟨x, hx1, hxp, hx3⟩ := h
    have hxp1 : x ≤ p - 1 := Nat.le_sub_one_of_lt hxp
    exact firstSqrt_none p a (p - 1) hfn x hx1 hxp1 hx3

/-- ★★★ **Zolotarev converse, given one odd witness.**  If `a₀` is a non-residue whose
    multiplication-permutation is odd (`psign (mulPerm a₀ p) = −1`), then *every* non-residue `a`
    has an odd permutation: `psign (mulPerm a p) = −1`.

    Mechanism: `a·a₀` is a residue (non·non = residue, `legendre_mul`), so its permutation is even
    (`psign_mulPerm_qr_pred`); by the homomorphism (`psign_mulPerm_hom`) that even sign equals
    `psign (mulPerm a) · (−1)`, forcing `psign (mulPerm a) = −1`. -/
theorem nonqr_psign_neg (p m a a₀ : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m)
    (ha1 : 1 ≤ a) (halt : a < p) (ha0_1 : 1 ≤ a₀) (ha0_lt : a₀ < p)
    (hna : ¬ ∃ x, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = a)
    (hna0 : ¬ ∃ x, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = a₀)
    (hsign0 : psign (mulPerm a₀ p) = -1) :
    psign (mulPerm a p) = -1 := by
  have hnpa : ¬ p ∣ a := fun h =>
    absurd (le_of_dvd_pos p a (Nat.lt_of_lt_of_le Nat.zero_lt_one ha1) h) (Nat.not_le.mpr halt)
  have hnpa0 : ¬ p ∣ a₀ := fun h =>
    absurd (le_of_dvd_pos p a₀ (Nat.lt_of_lt_of_le Nat.zero_lt_one ha0_1) h) (Nat.not_le.mpr ha0_lt)
  -- a·a₀ is a residue: non·non = residue
  have hab_qr : ∃ z, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = (a * a₀) % p :=
    (legendre_mul p m a a₀ hp hpr h2m hm1 ha1 halt ha0_1 ha0_lt).mpr
      ⟨fun hx => absurd hx hna, fun hy => absurd hy hna0⟩
  -- so its permutation is even
  have h1 : psign (mulPerm ((a * a₀) % p) p) = 1 :=
    psign_mulPerm_qr_pred ((a * a₀) % p) p hp hpr hab_qr
  -- and equals psign(mulPerm a) · psign(mulPerm a₀)
  have h2 : psign (mulPerm ((a * a₀) % p) p) = psign (mulPerm a p) * psign (mulPerm a₀ p) :=
    psign_mulPerm_hom a a₀ p hp hpr hnpa hnpa0
  have hXY : psign (mulPerm a p) * (-1 : Int) = 1 := by
    rw [← hsign0]; exact h2.symm.trans h1
  have hnegX : -(psign (mulPerm a p)) = 1 := by rw [← mul_neg_one_int (psign (mulPerm a p))]; exact hXY
  have hcong := congrArg (Neg.neg) hnegX
  rwa [Int.neg_neg] at hcong

/-- ★★★★★ **Full Zolotarev / Legendre–sign equivalence, given one odd witness.**  With a single
    non-residue `a₀` whose multiplication-permutation is odd (`psign (mulPerm a₀ p) = −1`):

      `psign (mulPerm a p) = 1  ⟺  a is a quadratic residue mod p`.

    Forward by decidability of the residue predicate (`qr_dec`) + the converse `nonqr_psign_neg`
    (a non-residue would force `psign = −1 ≠ 1`); backward by `psign_mulPerm_qr_pred`. -/
theorem zolotarev_iff (p m a a₀ : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m)
    (ha1 : 1 ≤ a) (halt : a < p) (ha0_1 : 1 ≤ a₀) (ha0_lt : a₀ < p)
    (hna0 : ¬ ∃ x, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = a₀)
    (hsign0 : psign (mulPerm a₀ p) = -1) :
    psign (mulPerm a p) = 1 ↔ ∃ x, 1 ≤ x ∧ x < p ∧ x ^ 2 % p = a := by
  constructor
  · intro hs
    rcases qr_dec p a hp with hqr | hnqr
    · exact hqr
    · exact absurd (hs.symm.trans
        (nonqr_psign_neg p m a a₀ hp hpr h2m hm1 ha1 halt ha0_1 ha0_lt hnqr hna0 hsign0))
        (by decide)
  · intro hqr
    exact psign_mulPerm_qr_pred a p hp hpr hqr

end E213.Lib.Math.NumberTheory.ModArith.ZolotarevReduction
