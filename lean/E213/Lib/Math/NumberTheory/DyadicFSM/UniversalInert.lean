import E213.Lib.Math.NumberTheory.ModArith.FP2Sqrt5
import E213.Lib.Math.NumberTheory.DyadicFSM.PellFibBridge
import E213.Lib.Math.NumberTheory.DyadicFSM.BinetBridge
/-!
# Universal Phase 3.3 (inert case): bridge from Frobenius FLT to F-identities

This file bridges the F_{p^2} infrastructure (FP2Sqrt5) with the
Pell-Fibonacci closure (PellFibBridge) for the inert case.

Given Frobenius FLT on phi (`phi^p = σ(phi)` in 𝔽_{p²}), we derive
the inert Fibonacci characteristic identities:
  · F_p ≡ -1 mod p (i.e., `fibFst p % p = p - 1`)
  · F_{p-1} ≡ 1 mod p (`fibFst (p - 1) % p = 1`)

via Binet expansion (Part 48) + inv2-cancellation (Part 49) +
mod-p Fibonacci recurrence (PellFibBridge).

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.UniversalInert

open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod mod_self zero_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure)
open E213.Tactic.NatHelper (add_mul sub_add_cancel)
open E213.Lib.Math.NumberTheory.DyadicFSM.PhiMod5 (inv2 fibLike two_mul_inv2)
open E213.Lib.Math.NumberTheory.ModArith.FP2Sqrt5
  (FP2 phiFP2 fp2Add fp2Pow fp2Frob fp2Mul fp2Mul_comm fp2Pow_succ
   phiFP2_pow_eq_fibLike phiFP2_mul_frob_phi_eq
   inv2_cancel_zero nmod_self_mod_zero
   fp2Pow_scalar_p fp2Pow_sqrt5_eq_frob inv2_lt_self
   p_minus_one_mul_mod)
open E213.Lib.Math.NumberTheory.DyadicFSM.PellFibBridge
  (fibFst fibLike_succ_fst fibLike_succ_snd fibFst_recur
   universal_inert_case)
open E213.Lib.Math.NumberTheory.DyadicFSM.BinetBridge (mod_eq_p_minus_one_of_succ_mod_zero)

/-- ★★★ **Frobenius-FLT-for-phi ⟹ F_p ≡ -1 mod p**.

    The .2 component of `phi^p = σ(phi)` gives
    `(F_p · inv2) % p = (p - inv2 % p) % p`.  Adding inv2 to both sides
    yields `((F_p + 1) · inv2) % p = 0`.  By `inv2_cancel_zero`,
    `(F_p + 1) % p = 0`, hence `F_p % p = p - 1`.  PURE. -/
theorem fp_eq_neg_one_of_frob_phi
    (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (h_frob : fp2Pow p (phiFP2 p) p = fp2Frob p (phiFP2 p)) :
    fibFst p % p = p - 1 := by
  have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
  -- Apply Binet expansion to phi^p.
  have h_binet := phiFP2_pow_eq_fibLike p hp hpo p
  rw [h_binet] at h_frob
  -- h_frob : ((F_p·inv2 + F_{p-1}) % p, (F_p·inv2) % p) = fp2Frob p phi
  -- Extract second component:
  have h2_eq : ((fibLike p).1 * inv2 p) % p = (p - inv2 p % p) % p :=
    congrArg Prod.snd h_frob
  -- (fibLike p).1 = fibFst p (definitional)
  show fibFst p % p = p - 1
  -- Derive (F_p · inv2 + inv2) % p = 0.
  have h_zero : (fibFst p * inv2 p + inv2 p) % p = 0 := by
    rw [add_mod_gen (fibFst p * inv2 p) (inv2 p) p]
    rw [show fibFst p * inv2 p = (fibLike p).1 * inv2 p from rfl]
    rw [h2_eq]
    exact nmod_self_mod_zero p (inv2 p) hp_pos
  -- ((F_p + 1) · inv2) % p = 0
  have h_mul_zero : ((fibFst p + 1) * inv2 p) % p = 0 := by
    rw [add_mul (fibFst p) 1 (inv2 p), Nat.one_mul]
    exact h_zero
  -- (F_p + 1) % p = 0
  have h_succ_zero : (fibFst p + 1) % p = 0 :=
    inv2_cancel_zero (fibFst p + 1) p hp hpo h_mul_zero
  -- F_p % p = p - 1
  exact mod_eq_p_minus_one_of_succ_mod_zero p (fibFst p) hp h_succ_zero

/-- ★★ **phi^(p+1) = (-1, 0) under Frobenius FLT**:
    `phi^(p+1) = phi · phi^p = phi · σ(phi) = (p - 1, 0)`. -/
theorem phiFP2_pow_pp1_of_frob
    (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (h_frob : fp2Pow p (phiFP2 p) p = fp2Frob p (phiFP2 p)) :
    fp2Pow p (phiFP2 p) (p + 1) = (p - 1, 0) := by
  rw [fp2Pow_succ p (phiFP2 p) p, h_frob, fp2Mul_comm p (fp2Frob p (phiFP2 p)) (phiFP2 p)]
  exact phiFP2_mul_frob_phi_eq p hp hpo

/-- ★★★ **Frobenius-FLT-for-phi ⟹ F_{p+1} ≡ 0 mod p**.

    Via phi^(p+1) = (-1, 0) (above) + Binet at p+1.  PURE. -/
theorem fpp1_eq_zero_of_frob_phi
    (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (h_frob : fp2Pow p (phiFP2 p) p = fp2Frob p (phiFP2 p)) :
    fibFst (p + 1) % p = 0 := by
  have h_pp1 := phiFP2_pow_pp1_of_frob p hp hpo h_frob
  -- Apply Binet to phi^(p+1).
  have h_binet := phiFP2_pow_eq_fibLike p hp hpo (p + 1)
  rw [h_binet] at h_pp1
  -- h_pp1 : ((F_{p+1}·inv2 + F_p) % p, (F_{p+1}·inv2) % p) = (p-1, 0)
  -- Extract second:
  have h2 : ((fibLike (p + 1)).1 * inv2 p) % p = 0 :=
    congrArg Prod.snd h_pp1
  -- (fibLike (p+1)).1 = fibFst (p+1) (definitional)
  show fibFst (p + 1) % p = 0
  -- Use inv2_cancel_zero with X = fibFst (p+1)
  exact inv2_cancel_zero (fibFst (p + 1)) p hp hpo h2

/-- ★★★ **Frobenius-FLT-for-phi ⟹ F_{p-1} ≡ 1 mod p**.

    Combines `F_p ≡ -1` and `F_{p+1} ≡ 0` with the Fibonacci recurrence
    `F_{p+1} = F_p + F_{p-1}` (via `fibFst_recur` at index p-1).
    Uses `mod_cancel_right` to compare residues.  PURE. -/
theorem fpm1_eq_one_of_frob_phi
    (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (h_frob : fp2Pow p (phiFP2 p) p = fp2Frob p (phiFP2 p)) :
    fibFst (p - 1) % p = 1 := by
  have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
  have hp_le : 1 ≤ p := Nat.le_of_lt hp
  have h_F_p : fibFst p % p = p - 1 := fp_eq_neg_one_of_frob_phi p hp hpo h_frob
  have h_F_pp1 : fibFst (p + 1) % p = 0 := fpp1_eq_zero_of_frob_phi p hp hpo h_frob
  -- Fibonacci recurrence: F_{p+1} = F_p + F_{p-1}.
  -- via fibFst_recur (p-1) : fibFst ((p-1) + 2) = fibFst ((p-1) + 1) + fibFst (p-1)
  -- with (p-1) + 1 = p, (p-1) + 2 = p + 1.
  have h_pm1_p1 : (p - 1) + 1 = p := sub_add_cancel hp_le
  have h_pm1_p2 : (p - 1) + 2 = p + 1 := by
    rw [show (p - 1) + 2 = ((p - 1) + 1) + 1 from rfl, h_pm1_p1]
  have h_F_pp1_eq : fibFst (p + 1) = fibFst p + fibFst (p - 1) := by
    rw [← h_pm1_p2, fibFst_recur (p - 1), h_pm1_p1]
  -- (F_p + F_{p-1}) % p = 0
  have h_zero : (fibFst p + fibFst (p - 1)) % p = 0 := by
    rw [← h_F_pp1_eq]; exact h_F_pp1
  -- Substitute F_p % p = p - 1 via add_mod_gen.
  rw [add_mod_gen (fibFst p) (fibFst (p - 1)) p] at h_zero
  rw [h_F_p] at h_zero
  -- h_zero : ((p - 1) + fibFst (p-1) % p) % p = 0
  -- Compare with ((p - 1) + 1) % p = 0:
  have h_compare : ((p - 1) + 1) % p = 0 := by
    rw [h_pm1_p1]; exact mod_self p
  -- Apply mod_cancel_right via comm:
  have h_lt_X : fibFst (p - 1) % p < p := Nat.mod_lt _ hp_pos
  have h_lt_1 : (1 : Nat) < p := hp
  -- Reorganize h_zero to (X + (p-1)) % p form via comm.
  have h_zero' : (fibFst (p - 1) % p + (p - 1)) % p = 0 := by
    rw [Nat.add_comm (fibFst (p - 1) % p) (p - 1)]; exact h_zero
  have h_compare' : (1 + (p - 1)) % p = 0 := by
    rw [Nat.add_comm 1 (p - 1)]; exact h_compare
  exact E213.Lib.Math.NumberTheory.ModArith.ModBezoutInvariant.mod_cancel_right
    p _ _ (p - 1) hp_pos h_lt_X h_lt_1 (h_zero'.trans h_compare'.symm)

/-- ★★★★★ **Universal Phase 3.3 via Frobenius FLT on phi**.

    The structurally cleanest formulation: given Frobenius FLT on phi
    in 𝔽_{p²} (`phi^p = σ(phi)`) — which is a single equation
    decidable per prime by `decide` — the full Phase 3.3 matrix-order
    closure follows.

    Internal chain:
      1. h_frob ⟹ F_p ≡ -1 mod p (`fp_eq_neg_one_of_frob_phi`)
      2. h_frob ⟹ F_{p-1} ≡ 1 mod p (`fpm1_eq_one_of_frob_phi`)
      3. Apply `universal_inert_case` (Part 44).

    PURE.  This compresses the inert F-identities (two hypotheses
    in universal_inert_case) into a single Frobenius FLT hypothesis. -/
theorem universal_inert_via_frob
    (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (h_frob : fp2Pow p (phiFP2 p) p = fp2Frob p (phiFP2 p)) :
    E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix.pellCoeff p hp (p + 1)
      = E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix.pellCoeff p hp 0 :=
  universal_inert_case p hp
    (fp_eq_neg_one_of_frob_phi p hp hpo h_frob)
    (fpm1_eq_one_of_frob_phi p hp hpo h_frob)

/-! ## Per-prime smokes for `universal_inert_via_frob` -/

/-- Smoke at p=3: phi^3 = sigma(phi) decided by `decide`. -/
theorem universal_inert_via_frob_at_3 :
    E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix.pellCoeff 3 (by decide) 4
      = E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix.pellCoeff 3 (by decide) 0 :=
  universal_inert_via_frob 3 (by decide) (by decide) (by decide)

/-- Smoke at p=7: phi^7 = sigma(phi) decided by `decide`. -/
theorem universal_inert_via_frob_at_7 :
    E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix.pellCoeff 7 (by decide) 8
      = E213.Lib.Math.NumberTheory.DyadicFSM.PellMatrix.pellCoeff 7 (by decide) 0 :=
  universal_inert_via_frob 7 (by decide) (by decide) (by decide)

/-! ## IF direction: Frobenius FLT for phi FROM inert F-identities

Combined with Parts 50/51 (ONLY-IF direction: Frobenius FLT for phi ⟹
inert F-identities), this establishes the equivalence:

  `phi^p = σ(phi)` in 𝔽_{p²}
    ⟺
  `F_p ≡ -1 ∧ F_{p-1} ≡ 1` (mod p)

for odd `1 < p`.  This IFF is the structural content of inert primes:
Frobenius FLT for phi and the inert Fibonacci characteristic are
two manifestations of the same algebraic fact.  PURE.
-/

open E213.Lib.Math.NumberTheory.ModArith.FP2Sqrt5
  (p_minus_one_mul_mod neg_inv2_plus_one_eq)

/-- ★★★★★ **Frobenius FLT for phi FROM the inert F-identities**.

    Given `h_F_p : fibFst p % p = p - 1` and `h_F_pm1 : fibFst (p-1) % p = 1`,
    derives `phi^p = σ(phi)` in 𝔽_{p²} for odd `1 < p`.

    Proof: apply Binet (Part 48) to phi^p; for each component, substitute
    the F-identities and use `p_minus_one_mul_mod` + `neg_inv2_plus_one_eq`
    to match σ(phi).  PURE. -/
theorem phiFP2_pow_p_eq_frob_of_F_identities
    (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (h_F_p : fibFst p % p = p - 1)
    (h_F_pm1 : fibFst (p - 1) % p = 1) :
    fp2Pow p (phiFP2 p) p = fp2Frob p (phiFP2 p) := by
  have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
  have hp_le : 1 ≤ p := Nat.le_of_lt hp
  -- Binet expansion at index p
  rw [phiFP2_pow_eq_fibLike p hp hpo p]
  -- LHS: (((fibLike p).1 * inv2 + (fibLike p).2) % p, ((fibLike p).1 * inv2) % p)
  -- RHS (fp2Frob p phi): (inv2 % p, (p - inv2 % p) % p)
  have h_snd_eq : (fibLike p).2 = fibFst (p - 1) := by
    show (fibLike p).2 = (fibLike (p - 1)).1
    rw [show p = (p - 1) + 1 from (sub_add_cancel hp_le).symm]
    exact fibLike_succ_snd (p - 1)
  show (((fibLike p).1 * inv2 p + (fibLike p).2) % p,
        ((fibLike p).1 * inv2 p) % p)
      = (inv2 p % p, (p - inv2 p % p) % p)
  rw [show (fibLike p).1 = fibFst p from rfl, h_snd_eq]
  apply Prod.ext
  · -- (fibFst p * inv2 + fibFst (p - 1)) % p = inv2 % p
    show (fibFst p * inv2 p + fibFst (p - 1)) % p = inv2 p % p
    rw [add_mod_gen (fibFst p * inv2 p) (fibFst (p - 1)) p]
    -- ((fibFst p * inv2) % p + fibFst (p-1) % p) % p = inv2 % p
    rw [mul_mod_left_pure (fibFst p) (inv2 p) p]
    -- ((fibFst p % p * inv2) % p + fibFst (p-1) % p) % p = inv2 % p
    rw [h_F_p, h_F_pm1]
    -- (((p - 1) * inv2) % p + 1) % p = inv2 % p
    rw [p_minus_one_mul_mod p (inv2 p) hp]
    -- ((p - inv2 % p) % p + 1) % p = inv2 % p
    exact neg_inv2_plus_one_eq p hp hpo
  · -- (fibFst p * inv2) % p = (p - inv2 % p) % p
    show (fibFst p * inv2 p) % p = (p - inv2 p % p) % p
    rw [mul_mod_left_pure (fibFst p) (inv2 p) p]
    rw [h_F_p]
    exact p_minus_one_mul_mod p (inv2 p) hp

/-- Smoke at p=3: phi^3 = sigma(phi) from F_3 ≡ 2, F_2 ≡ 1. -/
theorem phiFP2_pow_p_eq_frob_of_F_identities_3 :
    fp2Pow 3 (phiFP2 3) 3 = fp2Frob 3 (phiFP2 3) :=
  phiFP2_pow_p_eq_frob_of_F_identities 3 (by decide) (by decide)
    (by decide) (by decide)

/-- Smoke at p=7: phi^7 = sigma(phi). -/
theorem phiFP2_pow_p_eq_frob_of_F_identities_7 :
    fp2Pow 7 (phiFP2 7) 7 = fp2Frob 7 (phiFP2 7) :=
  phiFP2_pow_p_eq_frob_of_F_identities 7 (by decide) (by decide)
    (by decide) (by decide)

/-! ## ★★★★★★ Final goal: Frobenius FLT for phi via atomic-case combination

Combines the two atomic cases (Parts 53, 54) via freshman's dream and
`(x · y)^n = x^n · y^n` (taken as decidable-per-prime hypotheses).

The combining theorem `phiFP2_pow_p_eq_frob_via_atomic_cases` is the
structural realization of the user's directive: combine the atomic
Frobenius FLT cases via freshman's dream and (xy)^n to get Frobenius
FLT for phi.

Decomposition path:
  phi = (inv2, 0) + (0, inv2)                          [Step 1]
  (0, inv2) = (inv2, 0) · (0, 1)                       [Step 2]
  phi^p = ((inv2, 0) + (0, inv2))^p                    [Step 1 substitution]
        = (inv2, 0)^p + (0, inv2)^p                    [Freshman's dream]
        = (inv2, 0) + ((inv2, 0) · (0, 1))^p           [Part 54 FLT + Step 2]
        = (inv2, 0) + (inv2, 0)^p · (0, 1)^p           [(xy)^n]
        = (inv2, 0) + (inv2, 0) · σ((0, 1))            [Part 54 + Part 53]
        = (inv2, 0) + (inv2, 0) · (0, p - 1)
        = (inv2, 0) + (0, p - inv2)                    [fp2Mul computation]
        = (inv2, p - inv2)
        = σ(phi)                                       [definition]
-/

open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod mod_self zero_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure)

/-- ★★★★★★ **Frobenius FLT for phi via atomic-case combination**.

    Universal Frobenius FLT phi^p = σ(phi) in 𝔽_{p²}, derived by combining
    the two atomic cases (FLT in 𝔽_p ⊂ 𝔽_{p²} for `(inv2, 0)` per Part 54,
    and Frobenius FLT for sqrt5 `(0, 1)` per Part 53) via:
      · `h_fd` : freshman's dream `(x + y)^p = x^p + y^p` for the specific
        decomposition `phi = (inv2, 0) + (0, inv2)`.
      · `h_xy` : `(x·y)^p = x^p · y^p` for the specific factoring
        `(0, inv2) = (inv2, 0) · (0, 1)`.

    Both `h_fd` and `h_xy` are decidable per prime via `decide`.

    PURE. -/
theorem phiFP2_pow_p_eq_frob_via_atomic_cases
    (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (h_inert : 5^(p / 2) % p = p - 1)
    (h_flt_inv2 : (inv2 p)^p % p = inv2 p % p)
    (h_fd : fp2Pow p (fp2Add p (inv2 p, 0) (0, inv2 p)) p
          = fp2Add p (fp2Pow p (inv2 p, 0) p) (fp2Pow p (0, inv2 p) p))
    (h_xy : fp2Pow p (fp2Mul p (inv2 p, 0) (0, 1)) p
          = fp2Mul p (fp2Pow p (inv2 p, 0) p) (fp2Pow p (0, 1) p)) :
    fp2Pow p (phiFP2 p) p = fp2Frob p (phiFP2 p) := by
  have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
  have h_inv2_lt : inv2 p < p := inv2_lt_self p hp hpo
  have h_inv2_mod : inv2 p % p = inv2 p := Nat.mod_eq_of_lt h_inv2_lt
  -- Step 1: phi = fp2Add (inv2, 0) (0, inv2)  (canonical decomposition)
  have h_phi_eq : phiFP2 p = fp2Add p (inv2 p, 0) (0, inv2 p) := by
    show (inv2 p, inv2 p) = ((inv2 p + 0) % p, (0 + inv2 p) % p)
    apply Prod.ext
    · show inv2 p = (inv2 p + 0) % p
      rw [Nat.add_zero]; exact h_inv2_mod.symm
    · show inv2 p = (0 + inv2 p) % p
      rw [Nat.zero_add]; exact h_inv2_mod.symm
  -- Step 2: (0, inv2) = fp2Mul (inv2, 0) (0, 1)
  have h_zero_inv2_eq : ((0, inv2 p) : FP2) = fp2Mul p (inv2 p, 0) (0, 1) := by
    show (0, inv2 p) = ((inv2 p * 0 + 5 * 0 * 1) % p, (inv2 p * 1 + 0 * 0) % p)
    apply Prod.ext
    · show 0 = (inv2 p * 0 + 5 * 0 * 1) % p
      rw [Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
      exact (zero_mod p).symm
    · show inv2 p = (inv2 p * 1 + 0 * 0) % p
      rw [Nat.mul_one, Nat.zero_mul, Nat.add_zero]
      exact h_inv2_mod.symm
  -- Compute LHS = fp2Pow p (phiFP2 p) p via calc chain.
  have hpm1_lt : p - 1 < p := Nat.sub_lt hp_pos Nat.one_pos
  -- Target intermediate form:
  --   fp2Add p (inv2 p % p, 0) (fp2Mul p (inv2 p % p, 0) (fp2Frob p (0, 1)))
  -- This will equal both LHS (phi^p) and RHS (sigma(phi)).
  have h_lhs_chain :
      fp2Pow p (phiFP2 p) p
      = fp2Add p (inv2 p % p, 0)
                 (fp2Mul p (inv2 p % p, 0) (fp2Frob p (0, 1))) := by
    rw [h_phi_eq, h_fd, h_zero_inv2_eq, h_xy]
    rw [fp2Pow_scalar_p p (inv2 p) h_flt_inv2]
    rw [fp2Pow_sqrt5_eq_frob p hp hpo h_inert]
  -- Now show RHS chain.
  have h_rhs_chain :
      fp2Frob p (phiFP2 p)
      = fp2Add p (inv2 p % p, 0)
                 (fp2Mul p (inv2 p % p, 0) (fp2Frob p (0, 1))) := by
    -- fp2Frob p phi = (inv2 % p, (p - inv2 % p) % p)
    show ((phiFP2 p).1 % p, (p - (phiFP2 p).2 % p) % p)
       = fp2Add p (inv2 p % p, 0)
                  (fp2Mul p (inv2 p % p, 0) (fp2Frob p (0, 1)))
    show (inv2 p % p, (p - inv2 p % p) % p)
       = fp2Add p (inv2 p % p, 0)
                  (fp2Mul p (inv2 p % p, 0) (0 % p, (p - 1 % p) % p))
    rw [zero_mod p, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hpm1_lt]
    show (inv2 p % p, (p - inv2 p % p) % p)
       = ((inv2 p % p + (inv2 p % p * 0 + 5 * 0 * (p - 1)) % p) % p,
          (0 + (inv2 p % p * (p - 1) + 0 * 0) % p) % p)
    apply Prod.ext
    · show inv2 p % p
         = (inv2 p % p + (inv2 p % p * 0 + 5 * 0 * (p - 1)) % p) % p
      rw [Nat.mul_zero, Nat.zero_mul, Nat.add_zero, zero_mod p, Nat.add_zero, mod_mod]
    · show (p - inv2 p % p) % p
         = (0 + (inv2 p % p * (p - 1) + 0 * 0) % p) % p
      rw [Nat.zero_mul, Nat.add_zero, Nat.zero_add, mod_mod]
      rw [← mul_mod_left_pure (inv2 p) (p - 1) p]
      rw [Nat.mul_comm (inv2 p) (p - 1)]
      exact (p_minus_one_mul_mod p (inv2 p) hp).symm
  exact h_lhs_chain.trans h_rhs_chain.symm

/-- Smoke at p=3: phi^3 = sigma(phi) via atomic combination. -/
theorem phiFP2_pow_p_eq_frob_via_atomic_cases_3 :
    fp2Pow 3 (phiFP2 3) 3 = fp2Frob 3 (phiFP2 3) :=
  phiFP2_pow_p_eq_frob_via_atomic_cases 3 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- Smoke at p=7: phi^7 = sigma(phi). -/
theorem phiFP2_pow_p_eq_frob_via_atomic_cases_7 :
    fp2Pow 7 (phiFP2 7) 7 = fp2Frob 7 (phiFP2 7) :=
  phiFP2_pow_p_eq_frob_via_atomic_cases 7 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

end E213.Lib.Math.NumberTheory.DyadicFSM.UniversalInert
