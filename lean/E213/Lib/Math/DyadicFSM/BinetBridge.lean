import E213.Lib.Math.DyadicFSM.PsiMod5
import E213.Lib.Math.DyadicFSM.PellFibBridge
import E213.Lib.Math.DyadicFSM.MulOrderPigeonhole
/-!
# Binet bridge: FLT for φ + ψ → Fibonacci-Pisano `F_{p-1} ≡ 0 mod p`

The classical Binet-style derivation that, for split primes p (where
both φ and ψ are in F_p):

  · `phi^(p-1) ≡ F_{p-1} · phi + F_{p-2} ≡ 1 (mod p)` [FLT + Fib expansion]
  · `psi^(p-1) ≡ F_{p-1} · psi + F_{p-2} ≡ 1 (mod p)` [FLT + Fib expansion]
  · So both reduce to 1, and substituting `phi ≡ psi + s mod p`:
       `F_{p-1} · s + (F_{p-1} · psi + F_{p-2}) ≡ 1 ≡ F_{p-1} · psi + F_{p-2}`
       hence `F_{p-1} · s ≡ 0 mod p`.
  · Cancel `s` via `ModInverse p s`: `F_{p-1} ≡ 0 mod p`.

This bridges the **conditional Phase 3.2 closure** (`phase_3_2_closure`,
Part 13) to the universal Fibonacci-Pisano condition for split primes
— modulo the FLT hypothesis for both φ and ψ.

Per-prime: all hypotheses (FLT for φ, FLT for ψ, ModInverse for s)
are decidable.  Universal: depends on universal FLT (multi-session
Bezout for inverses).

All declarations PURE.
-/

namespace E213.Lib.Math.DyadicFSM.BinetBridge

open E213.Lib.Math.DyadicFSM.PhiMod5 (phi)
open E213.Lib.Math.DyadicFSM.PsiMod5 (psi fibLike_pow)
open E213.Lib.Math.DyadicFSM.PellFibBridge (fibFst)
open E213.Lib.Math.DyadicFSM.MulOrderPigeonhole (ModInverse)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod mod_diff_eq_zero_of_le)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Tactic.NatHelper (mul_assoc add_sub_cancel_right)

/-- ★ **Cancellation helper**:  if `(X + Y) % p = Y % p` and `0 < p`,
    then `X % p = 0`.

    Proof: from `(X + Y) % p = Y % p`, by `mod_diff_eq_zero_of_le`
    (AddMod213) we get `((X + Y) - Y) % p = 0`.  By Nat:
    `(X + Y) - Y = X`, so `X % p = 0`.  PURE. -/
theorem add_mod_eq_right_implies_zero (p X Y : Nat) (hp : 0 < p)
    (h : (X + Y) % p = Y % p) : X % p = 0 := by
  have h_le : Y ≤ X + Y := Nat.le_add_left Y X
  have h_diff : (X + Y - Y) % p = 0 :=
    mod_diff_eq_zero_of_le hp h_le h.symm
  rw [add_sub_cancel_right X Y] at h_diff
  exact h_diff

/-- ★ **Multiplicative cancellation via explicit inverse**:
    if `(X · a) % p = 0` and `mi : ModInverse p a`, then `X % p = 0`.

    PURE.  Multiply by `mi.inv` and use `mi.inv_eq` to cancel `a`. -/
theorem mul_mod_zero_cancel (p X a : Nat) (hp : 0 < p)
    (mi : ModInverse p a) (h : (X * a) % p = 0) : X % p = 0 := by
  -- (mi.inv * (X * a)) % p = (mi.inv * 0) % p = 0
  have h_mult : (mi.inv * (X * a)) % p = 0 := by
    rw [mul_mod_right_pure mi.inv (X * a) p, h, Nat.mul_zero]
    rfl
  -- Rearrange: mi.inv * (X * a) = X * (a * mi.inv) = X * ((a * mi.inv) % p)
  -- After substituting mi.inv_eq, this becomes X * (1 % p), then X % p.
  have h_rearrange : mi.inv * (X * a) = X * (a * mi.inv) := by
    rw [← mul_assoc, Nat.mul_comm mi.inv X, mul_assoc, Nat.mul_comm mi.inv a]
  rw [h_rearrange] at h_mult
  rw [mul_mod_right_pure X (a * mi.inv) p, mi.inv_eq,
      ← mul_mod_right_pure X 1 p, Nat.mul_one] at h_mult
  exact h_mult

/-- ★★★★★ **Binet bridge** (per-prime).

    Given (per-prime decidable hypotheses):
      · `h_phi_pow` : `(phi p s)^(p-1) % p = (F_{p-1}·phi + F_{p-2}) % p`
        — combined Fibonacci expansion + FLT for phi
      · `h_psi_pow` : `(psi p s)^(p-1) % p = (F_{p-1}·psi + F_{p-2}) % p`
        — combined Fibonacci expansion + FLT for psi
      · `h_phi_flt` : `(phi p s)^(p-1) % p = 1 % p`
      · `h_psi_flt` : `(psi p s)^(p-1) % p = 1 % p`
      · `h_phi_eq_psi_plus_s` : `(phi p s) % p = (psi p s + s) % p`
      · `mi_s` : ModInverse p s
    Conclude:  `(fibFst (2 * N)) % p = 0` where `2 * N = p - 1`.
    (Specifically `(fibFst (p - 1)) % p = 0` after the index manipulation.)

    PURE.  Combines all hypotheses via the Nat-mod helpers. -/
theorem binet_F_p_minus_1_zero (p s : Nat) (hp : 0 < p)
    (F1 F2 : Nat)  -- F1 = F_{p-1}, F2 = F_{p-2}
    (h_phi_pow_eq : (phi p s)^(p - 1) % p = (F1 * phi p s + F2) % p)
    (h_psi_pow_eq : (psi p s)^(p - 1) % p = (F1 * psi p s + F2) % p)
    (h_phi_flt : (phi p s)^(p - 1) % p = 1 % p)
    (h_psi_flt : (psi p s)^(p - 1) % p = 1 % p)
    (h_phi_eq_psi_plus_s : (phi p s) % p = (psi p s + s) % p)
    (mi_s : ModInverse p s) :
    F1 % p = 0 := by
  -- Combine FLT + Fib expansion to get:
  --   (F1 * phi + F2) % p = 1 % p
  --   (F1 * psi + F2) % p = 1 % p
  have h_phi_form : (F1 * phi p s + F2) % p = 1 % p := h_phi_pow_eq.symm.trans h_phi_flt
  have h_psi_form : (F1 * psi p s + F2) % p = 1 % p := h_psi_pow_eq.symm.trans h_psi_flt
  -- Substitute phi ≡ psi + s in h_phi_form
  -- (F1 * phi + F2) % p
  --   = (F1 * (phi % p) + F2) % p   [mul_mod_right_pure backward inside add]
  --   = (F1 * ((psi + s) % p) + F2) % p   [substitute]
  --   = (F1 * (psi + s) + F2) % p   [mul_mod_right_pure forward]
  --   = (F1 * psi + F1 * s + F2) % p   [Nat.mul_add]
  have h_subst : (F1 * phi p s + F2) % p
               = (F1 * psi p s + F1 * s + F2) % p := by
    -- Step: rewrite phi as psi+s mod p
    rw [add_mod_gen (F1 * phi p s) F2 p,
        mul_mod_right_pure F1 (phi p s) p,
        h_phi_eq_psi_plus_s,
        ← mul_mod_right_pure F1 (psi p s + s) p,
        Nat.mul_add F1 (psi p s) s,
        ← add_mod_gen (F1 * psi p s + F1 * s) F2 p]
  rw [h_subst] at h_phi_form
  -- h_phi_form: (F1 * psi + F1 * s + F2) % p = 1 % p
  -- h_psi_form: (F1 * psi + F2) % p = 1 % p
  -- Rearrange LHS of h_phi_form to (F1 * s + (F1 * psi + F2)) % p
  have h_rearr : F1 * psi p s + F1 * s + F2 = F1 * s + (F1 * psi p s + F2) := by
    -- LHS: (F1*psi + F1*s) + F2 = (F1*psi + F2) + F1*s (add_right_comm)
    --                          = F1*s + (F1*psi + F2) (add_comm)
    rw [Nat.add_right_comm (F1 * psi p s) (F1 * s) F2,
        Nat.add_comm (F1 * psi p s + F2) (F1 * s)]
  rw [h_rearr] at h_phi_form
  -- h_phi_form: (F1 * s + (F1 * psi + F2)) % p = 1 % p
  -- h_psi_form: (F1 * psi + F2) % p = 1 % p
  -- So (F1 * s + (F1 * psi + F2)) % p = (F1 * psi + F2) % p (both = 1 % p)
  have h_combo : (F1 * s + (F1 * psi p s + F2)) % p = (F1 * psi p s + F2) % p :=
    h_phi_form.trans h_psi_form.symm
  -- Apply add_mod_eq_right_implies_zero to extract: (F1 * s) % p = 0
  have h_F1_s_zero : (F1 * s) % p = 0 :=
    add_mod_eq_right_implies_zero p (F1 * s) (F1 * psi p s + F2) hp h_combo
  -- Cancel s via ModInverse to get F1 % p = 0
  exact mul_mod_zero_cancel p F1 s hp mi_s h_F1_s_zero

/-! ## Per-prime smokes: Binet bridge applied at split primes -/

open E213.Lib.Math.DyadicFSM.PhiMod5 (phi_pow_eq_fibLike phi_sq_eq_phi_add_one)
open E213.Lib.Math.DyadicFSM.PsiMod5
  (psi psi_pow_eq_fibLike_11 psi_pow_eq_fibLike_19
   phi_eq_psi_plus_s_11 psi_minus_phi_19)

/-- ModInverse witness: 4 · 3 = 12 ≡ 1 mod 11.  So s=4 has inverse 3 mod 11. -/
def modInv_4_mod_11 : ModInverse 11 4 :=
  { inv := 3, inv_lt := by decide, inv_eq := by decide }

/-- ★ **Binet at p=11**: F_10 ≡ 0 mod 11, derived from FLT for both
    phi and psi via `binet_F_p_minus_1_zero`. -/
theorem F_10_zero_mod_11_via_binet : (fibFst 10) % 11 = 0 := by
  -- Use the binet bridge.  All hypotheses are decide-able at p=11.
  have h_phi_pow_eq : (phi 11 4)^10 % 11 = (fibFst 10 * phi 11 4 + fibFst 9) % 11 := by
    exact phi_pow_eq_fibLike 11 4 (by decide) (by decide) (by decide) 10
  have h_psi_pow_eq : (psi 11 4)^10 % 11 = (fibFst 10 * psi 11 4 + fibFst 9) % 11 :=
    psi_pow_eq_fibLike_11 10
  have h_phi_flt : (phi 11 4)^10 % 11 = 1 % 11 := by decide
  have h_psi_flt : (psi 11 4)^10 % 11 = 1 % 11 := by decide
  exact binet_F_p_minus_1_zero 11 4 (by decide) (fibFst 10) (fibFst 9)
    h_phi_pow_eq h_psi_pow_eq h_phi_flt h_psi_flt
    phi_eq_psi_plus_s_11 modInv_4_mod_11

/-- ModInverse witness: 9 · 17 = 153 = 8·19 + 1 ≡ 1 mod 19. -/
def modInv_9_mod_19 : ModInverse 19 9 :=
  { inv := 17, inv_lt := by decide, inv_eq := by decide }

/-- Note: at p=19, `phi 19 9 = 5` and `psi 19 9 = 15`.
    `phi - psi ≡ -10 ≡ 9 ≡ s mod 19` (with `phi % 19 = 5 = (psi + s) % 19 = (15 + 9) % 19 = 24 % 19 = 5` ✓). -/
theorem phi_eq_psi_plus_s_19 : (phi 19 9) % 19 = (psi 19 9 + 9) % 19 := by decide

/-- ★ **Binet at p=19**: F_18 ≡ 0 mod 19. -/
theorem F_18_zero_mod_19_via_binet : (fibFst 18) % 19 = 0 := by
  have h_phi_pow_eq : (phi 19 9)^18 % 19 = (fibFst 18 * phi 19 9 + fibFst 17) % 19 := by
    exact phi_pow_eq_fibLike 19 9 (by decide) (by decide) (by decide) 18
  have h_psi_pow_eq : (psi 19 9)^18 % 19 = (fibFst 18 * psi 19 9 + fibFst 17) % 19 :=
    psi_pow_eq_fibLike_19 18
  have h_phi_flt : (phi 19 9)^18 % 19 = 1 % 19 := by decide
  have h_psi_flt : (psi 19 9)^18 % 19 = 1 % 19 := by decide
  exact binet_F_p_minus_1_zero 19 9 (by decide) (fibFst 18) (fibFst 17)
    h_phi_pow_eq h_psi_pow_eq h_phi_flt h_psi_flt
    phi_eq_psi_plus_s_19 modInv_9_mod_19

end E213.Lib.Math.DyadicFSM.BinetBridge
