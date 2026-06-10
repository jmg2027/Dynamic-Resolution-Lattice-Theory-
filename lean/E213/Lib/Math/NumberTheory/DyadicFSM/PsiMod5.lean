import E213.Lib.Math.NumberTheory.DyadicFSM.PhiMod5
/-!
# Psi (the other golden ratio mod p) + generic Fibonacci-power theorem

For split primes `p` (5 is QR mod p), the quadratic `x² = x + 1`
has TWO roots in `F_p`:

  · `phi p s := (1 + s) · inv2 p mod p`      (defined in PhiMod5)
  · `psi p s := (1 + p - s) · inv2 p mod p`  (the "other" root)

Both satisfy:
  · `x² ≡ x + 1 (mod p)` (the φ-recurrence)
  · `x^k ≡ F_k · x + F_{k-1} (mod p)` (Fibonacci expansion)
  · `x^(p-1) ≡ 1 (mod p)` (FLT for `x ≠ 0`)

Plus their relationships:
  · `phi + psi ≡ 1 (mod p)`
  · `phi · psi ≡ -1 (mod p)` (i.e., `(phi · psi + 1) % p = 0`)
  · `phi - psi ≡ s (mod p)`

This module provides:
  · A **generic** `fibLike_pow` theorem applicable to any element
    `x : Nat` satisfying `x² % p = (x + 1) % p` — used by both
    phi and psi.
  · `psi` definition + recurrence + Fibonacci expansion
    (1-line corollaries of the generic theorem).

For Phase 3.2: combining FLT for both phi and psi gives
`F_{p-1} · s ≡ 0 mod p`, which (with s invertible mod p) closes
`F_{p-1} ≡ 0 mod p` — the Fibonacci-Pisano condition for split
primes.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.PsiMod5

open E213.Lib.Math.NumberTheory.DyadicFSM.PhiMod5 (inv2 two_mul_inv2 fibLike phi)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Tactic.NatHelper (mul_assoc add_mul)

/-! ## Generic Fibonacci-power theorem -/

/-- ★ **Generic Fibonacci-power expansion**:
    For any `x` with `x² ≡ x + 1 (mod p)`,
    `x^k ≡ F_k · x + F_{k-1} (mod p)` (where F_k = (fibLike k).1).

    PURE.  By induction on `k`, using the recurrence hypothesis.
    Mirrors `phi_pow_eq_fibLike` from PhiMod5, generalised over
    the carrier `x`. -/
theorem fibLike_pow (p x : Nat) (h_recur : x * x % p = (x + 1) % p) :
    ∀ k, x^k % p = ((fibLike k).1 * x + (fibLike k).2) % p
  | 0 => by
    show 1 % p = (0 * x + 1) % p
    rw [Nat.zero_mul, Nat.zero_add]
  | k + 1 => by
    have ih := fibLike_pow p x h_recur k
    -- Unfold fibLike (k+1)
    show x^(k + 1) % p
       = (((fibLike k).1 + (fibLike k).2) * x + (fibLike k).1) % p
    -- x^(k+1) = x^k * x (Nat.pow def)
    show (x^k * x) % p
       = (((fibLike k).1 + (fibLike k).2) * x + (fibLike k).1) % p
    rw [mul_mod_left_pure (x^k) x p, ih,
        ← mul_mod_left_pure ((fibLike k).1 * x + (fibLike k).2) x p]
    -- Goal: ((a*x + b) * x) % p = ((a + b)*x + a) % p
    rw [add_mul ((fibLike k).1 * x) (fibLike k).2 x]
    rw [mul_assoc (fibLike k).1 x x]
    -- Substitute x*x ≡ x+1 mod p
    rw [add_mod_gen ((fibLike k).1 * (x * x)) ((fibLike k).2 * x) p,
        mul_mod_right_pure (fibLike k).1 (x * x) p,
        h_recur,
        ← mul_mod_right_pure (fibLike k).1 (x + 1) p,
        ← add_mod_gen ((fibLike k).1 * (x + 1)) ((fibLike k).2 * x) p]
    -- Goal: (a * (x + 1) + b * x) % p = ((a + b)*x + a) % p
    rw [Nat.mul_add (fibLike k).1 x 1, Nat.mul_one]
    rw [Nat.add_right_comm ((fibLike k).1 * x) (fibLike k).1
                           ((fibLike k).2 * x)]
    rw [← add_mul (fibLike k).1 (fibLike k).2 x]

/-! ## ψ definition + recurrence + Fibonacci expansion -/

/-- `psi p s := ((1 + p) - s) · inv2 p mod p` — the "other" root of
    `x² = x + 1` in `F_p`, given a sqrt5 witness `s` with `s² ≡ 5 mod p`.

    Equivalent to `(1 - s)/2` in F_p sense (using `1 - s ≡ 1 + p - s
    (mod p)` for `s ≤ p`).  For `s < p`: `1 + p - s > 0`. -/
def psi (p s : Nat) : Nat := ((1 + p) - s) * inv2 p % p

/-- `psi p s < p` for `p > 0`. -/
theorem psi_lt (p s : Nat) (hp : 0 < p) : psi p s < p :=
  Nat.mod_lt _ hp

/-- Smoke: at p=11, s=4: `psi 11 4 = 4` (since phi 11 4 = 8 and
    phi + psi ≡ 1 mod 11 implies psi ≡ -7 ≡ 4 mod 11). -/
theorem psi_11_4 : psi 11 4 = 4 := by decide

/-- Smoke: at p=19, s=9: `psi 19 9 = 15` (phi=5, phi+psi=1, so psi ≡ -4 ≡ 15). -/
theorem psi_19_9 : psi 19 9 = 15 := by decide

/-- ψ recurrence at p=11: `psi² ≡ psi + 1 mod 11`. -/
theorem psi_sq_11 : (psi 11 4 * psi 11 4) % 11 = (psi 11 4 + 1) % 11 := by decide

/-- ψ recurrence at p=19: `psi² ≡ psi + 1 mod 19`. -/
theorem psi_sq_19 : (psi 19 9 * psi 19 9) % 19 = (psi 19 9 + 1) % 19 := by decide

/-- ψ Fibonacci expansion at p=11 (corollary of generic `fibLike_pow`). -/
theorem psi_pow_eq_fibLike_11 :
    ∀ k, (psi 11 4)^k % 11
       = ((fibLike k).1 * psi 11 4 + (fibLike k).2) % 11 :=
  fibLike_pow 11 (psi 11 4) psi_sq_11

/-- ψ Fibonacci expansion at p=19. -/
theorem psi_pow_eq_fibLike_19 :
    ∀ k, (psi 19 9)^k % 19
       = ((fibLike k).1 * psi 19 9 + (fibLike k).2) % 19 :=
  fibLike_pow 19 (psi 19 9) psi_sq_19

/-! ## φ-ψ relationships at split primes -/

/-- At p=11: `phi + psi ≡ 1 mod 11`. -/
theorem phi_plus_psi_11 : (phi 11 4 + psi 11 4) % 11 = 1 % 11 := by decide

/-- At p=11: `phi - psi ≡ s mod 11` (additive form: `phi ≡ psi + s mod 11`). -/
theorem phi_eq_psi_plus_s_11 : phi 11 4 % 11 = (psi 11 4 + 4) % 11 := by decide

/-- At p=19: `phi + psi ≡ 1 mod 19`. -/
theorem phi_plus_psi_19 : (phi 19 9 + psi 19 9) % 19 = 1 % 19 := by decide

/-- At p=19: `psi ≡ phi + s mod 19` (additive form of psi - phi = -s ≡ p - s).
    Or rearranged: `psi - phi ≡ -s mod 19`, i.e., `phi + s ≡ psi mod 19`
    when phi < psi.  But psi (15) > phi (5) at p=19, so psi - phi = 10 ≡ -9 mod 19?
    Actually psi - phi = 10, and -s = -9 ≡ 10 mod 19. ✓ -/
theorem psi_minus_phi_19 : (phi 19 9 + 10) % 19 = psi 19 9 % 19 := by decide

end E213.Lib.Math.NumberTheory.DyadicFSM.PsiMod5
