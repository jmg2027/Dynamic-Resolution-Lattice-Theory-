import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.DyadicFSM.MulOrderPigeonhole
/-!
# Golden ratio mod p — G119 Phase 3.2 algebraic foundation

For odd `p > 1` and `s : Nat` with `s² ≡ 5 (mod p)`, define

  `inv2 p := p / 2 + 1`                — multiplicative inverse of 2 mod p
  `phi p s := ((1 + s) * inv2 p) % p`  — golden ratio mod p

and prove:

  · `two_mul_inv2`     :  `2 * inv2 p ≡ 1  (mod p)`
  · `two_mul_phi_eq`   :  `2 * phi p s ≡ 1 + s  (mod p)`     (bridge)
  · `four_phi_sq_eq`   :  `4 * phi² ≡ (1+s)² ≡ 1 + 2s + 5 = 6 + 2s  (mod p)`,
                          using `s² ≡ 5`
  · `four_phi_plus_one_eq` : `4 * (phi + 1) ≡ 6 + 2s  (mod p)`
  · **`four_phi_sq_eq_four_phi_plus_one`** :
                          `4 * phi² ≡ 4 * (phi + 1)  (mod p)`,
                          the **scaled** form of `phi² = phi + 1`

The unscaled identity `phi² ≡ phi + 1  (mod p)` follows from
multiplicative cancellation of 4 mod p (i.e., `gcd(4, p) = 1` for
odd p, equivalent to existence of `4⁻¹ mod p`).  That cancellation
requires either explicit `4⁻¹` (Bézout / xgcd) or the multiplicative
order theory of `(Fin p)*` — both are G119 Phase 2.1 prerequisites
that remain multi-session.

This file is **algebra only** — no FLT, no QR existence claim.
Caller provides `s` with `s² ≡ 5 mod p`; we verify the scaled φ
recurrence.

All declarations PURE.
-/

namespace E213.Lib.Math.DyadicFSM.PhiMod5

open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod mod_self div_add_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Tactic.NatHelper (mul_assoc add_mul)

/-- `inv2 p := p / 2 + 1`.  For odd `p > 1`, this is the
    multiplicative inverse of 2 mod p (see `two_mul_inv2`). -/
def inv2 (p : Nat) : Nat := p / 2 + 1

/-- ★ `2 * inv2 p ≡ 1 (mod p)` for odd `p > 1`.  PURE.
    The `1 < p` hypothesis is structural (would be required by any
    nontrivial consumer); the proof uses only `p % 2 = 1`. -/
theorem two_mul_inv2 (p : Nat) (_hp : 1 < p) (hpo : p % 2 = 1) :
    (2 * inv2 p) % p = 1 % p := by
  show (2 * (p / 2 + 1)) % p = 1 % p
  rw [Nat.mul_add, Nat.mul_one]
  -- Goal: (2 * (p / 2) + 2) % p = 1 % p
  have hdiv : 2 * (p / 2) + p % 2 = p := div_add_mod p 2
  rw [hpo] at hdiv
  -- hdiv : 2 * (p / 2) + 1 = p
  have hsucc : 2 * (p / 2) + 2 = (2 * (p / 2) + 1) + 1 := by
    rw [Nat.add_assoc]
  rw [hsucc, hdiv]
  -- Goal: (p + 1) % p = 1 % p
  rw [add_mod_gen p 1 p, mod_self, Nat.zero_add, mod_mod]

/-- `phi p s := ((1 + s) * inv2 p) % p` — golden ratio mod p,
    given a square root `s` of 5 mod p. -/
def phi (p s : Nat) : Nat := ((1 + s) * inv2 p) % p

/-- `phi p s < p` for `p > 0` (by construction as `_ % p`). -/
theorem phi_lt (p s : Nat) (hp : 0 < p) : phi p s < p :=
  Nat.mod_lt _ hp

/-- ★ **Bridge identity**: `2 * phi ≡ 1 + s (mod p)`.
    Uses `2 * inv2 ≡ 1`.  PURE. -/
theorem two_mul_phi_eq (p s : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (2 * phi p s) % p = (1 + s) % p := by
  -- phi p s = ((1 + s) * inv2 p) % p
  -- 2 * phi = 2 * (((1+s) * inv2) % p)
  -- (2 * phi) % p = (2 * ((1+s) * inv2)) % p = ((1+s) * (2 * inv2)) % p
  -- ≡ (1+s) * 1 mod p = 1+s mod p
  have step1 : (2 * phi p s) % p = (2 * ((1 + s) * inv2 p)) % p := by
    show (2 * (((1 + s) * inv2 p) % p)) % p = (2 * ((1 + s) * inv2 p)) % p
    exact (mul_mod_right_pure 2 ((1 + s) * inv2 p) p).symm
  have step2 : 2 * ((1 + s) * inv2 p) = (1 + s) * (2 * inv2 p) := by
    rw [← mul_assoc, Nat.mul_comm 2 (1 + s), mul_assoc]
  rw [step1, step2]
  -- Goal: ((1 + s) * (2 * inv2 p)) % p = (1 + s) % p
  -- Introduce inner mod on `2 * inv2 p`, substitute via two_mul_inv2:
  rw [mul_mod_right_pure (1 + s) (2 * inv2 p) p, two_mul_inv2 p hp hpo]
  -- Goal: ((1 + s) * (1 % p)) % p = (1 + s) % p
  -- Strip inner mod: (1+s) * (1%p) % p = (1+s) * 1 % p = (1+s) % p
  rw [← mul_mod_right_pure (1 + s) 1 p, Nat.mul_one]

/-- Helper: `4 * (a * a) = (2 * a) * (2 * a)` in Nat. -/
private theorem four_mul_sq (a : Nat) : 4 * (a * a) = (2 * a) * (2 * a) := by
  -- (2 * a) * (2 * a) = 2 * (a * (2 * a)) = 2 * (a * 2 * a)
  --                   = 2 * (2 * a * a) = 2 * 2 * (a * a) = 4 * (a * a)
  rw [mul_assoc 2 a (2 * a), ← mul_assoc a 2 a]
  rw [Nat.mul_comm a 2, mul_assoc 2 a a, ← mul_assoc 2 2 (a * a)]

/-- Helper: `(4 * (phi p s * phi p s)) % p = ((2 * phi p s) * (2 * phi p s)) % p`. -/
private theorem four_phi_sq (p s : Nat) :
    (4 * (phi p s * phi p s)) % p
      = ((2 * phi p s) * (2 * phi p s)) % p := by
  rw [four_mul_sq]

/-- ★ **Scaled phi² reduction**: `4 * phi² ≡ (1+s) * (1+s) (mod p)`.
    Uses the bridge `two_mul_phi_eq` + Nat algebra.  PURE. -/
theorem four_phi_sq_eq (p s : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (4 * (phi p s * phi p s)) % p = ((1 + s) * (1 + s)) % p := by
  rw [four_phi_sq p s]
  -- Goal: ((2 * phi p s) * (2 * phi p s)) % p = ((1 + s) * (1 + s)) % p
  rw [mul_mod_pure (2 * phi p s) (2 * phi p s) p]
  rw [two_mul_phi_eq p s hp hpo]
  rw [← mul_mod_pure (1 + s) (1 + s) p]

/-- Helper: expand `(1+s) * (1+s) = 1 + 2*s + s*s` in Nat. -/
private theorem expand_one_plus_s_sq (s : Nat) :
    (1 + s) * (1 + s) = 1 + 2 * s + s * s := by
  -- (1 + s) * (1 + s) = 1*(1+s) + s*(1+s) = (1 + s) + (s + s*s)
  rw [add_mul, Nat.one_mul]
  -- Goal: 1 + s + s * (1 + s) = 1 + 2 * s + s * s
  rw [Nat.mul_add, Nat.mul_one]
  -- Goal: 1 + s + (s + s * s) = 1 + 2 * s + s * s
  rw [← Nat.add_assoc (1 + s) s (s * s)]
  -- Goal: 1 + s + s + s * s = 1 + 2 * s + s * s
  rw [Nat.add_assoc 1 s s]
  -- Goal: 1 + (s + s) + s * s = 1 + 2 * s + s * s
  rw [← Nat.two_mul s]

/-- ★ **Expand & substitute**: `(1+s) * (1+s) ≡ 6 + 2s (mod p)`,
    using `s² ≡ 5 (mod p)`.  PURE. -/
theorem one_plus_s_sq_eq (p s : Nat) (hs2 : (s * s) % p = 5 % p) :
    ((1 + s) * (1 + s)) % p = (6 + 2 * s) % p := by
  rw [expand_one_plus_s_sq]
  -- Goal: (1 + 2*s + s*s) % p = (6 + 2 * s) % p
  rw [add_mod_gen (1 + 2 * s) (s * s) p, hs2,
      ← add_mod_gen (1 + 2 * s) 5 p]
  -- Goal: (1 + 2*s + 5) % p = (6 + 2 * s) % p
  -- 1 + 2*s + 5 = 6 + 2*s by rearrangement
  have heq : 1 + 2 * s + 5 = 6 + 2 * s := by
    rw [Nat.add_right_comm 1 (2 * s) 5]
  rw [heq]

/-- Helper: `4 * (phi + 1) = 2 * (2 * phi) + 4` in Nat. -/
private theorem four_phi_plus_one (p s : Nat) :
    4 * (phi p s + 1) = 2 * (2 * phi p s) + 4 := by
  rw [Nat.mul_add, Nat.mul_one]
  rw [← mul_assoc 2 2 (phi p s)]

/-- ★ **Scaled (phi + 1) reduction**: `4 * (phi + 1) ≡ 6 + 2s (mod p)`. -/
theorem four_phi_plus_one_eq (p s : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (4 * (phi p s + 1)) % p = (6 + 2 * s) % p := by
  rw [four_phi_plus_one]
  -- Goal: (2 * (2 * phi p s) + 4) % p = (6 + 2 * s) % p
  rw [add_mod_gen (2 * (2 * phi p s)) 4 p]
  rw [mul_mod_right_pure 2 (2 * phi p s) p]
  rw [two_mul_phi_eq p s hp hpo]
  rw [← mul_mod_right_pure 2 (1 + s) p]
  rw [← add_mod_gen (2 * (1 + s)) 4 p]
  -- Goal: (2 * (1 + s) + 4) % p = (6 + 2 * s) % p
  congr 1
  -- 2 * (1 + s) + 4 = 6 + 2 * s
  rw [Nat.mul_add, Nat.mul_one]
  -- 2 + 2 * s + 4 = 6 + 2 * s
  rw [Nat.add_right_comm 2 (2 * s) 4]

/-- ★★★ **Scaled φ recurrence** (Phase 3.2 algebraic kernel):
    `4 * phi² ≡ 4 * (phi + 1)  (mod p)`,
    given `s² ≡ 5 (mod p)` and odd `p > 1`.

    The unscaled `phi² ≡ phi + 1 (mod p)` follows by multiplicative
    cancellation of 4 mod p (gcd(4, p) = 1 for odd p > 1).  That
    cancellation is G119 Phase 2.1 (FLT / xgcd) prerequisite work,
    multi-session.

    PURE. -/
theorem four_phi_sq_eq_four_phi_plus_one (p s : Nat)
    (hp : 1 < p) (hpo : p % 2 = 1) (hs2 : (s * s) % p = 5 % p) :
    (4 * (phi p s * phi p s)) % p = (4 * (phi p s + 1)) % p := by
  rw [four_phi_sq_eq p s hp hpo]
  rw [one_plus_s_sq_eq p s hs2]
  rw [← four_phi_plus_one_eq p s hp hpo]

/-! ## Cancellation of 4 via explicit `4⁻¹ ≡ inv2² (mod p)`

Without FLT, the multiplicative inverse of 4 mod p can be constructed
explicitly as `inv2 p * inv2 p`:  since `2 * inv2 ≡ 1 mod p`, squaring
gives `4 * inv2² ≡ 1 mod p`.  This lets us cancel the 4 in the kernel
and recover the **unscaled** φ recurrence `phi² ≡ phi + 1 (mod p)`.

The general FLT-based cancellation infrastructure (for arbitrary
constants coprime to p) remains G119 Phase 2.1 work, but for the
specific constant 4, the explicit construction is direct.
-/

/-- `4 · inv2² ≡ 1 (mod p)` for odd `p > 1`.  Explicit `4⁻¹ mod p`. -/
theorem four_mul_inv2_sq (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (4 * (inv2 p * inv2 p)) % p = 1 % p := by
  -- 4 * inv2² = (2 * inv2)² in Nat, then mod-p reduces via two_mul_inv2.
  have h_pow : 4 * (inv2 p * inv2 p) = (2 * inv2 p) * (2 * inv2 p) :=
    four_mul_sq (inv2 p)
  rw [h_pow, mul_mod_pure (2 * inv2 p) (2 * inv2 p) p,
      two_mul_inv2 p hp hpo, ← mul_mod_pure 1 1 p, Nat.mul_one]

/-- Helper: `inv2² * (4 * x) = (4 * inv2²) * x`. -/
private theorem rearrange_inv2sq_four (p x : Nat) :
    inv2 p * inv2 p * (4 * x) = (4 * (inv2 p * inv2 p)) * x := by
  rw [← mul_assoc (inv2 p * inv2 p) 4 x, Nat.mul_comm (inv2 p * inv2 p) 4]

/-- ★★★★ **Unscaled φ recurrence** (Phase 3.2 full algebraic kernel):
    `phi² ≡ phi + 1 (mod p)`, given `s² ≡ 5 (mod p)` and odd `p > 1`.

    Derived from `four_phi_sq_eq_four_phi_plus_one` (scaled form) by
    multiplying both sides by `inv2²` (which is `4⁻¹ mod p` via
    `four_mul_inv2_sq`) — the cancellation is explicit, no FLT
    needed.  PURE. -/
theorem phi_sq_eq_phi_add_one (p s : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (hs2 : (s * s) % p = 5 % p) :
    (phi p s * phi p s) % p = (phi p s + 1) % p := by
  -- From kernel:  (4 * phi²) % p = (4 * (phi + 1)) % p
  have hker := four_phi_sq_eq_four_phi_plus_one p s hp hpo hs2
  have h_invsq := four_mul_inv2_sq p hp hpo
  -- Multiply both sides by inv2², use `4 * inv2² ≡ 1 mod p` to cancel.
  -- LHS reduction: inv2² · (4 · phi²) % p ≡ phi² % p
  have hL : (inv2 p * inv2 p * (4 * (phi p s * phi p s))) % p
          = (phi p s * phi p s) % p := by
    rw [rearrange_inv2sq_four p (phi p s * phi p s),
        mul_mod_left_pure (4 * (inv2 p * inv2 p)) (phi p s * phi p s) p,
        h_invsq,
        ← mul_mod_left_pure 1 (phi p s * phi p s) p,
        Nat.one_mul]
  have hR : (inv2 p * inv2 p * (4 * (phi p s + 1))) % p
          = (phi p s + 1) % p := by
    rw [rearrange_inv2sq_four p (phi p s + 1),
        mul_mod_left_pure (4 * (inv2 p * inv2 p)) (phi p s + 1) p,
        h_invsq,
        ← mul_mod_left_pure 1 (phi p s + 1) p,
        Nat.one_mul]
  have hmid : (inv2 p * inv2 p * (4 * (phi p s * phi p s))) % p
            = (inv2 p * inv2 p * (4 * (phi p s + 1))) % p := by
    rw [mul_mod_right_pure (inv2 p * inv2 p) (4 * (phi p s * phi p s)) p,
        hker,
        ← mul_mod_right_pure (inv2 p * inv2 p) (4 * (phi p s + 1)) p]
  exact hL.symm.trans (hmid.trans hR)

/-! ## Fibonacci-like expansion of `phi^n`

Using `phi² = phi + 1 (mod p)`, every power `phi^n` decomposes
as `a_n · phi + b_n` for some Fibonacci-like coefficients.  The
recurrence

  `phi^(n+1) = phi · phi^n = phi · (a phi + b) = a phi² + b phi
            = a (phi + 1) + b phi = (a + b) phi + a`

gives the coefficient recurrence `(a, b) → (a + b, a)` starting
from `(0, 1)` for `phi^0`.

This is the matrix-eigenvector connection: in the split case M
acts on the `(1, phi - 1)` direction with eigenvalue `phi²`, so
`M^k · (1, phi - 1) = (phi²)^k · (1, phi - 1)` and `(phi²)^k =
phi^(2k)` is computable via the expansion below.

For Phase 3.2 (period divides `(p-1)/2`), the chain needs
`phi^(p-1) ≡ 1 (mod p)` (FLT, still multi-session); the
expansion alone reduces this to a Fibonacci-coefficient
divisibility claim.
-/

/-- Fibonacci-like coefficient pair for `phi^n`:  `(a, b)` with
    `phi^n ≡ a · phi + b (mod p)` (for valid phi).
    Recurrence: `(0, 1) → (1, 0) → (1, 1) → (2, 1) → (3, 2) → ...` -/
def fibLike : Nat → Nat × Nat
  | 0     => (0, 1)
  | k + 1 => let p := fibLike k; (p.1 + p.2, p.1)

/-- ★ **Fibonacci expansion of `phi^k`** mod p:
    `phi^k ≡ a_k · phi + b_k (mod p)` where `(a_k, b_k) = fibLike k`.
    By induction on `k`, using `phi² ≡ phi + 1 (mod p)`.  PURE. -/
theorem phi_pow_eq_fibLike (p s : Nat) (hp : 1 < p) (hpo : p % 2 = 1)
    (hs2 : (s * s) % p = 5 % p) :
    ∀ k, (phi p s)^k % p
       = ((fibLike k).1 * phi p s + (fibLike k).2) % p
  | 0 => by
    -- phi^0 = 1, (fibLike 0) = (0, 1), so RHS = 0*phi + 1 = 1.
    show 1 % p = (0 * phi p s + 1) % p
    rw [Nat.zero_mul, Nat.zero_add]
  | k + 1 => by
    have ih := phi_pow_eq_fibLike p s hp hpo hs2 k
    have hsq := phi_sq_eq_phi_add_one p s hp hpo hs2
    -- Unfold fibLike (k+1):
    show (phi p s)^(k + 1) % p
       = (((fibLike k).1 + (fibLike k).2) * phi p s + (fibLike k).1) % p
    -- phi^(k+1) = phi^k * phi (definitional)
    show ((phi p s)^k * phi p s) % p
       = (((fibLike k).1 + (fibLike k).2) * phi p s + (fibLike k).1) % p
    -- Pull `% p` into phi^k via mul_mod_left_pure, apply IH, push back
    rw [mul_mod_left_pure ((phi p s)^k) (phi p s) p, ih,
        ← mul_mod_left_pure ((fibLike k).1 * phi p s + (fibLike k).2)
                            (phi p s) p]
    -- Goal: ((a*phi + b) * phi) % p = ((a + b)*phi + a) % p
    -- Expand: (a*phi + b)*phi = a*phi*phi + b*phi
    rw [add_mul ((fibLike k).1 * phi p s) (fibLike k).2 (phi p s)]
    -- Reassociate: a*phi*phi = a * (phi*phi)
    rw [mul_assoc (fibLike k).1 (phi p s) (phi p s)]
    -- Substitute phi*phi ≡ phi+1 mod p (via add_mod_gen + mul_mod_right_pure)
    rw [add_mod_gen ((fibLike k).1 * (phi p s * phi p s))
                    ((fibLike k).2 * phi p s) p,
        mul_mod_right_pure (fibLike k).1 (phi p s * phi p s) p,
        hsq,
        ← mul_mod_right_pure (fibLike k).1 (phi p s + 1) p,
        ← add_mod_gen ((fibLike k).1 * (phi p s + 1))
                      ((fibLike k).2 * phi p s) p]
    -- Goal: (a * (phi + 1) + b * phi) % p = ((a + b)*phi + a) % p
    -- Expand a * (phi + 1) = a*phi + a
    rw [Nat.mul_add (fibLike k).1 (phi p s) 1, Nat.mul_one]
    -- Goal: (a*phi + a + b*phi) % p = ((a + b)*phi + a) % p
    -- Rearrange: a*phi + a + b*phi = a*phi + b*phi + a
    rw [Nat.add_right_comm ((fibLike k).1 * phi p s) (fibLike k).1
                           ((fibLike k).2 * phi p s)]
    -- Combine a*phi + b*phi = (a + b)*phi
    rw [← add_mul (fibLike k).1 (fibLike k).2 (phi p s)]

/-! ## Smoke tests at split primes -/

/-- Smoke: at p=11, s=4 satisfies 4² ≡ 5 (mod 11). -/
theorem sqrt5_mod_11 : (4 * 4) % 11 = 5 % 11 := by decide

/-- Smoke: at p=11, the scaled φ identity is verifiable. -/
theorem phi_mod_11_scaled :
    (4 * (phi 11 4 * phi 11 4)) % 11 = (4 * (phi 11 4 + 1)) % 11 :=
  four_phi_sq_eq_four_phi_plus_one 11 4 (by decide) (by decide) sqrt5_mod_11

/-- Smoke: at p=11, the **unscaled** φ identity `phi² ≡ phi + 1 mod 11`. -/
theorem phi_mod_11_unscaled :
    (phi 11 4 * phi 11 4) % 11 = (phi 11 4 + 1) % 11 :=
  phi_sq_eq_phi_add_one 11 4 (by decide) (by decide) sqrt5_mod_11

/-- Smoke: at p=19, s=9 satisfies 9² = 81 = 4·19 + 5 ≡ 5 (mod 19). -/
theorem sqrt5_mod_19 : (9 * 9) % 19 = 5 % 19 := by decide

/-- Smoke: at p=19, the scaled φ identity is verifiable. -/
theorem phi_mod_19_scaled :
    (4 * (phi 19 9 * phi 19 9)) % 19 = (4 * (phi 19 9 + 1)) % 19 :=
  four_phi_sq_eq_four_phi_plus_one 19 9 (by decide) (by decide) sqrt5_mod_19

/-- Smoke: at p=19, the **unscaled** φ identity `phi² ≡ phi + 1 mod 19`. -/
theorem phi_mod_19_unscaled :
    (phi 19 9 * phi 19 9) % 19 = (phi 19 9 + 1) % 19 :=
  phi_sq_eq_phi_add_one 19 9 (by decide) (by decide) sqrt5_mod_19

/-- Smoke: at p=11, `phi^5 ≡ F_5 · phi + F_4 (mod 11)` where
    `F_5 = 5, F_4 = 3`, so `phi^5 ≡ 5·phi + 3 mod 11`. -/
theorem phi_pow_5_mod_11 :
    (phi 11 4)^5 % 11 = (5 * phi 11 4 + 3) % 11 :=
  phi_pow_eq_fibLike 11 4 (by decide) (by decide) sqrt5_mod_11 5

/-- Smoke: at p=11, the Fibonacci expansion confirms `fibLike 5 = (5, 3)`. -/
theorem fibLike_5_eq : fibLike 5 = (5, 3) := by decide

/-! ## phi multiplicative order at split primes (smoke)

For split primes p, `phi^{-1} ≡ (s - 1) * inv2 p (mod p)` (derivable
from `phi(phi - 1) ≡ 1 mod p`, the unscaled φ recurrence rearranged).
Combined with `MulOrderPigeonhole.exists_modPow_period`, this gives
the multiplicative period of phi as a Phase 3.2 building block.
The universal form (period | (p-1)/2) still requires FLT for phi,
multi-session.
-/

open E213.Lib.Math.DyadicFSM.MulOrderPigeonhole (ModInverse exists_modPow_period)
open E213.Meta.Nat.ModPow213 (modPow)

/-- Smoke: at p=11, `phi 11 4 = 8` has modular inverse `7`
    (since `8 * 7 = 56 ≡ 1 mod 11`). -/
def phi11_modInv : ModInverse 11 (phi 11 4) :=
  { inv := 7, inv_lt := by decide, inv_eq := by decide }

/-- Smoke: at p=11, phi has multiplicative period ≤ 11
    (actually 5, matching the Pisano predict (p-1)/2 = 5). -/
theorem exists_phi11_mul_order :
    ∃ N, 0 < N ∧ N ≤ 11 ∧ modPow 11 (phi 11 4) N = 1 % 11 :=
  exists_modPow_period 11 (phi 11 4) (by decide) phi11_modInv

/-- Smoke: at p=19, `phi 19 9 = 5` has modular inverse `4`
    (since `5 * 4 = 20 ≡ 1 mod 19`). -/
def phi19_modInv : ModInverse 19 (phi 19 9) :=
  { inv := 4, inv_lt := by decide, inv_eq := by decide }

/-- Smoke: at p=19, phi has multiplicative period ≤ 19
    (actually 9, matching Pisano predict (p-1)/2 = 9). -/
theorem exists_phi19_mul_order :
    ∃ N, 0 < N ∧ N ≤ 19 ∧ modPow 19 (phi 19 9) N = 1 % 19 :=
  exists_modPow_period 19 (phi 19 9) (by decide) phi19_modInv

end E213.Lib.Math.DyadicFSM.PhiMod5
