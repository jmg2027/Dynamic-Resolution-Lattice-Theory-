import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.DyadicFSM.PhiMod5
import E213.Lib.Math.ModArith.ModBezoutInvariant
/-!
# 𝔽_{p²} = 𝔽_p[x] / (x² - 5) — universal foundation for Phase 3.3 (inert case)

When 5 is NQR mod p (inert case), √5 ∉ 𝔽_p but √5 ∈ 𝔽_{p²}.
We construct 𝔽_{p²} as ordered pairs `(a, b)` representing
`a + b·√5`, with multiplication

  `(a + b√5)(c + d√5) = (ac + 5bd) + (ad + bc)·√5`.

Universal infrastructure (no specific primes hard-coded):

  · `FP2 := Nat × Nat` — representation as (a, b)
  · `fp2Add`, `fp2Mul` — ring operations mod p
  · `fp2Sub` — subtraction via additive inverse mod p
  · `fp2Zero`, `fp2One`, `fp2OfNat` — embeddings
  · `fp2Frob` — Frobenius `(a, b) ↦ (a, -b)` (sends √5 ↦ -√5)
  · `fp2Norm` — `Norm(a + b√5) = a² - 5b²` mod p
  · `fp2Pow` — recursive power

All declarations PURE.  This is Mathlib-level field-extension
infrastructure, 213-native.
-/

namespace E213.Lib.Math.ModArith.FP2Sqrt5

open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod mod_self zero_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Tactic.NatHelper (mul_assoc sub_add_cancel add_sub_cancel_right add_mul)
open E213.Lib.Math.DyadicFSM.FLT.ChoosePrime (mul_p_mod_eq_zero)
open E213.Lib.Math.DyadicFSM.PhiMod5 (inv2 four_mul_inv2_sq)

/-- 𝔽_{p²} element representation: `(a, b)` for `a + b·√5`. -/
abbrev FP2 : Type := Nat × Nat

/-- Zero element `0 + 0·√5`. -/
def fp2Zero : FP2 := (0, 0)

/-- Unit element `1 + 0·√5`. -/
def fp2One (p : Nat) : FP2 := (1 % p, 0)

/-- Scalar embedding: `n ↦ n + 0·√5 = (n % p, 0)`. -/
def fp2OfNat (p n : Nat) : FP2 := (n % p, 0)

/-- Addition: `(a + b√5) + (c + d√5) = (a + c) + (b + d)√5`. -/
def fp2Add (p : Nat) (x y : FP2) : FP2 :=
  ((x.1 + y.1) % p, (x.2 + y.2) % p)

/-- Subtraction via Nat: `(a + b√5) - (c + d√5) = (a - c) + (b - d)√5`
    using additive inverse mod p (`p - z % p mod p`). -/
def fp2Sub (p : Nat) (x y : FP2) : FP2 :=
  ((x.1 + (p - y.1 % p)) % p, (x.2 + (p - y.2 % p)) % p)

/-- Multiplication: `(a + b√5)(c + d√5) = (ac + 5bd) + (ad + bc)√5`. -/
def fp2Mul (p : Nat) (x y : FP2) : FP2 :=
  ((x.1 * y.1 + 5 * x.2 * y.2) % p,
   (x.1 * y.2 + x.2 * y.1) % p)

/-- Frobenius automorphism: `σ(a + b√5) = a - b·√5 = (a, -b)` in F_p.
    Sends `√5 ↦ -√5`. -/
def fp2Frob (p : Nat) (x : FP2) : FP2 :=
  (x.1 % p, (p - x.2 % p) % p)

/-- Norm: `Norm(a + b√5) = (a + b√5)(a - b√5) = a² - 5·b²`, mod p.
    PURE — uses Nat-style additive subtraction. -/
def fp2Norm (p : Nat) (x : FP2) : Nat :=
  let asq := (x.1 * x.1) % p
  let bsq5 := (5 * x.2 * x.2) % p
  (asq + (p - bsq5)) % p

/-- Recursive power: `x^n` in `FP2`. -/
def fp2Pow (p : Nat) (x : FP2) : Nat → FP2
  | 0 => fp2One p
  | n + 1 => fp2Mul p (fp2Pow p x n) x

/-! ## Basic identities (definitional / smoke) -/

theorem fp2Zero_def : fp2Zero = (0, 0) := rfl

theorem fp2One_def (p : Nat) : fp2One p = (1 % p, 0) := rfl

/-- Smoke: at p=3 (where 5 is NQR), 1 ≡ 1 mod 3. -/
theorem fp2One_3 : fp2One 3 = (1, 0) := by decide

/-- Smoke: at p=7 (where 5 is NQR), addition of `(2 + 3√5)` and `(4 + 1√5)`
    gives `(6 + 4√5)` mod 7 = `(6, 4)`. -/
theorem fp2Add_3_7 : fp2Add 7 (2, 3) (4, 1) = (6, 4) := by decide

/-- Smoke: multiplication `(2 + 3√5)(4 + 1√5)` at p=7.
    = `(2·4 + 5·3·1) + (2·1 + 3·4)·√5 = (8 + 15) + (2 + 12)·√5 = 23 + 14·√5`.
    Mod 7: `(23 % 7, 14 % 7) = (2, 0)`. -/
theorem fp2Mul_smoke_7 : fp2Mul 7 (2, 3) (4, 1) = (2, 0) := by decide

/-- Smoke: Frobenius of `(2, 3)` at p=7 is `(2, 4)` (since `7 - 3 = 4`). -/
theorem fp2Frob_smoke_7 : fp2Frob 7 (2, 3) = (2, 4) := by decide

/-- Smoke: norm of `(2, 3)` at p=7.
    Norm = `2² - 5·3² = 4 - 45 = -41 ≡ -41 + 7·6 = 1 mod 7`. -/
theorem fp2Norm_smoke_7 : fp2Norm 7 (2, 3) = 1 := by decide

/-- Smoke: pow at p=7, x=(2, 3), n=2.
    `(2 + 3√5)² = 4 + 12√5 + 9·5 = 49 + 12√5 = (49 % 7, 12 % 7) = (0, 5)`. -/
theorem fp2Pow_2_smoke_7 : fp2Pow 7 (2, 3) 2 = (0, 5) := by decide

/-! ## Frobenius algebraic properties

These are the universal properties making Phase 3.3 work:
  · σ ∘ σ = id (Frobenius is an involution).
  · σ(x · y) = σ(x) · σ(y) (ring homomorphism).
  · σ(x + y) = σ(x) + σ(y).
  · `x · σ(x) = norm(x)` as scalar.
-/

/-- `(p - (p - x % p) % p) % p = x % p` — double negation in mod p, for `0 < p`.
    PURE helper for the Frobenius involution. -/
private theorem double_neg_mod (p x : Nat) (hp : 0 < p) :
    (p - (p - x % p) % p) % p = x % p := by
  -- x % p < p, so p - x%p ∈ [1, p] (= p if x%p = 0).
  -- Case x % p = 0: p - 0 = p, p % p = 0, p - 0 = p, p % p = 0. So both = 0 ✓
  -- Case x % p > 0: p - x%p ∈ (0, p), so (p - x%p) % p = p - x%p.
  --                Then p - (p - x%p) = x%p ∈ (0, p), so the outer % p = x%p.
  have hr_lt : x % p < p := Nat.mod_lt _ hp
  have hr_le : x % p ≤ p := Nat.le_of_lt hr_lt
  -- (p - x%p) ≤ p (always, since x%p ≥ 0).
  have h_psub_le : p - x % p ≤ p := Nat.sub_le _ _
  -- Split by whether x % p = 0
  by_cases h0 : x % p = 0
  · -- x % p = 0: (p - 0) = p, p % p = 0, p - 0 = p, p % p = 0. So 0 = 0 ✓
    rw [h0]
    show (p - (p - 0) % p) % p = 0
    rw [Nat.sub_zero, mod_self, Nat.sub_zero, mod_self]
  · -- x % p > 0: p - x%p ∈ [1, p), so (p - x%p) % p = p - x%p.
    have h0_pos : 0 < x % p := Nat.pos_of_ne_zero h0
    have hpsub_lt : p - x % p < p := Nat.sub_lt hp h0_pos
    rw [Nat.mod_eq_of_lt hpsub_lt]
    -- Goal: (p - (p - x%p)) % p = x % p
    -- p - (p - r) = r (when r ≤ p, sub_sub_self)
    rw [E213.Tactic.NatHelper.sub_sub_self hr_le]
    rw [Nat.mod_eq_of_lt hr_lt]

/-- ★ **Frobenius is an involution**: `σ(σ(x)) = (x.1 % p, x.2 % p)` (mod-p
    representative of x).  For x already in canonical form `(a < p, b < p)`,
    σ ∘ σ is identity. -/
theorem fp2Frob_involution (p : Nat) (hp : 0 < p) (x : FP2) :
    fp2Frob p (fp2Frob p x) = (x.1 % p, x.2 % p) := by
  -- fp2Frob p x = (x.1 % p, (p - x.2 % p) % p)
  -- fp2Frob p (fp2Frob p x) = ((x.1 % p) % p, (p - ((p - x.2 % p) % p) % p) % p)
  --                        = (x.1 % p, double_neg_mod (x.2))
  show ((x.1 % p) % p, (p - (p - x.2 % p) % p % p) % p) = (x.1 % p, x.2 % p)
  congr 1
  · exact mod_mod x.1 p
  · -- (p - (p - x.2 % p) % p % p) % p = x.2 % p
    rw [mod_mod]
    exact double_neg_mod p x.2 hp

/-- Smoke: at p=7, σ(σ((2, 3))) = (2, 3) (canonical form). -/
theorem fp2Frob_involution_smoke_7 :
    fp2Frob 7 (fp2Frob 7 (2, 3)) = (2, 3) := by decide

/-! ## φ, ψ in 𝔽_{p²} (for the inert case)

In the inert case (5 NQR mod p), √5 ∉ 𝔽_p but √5 ∈ 𝔽_{p²}.
So φ = (1 + √5)/2 = `inv2 · 1 + inv2 · √5` lives naturally in 𝔽_{p²}.

  · `phiFP2 p` = `(inv2 p, inv2 p)` representing `inv2 + inv2·√5 = (1+√5)/2 = φ`
  · `psiFP2 p` = `(inv2 p, p - inv2 p mod p)` representing `(1-√5)/2 = ψ = σ(φ)`

Key relation (smoke per prime in next session): `phiFP2 · psiFP2 = (-1, 0)`,
i.e., `φ · ψ = -1` in 𝔽_{p²}.
-/

open E213.Lib.Math.DyadicFSM.PhiMod5 (inv2) in
/-- φ in 𝔽_{p²}: `(1 + √5)/2 = inv2 · 1 + inv2 · √5 = (inv2 p, inv2 p)`. -/
def phiFP2 (p : Nat) : FP2 := (inv2 p, inv2 p)

open E213.Lib.Math.DyadicFSM.PhiMod5 (inv2) in
/-- ψ in 𝔽_{p²}: `(1 - √5)/2 = σ(φ)`. -/
def psiFP2 (p : Nat) : FP2 := (inv2 p, (p - inv2 p % p) % p)

/-- Smoke at p=3: `inv2 3 = 2`, so phi = (2, 2), psi = (2, 1). -/
theorem phiFP2_3 : phiFP2 3 = (2, 2) := by decide

theorem psiFP2_3 : psiFP2 3 = (2, 1) := by decide

/-- Smoke: ψ = σ(φ) at p=3.  PURE. -/
theorem psi_eq_frob_phi_3 : psiFP2 3 = fp2Frob 3 (phiFP2 3) := by decide

/-- Smoke at p=7 (5 NQR mod 7, inert): `inv2 7 = 4`, phi = (4, 4), psi = (4, 3). -/
theorem phiFP2_7 : phiFP2 7 = (4, 4) := by decide

theorem psiFP2_7 : psiFP2 7 = (4, 3) := by decide

theorem psi_eq_frob_phi_7 : psiFP2 7 = fp2Frob 7 (phiFP2 7) := by decide

/-- ★ **Key Phase 3.3 identity (smoke)**: `phi · psi = -1` in 𝔽_{p²}.
    At p=3: phi·psi = (2, 2)·(2, 1) = (2·2 + 5·2·1, 2·1 + 2·2) = (4+10, 2+4)
                  = (14, 6).  Mod 3: (14 % 3, 6 % 3) = (2, 0) = (-1, 0). ✓ -/
theorem phi_psi_eq_neg_one_3 : fp2Mul 3 (phiFP2 3) (psiFP2 3) = (2, 0) := by decide

/-- At p=7: phi·psi = (4, 4)·(4, 3) = (4·4 + 5·4·3, 4·3 + 4·4) = (16+60, 12+16)
            = (76, 28).  Mod 7: (76 % 7, 28 % 7) = (6, 0) = (-1, 0). ✓ -/
theorem phi_psi_eq_neg_one_7 : fp2Mul 7 (phiFP2 7) (psiFP2 7) = (6, 0) := by decide

/-! ## φ² recurrence in 𝔽_{p²} (smoke)

In any 𝔽 containing √5, `φ² = φ + 1`. This holds in 𝔽_{p²}.
-/

/-- At p=3: φ² = (2, 2)² = (2·2 + 5·2·2, 2·2 + 2·2) = (4+20, 8) = (24, 8).
    Mod 3: (0, 2). And φ + 1 = (2+1, 2) = (3, 2). Mod 3: (0, 2). ✓ -/
theorem phi_sq_eq_phi_plus_one_3 :
    fp2Pow 3 (phiFP2 3) 2 = fp2Add 3 (phiFP2 3) (fp2One 3) := by decide

/-- At p=7: similar. -/
theorem phi_sq_eq_phi_plus_one_7 :
    fp2Pow 7 (phiFP2 7) 2 = fp2Add 7 (phiFP2 7) (fp2One 7) := by decide

/-! ## Universal ring properties

Universal (for all p : Nat) theorems that don't depend on specific primes.
These are the algebraic identities making 𝔽_{p²} a commutative ring.
-/

/-- ★ **Addition is commutative** (universal): `x + y = y + x` in 𝔽_{p²}.  PURE. -/
theorem fp2Add_comm (p : Nat) (x y : FP2) :
    fp2Add p x y = fp2Add p y x := by
  show ((x.1 + y.1) % p, (x.2 + y.2) % p) = ((y.1 + x.1) % p, (y.2 + x.2) % p)
  apply Prod.ext
  · show (x.1 + y.1) % p = (y.1 + x.1) % p
    rw [Nat.add_comm x.1 y.1]
  · show (x.2 + y.2) % p = (y.2 + x.2) % p
    rw [Nat.add_comm x.2 y.2]

/-- ★ **Multiplication is commutative** (universal): `x · y = y · x` in 𝔽_{p²}.  PURE. -/
theorem fp2Mul_comm (p : Nat) (x y : FP2) :
    fp2Mul p x y = fp2Mul p y x := by
  show ((x.1 * y.1 + 5 * x.2 * y.2) % p, (x.1 * y.2 + x.2 * y.1) % p)
     = ((y.1 * x.1 + 5 * y.2 * x.2) % p, (y.1 * x.2 + y.2 * x.1) % p)
  apply Prod.ext
  · show (x.1 * y.1 + 5 * x.2 * y.2) % p = (y.1 * x.1 + 5 * y.2 * x.2) % p
    rw [Nat.mul_comm x.1 y.1, mul_assoc 5 x.2 y.2,
        Nat.mul_comm x.2 y.2, ← mul_assoc 5 y.2 x.2]
  · show (x.1 * y.2 + x.2 * y.1) % p = (y.1 * x.2 + y.2 * x.1) % p
    rw [Nat.mul_comm x.1 y.2, Nat.mul_comm x.2 y.1,
        Nat.add_comm (y.2 * x.1) (y.1 * x.2)]

/-- ★ **Frobenius preserves zero** (universal): `σ(0) = 0` in 𝔽_{p²}.  PURE. -/
theorem fp2Frob_zero (p : Nat) (hp : 0 < p) :
    fp2Frob p fp2Zero = fp2Zero := by
  show (0 % p, (p - 0 % p) % p) = (0, 0)
  apply Prod.ext
  · show 0 % p = 0; rfl
  · show (p - 0 % p) % p = 0
    show (p - 0) % p = 0
    rw [Nat.sub_zero, mod_self]

/-- ★ **Frobenius preserves one** (universal, for `1 < p`):
    `σ(1) = 1` in 𝔽_{p²}.  PURE. -/
theorem fp2Frob_one (p : Nat) (hp : 1 < p) :
    fp2Frob p (fp2One p) = fp2One p := by
  show ((1 % p) % p, (p - 0 % p) % p) = (1 % p, 0)
  apply Prod.ext
  · show (1 % p) % p = 1 % p
    exact mod_mod 1 p
  · show (p - 0 % p) % p = 0
    show (p - 0) % p = 0
    rw [Nat.sub_zero, mod_self]

/-- σ canonicalizes the second component twice (idempotent under canonical form). -/
theorem fp2Frob_canonical (p : Nat) (hp : 0 < p) (x : FP2)
    (hx1 : x.1 < p) (hx2 : x.2 < p) :
    fp2Frob p (fp2Frob p x) = x := by
  rw [fp2Frob_involution p hp]
  -- Goal: (x.1 % p, x.2 % p) = x
  apply Prod.ext
  · show x.1 % p = x.1; exact Nat.mod_eq_of_lt hx1
  · show x.2 % p = x.2; exact Nat.mod_eq_of_lt hx2

/-- ★ **fp2Add zero left**: `0 + x = canonical(x)` (universal). -/
theorem fp2Add_zero_left (p : Nat) (x : FP2) :
    fp2Add p fp2Zero x = (x.1 % p, x.2 % p) := by
  show ((0 + x.1) % p, (0 + x.2) % p) = (x.1 % p, x.2 % p)
  rw [Nat.zero_add, Nat.zero_add]

/-- ★ **fp2Mul one left** (universal, for `1 ≤ p`):
    `1 · x` simplifies to `(x.1 mod p, x.2 mod p)`. -/
theorem fp2Mul_one_left (p : Nat) (hp : 1 ≤ p) (x : FP2) :
    fp2Mul p (fp2One p) x = (x.1 % p, x.2 % p) := by
  show ((1 % p * x.1 + 5 * 0 * x.2) % p, (1 % p * x.2 + 0 * x.1) % p)
     = (x.1 % p, x.2 % p)
  apply Prod.ext
  · show (1 % p * x.1 + 5 * 0 * x.2) % p = x.1 % p
    rw [Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
    -- Goal: (1 % p * x.1) % p = x.1 % p
    rw [← mul_mod_left_pure 1 x.1 p, Nat.one_mul]
  · show (1 % p * x.2 + 0 * x.1) % p = x.2 % p
    rw [Nat.zero_mul, Nat.add_zero]
    rw [← mul_mod_left_pure 1 x.2 p, Nat.one_mul]

/-- ★ **fp2Mul zero left**: `0 · x = (0, 0)` (universal). -/
theorem fp2Mul_zero_left (p : Nat) (x : FP2) :
    fp2Mul p fp2Zero x = (0, 0) := by
  show ((0 * x.1 + 5 * 0 * x.2) % p, (0 * x.2 + 0 * x.1) % p) = (0, 0)
  apply Prod.ext
  · show (0 * x.1 + 5 * 0 * x.2) % p = 0
    rw [Nat.zero_mul, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
    rfl
  · show (0 * x.2 + 0 * x.1) % p = 0
    rw [Nat.zero_mul, Nat.zero_mul, Nat.add_zero]
    rfl

/-- ★ **fp2 power 0**: `x^0 = 1` (canonical). -/
theorem fp2Pow_zero (p : Nat) (x : FP2) : fp2Pow p x 0 = fp2One p := rfl

/-- ★ **fp2 power succ**: `x^(n+1) = x^n · x`. -/
theorem fp2Pow_succ (p : Nat) (x : FP2) (n : Nat) :
    fp2Pow p x (n + 1) = fp2Mul p (fp2Pow p x n) x := rfl

/-! ## Mod-p negation (foundation for Frobenius ring hom) -/

/-- ★ **Negation-addition identity**: `((p - r%p)%p + r) ≡ 0 (mod p)` (universal).
    The "additive inverse" property in mod-p arithmetic.  PURE. -/
theorem nmod_add_self_zero (p r : Nat) (hp : 0 < p) :
    ((p - r % p) % p + r) % p = 0 := by
  -- Combine via add_mod_gen, then case on r % p.
  rw [add_mod_gen ((p - r % p) % p) r p, mod_mod (p - r % p) p]
  -- Goal: ((p - r%p) % p + r % p) % p = 0
  by_cases h : r % p = 0
  · rw [h, Nat.sub_zero, mod_self, Nat.zero_add, zero_mod]
  · have hr_pos : 0 < r % p := Nat.pos_of_ne_zero h
    have hr_lt : r % p < p := Nat.mod_lt _ hp
    have hp_sub_lt : p - r % p < p := Nat.sub_lt hp hr_pos
    rw [Nat.mod_eq_of_lt hp_sub_lt]
    rw [sub_add_cancel (Nat.le_of_lt hr_lt)]
    exact mod_self p

/-- ★ **Negation is additive** in mod-p arithmetic (universal):
    `(p - (a + b) % p) % p = ((p - a%p) % p + (p - b%p) % p) % p`.

    Both equal `-(a + b) ≡ -a + -b (mod p)`.  Proven by showing both sides
    cancel `(a + b)` to 0 mod p, then applying `mod_cancel_right`. -/
theorem neg_mod_add (p a b : Nat) (hp : 0 < p) :
    (p - (a + b) % p) % p
      = ((p - a % p) % p + (p - b % p) % p) % p := by
  -- Show both sides are equal by showing both + (a+b) ≡ 0 mod p.
  -- Use mod_cancel_right from ModBezoutInvariant.
  -- Plan:
  --   LHS := (p - (a+b) % p) % p < p
  --   RHS := ((p - a%p) % p + (p - b%p) % p) % p < p
  --   (LHS + (a+b)) % p = 0 by nmod_add_self_zero
  --   (RHS + (a+b)) % p = 0 by reorder + nmod_add_self_zero (twice)
  --   So LHS + (a+b) ≡ RHS + (a+b) mod p, so LHS = RHS by mod_cancel_right.
  have hLHS_lt : (p - (a + b) % p) % p < p := Nat.mod_lt _ hp
  have hRHS_lt : ((p - a % p) % p + (p - b % p) % p) % p < p := Nat.mod_lt _ hp
  -- LHS + (a + b) ≡ 0 mod p
  have h_LHS_add : ((p - (a + b) % p) % p + (a + b)) % p = 0 :=
    nmod_add_self_zero p (a + b) hp
  -- For RHS + (a + b) ≡ 0:
  -- RHS = ((p - a%p) % p + (p - b%p) % p) % p
  -- RHS + (a+b) = (RHS + a + b) by Nat.add_assoc reverse
  -- Strategy: ((p - a%p)%p + (p - b%p)%p + (a + b)) % p
  --        = ((p - a%p)%p + (p - b%p)%p + a + b) % p     [add_assoc]
  --        = (((p - a%p)%p + a) + ((p - b%p)%p + b)) % p  [reorder]
  --        = ((((p - a%p)%p + a) % p) + (((p - b%p)%p + b) % p)) % p  [add_mod_gen]
  --        = (0 + 0) % p = 0
  -- But the outer ((RHS % p) form ...) needs careful handling.
  have h_RHS_add : (((p - a % p) % p + (p - b % p) % p) % p + (a + b)) % p = 0 := by
    -- First, drop outer mod via add_mod_gen
    rw [add_mod_gen (((p - a % p) % p + (p - b % p) % p) % p) (a + b) p]
    rw [mod_mod ((p - a % p) % p + (p - b % p) % p) p]
    rw [← add_mod_gen ((p - a % p) % p + (p - b % p) % p) (a + b) p]
    -- Goal: ((p - a%p)%p + (p - b%p)%p + (a + b)) % p = 0
    -- Rearrange: ... + a + b ≡ (... + a) + (... + b)
    rw [show (p - a % p) % p + (p - b % p) % p + (a + b)
          = ((p - a % p) % p + a) + ((p - b % p) % p + b) from by
        rw [Nat.add_assoc ((p - a % p) % p) ((p - b % p) % p) (a + b)]
        rw [← Nat.add_assoc ((p - b % p) % p) a b]
        rw [Nat.add_comm ((p - b % p) % p) a]
        rw [Nat.add_assoc a ((p - b % p) % p) b]
        rw [← Nat.add_assoc ((p - a % p) % p) a ((p - b % p) % p + b)]]
    -- Goal: (((p - a%p)%p + a) + ((p - b%p)%p + b)) % p = 0
    rw [add_mod_gen (((p - a % p) % p + a)) (((p - b % p) % p + b)) p]
    rw [nmod_add_self_zero p a hp, nmod_add_self_zero p b hp]
    rfl
  -- Both have the same value + (a+b) ≡ 0 mod p, so LHS = RHS by cancellation
  have h_eq : ((p - (a + b) % p) % p + (a + b)) % p
            = (((p - a % p) % p + (p - b % p) % p) % p + (a + b)) % p :=
    h_LHS_add.trans h_RHS_add.symm
  exact E213.Lib.Math.ModArith.ModBezoutInvariant.mod_cancel_right
    p _ _ (a + b) hp hLHS_lt hRHS_lt h_eq

/-! ## Frobenius is a ring homomorphism (additive part) -/

/-- ★ **Frobenius is additive** (universal): `σ(x + y) = σ(x) + σ(y)` in 𝔽_{p²}.
    PURE.  Reduces to `neg_mod_add` on the second component. -/
theorem fp2Frob_add (p : Nat) (hp : 0 < p) (x y : FP2) :
    fp2Frob p (fp2Add p x y) = fp2Add p (fp2Frob p x) (fp2Frob p y) := by
  show (((x.1 + y.1) % p) % p, (p - ((x.2 + y.2) % p) % p) % p)
     = ((x.1 % p + y.1 % p) % p,
        ((p - x.2 % p) % p + (p - y.2 % p) % p) % p)
  apply Prod.ext
  · -- ((x.1 + y.1) % p) % p = (x.1 % p + y.1 % p) % p
    show ((x.1 + y.1) % p) % p = (x.1 % p + y.1 % p) % p
    rw [mod_mod, add_mod_gen]
  · -- (p - ((x.2 + y.2) % p) % p) % p
    --   = ((p - x.2 % p) % p + (p - y.2 % p) % p) % p
    show (p - ((x.2 + y.2) % p) % p) % p
       = ((p - x.2 % p) % p + (p - y.2 % p) % p) % p
    rw [mod_mod]
    exact neg_mod_add p x.2 y.2 hp

/-- Smoke at p=7: σ((2, 3) + (4, 1)) = σ((6, 4)) = (6, 3)
    = (2, 4) + (4, 6) = σ((2, 3)) + σ((4, 1)). -/
theorem fp2Frob_add_smoke_7 :
    fp2Frob 7 (fp2Add 7 (2, 3) (4, 1))
      = fp2Add 7 (fp2Frob 7 (2, 3)) (fp2Frob 7 (4, 1)) := by decide

/-! ## Mod-p negation × multiplication (foundation for Frobenius mul-hom) -/

/-- **Negation × y identity** (universal): `((p - x%p)%p) * y + x*y ≡ 0 mod p`.
    Reduces via `Nat.add_mul` (factoring `y` out) to `nmod_add_self_zero`. -/
theorem mul_neg_add_self (p x y : Nat) (hp : 0 < p) :
    ((p - x % p) % p * y + x * y) % p = 0 := by
  rw [← add_mul]
  -- Goal: (((p - x%p) % p + x) * y) % p = 0
  rw [mul_mod_left_pure ((p - x % p) % p + x) y p]
  -- Goal: (((p - x%p) % p + x) % p * y) % p = 0
  rw [nmod_add_self_zero p x hp]
  rw [Nat.zero_mul]
  exact zero_mod p

/-- ★ **Negation × left** (universal): `(-x) * y ≡ -(x*y) (mod p)`, i.e.,
    `((p - x%p)%p * y) % p = (p - (x*y)%p) % p`.  PURE. -/
theorem neg_mod_mul_left (p x y : Nat) (hp : 0 < p) :
    ((p - x % p) % p * y) % p = (p - (x * y) % p) % p := by
  have hLHS_lt : ((p - x % p) % p * y) % p < p := Nat.mod_lt _ hp
  have hRHS_lt : (p - (x * y) % p) % p < p := Nat.mod_lt _ hp
  -- LHS + (x*y) ≡ 0 mod p via mul_neg_add_self after add_mod_gen unification
  have h_LHS_add : (((p - x % p) % p * y) % p + x * y) % p = 0 := by
    rw [add_mod_gen (((p - x % p) % p * y) % p) (x * y) p]
    rw [mod_mod ((p - x % p) % p * y) p]
    rw [← add_mod_gen ((p - x % p) % p * y) (x * y) p]
    exact mul_neg_add_self p x y hp
  -- RHS + (x*y) ≡ 0 mod p by nmod_add_self_zero
  have h_RHS_add : ((p - (x * y) % p) % p + x * y) % p = 0 :=
    nmod_add_self_zero p (x * y) hp
  exact E213.Lib.Math.ModArith.ModBezoutInvariant.mod_cancel_right
    p _ _ (x * y) hp hLHS_lt hRHS_lt
    (h_LHS_add.trans h_RHS_add.symm)

/-- ★ **Negation × right** (universal): `x * (-y) ≡ -(x*y) (mod p)`.  PURE. -/
theorem neg_mod_mul_right (p x y : Nat) (hp : 0 < p) :
    (x * ((p - y % p) % p)) % p = (p - (x * y) % p) % p := by
  rw [Nat.mul_comm x ((p - y % p) % p)]
  rw [Nat.mul_comm x y]
  exact neg_mod_mul_left p y x hp

/-- ★ **Double-negation × multiplication** (universal):
    `(-x) * (-y) ≡ (x*y) (mod p)`.  PURE.  Two applications of
    `neg_mod_mul_left`/`right` reduce to `double_neg_mod`. -/
theorem neg_mod_mul_neg (p x y : Nat) (hp : 0 < p) :
    (((p - x % p) % p) * ((p - y % p) % p)) % p = (x * y) % p := by
  rw [neg_mod_mul_left p x ((p - y % p) % p) hp]
  -- Goal: (p - (x * ((p - y%p)%p)) % p) % p = (x*y) % p
  rw [neg_mod_mul_right p x y hp]
  -- Goal: (p - ((p - (x*y) % p) % p)) % p = (x*y) % p
  exact double_neg_mod p (x * y) hp

/-! ## Frobenius is a ring homomorphism (multiplicative part) -/

/-- ★ **Frobenius is multiplicative** (universal): `σ(x · y) = σ(x) · σ(y)`
    in 𝔽_{p²}.  PURE.  The first component uses `neg_mod_mul_neg`
    (since `(-x.2)(-y.2) ≡ x.2·y.2 mod p`); the second component
    uses `neg_mod_mul_left/right + neg_mod_add`. -/
theorem fp2Frob_mul (p : Nat) (hp : 0 < p) (x y : FP2) :
    fp2Frob p (fp2Mul p x y) = fp2Mul p (fp2Frob p x) (fp2Frob p y) := by
  show (((x.1*y.1 + 5*x.2*y.2) % p) % p,
        (p - ((x.1*y.2 + x.2*y.1) % p) % p) % p)
     = ((x.1%p * (y.1%p) + 5 * ((p - x.2%p)%p) * ((p - y.2%p)%p)) % p,
        (x.1%p * ((p - y.2%p)%p) + ((p - x.2%p)%p) * (y.1%p)) % p)
  apply Prod.ext
  · -- First component
    show ((x.1*y.1 + 5*x.2*y.2) % p) % p
       = (x.1%p * (y.1%p) + 5 * ((p - x.2%p)%p) * ((p - y.2%p)%p)) % p
    rw [mod_mod]
    -- Break both sides via add_mod_gen
    rw [add_mod_gen (x.1 * y.1) (5 * x.2 * y.2) p]
    rw [add_mod_gen (x.1 % p * (y.1 % p))
                    (5 * ((p - x.2 % p) % p) * ((p - y.2 % p) % p)) p]
    congr 1
    congr 1
    · -- (x.1 * y.1) % p = (x.1 % p * (y.1 % p)) % p
      exact mul_mod_pure x.1 y.1 p
    · -- (5 * x.2 * y.2) % p = (5 * ((p - x.2%p)%p) * ((p - y.2%p)%p)) % p
      rw [mul_assoc 5 x.2 y.2]
      rw [mul_assoc 5 ((p - x.2 % p) % p) ((p - y.2 % p) % p)]
      rw [mul_mod_right_pure 5 (x.2 * y.2) p]
      rw [mul_mod_right_pure 5 (((p - x.2 % p) % p) * ((p - y.2 % p) % p)) p]
      rw [← neg_mod_mul_neg p x.2 y.2 hp]
  · -- Second component
    show (p - ((x.1*y.2 + x.2*y.1) % p) % p) % p
       = (x.1%p * ((p - y.2%p)%p) + ((p - x.2%p)%p) * (y.1%p)) % p
    rw [mod_mod]
    -- Goal: (p - (x.1*y.2 + x.2*y.1) % p) % p
    --     = (x.1%p * ((p - y.2%p)%p) + ((p - x.2%p)%p) * (y.1%p)) % p
    rw [add_mod_gen (x.1 % p * ((p - y.2 % p) % p))
                    (((p - x.2 % p) % p) * (y.1 % p)) p]
    -- RHS = ((x.1%p * ((p - y.2%p)%p)) % p
    --        + (((p - x.2%p)%p) * (y.1%p)) % p) % p
    rw [← mul_mod_left_pure x.1 ((p - y.2 % p) % p) p]
    rw [neg_mod_mul_right p x.1 y.2 hp]
    rw [← mul_mod_right_pure ((p - x.2 % p) % p) y.1 p]
    rw [neg_mod_mul_left p x.2 y.1 hp]
    -- Now: (p - (x.1*y.2 + x.2*y.1) % p) % p
    --    = ((p - (x.1*y.2) % p) % p + (p - (x.2*y.1) % p) % p) % p
    exact neg_mod_add p (x.1 * y.2) (x.2 * y.1) hp

/-- Smoke at p=7: σ((2, 3) · (4, 1)) = σ((2, 0)) = (2, 0)
                  = (2, 4) · (4, 6) = σ((2, 3)) · σ((4, 1)).
    Check (2, 4)*(4, 6) = (2*4 + 5*4*6, 2*6 + 4*4) = (8+120, 12+16)
                       = (128, 28).  Mod 7: (128 % 7, 28 % 7) = (2, 0). ✓ -/
theorem fp2Frob_mul_smoke_7 :
    fp2Frob 7 (fp2Mul 7 (2, 3) (4, 1))
      = fp2Mul 7 (fp2Frob 7 (2, 3)) (fp2Frob 7 (4, 1)) := by decide

/-! ## Norm via Frobenius: `x · σ(x) = (Norm(x), 0)`

The key universal identity tying multiplication, Frobenius, and norm
together.  Sets up the Phase 3.3 closure chain `(φ · σ(φ)) = (-1, 0)`.
-/

/-- Helper: `((p - z%p)%p + z%p) % p = 0` (mod-p reduction of
    `nmod_add_self_zero`).  PURE. -/
theorem nmod_self_mod_zero (p z : Nat) (hp : 0 < p) :
    ((p - z % p) % p + z % p) % p = 0 := by
  have h_eq : ((p - z % p) % p + z % p) % p = ((p - z % p) % p + z) % p := by
    rw [add_mod_gen ((p - z % p) % p) (z % p) p]
    rw [mod_mod z p]
    rw [← add_mod_gen ((p - z % p) % p) z p]
  rw [h_eq]
  exact nmod_add_self_zero p z hp

/-- ★ **`x · σ(x) = (Norm(x), 0)`** (universal, for `0 < p`):
    multiplication of `x` by its Frobenius conjugate yields a scalar
    in `𝔽_p ⊂ 𝔽_{p²}` equal to the norm.  PURE. -/
theorem fp2Mul_self_frob (p : Nat) (hp : 0 < p) (x : FP2) :
    fp2Mul p x (fp2Frob p x) = (fp2Norm p x, 0) := by
  show ((x.1 * (x.1 % p) + 5 * x.2 * ((p - x.2 % p) % p)) % p,
        (x.1 * ((p - x.2 % p) % p) + x.2 * (x.1 % p)) % p)
     = (((x.1 * x.1) % p + (p - (5 * x.2 * x.2) % p)) % p, 0)
  apply Prod.ext
  · -- First component:
    -- (x.1 * (x.1 % p) + 5 * x.2 * ((p - x.2 % p) % p)) % p
    --   = ((x.1 * x.1) % p + (p - (5 * x.2 * x.2) % p)) % p
    show (x.1 * (x.1 % p) + 5 * x.2 * ((p - x.2 % p) % p)) % p
       = ((x.1 * x.1) % p + (p - (5 * x.2 * x.2) % p)) % p
    rw [add_mod_gen (x.1 * (x.1 % p)) (5 * x.2 * ((p - x.2 % p) % p)) p]
    rw [add_mod_gen ((x.1 * x.1) % p) (p - (5 * x.2 * x.2) % p) p]
    rw [mod_mod (x.1 * x.1) p]
    congr 1
    congr 1
    · -- (x.1 * (x.1 % p)) % p = (x.1 * x.1) % p
      exact (mul_mod_right_pure x.1 x.1 p).symm
    · -- (5 * x.2 * ((p - x.2 % p) % p)) % p = (p - (5 * x.2 * x.2) % p) % p
      exact neg_mod_mul_right p (5 * x.2) x.2 hp
  · -- Second component:
    -- (x.1 * ((p - x.2 % p) % p) + x.2 * (x.1 % p)) % p = 0
    show (x.1 * ((p - x.2 % p) % p) + x.2 * (x.1 % p)) % p = 0
    rw [add_mod_gen (x.1 * ((p - x.2 % p) % p)) (x.2 * (x.1 % p)) p]
    rw [neg_mod_mul_right p x.1 x.2 hp]
    rw [← mul_mod_right_pure x.2 x.1 p]
    rw [Nat.mul_comm x.2 x.1]
    -- Goal: ((p - (x.1*x.2) % p) % p + (x.1*x.2) % p) % p = 0
    exact nmod_self_mod_zero p (x.1 * x.2) hp

/-- Smoke at p=7: `(2, 3) · σ((2, 3)) = (2, 3) · (2, 4) = (Norm((2, 3)), 0)`.
    Norm((2, 3)) at p=7: `2² - 5·3² = 4 - 45 ≡ 1 mod 7`.  So result = (1, 0). -/
theorem fp2Mul_self_frob_smoke_7 :
    fp2Mul 7 (2, 3) (fp2Frob 7 (2, 3)) = (fp2Norm 7 (2, 3), 0) := by decide

/-! ## Norm of φ = -1 (universal Phase 3.3 closure step) -/

/-- Helper: `((X % p) + Y) % p = (X + Y) % p`.  Universal mod-p
    identity.  PURE. -/
theorem mod_add_eq_left (X Y p : Nat) : (X % p + Y) % p = (X + Y) % p := by
  rw [add_mod_gen (X % p) Y p, mod_mod X p, ← add_mod_gen X Y p]

/-- ★ **`5·inv2² ≡ 1 + inv2² (mod p)`** (universal, for odd `1 < p`):
    expansion `5 = 4 + 1` plus `4·inv2² ≡ 1`.  PURE. -/
theorem five_inv2_sq_eq (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (5 * inv2 p * inv2 p) % p = (1 + (inv2 p * inv2 p) % p) % p := by
  -- Expand 5 * inv2² = 4 * inv2² + inv2² via add_mul + mul_assoc.
  have h_expand : 5 * inv2 p * inv2 p
                = 4 * (inv2 p * inv2 p) + inv2 p * inv2 p := by
    show (4 + 1) * inv2 p * inv2 p = 4 * (inv2 p * inv2 p) + inv2 p * inv2 p
    rw [add_mul 4 1 (inv2 p)]
    rw [Nat.one_mul]
    rw [add_mul (4 * inv2 p) (inv2 p) (inv2 p)]
    rw [mul_assoc 4 (inv2 p) (inv2 p)]
  rw [h_expand]
  rw [add_mod_gen (4 * (inv2 p * inv2 p)) (inv2 p * inv2 p) p]
  rw [four_mul_inv2_sq p hp hpo]
  rw [Nat.mod_eq_of_lt hp]

/-- ★★ **Norm(φ) = p - 1** (universal Phase 3.3 closure key):
    in 𝔽_{p²}, `Norm(phiFP2 p) = -1 ≡ p - 1 (mod p)` for odd `1 < p`.

    The classical identity `N(φ) = φ · σ(φ) = (1+√5)/2 · (1-√5)/2
    = (1 - 5)/4 = -1` in any extension containing √5.

    Reduces via `five_inv2_sq_eq` + `mod_cancel_right` with `Z = 1`.
    PURE. -/
theorem fp2Norm_phi_eq_neg_one (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    fp2Norm p (phiFP2 p) = p - 1 := by
  have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
  show ((inv2 p * inv2 p) % p
        + (p - (5 * inv2 p * inv2 p) % p)) % p = p - 1
  have hLHS_lt :
      ((inv2 p * inv2 p) % p + (p - (5 * inv2 p * inv2 p) % p)) % p < p :=
    Nat.mod_lt _ hp_pos
  have hRHS_lt : p - 1 < p := Nat.sub_lt hp_pos Nat.one_pos
  -- LHS + 1 ≡ 0 (mod p)
  have h_LHS_succ :
      (((inv2 p * inv2 p) % p + (p - (5 * inv2 p * inv2 p) % p)) % p + 1) % p
        = 0 := by
    rw [mod_add_eq_left
          ((inv2 p * inv2 p) % p + (p - (5 * inv2 p * inv2 p) % p)) 1 p]
    rw [five_inv2_sq_eq p hp hpo]
    -- Goal: ((inv2 p * inv2 p) % p
    --         + (p - (1 + (inv2 p * inv2 p) % p) % p) + 1) % p = 0
    rw [show (inv2 p * inv2 p) % p
              + (p - (1 + (inv2 p * inv2 p) % p) % p) + 1
            = (p - (1 + (inv2 p * inv2 p) % p) % p)
                + (1 + (inv2 p * inv2 p) % p) from by
        rw [Nat.add_comm ((inv2 p * inv2 p) % p
                            + (p - (1 + (inv2 p * inv2 p) % p) % p)) 1]
        rw [← Nat.add_assoc 1 ((inv2 p * inv2 p) % p)
                              (p - (1 + (inv2 p * inv2 p) % p) % p)]
        rw [Nat.add_comm (1 + (inv2 p * inv2 p) % p)
                         (p - (1 + (inv2 p * inv2 p) % p) % p)]]
    rw [← mod_add_eq_left (p - (1 + (inv2 p * inv2 p) % p) % p)
                          (1 + (inv2 p * inv2 p) % p) p]
    exact nmod_add_self_zero p (1 + (inv2 p * inv2 p) % p) hp_pos
  -- RHS + 1 ≡ 0 (mod p)
  have h_RHS_succ : (p - 1 + 1) % p = 0 := by
    rw [sub_add_cancel (Nat.le_of_lt hp)]
    exact mod_self p
  exact E213.Lib.Math.ModArith.ModBezoutInvariant.mod_cancel_right
    p _ _ 1 hp_pos hLHS_lt hRHS_lt (h_LHS_succ.trans h_RHS_succ.symm)

/-- Smoke at p=3: `Norm(phiFP2 3) = 3 - 1 = 2`.
    phi = (2, 2), Norm = (2² + (3 - 5·2²)) % 3 = (4 + (3 - 20)) % 3
                      = (4 + 0) % 3 = 1 % 3 = 1.  Hmm that's not 2.
    Let me recompute: 5·2² = 20, 20 % 3 = 2. 3 - 2 = 1. 4 % 3 = 1.
    (1 + 1) % 3 = 2. ✓  (The literal computation uses asq = 4 % 3, bsq5 = 20 % 3.) -/
theorem fp2Norm_phi_eq_neg_one_3 : fp2Norm 3 (phiFP2 3) = 2 := by decide

/-- Smoke at p=7: `Norm(phiFP2 7) = 7 - 1 = 6`. -/
theorem fp2Norm_phi_eq_neg_one_7 : fp2Norm 7 (phiFP2 7) = 6 := by decide

/-! ## φ · σ(φ) = -1 (universal Phase 3.3 milestone) -/

/-- ★★★ **`φ · σ(φ) = (-1, 0)`** (universal, for odd `1 < p`):
    the key Phase 3.3 identity.  Combines `fp2Mul_self_frob` (Part 37)
    with `fp2Norm_phi_eq_neg_one` (Part 38).

    In 𝔽_{p²}: φ · σ(φ) = N(φ) = -1, identifying `-1 ∈ 𝔽_p` with `(p-1, 0)`.

    This is the Phase 3.3 analog of `phi * psi ≡ -1 (mod p)` in the split
    case (Phase 3.2), now lifted to 𝔽_{p²} for the inert case.  PURE. -/
theorem phiFP2_mul_frob_phi_eq (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    fp2Mul p (phiFP2 p) (fp2Frob p (phiFP2 p)) = (p - 1, 0) := by
  have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
  rw [fp2Mul_self_frob p hp_pos (phiFP2 p)]
  rw [fp2Norm_phi_eq_neg_one p hp hpo]

/-- Smoke at p=3: φ · σ(φ) = (2, 0) = (-1, 0). -/
theorem phiFP2_mul_frob_phi_3 :
    fp2Mul 3 (phiFP2 3) (fp2Frob 3 (phiFP2 3)) = (2, 0) := by decide

/-- Smoke at p=7: φ · σ(φ) = (6, 0) = (-1, 0). -/
theorem phiFP2_mul_frob_phi_7 :
    fp2Mul 7 (phiFP2 7) (fp2Frob 7 (phiFP2 7)) = (6, 0) := by decide

/-! ## φ² = φ + 1 in 𝔽_{p²} (universal recurrence)

Foundation for Binet expansion in 𝔽_{p²}.  Uses `four_mul_inv2_sq`
and `two_mul_inv2` from PhiMod5 — the same algebra that proves
`phi² = phi + 1` in 𝔽_p (split case), lifted componentwise to 𝔽_{p²}.
-/

open E213.Lib.Math.DyadicFSM.PhiMod5 (two_mul_inv2)

/-- ★ **`2·inv2² ≡ inv2 (mod p)`** for odd `1 < p`.  Direct corollary
    of `two_mul_inv2`.  PURE. -/
theorem two_inv2_sq_eq (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (2 * (inv2 p * inv2 p)) % p = inv2 p % p := by
  -- 2·(inv2·inv2) = (2·inv2)·inv2 [mul_assoc]
  -- mod p: ≡ (1 % p) · inv2 [two_mul_inv2]
  --      ≡ inv2 [Nat.one_mul + mod_mod]
  rw [← mul_assoc 2 (inv2 p) (inv2 p)]
  rw [mul_mod_left_pure (2 * inv2 p) (inv2 p) p]
  rw [two_mul_inv2 p hp hpo]
  rw [← mul_mod_left_pure 1 (inv2 p) p, Nat.one_mul]

/-- ★★ **`6·inv2² ≡ inv2 + 1 (mod p)`** for odd `1 < p`.  Combines
    `four_mul_inv2_sq` + `two_inv2_sq_eq`: `6·inv2² = 4·inv2² + 2·inv2²
    ≡ 1 + inv2`.  PURE. -/
theorem six_inv2_sq_eq (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (6 * (inv2 p * inv2 p)) % p = (inv2 p + 1) % p := by
  -- 6 = 4 + 2
  have h_expand : 6 * (inv2 p * inv2 p)
                = 4 * (inv2 p * inv2 p) + 2 * (inv2 p * inv2 p) := by
    show (4 + 2) * (inv2 p * inv2 p)
       = 4 * (inv2 p * inv2 p) + 2 * (inv2 p * inv2 p)
    exact add_mul 4 2 (inv2 p * inv2 p)
  rw [h_expand]
  rw [add_mod_gen (4 * (inv2 p * inv2 p)) (2 * (inv2 p * inv2 p)) p]
  rw [four_mul_inv2_sq p hp hpo]
  rw [two_inv2_sq_eq p hp hpo]
  -- (1 % p + inv2 p % p) % p = (inv2 p + 1) % p
  rw [← add_mod_gen 1 (inv2 p) p]
  rw [Nat.add_comm 1 (inv2 p)]

/-- ★★★ **`φ² = φ + 1` in 𝔽_{p²}** (universal recurrence for odd `1 < p`).

    The Lucas/golden-ratio recurrence, lifted from 𝔽_p to 𝔽_{p²}.
    First component:  inv2² + 5·inv2² = 6·inv2² ≡ inv2 + 1 mod p.
    Second component: inv2² + inv2² = 2·inv2² ≡ inv2 mod p.

    PURE.  Foundation for Binet expansion in 𝔽_{p²}. -/
theorem phiFP2_sq_eq_phi_add_one (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    fp2Mul p (phiFP2 p) (phiFP2 p) = fp2Add p (phiFP2 p) (fp2One p) := by
  show ((inv2 p * inv2 p + 5 * inv2 p * inv2 p) % p,
        (inv2 p * inv2 p + inv2 p * inv2 p) % p)
     = ((inv2 p + 1 % p) % p, (inv2 p + 0) % p)
  apply Prod.ext
  · -- First component: (inv2² + 5·inv2²) % p = (inv2 + 1 % p) % p
    show (inv2 p * inv2 p + 5 * inv2 p * inv2 p) % p
       = (inv2 p + 1 % p) % p
    -- Factor LHS as 6·inv2²
    rw [show inv2 p * inv2 p + 5 * inv2 p * inv2 p
            = 6 * (inv2 p * inv2 p) from by
        rw [mul_assoc 5 (inv2 p) (inv2 p)]
        show inv2 p * inv2 p + 5 * (inv2 p * inv2 p)
           = 6 * (inv2 p * inv2 p)
        rw [show (6 : Nat) = 1 + 5 from rfl]
        rw [add_mul 1 5 (inv2 p * inv2 p), Nat.one_mul]]
    rw [six_inv2_sq_eq p hp hpo]
    -- (inv2 + 1) % p = (inv2 + 1 % p) % p, convert 1 % p → 1
    rw [Nat.mod_eq_of_lt hp]
  · -- Second component: (inv2² + inv2²) % p = (inv2 + 0) % p = inv2 % p
    show (inv2 p * inv2 p + inv2 p * inv2 p) % p = (inv2 p + 0) % p
    rw [Nat.add_zero]
    rw [show inv2 p * inv2 p + inv2 p * inv2 p
            = 2 * (inv2 p * inv2 p) from by
        rw [show (2 : Nat) = 1 + 1 from rfl]
        rw [add_mul 1 1 (inv2 p * inv2 p), Nat.one_mul]]
    exact two_inv2_sq_eq p hp hpo

/-- Smoke at p=3: phi² = (2,2)·(2,2) = (4+20, 4+4) = (24, 8) % 3 = (0, 2).
    phi + 1 = (2+1, 2+0) % 3 = (0, 2). ✓ -/
theorem phiFP2_sq_eq_phi_add_one_3 :
    fp2Mul 3 (phiFP2 3) (phiFP2 3) = fp2Add 3 (phiFP2 3) (fp2One 3) := by decide

/-- Smoke at p=7. -/
theorem phiFP2_sq_eq_phi_add_one_7 :
    fp2Mul 7 (phiFP2 7) (phiFP2 7) = fp2Add 7 (phiFP2 7) (fp2One 7) := by decide

/-! ## Binet expansion in 𝔽_{p²}: `φ^k = F_k · φ + F_{k-1}` -/

open E213.Lib.Math.DyadicFSM.PhiMod5 (fibLike)

/-- Helper: `(F * (6 * (inv2² mod p))) % p = (F * (inv2 + 1)) % p`
    for odd `1 < p`.  PURE. -/
private theorem F_mul_six_inv2_sq (F p : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (F * (6 * (inv2 p * inv2 p))) % p = (F * (inv2 p + 1)) % p := by
  rw [mul_mod_right_pure F (6 * (inv2 p * inv2 p)) p]
  rw [six_inv2_sq_eq p hp hpo]
  rw [← mul_mod_right_pure F (inv2 p + 1) p]

/-- Helper: `(F * (2 * (inv2² mod p))) % p = (F * inv2) % p`
    for odd `1 < p`.  PURE. -/
private theorem F_mul_two_inv2_sq (F p : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (F * (2 * (inv2 p * inv2 p))) % p = (F * inv2 p) % p := by
  rw [mul_mod_right_pure F (2 * (inv2 p * inv2 p)) p]
  rw [two_inv2_sq_eq p hp hpo]
  rw [← mul_mod_right_pure F (inv2 p) p]

/-- Helper: `Fk · inv2 · inv2 + Fkm · inv2 + 5·Fk · inv2 · inv2 = 6·Fk · (inv2·inv2) + Fkm·inv2`
    Pure Nat algebra (combine inv2² terms). -/
private theorem fp2_pow_step_alg_lhs1 (Fk Fkm p : Nat) :
    Fk * inv2 p * inv2 p + Fkm * inv2 p + 5 * Fk * inv2 p * inv2 p
      = 6 * Fk * (inv2 p * inv2 p) + Fkm * inv2 p := by
  rw [Nat.add_right_comm (Fk * inv2 p * inv2 p) (Fkm * inv2 p)
                          (5 * Fk * inv2 p * inv2 p)]
  -- (Fk·inv2·inv2 + 5·Fk·inv2·inv2) + Fkm·inv2 = (6·Fk·(inv2·inv2)) + Fkm·inv2
  rw [mul_assoc Fk (inv2 p) (inv2 p)]
  rw [mul_assoc (5 * Fk) (inv2 p) (inv2 p)]
  -- Fk·(inv2·inv2) + 5·Fk·(inv2·inv2) + Fkm·inv2
  rw [← add_mul Fk (5 * Fk) (inv2 p * inv2 p)]
  -- (Fk + 5·Fk)·(inv2·inv2) + Fkm·inv2 = 6·Fk·(inv2·inv2) + Fkm·inv2
  rw [show Fk + 5 * Fk = 6 * Fk from by
      rw [show (5 : Nat) * Fk = 5 * Fk from rfl]
      rw [show (6 : Nat) = 1 + 5 from rfl]
      rw [add_mul 1 5 Fk, Nat.one_mul]]

/-- Helper: `Fk · inv2 · inv2 + Fkm · inv2 + Fk · inv2 · inv2 = 2·Fk · (inv2·inv2) + Fkm·inv2`
    Pure Nat algebra (combine inv2² terms). -/
private theorem fp2_pow_step_alg_lhs2 (Fk Fkm p : Nat) :
    Fk * inv2 p * inv2 p + Fkm * inv2 p + Fk * inv2 p * inv2 p
      = 2 * Fk * (inv2 p * inv2 p) + Fkm * inv2 p := by
  rw [Nat.add_right_comm (Fk * inv2 p * inv2 p) (Fkm * inv2 p)
                          (Fk * inv2 p * inv2 p)]
  rw [mul_assoc Fk (inv2 p) (inv2 p)]
  rw [← Nat.two_mul (Fk * (inv2 p * inv2 p))]
  rw [← mul_assoc 2 Fk (inv2 p * inv2 p)]

/-- Helper: `6 * Fk * (inv2² mod) ≡ Fk * (inv2 + 1) (mod p)` via mul_assoc + F_mul_six_inv2_sq. -/
private theorem six_Fk_inv2_sq_eq (Fk p : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (6 * Fk * (inv2 p * inv2 p)) % p = (Fk * (inv2 p + 1)) % p := by
  rw [Nat.mul_comm 6 Fk]
  rw [mul_assoc Fk 6 (inv2 p * inv2 p)]
  exact F_mul_six_inv2_sq Fk p hp hpo

/-- Helper: `2 * Fk * (inv2² mod) ≡ Fk * inv2 (mod p)`. -/
private theorem two_Fk_inv2_sq_eq (Fk p : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (2 * Fk * (inv2 p * inv2 p)) % p = (Fk * inv2 p) % p := by
  rw [Nat.mul_comm 2 Fk]
  rw [mul_assoc Fk 2 (inv2 p * inv2 p)]
  exact F_mul_two_inv2_sq Fk p hp hpo

/-- ★★ **Binet inductive step**: from
    `((Fk·inv2 + Fkm) % p, (Fk·inv2) % p)` (Binet form for index k)
    multiplied by `phiFP2`, get the Binet form for index k+1
    `((F_{k+1}·inv2 + Fk) % p, (F_{k+1}·inv2) % p)` where
    `F_{k+1} = Fk + Fkm`.  PURE for odd `1 < p`. -/
private theorem phiFP2_pow_step (Fk Fkm p : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    fp2Mul p ((Fk * inv2 p + Fkm) % p, (Fk * inv2 p) % p) (phiFP2 p)
      = (((Fk + Fkm) * inv2 p + Fk) % p, ((Fk + Fkm) * inv2 p) % p) := by
  apply Prod.ext
  · -- First component
    show ((((Fk * inv2 p + Fkm) % p) * inv2 p
            + 5 * ((Fk * inv2 p) % p) * inv2 p) % p)
       = ((Fk + Fkm) * inv2 p + Fk) % p
    rw [add_mod_gen (((Fk * inv2 p + Fkm) % p) * inv2 p)
                     (5 * ((Fk * inv2 p) % p) * inv2 p) p]
    rw [← mul_mod_left_pure (Fk * inv2 p + Fkm) (inv2 p) p]
    rw [show (5 * ((Fk * inv2 p) % p) * inv2 p) % p
            = (5 * (Fk * inv2 p) * inv2 p) % p from by
        rw [mul_mod_left_pure (5 * ((Fk * inv2 p) % p)) (inv2 p) p]
        rw [← mul_mod_right_pure 5 (Fk * inv2 p) p]
        rw [← mul_mod_left_pure (5 * (Fk * inv2 p)) (inv2 p) p]]
    rw [← add_mod_gen ((Fk * inv2 p + Fkm) * inv2 p)
                       (5 * (Fk * inv2 p) * inv2 p) p]
    rw [add_mul (Fk * inv2 p) Fkm (inv2 p)]
    rw [show 5 * (Fk * inv2 p) * inv2 p = 5 * Fk * inv2 p * inv2 p from by
        rw [mul_assoc 5 Fk (inv2 p)]]
    rw [fp2_pow_step_alg_lhs1 Fk Fkm p]
    rw [add_mod_gen (6 * Fk * (inv2 p * inv2 p)) (Fkm * inv2 p) p]
    rw [six_Fk_inv2_sq_eq Fk p hp hpo]
    rw [← add_mod_gen (Fk * (inv2 p + 1)) (Fkm * inv2 p) p]
    rw [Nat.mul_add Fk (inv2 p) 1, Nat.mul_one]
    rw [Nat.add_right_comm (Fk * inv2 p) Fk (Fkm * inv2 p)]
    rw [← add_mul Fk Fkm (inv2 p)]
  · -- Second component (no factor of 5)
    show ((((Fk * inv2 p + Fkm) % p) * inv2 p
            + ((Fk * inv2 p) % p) * inv2 p) % p)
       = ((Fk + Fkm) * inv2 p) % p
    rw [add_mod_gen (((Fk * inv2 p + Fkm) % p) * inv2 p)
                     (((Fk * inv2 p) % p) * inv2 p) p]
    rw [← mul_mod_left_pure (Fk * inv2 p + Fkm) (inv2 p) p]
    rw [← mul_mod_left_pure (Fk * inv2 p) (inv2 p) p]
    rw [← add_mod_gen ((Fk * inv2 p + Fkm) * inv2 p)
                       ((Fk * inv2 p) * inv2 p) p]
    rw [add_mul (Fk * inv2 p) Fkm (inv2 p)]
    rw [fp2_pow_step_alg_lhs2 Fk Fkm p]
    rw [add_mod_gen (2 * Fk * (inv2 p * inv2 p)) (Fkm * inv2 p) p]
    rw [two_Fk_inv2_sq_eq Fk p hp hpo]
    rw [← add_mod_gen (Fk * inv2 p) (Fkm * inv2 p) p]
    rw [← add_mul Fk Fkm (inv2 p)]

/-- ★★★★ **Binet expansion in 𝔽_{p²}**:
    `phiFP2^k = F_k · phiFP2 + F_{k-1}` (using fibLike convention
    `(F_k, F_{k-1})`).  Specifically:

      `fp2Pow p (phiFP2 p) k
         = ((F_k * inv2 + F_{k-1}) % p, (F_k * inv2) % p)`

    By induction on k using `phiFP2_pow_step` (which encodes
    `phi² = phi + 1` via the inductive step algebra).

    PURE for odd `1 < p`.  This is the 𝔽_{p²}-analog of
    `phi_pow_eq_fibLike` in PhiMod5 (split case). -/
theorem phiFP2_pow_eq_fibLike (p : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    ∀ k, fp2Pow p (phiFP2 p) k
       = (((fibLike k).1 * inv2 p + (fibLike k).2) % p,
          ((fibLike k).1 * inv2 p) % p)
  | 0 => by
    show fp2One p = ((0 * inv2 p + 1) % p, (0 * inv2 p) % p)
    show (1 % p, 0) = ((0 * inv2 p + 1) % p, (0 * inv2 p) % p)
    rw [Nat.zero_mul, Nat.zero_add, zero_mod p]
  | k + 1 => by
    have ih := phiFP2_pow_eq_fibLike p hp hpo k
    -- Recurrence on fibLike (k + 1):
    -- (fibLike (k+1)).1 = (fibLike k).1 + (fibLike k).2
    -- (fibLike (k+1)).2 = (fibLike k).1
    show fp2Pow p (phiFP2 p) (k + 1)
       = (((fibLike (k + 1)).1 * inv2 p + (fibLike (k + 1)).2) % p,
          ((fibLike (k + 1)).1 * inv2 p) % p)
    rw [fp2Pow_succ p (phiFP2 p) k, ih]
    -- Goal:
    --   fp2Mul p ((Fk * inv2 + Fkm) % p, (Fk * inv2) % p) phiFP2
    -- = ((F_{k+1} * inv2 + Fk) % p, (F_{k+1} * inv2) % p)
    -- where F_{k+1} = Fk + Fkm via fibLike_succ_fst.
    show fp2Mul p (((fibLike k).1 * inv2 p + (fibLike k).2) % p,
                    ((fibLike k).1 * inv2 p) % p)
                 (phiFP2 p)
       = ((((fibLike k).1 + (fibLike k).2) * inv2 p + (fibLike k).1) % p,
          (((fibLike k).1 + (fibLike k).2) * inv2 p) % p)
    exact phiFP2_pow_step (fibLike k).1 (fibLike k).2 p hp hpo

/-- Smoke at p=3 (k=2): fibLike 2 = (1, 1). phi² = (0, 2) mod 3.
    RHS: ((1 * 2 + 1) % 3, (1 * 2) % 3) = (0, 2). ✓ -/
theorem phiFP2_pow_eq_fibLike_3_2 :
    fp2Pow 3 (phiFP2 3) 2 = (0, 2) := by decide

/-- Smoke at p=7 (k=3): fibLike 3 = (2, 1). phi³ = (8 + 1, 8) mod 7 = (2, 1).
    Actually phi³ via fp2Mul at p=7. Compute: phi = (4, 4). phi² = (4·4 + 5·4·4, 4·4 + 4·4) = (96, 32) mod 7 = (5, 4).
    phi³ = phi² · phi = (5, 4) · (4, 4) = (20 + 80, 20 + 16) = (100, 36) mod 7 = (2, 1).
    RHS: ((2*4 + 1) % 7, (2*4) % 7) = (9 % 7, 8 % 7) = (2, 1). ✓ -/
theorem phiFP2_pow_eq_fibLike_7_3 :
    fp2Pow 7 (phiFP2 7) 3 = (2, 1) := by decide

end E213.Lib.Math.ModArith.FP2Sqrt5
