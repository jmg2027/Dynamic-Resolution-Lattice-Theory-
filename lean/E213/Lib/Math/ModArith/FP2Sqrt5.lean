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

end E213.Lib.Math.ModArith.FP2Sqrt5
