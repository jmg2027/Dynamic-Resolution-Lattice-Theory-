import E213.Meta.Nat.ModPow213
import E213.Lib.Math.NumberTheory.DyadicFSM.Forward.ForwardPeriodicity
/-!
# Multiplicative order via pigeonhole — Phase 2/3 prerequisite

For `a < p` with an explicit modular inverse witness `b` satisfying
`(a * b) % p = 1 % p`, the multiplicative orbit `a^0, a^1, a^2, ...`
mod p must return to 1 within `p` steps.

Closed via the constructive pigeonhole on `Fin (p + 1) → Fin p`
(reusing `Forward.ForwardPeriodicity.pigeonhole_collision`),
then cancellation via `modPow_mul_inv` from `ModPow213`.

The classical Fermat's Little Theorem (FLT) `∀ a coprime to p,
a^(p-1) ≡ 1 (mod p)` requires Lagrange's theorem on the
multiplicative group `(Fin p)*`; this module gives the weaker
**existential** form `∃ N ≤ p, a^N ≡ 1 mod p` which is sufficient
for many Phase 2/3 sub-goals (and is FLT-independent).

The link to phi: at split primes p where `phi p s = (1 + s) * inv2 p`
is well-defined and nonzero, providing an explicit `phi^{-1} mod p`
(constructible from `phi² ≡ phi + 1 ⟹ phi · (phi - 1) ≡ 1 ⟹
phi⁻¹ ≡ phi - 1 mod p`) yields the existential multiplicative
period for phi, which is the FLT-replacement Phase 3.2 needs.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.MulOrderPigeonhole

open E213.Meta.Nat.ModPow213
  (modPow modPow_zero modPow_succ modPow_one modPow_mod_left
   modPow_one_base modPow_lt modPow_add modPow_mul modPow_mul_inv)
open E213.Lib.Math.NumberTheory.DyadicFSM.Forward.ForwardPeriodicity
  (pigeonhole_collision collTest_imp_val_eq)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Tactic.NatHelper (sub_pos_of_lt mul_assoc sub_add_cancel)

/-- Explicit modular inverse witness:  `b < p` with `(a * b) % p = 1 % p`. -/
structure ModInverse (p a : Nat) where
  inv     : Nat
  inv_lt  : inv < p
  inv_eq  : (a * inv) % p = 1 % p

/-- Encode `modPow p a i.val ∈ Fin p` for the pigeonhole argument. -/
def modPowFin (p a : Nat) (hp : 0 < p) (i : Fin (p + 1)) : Fin p :=
  ⟨modPow p a i.val, modPow_lt p a hp i.val⟩

/-- Pigeonhole coincidence: two indices `i < j` in `[0, p]` give
    the same `modPow p a` value.  PURE. -/
theorem modPow_coincidence (p a : Nat) (hp : 0 < p) :
    ∃ i j, i < p + 1 ∧ j < p + 1 ∧ i < j
      ∧ modPow p a i = modPow p a j := by
  have hlt : p < p + 1 := Nat.lt_succ_self _
  obtain ⟨i, hi, j, hj, hij, hcoll⟩ :=
    pigeonhole_collision hlt (modPowFin p a hp)
  have hval_eq : (modPowFin p a hp ⟨i, hi⟩).val
              = (modPowFin p a hp ⟨j, hj⟩).val :=
    collTest_imp_val_eq (modPowFin p a hp) i j hi hj hcoll
  -- `(modPowFin p a hp ⟨i, hi⟩).val = modPow p a i` by definition
  exact ⟨i, j, hi, hj, hij, hval_eq⟩

/-- ★ **Translation engine** (modPow version): given coincidence
    `modPow p a i = modPow p a j` with `i ≤ j` and a modular inverse
    `b` for `a` mod p, derive `modPow p a (j - i) = 1 % p`.

    Proof: multiply the coincidence by `modPow p b i` on both sides,
    use `modPow_mul_inv` (`(modPow a i * modPow b i) % p = 1 % p`)
    to cancel the `modPow a i` factor.  PURE. -/
theorem modPow_translation (p a : Nat) (hp : 0 < p) (mi : ModInverse p a)
    (i j : Nat) (hij : i ≤ j) (h : modPow p a i = modPow p a j) :
    modPow p a (j - i) = 1 % p := by
  -- j = i + (j - i) via PURE NatHelper.sub_add_cancel + Nat.add_comm
  have hsum : i + (j - i) = j := by
    rw [Nat.add_comm]
    exact sub_add_cancel hij
  -- modPow a j = (modPow a i * modPow a (j - i)) % p
  have hadd : modPow p a j = (modPow p a i * modPow p a (j - i)) % p := by
    have key : modPow p a (i + (j - i))
             = (modPow p a i * modPow p a (j - i)) % p :=
      modPow_add p a hp i (j - i)
    rw [hsum] at key
    exact key
  -- modPow a i = (modPow a i * modPow a (j - i)) % p  from h + hadd
  have hcoll : modPow p a i = (modPow p a i * modPow p a (j - i)) % p :=
    h.trans hadd
  -- LHS: (modPow b i * modPow a i) % p = 1 % p via modPow_mul_inv
  have hLHS : (modPow p mi.inv i * modPow p a i) % p = 1 % p := by
    rw [Nat.mul_comm]
    exact modPow_mul_inv p a mi.inv hp mi.inv_eq i
  -- Multiplication preserves Eq:  multiply both sides of hcoll by modPow b i
  have hcongr : modPow p mi.inv i * modPow p a i
              = modPow p mi.inv i
                  * ((modPow p a i * modPow p a (j - i)) % p) :=
    congrArg (modPow p mi.inv i * ·) hcoll
  have hmid : (modPow p mi.inv i * modPow p a i) % p
            = (modPow p mi.inv i
                * ((modPow p a i * modPow p a (j - i)) % p)) % p :=
    congrArg (· % p) hcongr
  -- RHS reduction:  inv2-substitute, cancel inverse, reduce to modPow a (j-i)
  have hRHS_eq : (modPow p mi.inv i
                  * ((modPow p a i * modPow p a (j - i)) % p)) % p
               = modPow p a (j - i) := by
    rw [← mul_mod_right_pure (modPow p mi.inv i)
          (modPow p a i * modPow p a (j - i)) p,
        ← mul_assoc (modPow p mi.inv i) (modPow p a i) (modPow p a (j - i)),
        mul_mod_left_pure (modPow p mi.inv i * modPow p a i)
          (modPow p a (j - i)) p,
        Nat.mul_comm (modPow p mi.inv i) (modPow p a i),
        modPow_mul_inv p a mi.inv hp mi.inv_eq i,
        ← mul_mod_left_pure 1 (modPow p a (j - i)) p, Nat.one_mul]
    exact Nat.mod_eq_of_lt (modPow_lt p a hp (j - i))
  -- Chain: 1 % p = (modPow b i * modPow a i) % p = hmid = modPow a (j-i)
  exact (hLHS.symm.trans hmid).trans hRHS_eq |>.symm

/-- ★★★ **Existential multiplicative order**: for `a` with explicit
    modular inverse mod p (where p > 1), the modPow orbit returns to 1
    within `p` steps:

    `∃ N, 0 < N ∧ N ≤ p ∧ modPow p a N = 1 % p`.

    PURE.  Builds on `modPow_coincidence` (pigeonhole) and
    `modPow_translation` (cancellation via inverse). -/
theorem exists_modPow_period (p a : Nat) (hp : 1 < p) (mi : ModInverse p a) :
    ∃ N, 0 < N ∧ N ≤ p ∧ modPow p a N = 1 % p := by
  have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
  obtain ⟨i, j, hi, hj, hij, hcoll⟩ := modPow_coincidence p a hp_pos
  have hpt : modPow p a (j - i) = 1 % p :=
    modPow_translation p a hp_pos mi i j (Nat.le_of_lt hij) hcoll
  refine ⟨j - i, sub_pos_of_lt hij, ?_, hpt⟩
  exact Nat.le_trans (Nat.sub_le j i) (Nat.le_of_lt_succ hj)

/-! ## Smoke tests at small primes -/

/-- Smoke: at p=5, a=2 has inverse 3 (since 2*3=6≡1 mod 5). -/
def modInv5_of_2 : ModInverse 5 2 :=
  { inv := 3, inv_lt := by decide, inv_eq := by decide }

/-- Smoke: at p=5, 2 has multiplicative period ≤ 5
    (actually 4: 2^4 = 16 ≡ 1 mod 5). -/
theorem exists_modPow_period_5_2 :
    ∃ N, 0 < N ∧ N ≤ 5 ∧ modPow 5 2 N = 1 % 5 :=
  exists_modPow_period 5 2 (by decide) modInv5_of_2

/-- Smoke: at p=7, a=3 has inverse 5 (since 3*5=15≡1 mod 7). -/
def modInv7_of_3 : ModInverse 7 3 :=
  { inv := 5, inv_lt := by decide, inv_eq := by decide }

theorem exists_modPow_period_7_3 :
    ∃ N, 0 < N ∧ N ≤ 7 ∧ modPow 7 3 N = 1 % 7 :=
  exists_modPow_period 7 3 (by decide) modInv7_of_3

end E213.Lib.Math.NumberTheory.DyadicFSM.MulOrderPigeonhole
