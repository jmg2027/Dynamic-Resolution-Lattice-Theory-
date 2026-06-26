import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Lib.Math.NumberTheory.ModArith.EulerConverse
import E213.Lib.Math.NumberTheory.FourSquareSeed
import E213.Meta.Int213.PolyIntMTactic

/-!
# The three cube roots of unity mod `p` are `{1, x, x²}` (∅-axiom, Phase A1)

For a prime `p` and a rational cube root `x` (`p ∣ x²+x+1`, supplied by
`EisensteinConverse.cube_root_exists` for `p ≡ 1 mod 3`), **every** solution of `y³ ≡ 1 (mod p)` with
`0 ≤ y < p` is one of the three known roots:

  `y = 1 ∨ y = x % p ∨ y = (x·x) % p`.

This is the field fact behind the cubic character being **`μ₃`-valued as a function on `𝔽_p`**: the
value `χ(t) = t^m % p` (`CubicCharFp`, a cube root of unity by `cubicChar_cube_one`) is forced into the
three-element set `{1, x, x²}`, which the residue-field iso
(`EisensteinResidueFieldCubeRoots.cube_roots_rational`) carries onto `{1, ω, ω²} ⊂ ℤ[ω]`.  The Jacobi
sum's character then takes genuinely-`μ₃` values (Phase A1).

The argument is the cubic factorisation over `𝔽_p`: `y³−1 = (y−1)(y²+y+1)` and `(y−x)(y−x²) ≡ y²+y+1`
(using `x+x² ≡ −1`, `x³ ≡ 1`), each split by Euclid's lemma (`int_euclid` route).  ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.CubeRootsUnityModP

open E213.Lib.Math.NumberTheory.PolyRoot
  (nat_dvd_to_int int_dvd_to_nat natAbs_mul mod_eq_imp_dvd_sub dvd_add' dvd_mul_left')
open E213.Lib.Math.NumberTheory.ModArith.EulerConverse (mod_eq_of_dvd_sub)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Meta.Nat.NatRing213 (nat_sub_add_cancel)

/-- **`(↑a − ↑b).natAbs = a − b`** when `b ≤ a` (pure, avoiding `Int.ofNat_sub`). -/
private theorem natAbs_ofNat_sub {a b : Nat} (h : b ≤ a) :
    ((a : Int) - (b : Int)).natAbs = a - b := by
  have hc : (a : Int) - (b : Int) = ((a - b : Nat) : Int) := by
    have hadd : ((a - b : Nat) : Int) + (b : Int) = (a : Int) := by
      rw [show ((a - b : Nat) : Int) + (b : Int) = (((a - b) + b : Nat) : Int) from rfl,
          nat_sub_add_cancel h]
    rw [← hadd]; ring_intZ
  rw [hc]; exact Int.natAbs_ofNat (a - b)

/-- **`↑p ∣ (↑a − ↑b) ⟹ a % p = b % p`** — the residue bridge from a `ℤ`-divisibility. -/
theorem dvd_sub_to_mod_eq (a b p : Nat) (h : (p : Int) ∣ ((a : Int) - (b : Int))) :
    a % p = b % p := by
  rcases Nat.le_total b a with hba | hab
  · have hn : p ∣ (a - b) := by
      have hd := int_dvd_to_nat p _ h
      rwa [natAbs_ofNat_sub hba] at hd
    exact mod_eq_of_dvd_sub p a b hba hn
  · have hn : p ∣ (b - a) := by
      have hd := int_dvd_to_nat p _ h
      rw [show (a : Int) - (b : Int) = -((b : Int) - (a : Int)) from by ring_intZ,
          Int.natAbs_neg, natAbs_ofNat_sub hab] at hd
      exact hd
    exact (mod_eq_of_dvd_sub p b a hab hn).symm

/-- **Euclid split over `ℤ` for a prime, as a disjunction** — `↑p ∣ a·b ⟹ ↑p ∣ a ∨ ↑p ∣ b`.
    Via `natAbs` multiplicativity (`natAbs_mul`, pure) and `nat_prime_dvd_mul`. -/
theorem int_dvd_prime_mul (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (a b : Int) (h : (p : Int) ∣ a * b) : (p : Int) ∣ a ∨ (p : Int) ∣ b := by
  have h1 : p ∣ a.natAbs * b.natAbs := by rw [← natAbs_mul]; exact int_dvd_to_nat p (a * b) h
  rcases nat_prime_dvd_mul p hp hpr a.natAbs b.natAbs h1 with ha | hb
  · exact Or.inl (nat_dvd_to_int p a ha)
  · exact Or.inr (nat_dvd_to_int p b hb)

/-- ★★★★★ **The cube roots of unity mod `p` are `{1, x, x²}`.**  For a prime `p` and a rational cube
    root `x` (`p ∣ x²+x+1`), every `y < p` with `y³ ≡ 1 (mod p)` satisfies `y = 1 ∨ y = x % p ∨
    y = (x·x) % p`.  Cubic factorisation `y³−1 = (y−1)(y²+y+1)` then `(y−x)(y−x²) ≡ y²+y+1`, each split
    by `int_dvd_prime_mul`.  ∅-axiom. -/
theorem cube_root_trichotomy (p x y : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (hx : p ∣ (x * x + x + 1))
    (hylt : y < p) (hy3 : y ^ 3 % p = 1) :
    y = 1 ∨ y = x % p ∨ y = (x * x) % p := by
  -- cast the hypotheses into ℤ
  have hXint : (p : Int) ∣ ((x : Int) * (x : Int) + (x : Int) + 1) := by
    have hcast : ((x * x + x + 1 : Nat) : Int) = (x : Int) * (x : Int) + (x : Int) + 1 := rfl
    rw [← hcast]; exact nat_dvd_to_int p _ (by rw [Int.natAbs_ofNat]; exact hx)
  have hy3' : y ^ 3 % p = 1 % p := by rw [hy3, Nat.mod_eq_of_lt hp]
  have hpow : (y ^ 3 : Nat) = y * y * y := by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  have hY3 : (p : Int) ∣ ((y : Int) * (y : Int) * (y : Int) - 1) := by
    have hd := mod_eq_imp_dvd_sub (y ^ 3) 1 p hy3'
    have hcast : ((y ^ 3 : Nat) : Int) - ((1 : Nat) : Int)
        = (y : Int) * (y : Int) * (y : Int) - 1 := by rw [hpow]; rfl
    rwa [hcast] at hd
  -- y³ − 1 = (y − 1)(y² + y + 1)
  have hfac : (y : Int) * (y : Int) * (y : Int) - 1
      = ((y : Int) - 1) * ((y : Int) * (y : Int) + (y : Int) + 1) := by ring_intZ
  rw [hfac] at hY3
  rcases int_dvd_prime_mul p hp hpr _ _ hY3 with hA | hB
  · -- p ∣ (y − 1): y = 1
    left
    have hmod : y % p = 1 % p := dvd_sub_to_mod_eq y 1 p hA
    rwa [Nat.mod_eq_of_lt hylt, Nat.mod_eq_of_lt hp] at hmod
  · -- p ∣ (y² + y + 1): the (y − x)(y − x²) split
    have hX3 : (p : Int) ∣ ((x : Int) * (x : Int) * (x : Int) - 1) := by
      have he : (x : Int) * (x : Int) * (x : Int) - 1
          = ((x : Int) - 1) * ((x : Int) * (x : Int) + (x : Int) + 1) := by ring_intZ
      rw [he]; exact dvd_mul_left' hXint ((x : Int) - 1)
    have hlin : (p : Int) ∣ (-((x : Int) * (x : Int) + (x : Int) + 1) * (y : Int)) := by
      have he : -((x : Int) * (x : Int) + (x : Int) + 1) * (y : Int)
          = (-(y : Int)) * ((x : Int) * (x : Int) + (x : Int) + 1) := by ring_intZ
      rw [he]; exact dvd_mul_left' hXint (-(y : Int))
    have hdiff : (p : Int) ∣
        (((y : Int) - (x : Int)) * ((y : Int) - (x : Int) * (x : Int))
          - ((y : Int) * (y : Int) + (y : Int) + 1)) := by
      have he : ((y : Int) - (x : Int)) * ((y : Int) - (x : Int) * (x : Int))
            - ((y : Int) * (y : Int) + (y : Int) + 1)
          = -((x : Int) * (x : Int) + (x : Int) + 1) * (y : Int)
            + ((x : Int) * (x : Int) * (x : Int) - 1) := by ring_intZ
      rw [he]; exact dvd_add' hlin hX3
    have hYXX : (p : Int) ∣
        (((y : Int) - (x : Int)) * ((y : Int) - (x : Int) * (x : Int))) := by
      have he : ((y : Int) - (x : Int)) * ((y : Int) - (x : Int) * (x : Int))
          = ((y : Int) * (y : Int) + (y : Int) + 1)
            + (((y : Int) - (x : Int)) * ((y : Int) - (x : Int) * (x : Int))
              - ((y : Int) * (y : Int) + (y : Int) + 1)) := by ring_intZ
      rw [he]; exact dvd_add' hB hdiff
    rcases int_dvd_prime_mul p hp hpr _ _ hYXX with hYX | hYXsq
    · -- p ∣ (y − x): y = x % p
      right; left
      have hmod : y % p = x % p := dvd_sub_to_mod_eq y x p hYX
      rwa [Nat.mod_eq_of_lt hylt] at hmod
    · -- p ∣ (y − x²): y = (x·x) % p
      right; right
      have hcast : (x : Int) * (x : Int) = ((x * x : Nat) : Int) := rfl
      rw [hcast] at hYXsq
      have hmod : y % p = (x * x) % p := dvd_sub_to_mod_eq y (x * x) p hYXsq
      rwa [Nat.mod_eq_of_lt hylt] at hmod

end E213.Lib.Math.NumberTheory.ModArith.CubeRootsUnityModP
