import E213.Lib.Math.NumberTheory.PrimeFactorization
import E213.Meta.Nat.VpMul
import E213.Meta.Nat.VpSeparation
import E213.Meta.Nat.FoldCriterion

/-!
# FTA uniqueness as valuation-count invariance (∅-axiom, vein-A)

Classically FTA uniqueness is "lift to ℤ, use that ℤ is a UFD" or a
multiset-permutation argument.  ∅-axiom forces it as **valuation-count
invariance**: the multiplicity of a prime `q` in *any* prime-factorization
list of `n` equals the *computed* `vp q n`.  So the factorization multiset
is read off `n` — no abstract UFD, no permutation bookkeeping.

  * ★ `vp_prodL_eq_countOcc` — for a list `l` of positive primes,
    `vp q (prodL l) = countOcc q l` (`q` prime).  The multiplicity of `q`
    in the list is the valuation of the product.
  * `factorization_unique` — two prime lists with the same product have
    equal `countOcc` at every prime (both equal `vp q n`).  **This IS FTA
    uniqueness** (same multiset of primes).

Built only on `prodL` (`PrimeFactorization`), `vp`/`vp_mul`/`vp_self_pow`
(`VpMul`), `vp_eq_zero_of_not_dvd` (`VpSeparation`), `prime_not_dvd_prime`
(`FoldCriterion`).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.FTAUniqueness

open E213.Lib.Math.NumberTheory.PrimeFactorization (prodL prodL_cons)
open E213.Meta.Nat.VpMul (IsPrime213 vp_mul vp_self_pow)
open E213.Meta.Nat.Valuation (vp)
open E213.Meta.Nat.VpSeparation (vp_eq_zero_of_not_dvd)
open E213.Meta.Nat.FoldCriterion (prime_not_dvd_prime)

/-! ## §0 — structural occurrence count (PURE; no `List.count`) -/

/-- Number of times `q` appears in `l`.  Structural `List` recursion with the
    reducible `Nat.beq` equality test — avoids `List.count`/`List.countP`,
    which route through `propext`-carrying `Decidable` instances. -/
def countOcc (q : Nat) : List Nat → Nat
  | []      => 0
  | x :: xs => (if x = q then 1 else 0) + countOcc q xs

theorem countOcc_cons (q x : Nat) (xs : List Nat) :
    countOcc q (x :: xs) = (if x = q then 1 else 0) + countOcc q xs := rfl

/-- Product of a list of positive primes is positive. -/
theorem prodL_pos : ∀ l : List Nat, (∀ x, x ∈ l → IsPrime213 x) → 0 < prodL l
  | [],      _ => (by decide : (0:Nat) < 1)
  | y :: ys, hall => by
    have hy : IsPrime213 y := hall y (List.Mem.head ys)
    have hypos : 0 < y := Nat.lt_of_lt_of_le (by decide) hy.two_le
    have hys : ∀ x, x ∈ ys → IsPrime213 x :=
      fun x hx => hall x (List.Mem.tail y hx)
    show 0 < prodL (y :: ys)
    rw [prodL_cons]
    exact Nat.mul_pos hypos (prodL_pos ys hys)

/-! ## §1 — `vp q` of a single prime -/

/-- `vp q p` for primes `q`, `p`: `1` if `q = p`, else `0` (`q ∤ p`). -/
theorem vp_prime_single {q p : Nat} (hq : IsPrime213 q) (hp : IsPrime213 p) :
    vp q p = (if p = q then 1 else 0) := by
  by_cases hpq : p = q
  · rw [if_pos hpq, hpq]
    -- vp q q = 1
    have hsp := vp_self_pow hq 1
    rwa [Nat.pow_one] at hsp
  · rw [if_neg hpq]
    -- q ≠ p, both prime ⟹ q ∤ p ⟹ vp q p = 0
    have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
    have hqp : q ≠ p := fun e => hpq e.symm
    exact vp_eq_zero_of_not_dvd hq hppos (prime_not_dvd_prime hq hp hqp)

/-! ## §2 — the headline: valuation reads occurrence count -/

/-- ★ **Valuation = occurrence count.**  For a list `l` whose entries are all
    positive primes, the `q`-adic valuation of the product equals the number
    of times `q` occurs in `l` (`q` prime):

      `vp q (prodL l) = countOcc q l`.

    Induction on `l`: `prodL (p::rest) = p * prodL rest`, `vp` is additive over
    `×` (`vp_mul`, needs `p > 0` and `prodL rest > 0`), and `vp q p =
    (if p = q then 1 else 0) = countOcc q [p]`.  The multiplicity of `q` in any
    such list is therefore *determined by the product* `n = prodL l`. -/
theorem vp_prodL_eq_countOcc {q : Nat} (hq : IsPrime213 q) :
    ∀ l : List Nat, (∀ x, x ∈ l → IsPrime213 x) → vp q (prodL l) = countOcc q l := by
  intro l
  induction l with
  | nil =>
    intro _
    -- prodL [] = 1, countOcc q [] = 0, vp q 1 = 0
    show vp q (prodL []) = countOcc q []
    -- vp q 1 = 0 via vp_self_pow q 0 : vp q (q^0) = 0, and q^0 = 1
    have h0 := vp_self_pow hq 0
    rw [Nat.pow_zero] at h0
    show vp q 1 = 0
    exact h0
  | cons p rest ih =>
    intro hall
    have hp : IsPrime213 p := hall p (List.Mem.head rest)
    have hrest : ∀ x, x ∈ rest → IsPrime213 x :=
      fun x hx => hall x (List.Mem.tail p hx)
    have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.two_le
    -- prodL rest > 0 (product of positives)
    have hprodpos : 0 < prodL rest := prodL_pos rest hrest
    show vp q (prodL (p :: rest)) = countOcc q (p :: rest)
    rw [prodL_cons, vp_mul hq hppos hprodpos, vp_prime_single hq hp,
        ih hrest, countOcc_cons]

/-! ## §3 — FTA uniqueness -/

/-- **FTA uniqueness = valuation-count invariance.**  Two prime-factorization
    lists `l1`, `l2` of the same `n` (`prodL l1 = prodL l2`, all entries prime)
    have **equal occurrence count at every prime** `q` — because both equal
    `vp q n`.  No multiset-permutation bookkeeping, no UFD: the multiplicity of
    each prime is *read off the product*. -/
theorem factorization_unique {l1 l2 : List Nat}
    (h1 : ∀ x, x ∈ l1 → IsPrime213 x) (h2 : ∀ x, x ∈ l2 → IsPrime213 x)
    (heq : prodL l1 = prodL l2) :
    ∀ q, IsPrime213 q → countOcc q l1 = countOcc q l2 := by
  intro q hq
  calc countOcc q l1 = vp q (prodL l1) := (vp_prodL_eq_countOcc hq l1 h1).symm
    _ = vp q (prodL l2) := by rw [heq]
    _ = countOcc q l2 := vp_prodL_eq_countOcc hq l2 h2

/-! ## §4 — concrete smokes -/

-- countOcc reads the corpus factorizations
example : countOcc 2 [2, 2, 3] = 2 := by decide
example : countOcc 3 [2, 2, 3] = 1 := by decide
example : countOcc 5 [2, 2, 3] = 0 := by decide

-- factorize 12 = [2,2,3]; occurrence counts match the valuations of 12
example :
    E213.Lib.Math.NumberTheory.PrimeFactorization.factorize 12 = [2, 2, 3] := by decide
example : countOcc 2 (E213.Lib.Math.NumberTheory.PrimeFactorization.factorize 12) = 2 := by
  decide
example : countOcc 3 (E213.Lib.Math.NumberTheory.PrimeFactorization.factorize 12) = 1 := by
  decide
example : vp 2 12 = 2 := by decide
example : vp 3 12 = 1 := by decide

end E213.Lib.Math.NumberTheory.FTAUniqueness
