import E213.Lib.Math.NumberTheory.MobiusDivisorSum

/-!
# Multiplicative-function uniqueness — agreement on prime powers ⟹ equality

★★★ `mult_eq_of_prime_pow` — two multiplicative functions agreeing on every prime
power are equal everywhere.  The uniqueness counterpart to `summatory_mul`.

Proof: smallest-prime-power strong induction (the `isSquare_iff_all_vp_even`
template).  `n=1` by `f 1 = 1 = g 1`; `n>1` split `n = p^k·m`, multiplicativity
+ `hpp` on the prime power + IH on the smaller cofactor `m`.  All ∅-axiom
(`Eq` rewriting only; no `∣`/propext leak).
-/

namespace E213.Lib.Math.NumberTheory.MultiplicativeUniqueness

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213)
open E213.Lib.Math.NumberTheory.MobiusDivisorSum (exists_prime_pow_cofactor)

/-- One inductive step (extracted for axiom-localisation). -/
theorem step (f g : Nat → Nat)
    (hf : ∀ a b, gcd213 a b = 1 → f (a * b) = f a * f b)
    (hg : ∀ a b, gcd213 a b = 1 → g (a * b) = g a * g b)
    (h1f : f 1 = 1) (h1g : g 1 = 1)
    (hpp : ∀ p k, Prime213 p → f (p ^ k) = g (p ^ k))
    (n : Nat)
    (ih : ∀ j, j < n → 0 < j → f j = g j)
    (hn : 0 < n) :
    f n = g n := by
  rcases Nat.lt_or_ge 1 n with hgt | hle
  · -- n > 1
    obtain ⟨p, k, m, hp, _hk1, hmpos, hmlt, hcop, hmeq⟩ := exists_prime_pow_cofactor hgt
    -- f n = f (p^k · m) = f (p^k) · f m
    have hfn : f n = f (p ^ k) * f m := by
      rw [hmeq]; exact hf (p ^ k) m hcop
    have hgn : g n = g (p ^ k) * g m := by
      rw [hmeq]; exact hg (p ^ k) m hcop
    -- f (p^k) = g (p^k); f m = g m (IH)
    have hpkeq : f (p ^ k) = g (p ^ k) := hpp p k hp
    have hmeq' : f m = g m := ih m hmlt hmpos
    rw [hfn, hgn, hpkeq, hmeq']
  · -- n ≤ 1 with 0 < n ⟹ n = 1
    have hn_eq : n = 1 := Nat.le_antisymm hle hn
    rw [hn_eq, h1f, h1g]

/-- ★★★ **Multiplicative-function uniqueness**: two functions multiplicative on
    coprime arguments, normalised at `1`, and agreeing on every prime power, are
    equal on every positive `n`.  The uniqueness counterpart to
    `SummatoryMultiplicative.summatory_mul`. -/
theorem mult_eq_of_prime_pow (f g : Nat → Nat)
    (hf : ∀ a b, gcd213 a b = 1 → f (a * b) = f a * f b)
    (hg : ∀ a b, gcd213 a b = 1 → g (a * b) = g a * g b)
    (h1f : f 1 = 1) (h1g : g 1 = 1)
    (hpp : ∀ p k, Prime213 p → f (p ^ k) = g (p ^ k))
    (n : Nat) (hn : 0 < n) : f n = g n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    exact step f g hf hg h1f h1g hpp n (fun j hj hjpos => ih j hj hjpos) hn

end E213.Lib.Math.NumberTheory.MultiplicativeUniqueness
