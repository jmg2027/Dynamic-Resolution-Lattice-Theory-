import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.Gcd213
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum

/-!
# Euler totient φ + Gauss divisor-sum identity (∅-axiom)

Introduces Euler's totient as a ∅-axiom counting definition and the divisor-sum
machinery, with Gauss's identity verified over a range.

  * `totient n`        = count of `k ∈ {1,…,n}` with `gcd213 k n = 1`.
  * `divisorSum n f`   = `Σ_{d ∣ n, 1 ≤ d ≤ n} f d`.
  * `gaussSum n`       = `Σ_{d ∣ n} totient d`.
  * ★ `gauss_totient_table` — Gauss's identity `Σ_{d∣n} φ(d) = n`, verified n = 1..24.

All declarations PURE (propext-free): indicators are `Bool.toNat` (avoiding the
`if_pos`/`if_congr` propext leak), sums are the recursive `sumTo`, tables close by
`decide`.

**Open frontier** (`research-notes/frontiers/gauss_totient_general.md`): the
*general* theorem `∀ n ≥ 1, Σ_{d∣n} φ(d) = n` needs partition-by-gcd cardinality
machinery — `count{k ≤ n : gcd(k,n) = g} = φ(n/g)` summed over divisors `g ∣ n`.
The gcd-scaling fact `gcd213 (k·a) (k·b) = k·gcd213 a b` is PURE (`Gcd213`), but
lifting it to a count-preserving reindexing + a disjoint-cover cardinality lemma is
a from-scratch counting build (no `Finset.card` partition API).  Recorded, not yet
closed.  The totient definition and the verified identity table are genuinely new
∅-axiom content (the corpus had no `totient`/`eulerPhi`/divisor-sum machinery; the
`phi` elsewhere is the golden ratio).
-/

namespace E213.Lib.Math.NumberTheory.EulerTotient

open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)

/-! ## Euler totient -/

/-- Indicator: `1` if `gcd213 (k+1) n = 1`, else `0`; propext-free via `Bool`. -/
def coprimeInd (k n : Nat) : Nat := (gcd213 (k + 1) n == 1).toNat

/-- Euler totient: count of `k ∈ {1,…,n}` coprime to `n`.
    `totient n = Σ_{k=0}^{n-1} [gcd213 (k+1) n = 1]`. -/
def totient (n : Nat) : Nat := sumTo n (fun k => coprimeInd k n)

/-! ## Divisor sum -/

/-- Divisibility indicator over the divisor range (`1 ≤ d`):
    `1` if `d+1 ∣ n` (i.e. `n % (d+1) = 0`), else `0`.  propext-free. -/
def dvdInd (d n : Nat) : Nat := (n % (d + 1) == 0).toNat

/-- Divisor sum `Σ_{d ∣ n, 1 ≤ d ≤ n} f d`, ranging `d = 1 … n`
    (shifted index `j = d−1 ∈ {0,…,n−1}`).  propext-free. -/
def divisorSum (n : Nat) (f : Nat → Nat) : Nat :=
  sumTo n (fun j => dvdInd j n * f (j + 1))

/-- Gauss sum specialised to the totient: `Σ_{d ∣ n} φ(d)`. -/
def gaussSum (n : Nat) : Nat := divisorSum n totient

/-! ## Tables (∅-axiom, by `decide`) -/

/-- φ(1..12) = 1,1,2,2,4,2,6,4,6,4,10,4. -/
theorem totient_table :
    totient 1 = 1 ∧ totient 2 = 1 ∧ totient 3 = 2 ∧ totient 4 = 2 ∧
    totient 5 = 4 ∧ totient 6 = 2 ∧ totient 7 = 6 ∧ totient 8 = 4 ∧
    totient 9 = 6 ∧ totient 10 = 4 ∧ totient 11 = 10 ∧ totient 12 = 4 := by
  decide

/-- φ(p) = p − 1 for the small primes 2,3,5,7,11,13. -/
theorem totient_prime :
    totient 2 = 1 ∧ totient 3 = 2 ∧ totient 5 = 4 ∧
    totient 7 = 6 ∧ totient 11 = 10 ∧ totient 13 = 12 := by
  decide

/-- ★ **Gauss divisor-sum identity**, verified n = 1..24:
    `Σ_{d ∣ n} φ(d) = n`. -/
theorem gauss_totient_table :
    gaussSum 1 = 1 ∧ gaussSum 2 = 2 ∧ gaussSum 3 = 3 ∧ gaussSum 4 = 4 ∧
    gaussSum 5 = 5 ∧ gaussSum 6 = 6 ∧ gaussSum 7 = 7 ∧ gaussSum 8 = 8 ∧
    gaussSum 9 = 9 ∧ gaussSum 10 = 10 ∧ gaussSum 11 = 11 ∧ gaussSum 12 = 12 ∧
    gaussSum 13 = 13 ∧ gaussSum 14 = 14 ∧ gaussSum 15 = 15 ∧ gaussSum 16 = 16 ∧
    gaussSum 17 = 17 ∧ gaussSum 18 = 18 ∧ gaussSum 19 = 19 ∧ gaussSum 20 = 20 ∧
    gaussSum 21 = 21 ∧ gaussSum 22 = 22 ∧ gaussSum 23 = 23 ∧ gaussSum 24 = 24 := by
  decide

end E213.Lib.Math.NumberTheory.EulerTotient
