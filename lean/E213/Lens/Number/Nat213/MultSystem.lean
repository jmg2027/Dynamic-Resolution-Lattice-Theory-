import E213.Meta.Tactic.NatHelper

/-!
# Lens.Number.Nat213.MultSystem — the system multiplication makes

Not "ℕ⁺ with × bolted on" (which forces the unit `1` to be an exception), but
**the structure `×` itself generates**: monomials over a set of bases, graded by
total count.  Over bases `a, b, c, …` the elements are

```
1 base   : a, aa, aaa, …                                  (= ℕ⁺, count = the number)
2 bases  : a, b, ab, aa, bb, aaa, aab, abb, bbb, …
3 bases  : a, b, c, aa, ab, ac, bb, bc, cc, aaa, …
```

each written once in canonical (sorted) form — `aab` not `aba` — i.e. a
**multiset** over the bases.  The carrier here is the exponent vector
(`Mono := List Nat`, entry `i` = multiplicity of base `i`); `×` is exponent-wise
addition (`mul`); and the **total count `deg` is the projection to ℕ** under which
`×` becomes `+` (`deg_mul`) and each base is an atom of count `1` (`deg_unit`).
So "a natural number is the count-projection of a multiplicative element."

The same frame at `|bases| = ∞ (primes)` is `Meta/Nat/ExpVector.lean`; ℕ⁺ is its
count-projection (forget which prime, keep total degree).  Counting layer:
`monoCount k n` = number of degree-`n` monomials over `k` bases, with the
**per-base increment** `monoCount_base_increment` — the user's question "how much
is added each time a base appears" — falling straight out of the recurrence.

`^` does *not* fit this frame: `a^b ≠ b^a`, so permutations do not collapse to a
multiset — which is exactly why `^` is a different system (the `^`-wall).

∅-axiom standard; no Mathlib, no Classical, no propext / Quot.sound.
-/

namespace E213.Lens.Number.Nat213.MultSystem

/-! ## The carrier and the operation -/

/-- A monomial / multiset over the bases, as an exponent vector:
    entry `i` = multiplicity of base `i`. -/
abbrev Mono := List Nat

/-- Total count of a monomial = sum of exponents.  **The projection to ℕ.** -/
def deg : Mono → Nat
  | []      => 0
  | x :: xs => x + deg xs

/-- `×` on the system = exponent-wise addition (combine the multisets).
    Padding makes the all-zero vector `[]` a two-sided identity. -/
def mul : Mono → Mono → Mono
  | [],      f       => f
  | x :: e', []      => x :: e'
  | x :: e', y :: f' => (x + y) :: mul e' f'

/-- **The count projection is a homomorphism: `×` becomes `+`.**  `deg (a × b) =
    deg a + deg b`.  This is "a natural number is the count-projection of a
    multiplicative element", formalized. -/
theorem deg_mul : ∀ e f : Mono, deg (mul e f) = deg e + deg f
  | [],      f       => by
      show deg f = 0 + deg f
      rw [Nat.zero_add]
  | x :: e', []      => by
      show deg (x :: e') = deg (x :: e') + 0
      rw [Nat.add_zero]
  | x :: e', y :: f' => by
      show (x + y) + deg (mul e' f') = (x + deg e') + (y + deg f')
      rw [deg_mul e' f', Nat.add_add_add_comm]

/-- The `i`-th base (generator): exponent `1` at position `i`. -/
def unit : Nat → Mono
  | 0     => [1]
  | i + 1 => 0 :: unit i

/-- **Each base is an atom of count `1`.**  `deg (unit i) = 1`. -/
theorem deg_unit : ∀ i, deg (unit i) = 1
  | 0     => rfl
  | i + 1 => by
      show 0 + deg (unit i) = 1
      rw [Nat.zero_add, deg_unit i]

/-! ## Counting — how many degree-`n` monomials over `k` bases

`monoCount k n` counts the degree-`n` monomials over `k` bases by the
stars-and-bars recurrence: fix the last base's exponent `j ∈ {0,…,n}` and recurse
on the remaining `k` bases at degree `n − j`, i.e. `Σ_{i=0}^{n} monoCount k i`. -/

/-- `sumf g n = Σ_{i=0}^{n} g i`. -/
def sumf (g : Nat → Nat) : Nat → Nat
  | 0     => g 0
  | n + 1 => sumf g n + g (n + 1)

/-- Number of degree-`n` monomials over `k` bases.  `0` bases generate only the
    empty monomial (degree `0`); each extra base sums over the last exponent. -/
def monoCount : Nat → Nat → Nat
  | 0,     0     => 1
  | 0,     _ + 1 => 0
  | k + 1, n     => sumf (fun i => monoCount k i) n

/-- One base: exactly one monomial per degree (`a, aa, aaa, …`) — this *is* ℕ⁺. -/
theorem monoCount_one : ∀ n, monoCount 1 n = 1
  | 0     => rfl
  | n + 1 => by
      show sumf (fun i => monoCount 0 i) n + monoCount 0 (n + 1) = 1
      rw [show monoCount 0 (n + 1) = 0 from rfl, Nat.add_zero]
      exact monoCount_one n

/-- Two bases: `n + 1` monomials of degree `n` (`a,b` / `aa,ab,bb` / …). -/
theorem monoCount_two : ∀ n, monoCount 2 n = n + 1
  | 0     => rfl
  | n + 1 => by
      show sumf (fun i => monoCount 1 i) n + monoCount 1 (n + 1) = (n + 1) + 1
      rw [monoCount_one (n + 1)]
      show monoCount 2 n + 1 = (n + 1) + 1
      rw [monoCount_two n]

/-- Per-degree Pascal step (a building block, *not* the per-base increase):
    `monoCount (k+1) (n+1) = monoCount k (n+1) + monoCount (k+1) n`. -/
theorem monoCount_pascal (k n : Nat) :
    monoCount (k + 1) (n + 1) = monoCount k (n + 1) + monoCount (k + 1) n :=
  Nat.add_comm _ _

/-! ### Cumulative total — "all the monomials up to degree N" (the summation)

The increase from adding a base is **not** a per-degree comparison; it is the
comparison of the *running totals*.  `totalCount k N = Σ_{n=0}^{N} monoCount k n`
= the number of monomials of degree ≤ N over `k` bases ("모든 갯수").  Elegantly,
this cumulative total over `k` bases equals the per-degree count over `k+1`
bases — the dimension shift `Σ` performs. -/

/-- Total monomials of degree ≤ `N` over `k` bases: `Σ_{n=0}^{N} monoCount k n`. -/
def totalCount (k N : Nat) : Nat := sumf (fun n => monoCount k n) N

/-- The running total over `k` bases = the per-degree count over `k+1` bases. -/
theorem totalCount_eq (k N : Nat) : totalCount k N = monoCount (k + 1) N := rfl

/-- `1` base: total up to `N` is `N + 1` (degrees `0..N`, one monomial each). -/
theorem totalCount_one (N : Nat) : totalCount 1 N = N + 1 := monoCount_two N

/-- **Per-base increase, on the totals** (the right comparison).  Adding one base
    raises the total-up-to-degree-`(N+1)` by exactly the `(k+1)`-base total up to
    `N`:

    `totalCount (k+1) (N+1) = totalCount k (N+1) + totalCount (k+1) N`,

    i.e. `totalCount (k+1) (N+1) − totalCount k (N+1) = totalCount (k+1) N` —
    the increase from one more base is "the same system, one degree lower."
    Concretely `k = 1`: `totalCount 2 (N+1) − totalCount 1 (N+1) = totalCount 2 N`. -/
theorem totalCount_base_increment (k N : Nat) :
    totalCount (k + 1) (N + 1) = totalCount k (N + 1) + totalCount (k + 1) N :=
  monoCount_pascal (k + 1) N

/-! ### Closed form — the count formula `C(N+k, k)`

The running total over `k` bases up to degree `N` is the binomial coefficient
`binom (N+k) k`.  Proof: hockey-stick on Pascal's triangle. -/

/-- Binomial coefficient via Pascal recursion (repo-native, `GenerationCount`
    carries the same; local copy keeps this file dependency-light). -/
def binom : Nat → Nat → Nat
  | _,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

/-- `binom n 0 = 1` for every `n` (the def splits on the first argument, so this
    is not definitional for a variable `n`). -/
theorem binom_zero (n : Nat) : binom n 0 = 1 := by cases n <;> rfl

/-- Pascal step (the defining recursion). -/
theorem binom_succ (n k : Nat) : binom (n + 1) (k + 1) = binom n k + binom n (k + 1) := rfl

/-- `binom n m = 0` when `n < m`. -/
theorem binom_zero_of_lt : ∀ {n m : Nat}, n < m → binom n m = 0
  | n,     0,     h => absurd h (Nat.not_lt_zero n)
  | 0,     _ + 1, _ => rfl
  | n + 1, m + 1, h => by
      show binom n m + binom n (m + 1) = 0
      rw [binom_zero_of_lt (Nat.lt_of_succ_lt_succ h),
          binom_zero_of_lt (Nat.lt_succ_of_lt (Nat.lt_of_succ_lt_succ h))]

/-- `binom n n = 1` (the diagonal). -/
theorem binom_self : ∀ n, binom n n = 1
  | 0     => rfl
  | n + 1 => by
      show binom n n + binom n (n + 1) = 1
      rw [binom_self n, binom_zero_of_lt (Nat.lt_succ_self n)]

/-- **Row bound**: `C(n,k) ≤ 2^n` (every binomial is at most the row sum). -/
theorem binom_le_two_pow : ∀ (n k : Nat), binom n k ≤ 2 ^ n
  | 0,     0     => Nat.le_refl 1
  | 0,     _ + 1 => Nat.zero_le _
  | n + 1, 0     => by rw [binom_zero]; exact Nat.pos_pow_of_pos (n + 1) (by decide)
  | n + 1, k + 1 => by
      show binom n k + binom n (k + 1) ≤ 2 ^ (n + 1)
      calc binom n k + binom n (k + 1)
            ≤ 2 ^ n + 2 ^ n := Nat.add_le_add (binom_le_two_pow n k) (binom_le_two_pow n (k + 1))
        _ = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_two]

/-- **Central binomial bound** `C(2n,n) ≤ 4^n` (= `2^{2n}`) — the Chebyshev
    upper-estimate ingredient (every prime in `(n,2n]` divides `C(2n,n) ≤ 4^n`). -/
theorem central_binom_le (n : Nat) : binom (2 * n) n ≤ 2 ^ (2 * n) :=
  binom_le_two_pow (2 * n) n

/-- Pointwise-equal summands give equal sums. -/
theorem sumf_congr (f g : Nat → Nat) (h : ∀ i, f i = g i) :
    ∀ n, sumf f n = sumf g n
  | 0     => h 0
  | n + 1 => by
      show sumf f n + f (n + 1) = sumf g n + g (n + 1)
      rw [sumf_congr f g h n, h (n + 1)]

/-- **Hockey-stick**: `Σ_{i=0}^{n} C(i+k, k) = C(n+k+1, k+1)`. -/
theorem hockey : ∀ (k n : Nat),
    sumf (fun i => binom (i + k) k) n = binom (n + k + 1) (k + 1)
  | k, 0     => by
      show binom (0 + k) k = binom (0 + k + 1) (k + 1)
      rw [Nat.zero_add, binom_self, binom_self]
  | k, n + 1 => by
      show sumf (fun i => binom (i + k) k) n + binom ((n + 1) + k) k
            = binom ((n + 1) + k + 1) (k + 1)
      rw [hockey k n, Nat.succ_add n k]
      show binom ((n + k) + 1) (k + 1) + binom ((n + k) + 1) k
            = binom ((n + k) + 1) k + binom ((n + k) + 1) (k + 1)
      exact Nat.add_comm _ _

/-- **Count formula** for the per-degree count: `monoCount (k+1) N = C(N+k, k)`. -/
theorem monoCount_closed : ∀ (k N : Nat), monoCount (k + 1) N = binom (N + k) k
  | 0,     N => by rw [monoCount_one, binom_zero]
  | k + 1, N => by
      show sumf (fun i => monoCount (k + 1) i) N = binom (N + (k + 1)) (k + 1)
      rw [sumf_congr (fun i => monoCount (k + 1) i) (fun i => binom (i + k) k)
            (fun i => monoCount_closed k i) N, hockey k N, Nat.add_assoc N k 1]

/-- **The count formula** (the user's "공식"): the total number of monomials of
    degree ≤ `N` over `k` bases is `C(N+k, k)`.  `totalCount k N = binom (N+k) k`.
    With `totalCount_base_increment`, the per-base increase `C(N+k+1, k+1) −
    C(N+k, k) = C(N+k, k+1)` is Pascal's identity. -/
theorem totalCount_closed (k N : Nat) : totalCount k N = binom (N + k) k :=
  monoCount_closed k N

/-! ### Cutting both axes at `N` — the double sum collapses to a central binomial

Capping *both* the number of bases `k` and the degree `n` at `N` and summing all
the monomial counts gives a single central binomial coefficient `C(2N+1, N)`.
Needs the **diagonal** hockey-stick `Σ_{k=0}^{M} C(N+k, k) = C(N+M+1, M)` (the
previous `hockey` sums the top index; this sums the bottom). -/

/-- Diagonal hockey-stick: `Σ_{k=0}^{M} C(N+k, k) = C(N+M+1, M)`. -/
theorem hockeyDiag : ∀ (N M : Nat),
    sumf (fun k => binom (N + k) k) M = binom (N + M + 1) M
  | N, 0     => by
      show binom (N + 0) 0 = binom (N + 0 + 1) 0
      rw [binom_zero, binom_zero]
  | N, M + 1 => by
      show sumf (fun k => binom (N + k) k) M + binom (N + (M + 1)) (M + 1)
            = binom (N + (M + 1) + 1) (M + 1)
      rw [hockeyDiag N M, binom_succ (N + (M + 1)) M, Nat.add_assoc N M 1]

/-- Sum of every monomial count with both `k ≤ N` and `n ≤ N`:
    `Σ_{k=0}^{N} totalCount k N = Σ_{k=0}^{N} Σ_{n=0}^{N} monoCount k n`. -/
def doubleTotal (N : Nat) : Nat := sumf (fun k => totalCount k N) N

/-- **Both axes cut at `N` ⇒ central binomial.**  `doubleTotal N = C(2N+1, N)`.
    The user's strictly-positive sum `Σ_{k=1}^{N} Σ_{n=1}^{N} monoCount k n` is
    this minus the `0`-boundary (`k=0` row contributes `1`, `n=0` column another
    `N`), i.e. `C(2N+1, N) − N − 1`. -/
theorem doubleTotal_closed (N : Nat) : doubleTotal N = binom (2 * N + 1) N := by
  show sumf (fun k => totalCount k N) N = binom (2 * N + 1) N
  rw [sumf_congr (fun k => totalCount k N) (fun k => binom (N + k) k)
        (fun k => totalCount_closed k N) N, hockeyDiag N N, Nat.two_mul]

/-! ### Strictly-positive (1-indexed) double sum

The user's sum ranges `k, n ∈ {1,…,N}` (no `0` row/column).  `sumf1 g n =
Σ_{i=1}^{n} g i`.  The strictly-positive double sum `doubleSumPos N` then
satisfies `doubleSumPos N + N + 1 = C(2N+1, N)` — i.e. `#(Nmul) + (N+1) = #ℕ`-cap
in the additive (subtraction-free) form, so `#(Nmul) = C(2N+1,N) − N − 1`. -/

/-- `sumf1 g n = Σ_{i=1}^{n} g i` (starts at `1`, excludes the `0` term). -/
def sumf1 (g : Nat → Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => sumf1 g n + g (n + 1)

/-- Split off the `0` term: `Σ_{i=0}^n = g 0 + Σ_{i=1}^n`. -/
theorem sumf_split (f : Nat → Nat) : ∀ n, sumf f n = f 0 + sumf1 f n
  | 0     => by show f 0 = f 0 + 0; rw [Nat.add_zero]
  | n + 1 => by
      show sumf f n + f (n + 1) = f 0 + (sumf1 f n + f (n + 1))
      rw [sumf_split f n, Nat.add_assoc]

/-- `Σ_{i=0}^n (1 + h i) = (n+1) + Σ_{i=0}^n h i`. -/
theorem sumf_one_add (h : Nat → Nat) :
    ∀ n, sumf (fun k => 1 + h k) n = (n + 1) + sumf h n
  | 0     => rfl
  | n + 1 => by
      show sumf (fun k => 1 + h k) n + (1 + h (n + 1))
            = ((n + 1) + 1) + (sumf h n + h (n + 1))
      rw [sumf_one_add h n, Nat.add_add_add_comm]

/-- The `k = 0` (no-base) column sums to `0` over strictly-positive degrees. -/
theorem sumf1_monoCount0 : ∀ N, sumf1 (fun n => monoCount 0 n) N = 0
  | 0     => rfl
  | N + 1 => by
      show sumf1 (fun n => monoCount 0 n) N + 0 = 0
      rw [Nat.add_zero, sumf1_monoCount0 N]

/-- Every base count has exactly one degree-`0` monomial (the unit). -/
theorem monoCount_col0 : ∀ k, monoCount k 0 = 1
  | 0     => rfl
  | k + 1 => monoCount_col0 k

/-- `totalCount` with the degree-`0` term split off: `= 1 + Σ_{n=1}^N`. -/
theorem totalCount_split (k N : Nat) :
    totalCount k N = 1 + sumf1 (fun n => monoCount k n) N := by
  show sumf (fun n => monoCount k n) N = 1 + sumf1 (fun n => monoCount k n) N
  rw [sumf_split (fun n => monoCount k n) N]
  show monoCount k 0 + sumf1 (fun n => monoCount k n) N
        = 1 + sumf1 (fun n => monoCount k n) N
  rw [monoCount_col0]

/-- Strictly-positive double sum `Σ_{k=1}^{N} Σ_{n=1}^{N} monoCount k n`. -/
def doubleSumPos (N : Nat) : Nat :=
  sumf1 (fun k => sumf1 (fun n => monoCount k n) N) N

/-- **The user's count** (1-indexed), subtraction-free: `#(Nmul) + (N+1) = C(2N+1,N)`,
    i.e. `Σ_{k=1}^N Σ_{n=1}^N monoCount k n = C(2N+1, N) − N − 1`.  Cutting both
    axes at `N`, the strictly-positive multiplicative count is the central
    binomial minus the `(N+1)` boundary. -/
theorem doubleSumPos_closed (N : Nat) :
    doubleSumPos N + N + 1 = binom (2 * N + 1) N := by
  have step : binom (2 * N + 1) N
      = sumf (fun k => 1 + sumf1 (fun n => monoCount k n) N) N := by
    rw [← doubleTotal_closed]
    exact sumf_congr (fun k => totalCount k N)
      (fun k => 1 + sumf1 (fun n => monoCount k n) N)
      (fun k => totalCount_split k N) N
  rw [sumf_one_add (fun k => sumf1 (fun n => monoCount k n) N) N,
      sumf_split (fun k => sumf1 (fun n => monoCount k n) N) N] at step
  show doubleSumPos N + N + 1 = binom (2 * N + 1) N
  rw [step]
  show doubleSumPos N + N + 1
        = (N + 1) + (sumf1 (fun n => monoCount 0 n) N + doubleSumPos N)
  rw [sumf1_monoCount0 N, Nat.zero_add, Nat.add_comm (N + 1) (doubleSumPos N),
      Nat.add_assoc]

end E213.Lens.Number.Nat213.MultSystem
