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

/-! ### Dimension without ∞ — the finite-difference depth

The "dimension" of the rung need not be written as a cardinal (`+`:1, `×`:∞).
Read it off **how the graded count moves under degree-differencing**: the
degree-difference of rung `k+1` is rung `k` (`diff_drops_rung`), so each
difference **drops the dimension by one**.  Hence the dimension is the number of
differences that annihilate the count: `+` (rung 1) is constant already
(`monoCount 1 = 1`, 0 differences → 1-dimensional); `×` (the `∞`-generator
limit) is the count whose difference-tower **never terminates** — "infinite
dimension" as a *non-terminating finite-difference tower*, not a cardinal.  (The
generating-function dual: differencing ↔ multiplying by `(1−x)`; the rung's
Hilbert series is `(1−x)^{−k}`, dimension = pole order at `x=1`, and `×`'s
essential singularity there is the Euler product `∏_p` = `ζ`.) -/

/-- The graded count is non-decreasing in the degree (Pascal: each step adds the
    next-lower rung). -/
theorem monoCount_mono_deg (k d : Nat) :
    monoCount (k + 1) d ≤ monoCount (k + 1) (d + 1) := by
  rw [monoCount_pascal]
  exact Nat.le_add_left _ _

/-- ★ **The degree-difference drops the rung by one** — the dimension step,
    subtraction-free-grounded.  `monoCount (k+1)(d+1) − monoCount (k+1) d =
    monoCount k (d+1)`: differencing the graded count in the degree returns the
    next-lower rung (`monoCount_pascal` then cancel).  So the dimension is the
    finite-difference depth — `k+1` differences send rung `k+1` to the zero rung
    (`monoCount 0`), the constructive reading of "dimension" with no cardinal `∞`. -/
theorem diff_drops_rung (k d : Nat) :
    monoCount (k + 1) (d + 1) - monoCount (k + 1) d = monoCount k (d + 1) := by
  rw [monoCount_pascal]
  exact E213.Tactic.NatHelper.add_sub_cancel_right (monoCount k (d + 1)) (monoCount (k + 1) d)

/-! #### The finite-difference dimension detector (computational)

Dimension is **computed**, not posited.  The forward difference `Δf(d) =
f(d+1) − f(d)`, iterated, peels one rung per step (`diffIter_monoCount`), so
`Δ^{k+1}` annihilates the rung-`(k+1)` count (`diffIter_dim_zero`) while `Δ^k`
leaves the constant `1` (`diffIter_dim_const`).  The **dimension `= k+1` = the
least difference-depth that annihilates** — read off by finite arithmetic, no
cardinal `∞`.  (On the non-decreasing `monoCount` sequences every intermediate
difference is again a `monoCount`, so the `Nat`-truncated subtraction is exact
throughout.) -/

/-- Forward difference of a sequence (pointwise; exact on non-decreasing seqs). -/
def diff (f : Nat → Nat) : Nat → Nat := fun d => f (d + 1) - f d

/-- The iterated forward difference `Δ^j`. -/
def diffIter (f : Nat → Nat) : Nat → (Nat → Nat)
  | 0     => f
  | j + 1 => diff (diffIter f j)

/-- ★ **`Δ^j` peels `j` rungs (shifted).**  For `j < N`, `Δ^j (monoCount N)(d) =
    monoCount (N−j)(d+j)` — each difference drops the rung by one
    (`diff_drops_rung`), `j` of them drop `j`.  Pointwise (no `funext`), induction
    on `j` with `N` fixed. -/
theorem diffIter_monoCount : ∀ (N j : Nat), j < N → ∀ d,
    diffIter (monoCount N) j d = monoCount (N - j) (d + j)
  | _, 0,     _,  d => by
      show monoCount _ d = monoCount _ (d + 0)
      rw [Nat.sub_zero, Nat.add_zero]
  | N, j + 1, hj, d => by
      have hjN : j < N := Nat.lt_of_succ_lt hj
      have hsub : (N - (j + 1)) + 1 = N - j := by
        rw [Nat.sub_succ]
        exact Nat.succ_pred_eq_of_pos (E213.Tactic.NatHelper.sub_pos_of_lt hjN)
      show (diffIter (monoCount N) j) (d + 1) - (diffIter (monoCount N) j) d
            = monoCount (N - (j + 1)) (d + (j + 1))
      rw [diffIter_monoCount N j hjN (d + 1), diffIter_monoCount N j hjN d,
          ← hsub, Nat.add_right_comm d 1 j, diff_drops_rung (N - (j + 1)) (d + j),
          Nat.add_assoc d j 1]

/-- ★ **`Δ^k` lands on the constant `1`** (the dimension-`(k+1)` floor): `Δ^k
    (monoCount (k+1))(d) = 1`.  After `k` differences the rung-`(k+1)` count has
    been peeled down to rung `1` = `ℕ⁺` = the constant sequence `1`
    (`monoCount_one`). -/
theorem diffIter_dim_const (k d : Nat) : diffIter (monoCount (k + 1)) k d = 1 := by
  rw [diffIter_monoCount (k + 1) k (Nat.lt_succ_self k) d,
      show (k + 1) - k = 1 by rw [Nat.add_comm k 1]; exact E213.Tactic.NatHelper.add_sub_cancel_right 1 k]
  exact monoCount_one (d + k)

/-- ★★ **`Δ^{k+1}` annihilates the rung — the computed dimension.**  `Δ^{k+1}
    (monoCount (k+1))(d) = 0`: one difference past the constant floor kills it
    (`1 − 1 = 0`).  So the dimension of the rung-`(k+1)` count *is* `k+1` =
    the least difference-depth at which it vanishes — `∞` for the `×`-limit
    becomes "the depth never reached", computed, not enshrined. -/
theorem diffIter_dim_zero (k d : Nat) : diffIter (monoCount (k + 1)) (k + 1) d = 0 := by
  show (diffIter (monoCount (k + 1)) k) (d + 1) - (diffIter (monoCount (k + 1)) k) d = 0
  rw [diffIter_dim_const k (d + 1), diffIter_dim_const k d]

/-! #### `Δ` and `Σ` are the dimension ∓1 operators (the discrete calculus)

The difference `Δ` (lowers the rung, `diff_drops_rung`) and the partial sum `Σ`
(`sumf`, raises it, `totalCount_eq`) are an **inverse pair** on the dimension
tower — the discrete derivative/integral.  `Σ` adds a generator (rung `k → k+1`,
`+1` dimension); `Δ` removes one (`k+1 → k`).  Their composite is the **discrete
fundamental theorem** `Δ(Σf) = shift` (`diff_sumf`), the telescoping identity. -/

/-- ★ **Discrete fundamental theorem: `Δ ∘ Σ = shift`.**  `diff (sumf f) d =
    f (d+1)` — differencing the running sum returns the summand (telescoping).
    With `totalCount_eq` (`Σ` raises the rung) and `diff_drops_rung` (`Δ` lowers
    it), `Δ`/`Σ` move ∓1 along the dimension tower: the finite-calculus pair that
    computes dimension up and down with no cardinal `∞`. -/
theorem diff_sumf (f : Nat → Nat) (d : Nat) : diff (sumf f) d = f (d + 1) := by
  show (sumf f d + f (d + 1)) - sumf f d = f (d + 1)
  rw [Nat.add_comm]
  exact E213.Tactic.NatHelper.add_sub_cancel_right (f (d + 1)) (sumf f d)

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

/-! #### `Σ^k` builds the rung from `1` — the dual of `Δ^k` annihilating

The pole-order / generating-function content `monoCount(k+1) ↔ (1−x)^{−(k+1)}`,
computed **without formal power series**: applying the partial sum `Σ` (`sumf`)
`k` times to the constant sequence `1` *builds* the rung-`(k+1)` count
(`sumfIter_const_one`).  Each `Σ` is one `×(1−x)^{−1}` = one pole-order = one
dimension, so `Σ^k 1 = monoCount(k+1)` is the `(1−x)^{−(k+1)}` expansion as
iterated summation — the exact dual of `Δ^{k+1}` annihilating it
(`diffIter_dim_zero`). -/

/-- The iterated partial sum `Σ^k`. -/
def sumfIter (f : Nat → Nat) : Nat → (Nat → Nat)
  | 0     => f
  | k + 1 => sumf (sumfIter f k)

/-- ★★ **`Σ^k 1 = monoCount(k+1)`** — the rung built from the constant by iterated
    summation (the `(1−x)^{−(k+1)}` Hilbert series, computed).  Each `Σ` raises the
    rung by one (`totalCount_eq`); `k` of them build rung `k+1` from rung `1` (`=
    ℕ⁺ =` the constant `1`, `monoCount_one`).  Pointwise (no `funext`); the dual of
    `diffIter_dim_zero`. -/
theorem sumfIter_const_one : ∀ (k d : Nat),
    sumfIter (fun _ => 1) k d = monoCount (k + 1) d
  | 0,     d => (monoCount_one d).symm
  | k + 1, d => by
      show sumf (sumfIter (fun _ => 1) k) d = monoCount (k + 1 + 1) d
      rw [sumf_congr (sumfIter (fun _ => 1) k) (monoCount (k + 1))
            (fun i => sumfIter_const_one k i) d]
      exact totalCount_eq (k + 1) d

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

/-- ★ **Vertices = generators = axes** — the unifying anchor.  `monoCount k 1 = k`:
    the degree-`1` elements are exactly the `k` generators (each base once), so the
    rung over `k` bases is the cone over the **`(k−1)`-simplex** — `k` vertices.  This
    pins the *generative* simplex (L3) to the *demotion* lattice (R4,
    `number_tower_theory.md`): the `k` simplex vertices **are** the `k` independent
    lattice axes.  Hence `+` (`k = 1`, `monoCount 1 1 = 1`) is the cone over a single
    vertex (the 0-simplex = the point, the ray ℕ⁺); `×` (`k → ∞`, the prime axes) is
    the cone over the **∞-simplex** — already infinite-dimensional, no finite figure. -/
theorem monoCount_vertices : ∀ k, monoCount k 1 = k
  | 0     => rfl
  | k + 1 => by
      show monoCount k 0 + monoCount k 1 = k + 1
      rw [monoCount_col0, monoCount_vertices k, Nat.add_comm]

/-- **A calculation bound: sorted-readings ≤ ordered-readings**, `monoCount t d ≤
    t^d`.  `monoCount t d` = the *sorted* readings (multisets = the simplex slice
    over `t` generators at degree `d`); `t^d` = the *ordered* readings (length-`d`
    strings over `t` symbols).  Sorting `aba ↦ aab` surjects strings ↠ multisets, so
    sorted never exceeds ordered.  **NB (framing):** these are two *reference
    readings* of one generating set — a fast-calculation comparison, a
    one-dimensional cross-section (arrangement-forgetting is a *shadow*,
    `theory/essays/analysis/where_commutativity_is_born.md`).  It does **not** assert
    a higher rung 'is' the ordered/`t^d` structure; a rung's intrinsic form is its
    own (higher-dimensional) simplex + twist (`simplicial_operation_tower.md` L5).
    Nested induction on `(d,t)` via `monoCount (t+1)(d+1) = monoCount t (d+1) +
    monoCount (t+1) d`: `≤ t^{d+1} + (t+1)^d ≤ (t+1)^{d+1}` (since `t^d ≤ (t+1)^d`). -/
theorem monoCount_le_pow : ∀ d t, monoCount t d ≤ t ^ d := by
  intro d
  induction d with
  | zero =>
      intro t
      rw [monoCount_col0 t]
      exact Nat.le_of_eq (Nat.pow_zero t).symm
  | succ d ihd =>
      intro t
      induction t with
      | zero => exact Nat.zero_le _
      | succ t iht =>
          rw [monoCount_pascal t d]
          have hp : t ^ (d + 1) ≤ t * (t + 1) ^ d := by
            rw [Nat.pow_succ, Nat.mul_comm (t ^ d) t]
            exact Nat.mul_le_mul (Nat.le_refl t) (Nat.pow_le_pow_left (Nat.le_succ t) d)
          have hstep : t ^ (d + 1) + (t + 1) ^ d ≤ (t + 1) ^ (d + 1) :=
            calc t ^ (d + 1) + (t + 1) ^ d
                ≤ t * (t + 1) ^ d + (t + 1) ^ d := Nat.add_le_add_right hp _
              _ = (t + 1) ^ (d + 1) := by
                  rw [Nat.pow_succ, Nat.mul_succ, Nat.mul_comm t ((t + 1) ^ d)]
          exact Nat.le_trans (Nat.add_le_add iht (ihd (t + 1))) hstep

/-- Base-strict power monotonicity: `sᵉ⁺¹ < (s+1)ᵉ⁺¹` (pure; no
    `Nat.pow_lt_pow_left` in core). -/
theorem pow_succ_lt_pow_succ (s : Nat) : ∀ e, s ^ (e + 1) < (s + 1) ^ (e + 1)
  | 0     => by rw [Nat.pow_one, Nat.pow_one]; exact Nat.lt_succ_self s
  | e + 1 => by
      have ih := pow_succ_lt_pow_succ s e
      have hrw : (s + 1) ^ (e + 1 + 1) = (s + 1) ^ (e + 1) * s + (s + 1) ^ (e + 1) := by
        rw [Nat.pow_succ, Nat.mul_succ]
      rw [Nat.pow_succ, hrw]
      calc s ^ (e + 1) * s ≤ (s + 1) ^ (e + 1) * s := Nat.mul_le_mul (Nat.le_of_lt ih) (Nat.le_refl s)
        _ < (s + 1) ^ (e + 1) * s + (s + 1) ^ (e + 1) :=
            Nat.lt_add_of_pos_right (Nat.pos_pow_of_pos (e + 1) (Nat.succ_pos s))

/-- `sᵉ < (s+1)ᵉ` for `e ≥ 1`. -/
theorem pow_lt_pow_base (s : Nat) {e : Nat} (he : 1 ≤ e) : s ^ e < (s + 1) ^ e := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, (Nat.succ_pred_eq_of_pos he).symm⟩
  exact pow_succ_lt_pow_succ s e'

/-- **Strict form: sorted-readings `<` ordered-readings** for `t ≥ 2`, `d ≥ 2`:
    `monoCount t d < t^d`.  Sorting genuinely identifies distinct strings
    (`ab`/`ba ↦ {a,b}`) once two distinguishable atoms each appear, so the two
    reference readings differ.  (Same NB as `monoCount_le_pow`: a cross-section
    comparison, not a claim about a higher rung's intrinsic structure.) -/
theorem monoCount_lt_pow {t d : Nat} (ht : 2 ≤ t) (hd : 2 ≤ d) : monoCount t d < t ^ d := by
  cases t with
  | zero => exact absurd ht (by decide)
  | succ s =>
      cases d with
      | zero => exact absurd hd (by decide)
      | succ e =>
          have hs : 1 ≤ s := Nat.le_of_succ_le_succ ht
          have he : 1 ≤ e := Nat.le_of_succ_le_succ hd
          rw [monoCount_pascal s e]
          have hbase : s ^ e + 1 ≤ (s + 1) ^ e := pow_lt_pow_base s he
          have hle : (s ^ e + 1) * s ≤ (s + 1) ^ e * s := Nat.mul_le_mul hbase (Nat.le_refl s)
          rw [Nat.succ_mul] at hle
          have hpe1 : s ^ (e + 1) < (s + 1) ^ e * s := by
            rw [Nat.pow_succ]
            exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hs) hle
          have hrw : (s + 1) ^ (e + 1) = (s + 1) ^ e * s + (s + 1) ^ e := by
            rw [Nat.pow_succ, Nat.mul_succ]
          have hstrict : s ^ (e + 1) + (s + 1) ^ e < (s + 1) ^ (e + 1) := by
            rw [hrw]; exact Nat.add_lt_add_right hpe1 _
          exact Nat.lt_of_le_of_lt
            (Nat.add_le_add (monoCount_le_pow (e + 1) s) (monoCount_le_pow e (s + 1))) hstrict

/-- `Σ_{i≤n} f i ≤ (n+1)·c` when each summand `≤ c`. -/
theorem sumf_le_bound {f : Nat → Nat} {c : Nat} :
    ∀ n, (∀ i, i ≤ n → f i ≤ c) → sumf f n ≤ (n + 1) * c
  | 0,     h => by
      show f 0 ≤ (0 + 1) * c
      calc f 0 ≤ c := h 0 (Nat.le_refl 0)
        _ = (0 + 1) * c := by rw [Nat.succ_mul, Nat.zero_mul, Nat.zero_add]
  | n + 1, h => by
      show sumf f n + f (n + 1) ≤ (n + 1 + 1) * c
      calc sumf f n + f (n + 1)
          ≤ (n + 1) * c + c :=
            Nat.add_le_add (sumf_le_bound n (fun i hi => h i (Nat.le_succ_of_le hi)))
              (h (n + 1) (Nat.le_refl _))
        _ = (n + 1 + 1) * c := (Nat.succ_mul (n + 1) c).symm

/-- **The simplex slice count is polynomial in the degree**: `monoCount t d ≤
    (d+1)^t` — for a fixed generator count `t`, the count grows as a *polynomial* in
    the degree `d` (degree `t`).  A positive fact about the simplex's own growth
    (its intrinsic value is the multiset coefficient `C(d+t−1,t−1)`,
    `monoCount_closed`); with `monoCount_le_pow` it brackets the count `≤ (d+1)^t`
    and `≤ t^d`.  Induction on `t`: `monoCount (t+1) d = Σ_{i≤d} monoCount t i ≤
    (d+1)·(d+1)^t`. -/
theorem monoCount_le_succ_pow : ∀ t d, monoCount t d ≤ (d + 1) ^ t := by
  intro t
  induction t with
  | zero =>
      intro d
      cases d with
      | zero => exact Nat.le_refl 1
      | succ e => exact Nat.zero_le _
  | succ t iht =>
      intro d
      show sumf (fun i => monoCount t i) d ≤ (d + 1) ^ (t + 1)
      have hbound : ∀ i, i ≤ d → monoCount t i ≤ (d + 1) ^ t := fun i hi =>
        Nat.le_trans (iht i) (Nat.pow_le_pow_left (Nat.succ_le_succ hi) t)
      calc sumf (fun i => monoCount t i) d
          ≤ (d + 1) * (d + 1) ^ t := sumf_le_bound d hbound
        _ = (d + 1) ^ (t + 1) := by rw [Nat.pow_succ]; exact Nat.mul_comm (d + 1) ((d + 1) ^ t)

/-- `totalCount` with the degree-`0` term split off: `= 1 + Σ_{n=1}^N`. -/
theorem totalCount_split (k N : Nat) :
    totalCount k N = 1 + sumf1 (fun n => monoCount k n) N := by
  show sumf (fun n => monoCount k n) N = 1 + sumf1 (fun n => monoCount k n) N
  rw [sumf_split (fun n => monoCount k n) N]
  show monoCount k 0 + sumf1 (fun n => monoCount k n) N
        = 1 + sumf1 (fun n => monoCount k n) N
  rw [monoCount_col0]

/-- **The no-identity decomposition (L2)**: the *natural* object is the **semigroup**
    — the degree-`≥1` monomials, count `Σ_{n=1}^N monoCount k n` (built from
    `(bases, ×)` alone) — and the full **monoid** count is exactly that **plus one**:
    `Σ_{n=1}^N monoCount k n + 1 = C(N+k, k)`.  The `+1` is the single degree-`0`
    monomial (the empty product = the identity, `monoCount_col0`), adjoined as an
    *exception* to the otherwise self-contained semigroup. -/
theorem monoCountPos_closed (k N : Nat) :
    sumf1 (fun n => monoCount k n) N + 1 = binom (N + k) k := by
  have h := totalCount_split k N
  rw [totalCount_closed k N] at h
  rw [h]; exact Nat.add_comm _ _

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

/-! ## Stacking the next rung — the layer rule applied directly (L1)

`×` took the `+`-rung's **elements** as axes and stacked their degree-graded
multisets.  Apply the *same* rule one more time: `^` takes the `×`-rung's elements
as axes.  The `×`-monomials of degree `≤ N` over `k` `+`-bases number
`totalCount k N`; the `^`-rung over them, at degree `d`, is their degree-`d`
multiset count — built directly. -/

/-- The `^`-rung built by the layer rule: degree-`d` multisets of `×`-monomials
    (the `×`-monomials of degree `≤ N` over `k` `+`-bases as the axis set).

    This is the **abstract axis-count** reading of the `^`-rung (the symmetric
    skeleton, which stays simplicial — `hyperCount_simplex`).  Its **geometric
    value** sibling is the object `Meta/Nat/UnitHyper`: `count (hcube a b) =
    a^b = side ^ dim`, where the base/exponent twist (here folded away as the
    symmetric multiset count) is carried *positively* as the side-vs-dimension
    type-asymmetry (`UnitHyper.count_eq_side_pow_dim`).  Two readouts of one
    `^`-rung (`simplicial_operation_tower.md` L4/L5). -/
def hyperCount (k N d : Nat) : Nat := monoCount (totalCount k N) d

/-- **The tower stays simplicial.**  Stacking the rule again, the `^`-rung is *again*
    a simplex: its count is the multiset coefficient over `totalCount k N` axes,
    `hyperCount k N d = C(d + (M−1), M−1)` with `M = totalCount k N = C(N+k, k)`.  The
    **number of axes explodes** (`+`: 1 → `×`: `C(N+k,k)` → `^`: `C(d+M−1,M−1)` → …)
    but the **shape is invariantly the simplex** — nothing becomes a cube.  (The
    base/exponent asymmetry — the twist — is extra positive structure *on* this
    simplex, the dimensional/`−1`-cross-determinant content of L5, not a change of
    its combinatorial shape.) -/
theorem hyperCount_simplex (k N d : Nat) :
    hyperCount k N d = binom (d + (totalCount k N - 1)) (totalCount k N - 1) := by
  have hpos : 1 ≤ totalCount k N := by
    rw [totalCount_split]; exact Nat.le_add_right 1 _
  obtain ⟨m, hm⟩ : ∃ m, totalCount k N = m + 1 :=
    ⟨totalCount k N - 1, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  show monoCount (totalCount k N) d = binom (d + (totalCount k N - 1)) (totalCount k N - 1)
  rw [hm]
  exact monoCount_closed m d

end E213.Lens.Number.Nat213.MultSystem
