import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Core

/-!
# Binomial orthogonality + binomial inversion (∅-axiom)

★★★ **Binomial orthogonality**: `Σ_{k} (−1)^{n−k}·C(n,k)·C(k,m) = [n=m]`.

Stated subtraction-free via a SIGNED binomial coefficient `sb n k = (−1)^{n−k}·C(n,k)`
defined by the signed Pascal recurrence
  `sb 0 0 = 1`, `sb 0 (k+1) = 0`, `sb (n+1) 0 = − sb n 0`,
  `sb (n+1) (k+1) = sb n k − sb n (k+1)`.
(So `sb n k = (−1)^{n−k}·C(n,k)`: the diagonal sign on the row is `(−1)^{n−k}`.)

The orthogonality double-sum `T(n,m) = Σ_{k=0}^{n} sb(n,k)·C(k,m)` satisfies the same
recurrence template as the Stirling orthogonality
(`Combinatorics/StirlingOrthogonality.lean`): `T(n+1,m'+1) = T(n,m') − T(n,m'+1)·?`…
here the Pascal split of `C(j+1,m'+1) = C(j,m') + C(j,m'+1)` gives
  `T(n+1, m'+1) = T(n, m') − T(n, m'+1) + (boundary)`,
which collapses to the Kronecker delta by induction.

★★★ **Binomial inversion**: `(∀ n, g n = Σ C(n,k)·f k) → f n = Σ (−1)^{n−k}·C(n,k)·g k`.

Reuses `choose` (Pascal) from `DyadicFSM.FLT.Binomial`.  `Int` toolkit = `ring_intZ`.
All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.BinomialInversion

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_zero_succ choose_succ_succ choose_self
   choose_eq_zero_of_lt)

/-! ## Int-valued Σ toolkit (mirrors StirlingOrthogonality.sumZ) -/

/-- Int-valued Σ over `[0, n)`. -/
def sumZ : Nat → (Nat → Int) → Int
  | 0,     _ => 0
  | n + 1, f => sumZ n f + f n

theorem sumZ_succ (n : Nat) (f : Nat → Int) : sumZ (n + 1) f = sumZ n f + f n := rfl

theorem sumZ_congr (n : Nat) (f g : Nat → Int) (h : ∀ k, k < n → f k = g k) :
    sumZ n f = sumZ n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),
        h m (Nat.lt_succ_self m)]

theorem sumZ_const_zero (n : Nat) : sumZ n (fun _ => (0 : Int)) = 0 := by
  induction n with
  | zero => rfl
  | succ m ih => rw [sumZ_succ, ih]; rfl

theorem sumZ_add (n : Nat) (f g : Nat → Int) :
    sumZ n (fun k => f k + g k) = sumZ n f + sumZ n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, sumZ_succ, ih]
    show sumZ m f + sumZ m g + (f m + g m)
       = sumZ m f + f m + (sumZ m g + g m)
    ring_intZ

theorem sumZ_mul_left (c : Int) (n : Nat) (f : Nat → Int) :
    sumZ n (fun k => c * f k) = c * sumZ n f := by
  induction n with
  | zero => show (0 : Int) = c * 0; rw [E213.Meta.Int213.PolyIntM.mul_zeroZ]
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, ih]
    show c * sumZ m f + c * f m = c * (sumZ m f + f m)
    ring_intZ

theorem sumZ_neg (n : Nat) (f : Nat → Int) :
    sumZ n (fun k => - f k) = - sumZ n f := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, ih]
    show - sumZ m f + - f m = -(sumZ m f + f m)
    ring_intZ

theorem sumZ_sub (n : Nat) (f g : Nat → Int) :
    sumZ n (fun k => f k - g k) = sumZ n f - sumZ n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, sumZ_succ, ih]
    show sumZ m f - sumZ m g + (f m - g m)
       = sumZ m f + f m - (sumZ m g + g m)
    ring_intZ

/-- Peel the first term and reindex: `Σ_{k<n+1} f k = f 0 + Σ_{k<n} f (k+1)`. -/
theorem sumZ_split_first (n : Nat) (f : Nat → Int) :
    sumZ (n + 1) f = f 0 + sumZ n (fun k => f (k + 1)) := by
  induction n with
  | zero => show sumZ 1 f = f 0 + 0; rw [E213.Meta.Int213.add_comm]; rfl
  | succ m ih =>
    rw [sumZ_succ, ih]
    show f 0 + sumZ m (fun k => f (k + 1)) + f (m + 1)
       = f 0 + (sumZ m (fun k => f (k + 1)) + f (m + 1))
    rw [E213.Meta.Int213.add_assoc]

/-! ## Signed binomial coefficient `sb n k = (−1)^{n−k}·C(n,k)` -/

/-- Signed binomial via the signed Pascal recurrence. -/
def sb : Nat → Nat → Int
  | 0,     0     => 1
  | 0,     _ + 1 => 0
  | n + 1, 0     => - sb n 0
  | n + 1, k + 1 => sb n k - sb n (k + 1)

theorem sb_zero_succ (k : Nat) : sb 0 (k + 1) = 0 := rfl
theorem sb_succ_zero (n : Nat) : sb (n + 1) 0 = - sb n 0 := rfl
theorem sb_succ (n k : Nat) : sb (n + 1) (k + 1) = sb n k - sb n (k + 1) := rfl

/-- `sb m k = 0` for `k > m` (above-diagonal vanishing). -/
theorem sb_zero_above : ∀ {m k : Nat}, m < k → sb m k = 0
  | 0,     0,     h => absurd h (Nat.lt_irrefl 0)
  | 0,     _ + 1, _ => rfl
  | _ + 1, 0,     h => absurd h (Nat.not_lt_zero _)
  | m + 1, k + 1, h => by
      have hmk : m < k := Nat.lt_of_succ_lt_succ h
      rw [sb_succ, sb_zero_above (Nat.lt_succ_of_lt hmk), sb_zero_above hmk]
      rfl

/-- Signed-binomial table sanity (row n=3: −1, 3, −3, 1). -/
theorem sb_table :
    sb 0 0 = 1 ∧ sb 1 0 = (-1) ∧ sb 1 1 = 1
    ∧ sb 2 0 = 1 ∧ sb 2 1 = (-2) ∧ sb 2 2 = 1
    ∧ sb 3 0 = (-1) ∧ sb 3 1 = 3 ∧ sb 3 2 = (-3) ∧ sb 3 3 = 1 := by
  refine ⟨rfl, ?_, rfl, ?_, ?_, rfl, ?_, ?_, ?_, rfl⟩ <;> decide

/-! ## The orthogonality double-sum `T(n,m) = Σ_{k} sb(n,k)·C(k,m)` -/

/-- `T(n,m) = Σ_{k=0}^{n} sb(n,k)·C(k,m)`.  Range `[0,n+1)` captures all nonzero terms
    (`sb(n,k)=0` for `k>n`). -/
def T (n m : Nat) : Int := sumZ (n + 1) (fun k => sb n k * (choose k m : Int))

/-- `choose` Pascal recurrence, cast to `Int`. -/
theorem choose_succ_succ_Z (j m : Nat) :
    ((choose (j + 1) (m + 1) : Nat) : Int)
      = (choose j m : Int) + (choose j (m + 1) : Int) := by
  show ((choose j m + choose j (m + 1) : Nat) : Int)
     = (choose j m : Int) + (choose j (m + 1) : Int)
  rw [Int.ofNat_add (choose j m) (choose j (m + 1))]

/-- The shifted sum `shiftSum n m = Σ_{j=0}^{n} sb(n,j)·C(j+1,m)`. -/
def shiftSum (n m : Nat) : Int := sumZ (n + 1) (fun j => sb n j * (choose (j + 1) m : Int))

/-- Reindexing identity: `Σ_{j=0}^{n} sb(n,j+1)·C(j+1,m) = T n m − sb(n,0)·C(0,m)`.
    (`Σ_{k=1}^{n+1} sb(n,k)·C(k,m)`; the top term `sb(n,n+1)·C(n+1,m)=0` vanishes, and
    the `k=0` term is subtracted off from `T`.) -/
theorem reindex_shift (n m : Nat) :
    sumZ (n + 1) (fun j => sb n (j + 1) * (choose (j + 1) m : Int))
      = T n m - sb n 0 * (choose 0 m : Int) := by
  -- T n m = sb(n,0)·C(0,m) + Σ_{j<n+1} sb(n,j+1)·C(j+1,m), via sumZ_split_first.
  -- But T ranges [0,n+1); the tail of the split has n terms, not n+1.  We instead
  -- compute Σ_{j<n+1} sb(n,j+1)·C(j+1,m) = [Σ_{j<n} sb(n,j+1)·C(j+1,m)] + top,
  -- where top = sb(n,n+1)·C(n+1,m) = 0.
  rw [sumZ_succ n (fun j => sb n (j + 1) * (choose (j + 1) m : Int))]
  have htop : sb n (n + 1) * (choose (n + 1) m : Int) = 0 := by
    rw [sb_zero_above (Nat.lt_succ_self n), E213.Meta.Int213.zero_mul]
  rw [htop, Int.add_zero]
  -- Now LHS = Σ_{j<n} sb(n,j+1)·C(j+1,m).  And T n m = Σ_{k<n+1} sb(n,k)·C(k,m)
  --   = sb(n,0)·C(0,m) + Σ_{j<n} sb(n,j+1)·C(j+1,m)   (sumZ_split_first).
  show sumZ n (fun j => sb n (j + 1) * (choose (j + 1) m : Int))
     = T n m - sb n 0 * (choose 0 m : Int)
  have hT : T n m
      = sb n 0 * (choose 0 m : Int)
        + sumZ n (fun j => sb n (j + 1) * (choose (j + 1) m : Int)) := by
    show sumZ (n + 1) (fun k => sb n k * (choose k m : Int))
       = sb n 0 * (choose 0 m : Int)
         + sumZ n (fun j => sb n (j + 1) * (choose (j + 1) m : Int))
    rw [sumZ_split_first n (fun k => sb n k * (choose k m : Int))]
  rw [hT]
  generalize sumZ n (fun j => sb n (j + 1) * (choose (j + 1) m : Int)) = S
  generalize sb n 0 * (choose 0 m : Int) = h0
  ring_intZ

/-- `T(n+1, m) = shiftSum n m − T n m` (for all `m`).  Split `sb(n+1,·)` by its signed
    recurrence; the head and the reindexed `sb(n,j+1)`-sum combine via `reindex_shift`. -/
theorem T_succ_shift (n m : Nat) :
    T (n + 1) m = shiftSum n m - T n m := by
  show sumZ (n + 2) (fun k => sb (n + 1) k * (choose k m : Int)) = shiftSum n m - T n m
  rw [sumZ_split_first (n + 1) (fun k => sb (n + 1) k * (choose k m : Int))]
  -- head term: sb(n+1,0)·C(0,m) = -sb(n,0)·C(0,m)
  show sb (n + 1) 0 * (choose 0 m : Int)
       + sumZ (n + 1) (fun j => sb (n + 1) (j + 1) * (choose (j + 1) m : Int))
     = shiftSum n m - T n m
  rw [sb_succ_zero n]
  -- expand each tail summand via sb_succ:
  --   sb(n+1,j+1)·C(j+1,m) = (sb(n,j) − sb(n,j+1))·C(j+1,m)
  --     = sb(n,j)·C(j+1,m) − sb(n,j+1)·C(j+1,m)
  rw [sumZ_congr (n + 1)
        (fun j => sb (n + 1) (j + 1) * (choose (j + 1) m : Int))
        (fun j => sb n j * (choose (j + 1) m : Int)
                  - sb n (j + 1) * (choose (j + 1) m : Int))
        (fun j _ => by
          show sb (n + 1) (j + 1) * (choose (j + 1) m : Int)
             = sb n j * (choose (j + 1) m : Int)
               - sb n (j + 1) * (choose (j + 1) m : Int)
          rw [sb_succ n j]
          generalize (sb n j : Int) = a
          generalize (sb n (j + 1) : Int) = b
          generalize ((choose (j + 1) m : Nat) : Int) = c
          ring_intZ)]
  rw [sumZ_sub (n + 1)
        (fun j => sb n j * (choose (j + 1) m : Int))
        (fun j => sb n (j + 1) * (choose (j + 1) m : Int))]
  -- first sum is shiftSum n m (defeq); second sum reindexes via reindex_shift
  rw [reindex_shift n m]
  show (- sb n 0) * (choose 0 m : Int)
       + (shiftSum n m - (T n m - sb n 0 * (choose 0 m : Int)))
     = shiftSum n m - T n m
  generalize shiftSum n m = Sh
  generalize sb n 0 = s0
  generalize (choose 0 m : Int) = c0
  generalize T n m = Tn
  ring_intZ

/-- `shiftSum n (m'+1) = T n m' + T n (m'+1)`.  Pascal-split `C(j+1,m'+1) = C(j,m') +
    C(j,m'+1)` pointwise, then split the sum. -/
theorem shiftSum_succ (n m' : Nat) :
    shiftSum n (m' + 1) = T n m' + T n (m' + 1) := by
  show sumZ (n + 1) (fun j => sb n j * (choose (j + 1) (m' + 1) : Int))
     = T n m' + T n (m' + 1)
  rw [sumZ_congr (n + 1)
        (fun j => sb n j * (choose (j + 1) (m' + 1) : Int))
        (fun j => sb n j * (choose j m' : Int) + sb n j * (choose j (m' + 1) : Int))
        (fun j _ => by
          show sb n j * (choose (j + 1) (m' + 1) : Int)
             = sb n j * (choose j m' : Int) + sb n j * (choose j (m' + 1) : Int)
          rw [choose_succ_succ_Z j m']
          generalize (sb n j : Int) = a
          generalize ((choose j m' : Nat) : Int) = c
          generalize ((choose j (m' + 1) : Nat) : Int) = d
          ring_intZ)]
  rw [sumZ_add (n + 1)
        (fun j => sb n j * (choose j m' : Int))
        (fun j => sb n j * (choose j (m' + 1) : Int))]
  rfl

/-- ★ **The `T`-recurrence**: `T(n+1, m'+1) = T(n, m')`. -/
theorem T_succ_rec (n m' : Nat) : T (n + 1) (m' + 1) = T n m' := by
  rw [T_succ_shift n (m' + 1), shiftSum_succ n m']
  generalize T n m' = a
  generalize T n (m' + 1) = b
  ring_intZ

/-! ## Boundary values of `T` -/

theorem T_zero_zero : T 0 0 = 1 := rfl

/-- `T(0, m'+1) = 0`: the only term is `sb(0,0)·C(0,m'+1) = 1·0`. -/
theorem T_zero_succ (m' : Nat) : T 0 (m' + 1) = 0 := by
  show sumZ 1 (fun k => sb 0 k * (choose k (m' + 1) : Int)) = 0
  show (0 : Int) + sb 0 0 * (choose 0 (m' + 1) : Int) = 0
  show (0 : Int) + sb 0 0 * ((0 : Nat) : Int) = 0
  rw [Int.natCast_zero, E213.Meta.Int213.PolyIntM.mul_zeroZ, Int.add_zero]

/-- `T(n+1, 0) = 0`.  Via the recurrence `T(n+1,0) = shiftSum n 0 − T n 0` and the
    fact that `C(·,0) = 1`, this is the alternating row sum; we close it by induction
    using `T_succ_shift` and `shiftSum` at `m = 0`. -/
theorem T_succ_zero : ∀ n : Nat, T (n + 1) 0 = 0
  | 0 => by decide
  | n + 1 => by
      -- T(n+2,0) = shiftSum (n+1) 0 − T (n+1) 0, and shiftSum (n+1) 0 = T (n+1) 0
      -- (since C(j+1,0) = 1 = C(j,0)), so the difference is 0.
      rw [T_succ_shift (n + 1) 0]
      have hsh : shiftSum (n + 1) 0 = T (n + 1) 0 := by
        show sumZ (n + 2) (fun j => sb (n + 1) j * (choose (j + 1) 0 : Int))
           = sumZ (n + 2) (fun k => sb (n + 1) k * (choose k 0 : Int))
        exact sumZ_congr (n + 2)
          (fun j => sb (n + 1) j * (choose (j + 1) 0 : Int))
          (fun k => sb (n + 1) k * (choose k 0 : Int))
          (fun j _ => by
            show sb (n + 1) j * (choose (j + 1) 0 : Int)
               = sb (n + 1) j * (choose j 0 : Int)
            rw [choose_zero_right (j + 1), choose_zero_right j])
      rw [hsh]
      exact E213.Meta.Int213.add_neg_cancel (T (n + 1) 0)

/-! ## Kronecker delta and the orthogonality theorem -/

/-- Kronecker delta `δ(n,m) : Int`. -/
def delta : Nat → Nat → Int
  | 0,     0     => 1
  | 0,     _ + 1 => 0
  | _ + 1, 0     => 0
  | n + 1, m + 1 => delta n m

theorem delta_succ (n m : Nat) : delta (n + 1) (m + 1) = delta n m := rfl

theorem delta_diag : ∀ n, delta n n = 1
  | 0     => rfl
  | n + 1 => by rw [delta_succ]; exact delta_diag n

theorem delta_off : ∀ {n m : Nat}, n ≠ m → delta n m = 0
  | 0,     0,     h => absurd rfl h
  | 0,     _ + 1, _ => rfl
  | _ + 1, 0,     _ => rfl
  | n + 1, m + 1, h => by
      rw [delta_succ]
      exact delta_off (fun hnm => h (congrArg (· + 1) hnm))

/-- ★★★ **Binomial orthogonality** — the binomial matrix `C(n,k)` and its signed
    transpose `(−1)^{n−k}·C(n,k)` are mutually inverse:
    `Σ_{k} (−1)^{n−k}·C(n,k)·C(k,m) = δ(n,m)`  for all `n, m`.

    Induction on `n` (`m` universally quantified).  Step uses the clean recurrence
    `T(n+1,m'+1) = T(n,m')` (`T_succ_rec`) plus the boundary values. -/
theorem binomial_orthogonality : ∀ (n m : Nat), T n m = delta n m
  | 0,     0      => rfl
  | 0,     m' + 1 => by rw [T_zero_succ]; rfl
  | n + 1, 0      => by rw [T_succ_zero]; rfl
  | n + 1, m' + 1 => by
      rw [T_succ_rec n m', binomial_orthogonality n m', delta_succ]

/-- Explicit `Σ`-form of binomial orthogonality (unfolds `T` and `delta`):
    `Σ_{k=0}^{n} (−1)^{n−k}·C(n,k)·C(k,m) = [n=m]`, with the alternating sign carried
    by `sb n k = (−1)^{n−k}·C(n,k)`. -/
theorem binomial_orthogonality_sum (n m : Nat) :
    sumZ (n + 1) (fun k => sb n k * (choose k m : Int)) = delta n m :=
  binomial_orthogonality n m

/-- Orthogonality table check: `T(n,m) = [n=m]` for small `n,m`. -/
theorem T_table :
    T 0 0 = 1 ∧ T 1 1 = 1 ∧ T 2 2 = 1 ∧ T 3 3 = 1 ∧ T 4 4 = 1
    ∧ T 1 0 = 0 ∧ T 2 0 = 0 ∧ T 2 1 = 0 ∧ T 3 1 = 0 ∧ T 3 2 = 0
    ∧ T 4 1 = 0 ∧ T 4 2 = 0 ∧ T 4 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Binomial inversion -/

/-- Range split: `Σ_{i<a+b} F i = Σ_{i<a} F i + Σ_{j<b} F (a+j)`. -/
theorem sumZ_add_range (a : Nat) : ∀ (b : Nat) (F : Nat → Int),
    sumZ (a + b) F = sumZ a F + sumZ b (fun j => F (a + j))
  | 0, F => by
      show sumZ a F = sumZ a F + 0
      rw [Int.add_zero]
  | b + 1, F => by
      show sumZ (a + b + 1) F = sumZ a F + sumZ (b + 1) (fun j => F (a + j))
      rw [sumZ_succ (a + b) F, sumZ_add_range a b F,
          sumZ_succ b (fun j => F (a + j))]
      show sumZ a F + sumZ b (fun j => F (a + j)) + F (a + b)
         = sumZ a F + (sumZ b (fun j => F (a + j)) + F (a + b))
      rw [E213.Meta.Int213.add_assoc]

/-- Double-sum Fubini over a square range:
    `Σ_{k<P} Σ_{i<Q} F k i = Σ_{i<Q} Σ_{k<P} F k i`.
    Induction on `P`; the step uses `sumZ_add` to distribute the new row. -/
theorem sumZ_swap : ∀ (P Q : Nat) (F : Nat → Nat → Int),
    sumZ P (fun k => sumZ Q (fun i => F k i))
      = sumZ Q (fun i => sumZ P (fun k => F k i))
  | 0, Q, F => by
      show (0 : Int) = sumZ Q (fun i => sumZ 0 (fun k => F k i))
      rw [show (fun i => sumZ 0 (fun k => F k i)) = (fun _ => (0 : Int)) from rfl,
          sumZ_const_zero Q]
  | P + 1, Q, F => by
      rw [sumZ_succ P (fun k => sumZ Q (fun i => F k i)), sumZ_swap P Q F]
      -- RHS row P added: Σ_i (Σ_{k<P} F k i) + Σ_i F P i = Σ_i (Σ_{k<P} F k i + F P i)
      rw [← sumZ_add Q (fun i => sumZ P (fun k => F k i)) (fun i => F P i)]
      rfl

/-- Forward binomial transform `Σ_{k=0}^{n} C(n,k)·f k`, as an `Int` sum. -/
def fwd (f : Nat → Int) (n : Nat) : Int :=
  sumZ (n + 1) (fun k => (choose n k : Int) * f k)

/-- Extend the inner forward-transform range: for `k ≤ n`,
    `Σ_{i<k+1} C(k,i)·f i = Σ_{i<n+1} C(k,i)·f i` — the extra terms `i ∈ (k, n]`
    vanish because `C(k,i) = 0` there. -/
theorem fwd_extend (f : Nat → Int) (k n : Nat) (hk : k ≤ n) :
    fwd f k = sumZ (n + 1) (fun i => (choose k i : Int) * f i) := by
  -- Both equal Σ_{i<n+1} restricted; prove by splitting the larger range at k+1.
  -- Σ_{i<n+1} C(k,i) f i, with the tail i ∈ [k+1, n+1) all zero.
  obtain ⟨d, hd⟩ := Nat.le.dest hk
  -- n + 1 = (k + 1) + d
  have hsplit : sumZ (n + 1) (fun i => (choose k i : Int) * f i)
      = sumZ (k + 1) (fun i => (choose k i : Int) * f i)
        + sumZ d (fun j => (choose k (k + 1 + j) : Int) * f (k + 1 + j)) := by
    -- general: sumZ (a + b) F = sumZ a F + sumZ b (fun j => F (a + j))
    rw [show n + 1 = (k + 1) + d from by rw [Nat.add_right_comm k 1 d, hd]]
    exact sumZ_add_range (k + 1) d (fun i => (choose k i : Int) * f i)
  rw [hsplit]
  have htail : sumZ d (fun j => (choose k (k + 1 + j) : Int) * f (k + 1 + j)) = 0 := by
    rw [sumZ_congr d
          (fun j => (choose k (k + 1 + j) : Int) * f (k + 1 + j))
          (fun _ => (0 : Int))
          (fun j _ => by
            show (choose k (k + 1 + j) : Int) * f (k + 1 + j) = 0
            rw [choose_eq_zero_of_lt k (k + 1 + j)
                  (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_add_right (k + 1) j)),
                Int.natCast_zero, E213.Meta.Int213.zero_mul])]
    rw [sumZ_const_zero d]
  rw [htail, Int.add_zero]
  rfl

/-- Delta collapse: `Σ_{i=0}^{n} δ(n,i)·f i = f n`.  Only the `i=n` term survives
    (`δ(n,i)=0` for `i<n`); the top term is `δ(n,n)·f n = f n`. -/
theorem sumZ_delta_collapse (f : Nat → Int) (n : Nat) :
    sumZ (n + 1) (fun i => delta n i * f i) = f n := by
  rw [sumZ_succ n (fun i => delta n i * f i)]
  have hlow : sumZ n (fun i => delta n i * f i) = 0 := by
    rw [sumZ_congr n (fun i => delta n i * f i) (fun _ => (0 : Int))
          (fun i hi => by
            show delta n i * f i = 0
            rw [delta_off (Nat.ne_of_gt hi),
                E213.Meta.Int213.zero_mul])]
    rw [sumZ_const_zero n]
  rw [hlow, delta_diag n, E213.Meta.Int213.zero_add,
      E213.Meta.Int213.PolyIntM.one_mulZ]

/-- ★★★ **Binomial inversion**: given the forward binomial transform
    `g n = Σ_{k=0}^{n} C(n,k)·f k`, the inverse transform recovers `f`:
    `f n = Σ_{k=0}^{n} (−1)^{n−k}·C(n,k)·g k`  (alternating sign carried by `sb`).

    Substitute `g`, extend each inner range to `[0,n+1)` (`fwd_extend`), Fubini-swap
    (`sumZ_swap`), and the inner `Σ_k sb(n,k)·C(k,i) = δ(n,i)`
    (`binomial_orthogonality`) collapses to `f n` (`sumZ_delta_collapse`). -/
theorem binomial_inversion (f g : Nat → Int)
    (hg : ∀ n, g n = fwd f n) :
    ∀ n, f n = sumZ (n + 1) (fun k => sb n k * g k) := by
  intro n
  have step1 : sumZ (n + 1) (fun k => sb n k * g k)
      = sumZ (n + 1) (fun k =>
          sumZ (n + 1) (fun i => sb n k * ((choose k i : Int) * f i))) := by
    apply sumZ_congr
    intro k hk
    show sb n k * g k
       = sumZ (n + 1) (fun i => sb n k * ((choose k i : Int) * f i))
    rw [hg k, fwd_extend f k n (Nat.le_of_lt_succ hk)]
    rw [sumZ_mul_left (sb n k) (n + 1) (fun i => (choose k i : Int) * f i)]
  rw [step1]
  rw [sumZ_swap (n + 1) (n + 1)
        (fun k i => sb n k * ((choose k i : Int) * f i))]
  rw [sumZ_congr (n + 1)
        (fun i => sumZ (n + 1) (fun k => sb n k * ((choose k i : Int) * f i)))
        (fun i => delta n i * f i)
        (fun i _ => by
          show sumZ (n + 1) (fun k => sb n k * ((choose k i : Int) * f i))
             = delta n i * f i
          -- rewrite each term to  f i * (sb(n,k)·C(k,i))  so f i pulls out on the left
          rw [sumZ_congr (n + 1)
                (fun k => sb n k * ((choose k i : Int) * f i))
                (fun k => f i * (sb n k * (choose k i : Int)))
                (fun k _ => by
                  show sb n k * ((choose k i : Int) * f i)
                     = f i * (sb n k * (choose k i : Int))
                  generalize (sb n k : Int) = a
                  generalize ((choose k i : Nat) : Int) = c
                  generalize (f i : Int) = d
                  ring_intZ)]
          rw [sumZ_mul_left (f i) (n + 1) (fun k => sb n k * (choose k i : Int))]
          rw [show sumZ (n + 1) (fun k => sb n k * (choose k i : Int)) = T n i from rfl,
              binomial_orthogonality n i]
          generalize (f i : Int) = d
          generalize delta n i = e
          ring_intZ)]
  exact (sumZ_delta_collapse f n).symm

/-- Smoke: inversion instance at `n = 3` with `f = id` (`f i = i`).
    Forward `g 3 = Σ_{k≤3} C(3,k)·k` and inverse recovers `f 3 = 3`. -/
theorem binomial_inversion_smoke :
    sumZ 4 (fun k => sb 3 k * (sumZ (k + 1) (fun i => (choose k i : Int) * (i : Int))))
      = (3 : Int) := by decide

end E213.Lib.Math.Combinatorics.BinomialInversion
