import E213.Lib.Math.Combinatorics.Stirling
import E213.Lib.Math.Combinatorics.StirlingFirstKind
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Core
import E213.Meta.Tactic.NatHelper

/-!
# Stirling orthogonality `Σ_k s(n,k)·S(k,m) = [n=m]` (∅-axiom)

★★★ The defining **inverse relation** between the two Stirling matrices — absent
from `Stirling.lean` / `StirlingFirstKind.lean` / `StirlingFalling.lean`.

Signed first-kind Stirling `s(n,k)` via the SIGNED recurrence `s(0,0)=1`,
`s(0,k+1)=0`, `s(n+1,0)=0`, `s(n+1,k+1) = s(n,k) − n·s(n,k+1)` (so
`s(n,k) = (−1)^{n−k}·c(n,k)`, `c` = unsigned `StirlingFirstKind.stirling1`).

  ★★★ `stirling_orthogonality (n m) : T n m = delta n m`, i.e.
       `Σ_{k=0}^{n} s(n,k)·(stirling2 k m : Int) = [n=m]`.

Proof: the heart is `T_succ_rec : T(n+1,m'+1) = ((m'+1)−n)·T(n,m'+1) + T(n,m')`
(split `s(n+1,·)` by its recurrence, expand `stirling2(j+1,·)` by the second-kind
recurrence, reindex with the top/bottom terms vanishing), plus
`coeff_delta_zero : ((m'+1)−n)·δ(n,m'+1)=0`, then induction on `n` (m universally
quantified).  A new Int `sumZ` algebra toolkit is included.  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.StirlingOrthogonality

open E213.Lib.Math.Combinatorics.Stirling (stirling2 stirling2_zero_above stirling_diag)
open E213.Lib.Math.Combinatorics.StirlingFirstKind (stirling1 stirling1_zero_above)

/-- Signed first-kind Stirling number via the signed recurrence. -/
def s : Nat → Nat → Int
  | 0,     0     => 1
  | 0,     _ + 1 => 0
  | _ + 1, 0     => 0
  | n + 1, k + 1 => s n k - (n : Int) * s n (k + 1)

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

/-- `Σ (f + g) = Σ f + Σ g`. -/
theorem sumZ_add (n : Nat) (f g : Nat → Int) :
    sumZ n (fun k => f k + g k) = sumZ n f + sumZ n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, sumZ_succ, ih]
    show sumZ m f + sumZ m g + (f m + g m)
       = sumZ m f + f m + (sumZ m g + g m)
    ring_intZ

/-- `Σ (c·f) = c·Σ f`. -/
theorem sumZ_mul_left (c : Int) (n : Nat) (f : Nat → Int) :
    sumZ n (fun k => c * f k) = c * sumZ n f := by
  induction n with
  | zero => show (0 : Int) = c * 0; rw [E213.Meta.Int213.PolyIntM.mul_zeroZ]
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, ih]
    show c * sumZ m f + c * f m = c * (sumZ m f + f m)
    ring_intZ

/-- `Σ (-f) = - Σ f`. -/
theorem sumZ_neg (n : Nat) (f : Nat → Int) :
    sumZ n (fun k => - f k) = - sumZ n f := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, ih]
    show - sumZ m f + - f m = -(sumZ m f + f m)
    ring_intZ

/-- `Σ (f − g) = Σ f − Σ g`. -/
theorem sumZ_sub (n : Nat) (f g : Nat → Int) :
    sumZ n (fun k => f k - g k) = sumZ n f - sumZ n g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [sumZ_succ, sumZ_succ, sumZ_succ, ih]
    show sumZ m f - sumZ m g + (f m - g m)
       = sumZ m f + f m - (sumZ m g + g m)
    ring_intZ

/-- Signed table sanity (row n=3: 2, −3, 1). -/
theorem s_table :
    s 0 0 = 1 ∧ s 1 1 = 1 ∧ s 2 1 = (-1) ∧ s 2 2 = 1
    ∧ s 3 1 = 2 ∧ s 3 2 = (-3) ∧ s 3 3 = 1 := by
  refine ⟨rfl, rfl, ?_, rfl, ?_, ?_, rfl⟩ <;> decide

/-! ## Structural lemmas for the signed first-kind `s` -/

theorem s_zero (k : Nat) : s 0 (k + 1) = 0 := rfl

theorem s_succ_zero (n : Nat) : s (n + 1) 0 = 0 := rfl

/-- The defining signed recurrence as a rewrite lemma. -/
theorem s_succ (n k : Nat) :
    s (n + 1) (k + 1) = s n k - (n : Int) * s n (k + 1) := rfl

/-- `s(m, k) = 0` for `k > m` (above-diagonal vanishing).  Mirrors
    `stirling1_zero_above`. -/
theorem s_zero_above : ∀ {m k : Nat}, m < k → s m k = 0
  | 0,     0,     h => absurd h (Nat.lt_irrefl 0)
  | 0,     _ + 1, _ => rfl
  | _ + 1, 0,     h => absurd h (Nat.not_lt_zero _)
  | m + 1, k + 1, h => by
      have hmk : m < k := Nat.lt_of_succ_lt_succ h
      rw [s_succ, s_zero_above (Nat.lt_succ_of_lt hmk), s_zero_above hmk,
          E213.Meta.Int213.PolyIntM.mul_zeroZ]
      rfl

/-! ## sumZ split / shift helpers -/

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

/-- The orthogonality (double) sum `T(n,m) = Σ_{k=0}^{n} s(n,k)·S(k,m)`,
    where `S = stirling2`.  Range `[0, n+1)` captures all nonzero terms
    (`s(n,k)=0` for `k>n`). -/
def T (n m : Nat) : Int := sumZ (n + 1) (fun k => s n k * (stirling2 k m : Int))

/-! ## The `T`-recurrence (the heart of the orthogonality proof)

We show `T(n+1,m'+1) = ((m'+1) − n)·T(n,m'+1) + T(n,m')`.  Combined with the
boundary values this reproduces the Kronecker delta. -/

open E213.Lib.Math.Combinatorics.Stirling (stirling2)

/-- `stirling2` recurrence, cast to `Int`. -/
theorem stirling2_succ_Z (n m : Nat) :
    ((stirling2 (n + 1) (m + 1) : Nat) : Int)
      = ((m + 1 : Nat) : Int) * (stirling2 n (m + 1) : Int)
        + (stirling2 n m : Int) := by
  show ((((m + 1) * stirling2 n (m + 1) + stirling2 n m : Nat)) : Int)
     = ((m + 1 : Nat) : Int) * (stirling2 n (m + 1) : Int) + (stirling2 n m : Int)
  rw [Int.ofNat_add ((m + 1) * stirling2 n (m + 1)) (stirling2 n m),
      Int.ofNat_mul (m + 1) (stirling2 n (m + 1))]

/-- The reindexed `B`-sum equals `T(n,m'+1)`:
    `Σ_{j<n+1} s(n,j+1)·S(j+1,m'+1) = T(n,m'+1)`.
    The bottom term of `T` (`s(n,0)·S(0,m'+1)=0`) and the top term of the LHS
    (`s(n,n+1)·S(n+1,m'+1)=0`, above-diagonal) both vanish. -/
theorem B_eq (n m' : Nat) :
    sumZ (n + 1) (fun j => s n (j + 1) * (stirling2 (j + 1) (m' + 1) : Int))
      = T n (m' + 1) := by
  show sumZ (n + 1) (fun j => s n (j + 1) * (stirling2 (j + 1) (m' + 1) : Int))
     = sumZ (n + 1) (fun k => s n k * (stirling2 k (m' + 1) : Int))
  rw [sumZ_split_first n (fun k => s n k * (stirling2 k (m' + 1) : Int))]
  show sumZ (n + 1) (fun j => s n (j + 1) * (stirling2 (j + 1) (m' + 1) : Int))
     = s n 0 * (stirling2 0 (m' + 1) : Int)
       + sumZ n (fun k => s n (k + 1) * (stirling2 (k + 1) (m' + 1) : Int))
  have h0 : s n 0 * (stirling2 0 (m' + 1) : Int) = 0 := by
    show s n 0 * ((0 : Nat) : Int) = 0
    rw [Int.natCast_zero, E213.Meta.Int213.PolyIntM.mul_zeroZ]
  rw [h0, E213.Meta.Int213.zero_add]
  rw [sumZ_succ n (fun j => s n (j + 1) * (stirling2 (j + 1) (m' + 1) : Int))]
  have htop : s n (n + 1) * (stirling2 (n + 1) (m' + 1) : Int) = 0 := by
    rw [s_zero_above (Nat.lt_succ_self n), E213.Meta.Int213.zero_mul]
  rw [htop, Int.add_zero]

/-- ★ **The `T`-recurrence**:
    `T(n+1, m'+1) = ((m'+1) − n)·T(n, m'+1) + T(n, m')`. -/
theorem T_succ_rec (n m' : Nat) :
    T (n + 1) (m' + 1)
      = (((m' + 1 : Nat) : Int) - (n : Int)) * T n (m' + 1) + T n m' := by
  show sumZ (n + 2) (fun k => s (n + 1) k * (stirling2 k (m' + 1) : Int))
     = (((m' + 1 : Nat) : Int) - (n : Int)) * T n (m' + 1) + T n m'
  rw [sumZ_split_first (n + 1) (fun k => s (n + 1) k * (stirling2 k (m' + 1) : Int))]
  -- head term s(n+1,0)·S(0,m'+1) = 0
  have hhead : s (n + 1) 0 * (stirling2 0 (m' + 1) : Int) = 0 := by
    rw [s_succ_zero, E213.Meta.Int213.zero_mul]
  rw [hhead, E213.Meta.Int213.zero_add]
  -- expand the summand: s(n+1)(j+1)·S(j+1,m'+1)
  --   = [s n j − n·s n (j+1)]·[(m'+1)·S(j,m'+1) + S(j,m')]
  rw [sumZ_congr (n + 1)
        (fun j => s (n + 1) (j + 1) * (stirling2 (j + 1) (m' + 1) : Int))
        (fun j =>
          (((m' + 1 : Nat) : Int) * (s n j * (stirling2 j (m' + 1) : Int))
            + s n j * (stirling2 j m' : Int))
          - (n : Int) * (s n (j + 1) * (stirling2 (j + 1) (m' + 1) : Int)))
        (fun j _ => by
          show s (n + 1) (j + 1) * (stirling2 (j + 1) (m' + 1) : Int)
             = (((m' + 1 : Nat) : Int) * (s n j * (stirling2 j (m' + 1) : Int))
                 + s n j * (stirling2 j m' : Int))
               - (n : Int) * (s n (j + 1) * (stirling2 (j + 1) (m' + 1) : Int))
          rw [s_succ n j, stirling2_succ_Z j m']
          generalize (s n j : Int) = a
          generalize (s n (j + 1) : Int) = b
          generalize ((m' + 1 : Nat) : Int) = p
          generalize (stirling2 j (m' + 1) : Int) = pp
          generalize (stirling2 j m' : Int) = qq
          generalize (n : Int) = nn
          ring_intZ)]
  -- split: Σ (A + B') − Σ C
  rw [sumZ_sub (n + 1)
        (fun j => ((m' + 1 : Nat) : Int) * (s n j * (stirling2 j (m' + 1) : Int))
                  + s n j * (stirling2 j m' : Int))
        (fun j => (n : Int) * (s n (j + 1) * (stirling2 (j + 1) (m' + 1) : Int)))]
  rw [sumZ_add (n + 1)
        (fun j => ((m' + 1 : Nat) : Int) * (s n j * (stirling2 j (m' + 1) : Int)))
        (fun j => s n j * (stirling2 j m' : Int))]
  rw [sumZ_mul_left ((m' + 1 : Nat) : Int) (n + 1)
        (fun j => s n j * (stirling2 j (m' + 1) : Int))]
  rw [sumZ_mul_left (n : Int) (n + 1)
        (fun j => s n (j + 1) * (stirling2 (j + 1) (m' + 1) : Int))]
  rw [B_eq n m']
  -- now: (m'+1)·T(n,m'+1) + T(n,m') − n·T(n,m'+1) = ((m'+1)−n)·T(n,m'+1) + T(n,m')
  show ((m' + 1 : Nat) : Int) * T n (m' + 1) + T n m' - (n : Int) * T n (m' + 1)
     = (((m' + 1 : Nat) : Int) - (n : Int)) * T n (m' + 1) + T n m'
  ring_intZ

/-! ## Boundary values of `T` -/

theorem T_zero_zero : T 0 0 = 1 := rfl

/-- `T(0, m'+1) = 0`: the only term is `s(0,0)·S(0,m'+1) = 1·0`. -/
theorem T_zero_succ (m' : Nat) : T 0 (m' + 1) = 0 := by
  show sumZ 1 (fun k => s 0 k * (stirling2 k (m' + 1) : Int)) = 0
  show (0 : Int) + s 0 0 * (stirling2 0 (m' + 1) : Int) = 0
  show (0 : Int) + s 0 0 * ((0 : Nat) : Int) = 0
  rw [Int.natCast_zero, E213.Meta.Int213.PolyIntM.mul_zeroZ, Int.add_zero]

/-- `T(n+1, 0) = 0`: `S(k,0)=0` for `k≥1`, and the head `s(n+1,0)·S(0,0)=0`. -/
theorem T_succ_zero (n : Nat) : T (n + 1) 0 = 0 := by
  show sumZ (n + 2) (fun k => s (n + 1) k * (stirling2 k 0 : Int)) = 0
  rw [sumZ_split_first (n + 1) (fun k => s (n + 1) k * (stirling2 k 0 : Int))]
  have hhead : s (n + 1) 0 * (stirling2 0 0 : Int) = 0 := by
    rw [s_succ_zero, E213.Meta.Int213.zero_mul]
  rw [hhead, E213.Meta.Int213.zero_add]
  -- tail: every term s(n+1)(j+1)·S(j+1,0) = 0 since S(j+1,0)=0
  rw [sumZ_congr (n + 1)
        (fun j => s (n + 1) (j + 1) * (stirling2 (j + 1) 0 : Int))
        (fun _ => (0 : Int))
        (fun j _ => by
          show s (n + 1) (j + 1) * ((stirling2 (j + 1) 0 : Nat) : Int) = 0
          show s (n + 1) (j + 1) * ((0 : Nat) : Int) = 0
          rw [Int.natCast_zero, E213.Meta.Int213.PolyIntM.mul_zeroZ])]
  rw [sumZ_const_zero (n + 1)]

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

/-- Off-diagonal vanishing: `δ(n,m) = 0` when `n ≠ m`. -/
theorem delta_off : ∀ {n m : Nat}, n ≠ m → delta n m = 0
  | 0,     0,     h => absurd rfl h
  | 0,     _ + 1, _ => rfl
  | _ + 1, 0,     _ => rfl
  | n + 1, m + 1, h => by
      rw [delta_succ]
      exact delta_off (fun hnm => h (congrArg (· + 1) hnm))

/-- The coefficient times the off-diagonal delta vanishes:
    `((m'+1) − n)·δ(n, m'+1) = 0`.  Either `n = m'+1` (coefficient zero) or
    `δ(n, m'+1) = 0`. -/
theorem coeff_delta_zero (n m' : Nat) :
    (((m' + 1 : Nat) : Int) - (n : Int)) * delta n (m' + 1) = 0 := by
  match Nat.decEq n (m' + 1) with
  | isTrue h =>
      rw [h]
      have hc : ((m' + 1 : Nat) : Int) - ((m' + 1 : Nat) : Int) = 0 :=
        E213.Meta.Int213.add_neg_cancel ((m' + 1 : Nat) : Int)
      rw [hc, E213.Meta.Int213.zero_mul]
  | isFalse h =>
      rw [delta_off h, E213.Meta.Int213.PolyIntM.mul_zeroZ]

/-- ★★★ **Stirling orthogonality** — the first-kind (signed) and second-kind
    Stirling matrices are mutually inverse:
    `Σ_{k} s(n,k)·S(k,m) = δ(n,m)`  for all `n, m`.

    Induction on `n` (with `m` universally quantified so the IH covers both
    `T(n,m'+1)` and `T(n,m')`).  Step uses `T_succ_rec` and `coeff_delta_zero`. -/
theorem stirling_orthogonality : ∀ (n m : Nat), T n m = delta n m
  | 0,     0      => rfl
  | 0,     m' + 1 => by rw [T_zero_succ]; rfl
  | n + 1, 0      => by rw [T_succ_zero]; rfl
  | n + 1, m' + 1 => by
      rw [T_succ_rec n m', stirling_orthogonality n (m' + 1),
          stirling_orthogonality n m', delta_succ]
      -- ((m'+1) − n)·δ(n,m'+1) + δ(n,m') = δ(n,m')
      rw [coeff_delta_zero n m', E213.Meta.Int213.zero_add]

/-- Explicit `Σ`-form of orthogonality (unfolds `T` and `delta`). -/
theorem stirling_orthogonality_sum (n m : Nat) :
    sumZ (n + 1) (fun k => s n k * (stirling2 k m : Int)) = delta n m :=
  stirling_orthogonality n m

/-- Orthogonality table check: `T(n,m) = [n=m]` for `n,m ≤ 4`. -/
theorem T_table :
    T 0 0 = 1 ∧ T 1 1 = 1 ∧ T 2 2 = 1 ∧ T 3 3 = 1 ∧ T 4 4 = 1
    ∧ T 1 0 = 0 ∧ T 2 0 = 0 ∧ T 2 1 = 0 ∧ T 3 1 = 0 ∧ T 3 2 = 0
    ∧ T 4 1 = 0 ∧ T 4 2 = 0 ∧ T 4 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Combinatorics.StirlingOrthogonality
