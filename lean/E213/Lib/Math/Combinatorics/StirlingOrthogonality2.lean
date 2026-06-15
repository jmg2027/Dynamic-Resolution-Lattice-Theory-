import E213.Lib.Math.Combinatorics.Stirling
import E213.Lib.Math.Combinatorics.StirlingFirstKind
import E213.Lib.Math.Combinatorics.StirlingOrthogonality
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Core
import E213.Meta.Tactic.NatHelper

/-!
# Stirling orthogonality — the OTHER direction `Σ_k S(n,k)·s(k,m) = [n=m]` (∅-axiom)

Complement of `StirlingOrthogonality.lean` (which proved `Σ_k s(n,k)·S(k,m) = δ`).
Here the SECOND-kind matrix multiplies the SIGNED-FIRST-kind one:
`U(n,m) = Σ_k S(n,k)·s(k,m) = δ(n,m)`.

REUSE: `s`, `stirling2`, `delta`, and the whole `sumZ` toolkit are imported from
`StirlingOrthogonality`.

The proof DOES NOT dualize the `T`-architecture directly: the recurrence
`U(n+1,m'+1) = ((m'+1)−n)·U(n,m'+1) + U(n,m')` is FALSE structurally (it holds
only because both sides are δ).  The second-kind recurrence carries a `(k+1)`
weight that breaks the clean telescoping.

Instead there is a CLEANER structurally-provable recurrence (verified symbolically):
  ★ `U(n+1, m'+1) = U(n, m')`   (`U_succ_rec`)
The `k`-weighted sums from the second-kind (outer) and signed-first-kind (inner)
recurrences cancel EXACTLY.  Combined with the boundaries this is δ.
-/

namespace E213.Lib.Math.Combinatorics.StirlingOrthogonality2

open E213.Lib.Math.Combinatorics.Stirling
  (stirling2 stirling2_zero_above stirling_diag)
open E213.Lib.Math.Combinatorics.StirlingOrthogonality
  (s sumZ sumZ_succ sumZ_congr sumZ_const_zero sumZ_add sumZ_mul_left sumZ_neg
   sumZ_sub sumZ_split_first s_zero s_succ_zero s_succ s_zero_above
   delta delta_succ delta_diag delta_off)

/-- The second ⨯ signed-first double sum `U(n,m) = Σ_{k=0}^{n} S(n,k)·s(k,m)`.
    Range `[0, n+1)` captures all nonzero terms (`S(n,k)=0` for `k>n`). -/
def U (n m : Nat) : Int := sumZ (n + 1) (fun k => (stirling2 n k : Int) * s k m)

/-- `stirling2` recurrence cast to `Int` (mirrors `stirling2_succ_Z`). -/
theorem stirling2_succ_Z (n m : Nat) :
    ((stirling2 (n + 1) (m + 1) : Nat) : Int)
      = ((m + 1 : Nat) : Int) * (stirling2 n (m + 1) : Int)
        + (stirling2 n m : Int) := by
  show ((((m + 1) * stirling2 n (m + 1) + stirling2 n m : Nat)) : Int)
     = ((m + 1 : Nat) : Int) * (stirling2 n (m + 1) : Int) + (stirling2 n m : Int)
  rw [Int.ofNat_add ((m + 1) * stirling2 n (m + 1)) (stirling2 n m),
      Int.ofNat_mul (m + 1) (stirling2 n (m + 1))]

/-! ## The two auxiliary sums and their reindexing -/

/-- `f1(n,m) := Σ_{k=0}^{n} k·S(n,k)·s(k,m)`. -/
def f1 (n m : Nat) : Int :=
  sumZ (n + 1) (fun k => (k : Int) * ((stirling2 n k : Int) * s k m))

/-- The `G`-reindex: `Σ_{k=0}^{n} (k+1)·S(n,k+1)·s(k+1,m) = f1(n,m)`.
    The bottom term of `f1` (`0·S(n,0)·s(0,m)=0`) and the top term of the LHS
    (`(n+1)·S(n,n+1)·s(n+1,m)=0`, above-diagonal in `S`) both vanish. -/
theorem G_eq (n m : Nat) :
    sumZ (n + 1)
      (fun k => ((k + 1 : Nat) : Int) * ((stirling2 n (k + 1) : Int) * s (k + 1) m))
      = f1 n m := by
  show sumZ (n + 1)
        (fun k => ((k + 1 : Nat) : Int) * ((stirling2 n (k + 1) : Int) * s (k + 1) m))
     = sumZ (n + 1) (fun k => (k : Int) * ((stirling2 n k : Int) * s k m))
  rw [sumZ_split_first n (fun k => (k : Int) * ((stirling2 n k : Int) * s k m))]
  show sumZ (n + 1)
        (fun k => ((k + 1 : Nat) : Int) * ((stirling2 n (k + 1) : Int) * s (k + 1) m))
     = ((0 : Nat) : Int) * ((stirling2 n 0 : Int) * s 0 m)
       + sumZ n (fun k => ((k + 1 : Nat) : Int) * ((stirling2 n (k + 1) : Int) * s (k + 1) m))
  have h0 : ((0 : Nat) : Int) * ((stirling2 n 0 : Int) * s 0 m) = 0 := by
    rw [Int.natCast_zero, E213.Meta.Int213.zero_mul]
  rw [h0, E213.Meta.Int213.zero_add]
  rw [sumZ_succ n
        (fun k => ((k + 1 : Nat) : Int) * ((stirling2 n (k + 1) : Int) * s (k + 1) m))]
  have htop : ((n + 1 : Nat) : Int) * ((stirling2 n (n + 1) : Int) * s (n + 1) m) = 0 := by
    rw [stirling2_zero_above (Nat.lt_succ_self n)]
    show ((n + 1 : Nat) : Int) * (((0 : Nat) : Int) * s (n + 1) m) = 0
    rw [Int.natCast_zero, E213.Meta.Int213.zero_mul,
        E213.Meta.Int213.PolyIntM.mul_zeroZ]
  rw [htop, Int.add_zero]

/-- The `H`-reindex with the inner expansion:
    `Σ_{k=0}^{n} S(n,k)·s(k+1,m'+1) = U(n,m') − f1(n,m'+1)`.
    Use `s(k+1,m'+1) = s(k,m') − k·s(k,m'+1)`; the `U(n,m')` sum has range `[0,n+1)`. -/
theorem H_eq (n m' : Nat) :
    sumZ (n + 1) (fun k => (stirling2 n k : Int) * s (k + 1) (m' + 1))
      = U n m' - f1 n (m' + 1) := by
  rw [sumZ_congr (n + 1)
        (fun k => (stirling2 n k : Int) * s (k + 1) (m' + 1))
        (fun k =>
          (stirling2 n k : Int) * s k m'
            - (k : Int) * ((stirling2 n k : Int) * s k (m' + 1)))
        (fun k _ => by
          show (stirling2 n k : Int) * s (k + 1) (m' + 1)
             = (stirling2 n k : Int) * s k m'
                 - (k : Int) * ((stirling2 n k : Int) * s k (m' + 1))
          rw [s_succ k m']
          generalize (stirling2 n k : Int) = a
          generalize (s k m' : Int) = b
          generalize (s k (m' + 1) : Int) = c
          generalize (k : Int) = kk
          ring_intZ)]
  rw [sumZ_sub (n + 1)
        (fun k => (stirling2 n k : Int) * s k m')
        (fun k => (k : Int) * ((stirling2 n k : Int) * s k (m' + 1)))]
  rfl

/-! ## The `U`-recurrence (the heart) -/

/-- ★ **The `U`-recurrence**: `U(n+1, m'+1) = U(n, m')`.

    Split `U(n+1,m'+1)` via the second-kind recurrence on the OUTER index,
    reindex the `(k+1)`-weighted part (`G_eq` → `f1(n,m'+1)`) and expand the
    other via the signed-first-kind recurrence on the INNER index
    (`H_eq` → `U(n,m') − f1(n,m'+1)`).  The two `f1(n,m'+1)` cancel. -/
theorem U_succ_rec (n m' : Nat) : U (n + 1) (m' + 1) = U n m' := by
  show sumZ (n + 2) (fun k => (stirling2 (n + 1) k : Int) * s k (m' + 1)) = U n m'
  rw [sumZ_split_first (n + 1)
        (fun k => (stirling2 (n + 1) k : Int) * s k (m' + 1))]
  -- head term S(n+1,0)·s(0,m'+1) = 0
  have hhead : (stirling2 (n + 1) 0 : Int) * s 0 (m' + 1) = 0 := by
    show (((0 : Nat)) : Int) * s 0 (m' + 1) = 0
    rw [Int.natCast_zero, E213.Meta.Int213.zero_mul]
  rw [hhead, E213.Meta.Int213.zero_add]
  -- expand S(n+1,k+1) = (k+1)·S(n,k+1) + S(n,k)
  rw [sumZ_congr (n + 1)
        (fun k => (stirling2 (n + 1) (k + 1) : Int) * s (k + 1) (m' + 1))
        (fun k =>
          ((k + 1 : Nat) : Int) * ((stirling2 n (k + 1) : Int) * s (k + 1) (m' + 1))
          + (stirling2 n k : Int) * s (k + 1) (m' + 1))
        (fun k _ => by
          show (stirling2 (n + 1) (k + 1) : Int) * s (k + 1) (m' + 1)
             = ((k + 1 : Nat) : Int) * ((stirling2 n (k + 1) : Int) * s (k + 1) (m' + 1))
               + (stirling2 n k : Int) * s (k + 1) (m' + 1)
          rw [stirling2_succ_Z n k]
          generalize ((k + 1 : Nat) : Int) = p
          generalize (stirling2 n (k + 1) : Int) = q
          generalize (stirling2 n k : Int) = r
          generalize (s (k + 1) (m' + 1) : Int) = w
          ring_intZ)]
  -- split into G + H
  rw [sumZ_add (n + 1)
        (fun k => ((k + 1 : Nat) : Int) * ((stirling2 n (k + 1) : Int) * s (k + 1) (m' + 1)))
        (fun k => (stirling2 n k : Int) * s (k + 1) (m' + 1))]
  rw [G_eq n (m' + 1), H_eq n m']
  -- now: f1(n,m'+1) + (U(n,m') − f1(n,m'+1)) = U(n,m')
  generalize (f1 n (m' + 1) : Int) = F
  generalize (U n m' : Int) = V
  ring_intZ

/-! ## Boundary values of `U` -/

theorem U_zero_zero : U 0 0 = 1 := rfl

/-- `U(0, m'+1) = 0`: the only term is `S(0,0)·s(0,m'+1) = 1·0`. -/
theorem U_zero_succ (m' : Nat) : U 0 (m' + 1) = 0 := by
  show sumZ 1 (fun k => (stirling2 0 k : Int) * s k (m' + 1)) = 0
  show (0 : Int) + (stirling2 0 0 : Int) * s 0 (m' + 1) = 0
  show (0 : Int) + (stirling2 0 0 : Int) * (0 : Int) = 0
  rw [E213.Meta.Int213.PolyIntM.mul_zeroZ, Int.add_zero]

/-- `U(n+1, 0) = 0`: `s(k,0)=0` for `k≥1`, and the head `S(n+1,0)·s(0,0)=0`. -/
theorem U_succ_zero (n : Nat) : U (n + 1) 0 = 0 := by
  show sumZ (n + 2) (fun k => (stirling2 (n + 1) k : Int) * s k 0) = 0
  rw [sumZ_split_first (n + 1) (fun k => (stirling2 (n + 1) k : Int) * s k 0)]
  have hhead : (stirling2 (n + 1) 0 : Int) * s 0 0 = 0 := by
    show (((0 : Nat)) : Int) * s 0 0 = 0
    rw [Int.natCast_zero, E213.Meta.Int213.zero_mul]
  rw [hhead, E213.Meta.Int213.zero_add]
  -- tail: every term S(n+1,k+1)·s(k+1,0) = 0 since s(k+1,0)=0
  rw [sumZ_congr (n + 1)
        (fun k => (stirling2 (n + 1) (k + 1) : Int) * s (k + 1) 0)
        (fun _ => (0 : Int))
        (fun k _ => by
          show (stirling2 (n + 1) (k + 1) : Int) * s (k + 1) 0 = 0
          rw [s_succ_zero, E213.Meta.Int213.PolyIntM.mul_zeroZ])]
  rw [sumZ_const_zero (n + 1)]

/-! ## The orthogonality theorem (second ∘ signed-first) -/

/-- ★★★ **Stirling orthogonality, second direction**:
    `Σ_{k} S(n,k)·s(k,m) = δ(n,m)`  for all `n, m`.

    Together with `StirlingOrthogonality.stirling_orthogonality` this shows the
    second-kind and signed-first-kind matrices are TWO-SIDED inverses.

    Induction on `n` (`m` universally quantified).  The step is the clean
    `U(n+1,m'+1) = U(n,m')` recurrence + `delta(n+1,m'+1) = delta(n,m')`. -/
theorem stirling_orthogonality2 : ∀ (n m : Nat), U n m = delta n m
  | 0,     0      => rfl
  | 0,     m' + 1 => by rw [U_zero_succ]; rfl
  | n + 1, 0      => by rw [U_succ_zero]; rfl
  | n + 1, m' + 1 => by
      rw [U_succ_rec n m', stirling_orthogonality2 n m', delta_succ]

/-- Explicit `Σ`-form (unfolds `U` and `delta`). -/
theorem stirling_orthogonality2_sum (n m : Nat) :
    sumZ (n + 1) (fun k => (stirling2 n k : Int) * s k m) = delta n m :=
  stirling_orthogonality2 n m

/-- Orthogonality table check (second direction): `U(n,m) = [n=m]` for `n,m ≤ 4`. -/
theorem U_table :
    U 0 0 = 1 ∧ U 1 1 = 1 ∧ U 2 2 = 1 ∧ U 3 3 = 1 ∧ U 4 4 = 1
    ∧ U 1 0 = 0 ∧ U 2 0 = 0 ∧ U 2 1 = 0 ∧ U 3 1 = 0 ∧ U 3 2 = 0
    ∧ U 4 1 = 0 ∧ U 4 2 = 0 ∧ U 4 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Combinatorics.StirlingOrthogonality2
