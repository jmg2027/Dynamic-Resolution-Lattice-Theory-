import E213.Lib.Math.Analysis.UniformLimitContinuous
import E213.Meta.Tactic.NatHelper

/-!
# Cesàro mean convergence — constructive (modulus) form (∅-axiom, vein-C)

Classically: if `a n → L`, the Cesàro averages `S n = (a 0 + … + a (n-1)) / n`
also converge to `L`.  The ε/2 split (early terms shrink as `1/n`, tail terms
already within ε) hides an existential `∃δ`.  ∅-axiom forces the **averaging
modulus into the open**: it is *computed* from the convergence modulus + the
early-term spread `E`.

We work over `Nat`-valued `a` in the dyadic graduation of
`UniformLimitContinuous` (`distN` = `|·−·|`, `closeN` = `2^m·|·| < 2^(L0+1)`).
No real division: "the average `S n` is within `1/2^m` of `L`" is multiplied out
to the pure `Nat` inequality

    closeAvg L0 m n  :=  2^m · |P n − n·L|  <  n · 2^(L0+1)

where `P n = Σ_{k<n} a k` (`= n · S n`).  The forcing heart:

* `psum_close_to_nL` — for an eventually-constant `a` (`∀ k ≥ N, a k = L`,
  the modulus-`r` limit's discrete shadow), `|P n − n·L| ≤ E` for every `n`,
  with `E = Σ_{k<N} |a k − L|` the **fixed** early-term spread (tail terms add 0);
* `cesaro_step` — the averaging step: `2^m · E < n  ⟹  closeAvg L0 m n`;
* `cesaro_converges` — assemble: the computed averaging modulus
  `Nstep m = 2^m · E + 1` (any `n ≥ Nstep m` and `n ≥ N` gives the bound),
  explicit in `r` (via `N`, `E`), not an `∃δ`.
-/

namespace E213.Lib.Math.Analysis.CesaroMean

open E213.Lib.Math.Analysis.UniformLimitContinuous
  (distN distN_symm distN_self distN_tri le_sub_add)

/-! ## 1. Partial sums `P n = Σ_{k<n} a k` and early-spread `E` -/

/-- Partial sum `psum a n = a 0 + a 1 + … + a (n-1)` (`= n · S n`). -/
def psum (a : Nat → Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => psum a n + a n

/-- Early-term spread `spread a L N = Σ_{k<N} |a k − L|`. -/
def spread (a : Nat → Nat) (L : Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => spread a L n + distN (a n) L

/-! ## 2. The core distance bound `|P n − n·L| ≤ E` (tail terms add 0)

The single-step triangle:  `|P (n+1) − (n+1)·L| ≤ |P n − n·L| + |a n − L|`,
since `P (n+1) = P n + a n` and `(n+1)·L = n·L + L`.  Summing, the total gap is
bounded by `Σ_{k<n} |a k − L|`.  For an eventually-constant `a` (`a k = L` once
`k ≥ N`) every term with `k ≥ N` is `0`, so the running sum freezes at `E`. -/

/-- One-step triangle for the partial-sum gap:
    `|P(n+1) − (n+1)L| ≤ |Pn − nL| + |a n − L|`. -/
theorem psum_step_tri (a : Nat → Nat) (L n : Nat) :
    distN (psum a (n + 1)) ((n + 1) * L)
      ≤ distN (psum a n) (n * L) + distN (a n) L := by
  -- psum a (n+1) = psum a n + a n ;  (n+1)*L = n*L + L
  have hP : psum a (n + 1) = psum a n + a n := rfl
  have hnL : (n + 1) * L = n * L + L := by
    rw [E213.Tactic.NatHelper.add_mul, Nat.one_mul]
  rw [hP, hnL]
  -- |(p + a) − (q + b)| ≤ |p − q| + |a − b|  with p=psum,q=nL,a=a n,b=L
  -- use triangle through the midpoint (q + a) = n*L + a n
  -- distN (p+a) (q+b) ≤ distN (p+a) (q+a) + distN (q+a) (q+b)
  have htri : distN (psum a n + a n) (n * L + L)
      ≤ distN (psum a n + a n) (n * L + a n)
        + distN (n * L + a n) (n * L + L) :=
    distN_tri _ _ _
  -- first leg = distN (psum a n) (n*L)  (cancel +a n on the right slot)
  have hleg1 : distN (psum a n + a n) (n * L + a n) = distN (psum a n) (n * L) := by
    show ((psum a n + a n) - (n * L + a n)) + ((n * L + a n) - (psum a n + a n))
       = (psum a n - n * L) + (n * L - psum a n)
    rw [E213.Tactic.NatHelper.add_sub_add_right (psum a n) (a n) (n * L),
        E213.Tactic.NatHelper.add_sub_add_right (n * L) (a n) (psum a n)]
  -- second leg = distN (a n) L  (cancel n*L + on the left slot)
  have hleg2 : distN (n * L + a n) (n * L + L) = distN (a n) L := by
    show ((n * L + a n) - (n * L + L)) + ((n * L + L) - (n * L + a n))
       = (a n - L) + (L - a n)
    rw [E213.Tactic.NatHelper.add_sub_add_left (n * L) (a n) L,
        E213.Tactic.NatHelper.add_sub_add_left (n * L) L (a n)]
  rw [hleg1, hleg2] at htri
  exact htri

/-- **Cumulative bound (general):**  `|P n − n·L| ≤ Σ_{k<n} |a k − L|`. -/
theorem psum_le_spread (a : Nat → Nat) (L : Nat) :
    ∀ n, distN (psum a n) (n * L) ≤ spread a L n := by
  intro n
  induction n with
  | zero =>
      -- distN 0 0 = 0 = spread … 0
      show distN (psum a 0) (0 * L) ≤ spread a L 0
      have : (0 : Nat) * L = 0 := Nat.zero_mul L
      rw [this]
      show distN 0 0 ≤ 0
      rw [distN_self 0]
      exact Nat.le_refl 0
  | succ k ih =>
      have hstep : distN (psum a (k + 1)) ((k + 1) * L)
          ≤ distN (psum a k) (k * L) + distN (a k) L :=
        psum_step_tri a L k
      have hmono : distN (psum a k) (k * L) + distN (a k) L
          ≤ spread a L k + distN (a k) L :=
        Nat.add_le_add_right ih (distN (a k) L)
      -- spread a L (k+1) = spread a L k + distN (a k) L
      have hsp : spread a L (k + 1) = spread a L k + distN (a k) L := rfl
      rw [hsp]
      exact Nat.le_trans hstep hmono

/-- For an eventually-constant `a` (`a k = L` for `k ≥ N`), the spread freezes:
    `spread a L n = spread a L N` for all `n ≥ N` (tail terms add `0`). -/
theorem spread_freezes (a : Nat → Nat) (L N : Nat)
    (hev : ∀ k, k ≥ N → a k = L) :
    ∀ j, spread a L (N + j) = spread a L N := by
  intro j
  induction j with
  | zero => rw [Nat.add_zero]
  | succ j ih =>
      -- spread a L (N + (j+1)) = spread a L (N+j) + distN (a (N+j)) L
      have hidx : N + (j + 1) = (N + j) + 1 := by rw [Nat.add_assoc]
      rw [hidx]
      show spread a L (N + j) + distN (a (N + j)) L = spread a L N
      -- a (N+j) = L  ⟹  distN (a (N+j)) L = 0
      have haL : a (N + j) = L := hev (N + j) (Nat.le_add_right N j)
      rw [haL, distN_self L, Nat.add_zero]
      exact ih

/-- **★ Forcing heart (eventually-constant shadow):**  for `a k = L` once
    `k ≥ N`, the partial-sum gap is bounded by the **fixed** early spread
    `E = spread a L N` at every `n ≥ N`:  `|P n − n·L| ≤ E`. -/
theorem psum_gap_bounded (a : Nat → Nat) (L N : Nat)
    (hev : ∀ k, k ≥ N → a k = L) :
    ∀ n, n ≥ N → distN (psum a n) (n * L) ≤ spread a L N := by
  intro n hn
  obtain ⟨j, hj⟩ := Nat.le.dest hn   -- N + j = n
  have hbound : distN (psum a n) (n * L) ≤ spread a L n := psum_le_spread a L n
  have hfreeze : spread a L n = spread a L N := by
    rw [← hj]; exact spread_freezes a L N hev j
  rw [hfreeze] at hbound
  exact hbound

/-! ## 3. The averaging step + the computed modulus

`closeAvg L0 m n a L`: "the average `S n = P n / n` is within `1/2^m` of `L`"
multiplied out over the denominator `2^(L0+1)` (no division):

    2^m · |P n − n·L|  <  n · 2^(L0+1).

The **computed averaging modulus**: pick `n` with `2^m · E < n`.  Then
`2^m · |P n − n·L| ≤ 2^m · E < n ≤ n · 2^(L0+1)` (since `2^(L0+1) ≥ 1`). -/

/-- The multiplied-out "`S n` within `1/2^m` of `L`" relation (no division). -/
def closeAvg (L0 m n : Nat) (a : Nat → Nat) (L : Nat) : Prop :=
  2 ^ m * distN (psum a n) (n * L) < n * 2 ^ (L0 + 1)

/-- **★ The averaging step:**  if the early spread satisfies `2^m · E < n`
    (and `a` is eventually constant past `N ≤ n`), then the average is within
    `1/2^m`:  `closeAvg L0 m n a L`.  The modulus is **computed**: `n` need only
    exceed `2^m · E`. -/
theorem cesaro_step (a : Nat → Nat) (L L0 N m n : Nat)
    (hev : ∀ k, k ≥ N → a k = L) (hnN : n ≥ N)
    (hbig : 2 ^ m * spread a L N < n) :
    closeAvg L0 m n a L := by
  show 2 ^ m * distN (psum a n) (n * L) < n * 2 ^ (L0 + 1)
  -- |P n − n·L| ≤ E
  have hgap : distN (psum a n) (n * L) ≤ spread a L N :=
    psum_gap_bounded a L N hev n hnN
  -- 2^m · |P n − n·L| ≤ 2^m · E
  have h1 : 2 ^ m * distN (psum a n) (n * L) ≤ 2 ^ m * spread a L N :=
    Nat.mul_le_mul_left _ hgap
  -- 2^m · E < n
  have h2 : 2 ^ m * distN (psum a n) (n * L) < n := Nat.lt_of_le_of_lt h1 hbig
  -- n ≤ n · 2^(L0+1)  since 2^(L0+1) ≥ 1
  have hden : 1 ≤ 2 ^ (L0 + 1) := Nat.pos_pow_of_pos (L0 + 1) (by decide)
  have h3 : n ≤ n * 2 ^ (L0 + 1) := by
    calc n = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * 2 ^ (L0 + 1) := Nat.mul_le_mul_left n hden
  exact Nat.lt_of_lt_of_le h2 h3

/-- **★★ `cesaro_converges` — the headline (∅-axiom, constructive).**

    From an eventually-constant `a` (`a k = L` once `k ≥ N` — the modulus-`r`
    limit's discrete shadow), the Cesàro averages converge to `L` with the
    **explicitly computed averaging modulus**

        Nstep m = N + 2^m · E + 1,        E = spread a L N.

    For every scale `m` and every `n ≥ Nstep m`, the average `S n = P n / n` is
    within `1/2^m` of `L` (`closeAvg L0 m n a L`).  The modulus is *computed*
    from the convergence data (`N`, `E`), not an `∃δ` assertion: it grows
    linearly with `2^m` and the early-term spread `E` — the ε/2 split, in the
    open. -/
theorem cesaro_converges (a : Nat → Nat) (L L0 N : Nat)
    (hev : ∀ k, k ≥ N → a k = L) :
    ∃ Nstep : Nat → Nat,
      (∀ m, Nstep m = N + 2 ^ m * spread a L N + 1) ∧
      (∀ m, ∀ n, n ≥ Nstep m → closeAvg L0 m n a L) := by
  refine ⟨fun m => N + 2 ^ m * spread a L N + 1, fun _ => rfl, ?_⟩
  intro m n hn
  -- hn : n ≥ N + 2^m·E + 1
  -- ⟹ n ≥ N   and   2^m·E < n
  have hge : n ≥ N + 2 ^ m * spread a L N + 1 := hn
  -- n ≥ N
  have hnN : n ≥ N := by
    have hstep1 : N ≤ N + 2 ^ m * spread a L N :=
      Nat.le_add_right N (2 ^ m * spread a L N)
    have hstep2 : N + 2 ^ m * spread a L N ≤ N + 2 ^ m * spread a L N + 1 :=
      Nat.le_add_right _ 1
    exact Nat.le_trans (Nat.le_trans hstep1 hstep2) hge
  -- 2^m·E < n  :  2^m·E < N + 2^m·E + 1 ≤ n
  have hbig : 2 ^ m * spread a L N < n := by
    have hlt : 2 ^ m * spread a L N < N + 2 ^ m * spread a L N + 1 := by
      have h0 : 2 ^ m * spread a L N ≤ N + 2 ^ m * spread a L N :=
        Nat.le_add_left (2 ^ m * spread a L N) N
      exact Nat.lt_of_le_of_lt h0 (Nat.lt_succ_self _)
    exact Nat.lt_of_lt_of_le hlt hge
  exact cesaro_step a L L0 N m n hev hnN hbig

/-! ## 4. Non-vacuous instances

* the **constant sequence** `a ≡ c`: `N = 0`, `E = 0`, the average is `c`
  exactly at every `n ≥ 1` (modulus `Nstep m = 1`);
* a genuinely **eventually-constant** witness whose early spread `E > 0`. -/

/-- The constant sequence `a ≡ c` is its own eventual limit (`N = 0`). -/
theorem const_eventually (c : Nat) :
    ∀ k, k ≥ 0 → (fun _ : Nat => c) k = c := fun _ _ => rfl

/-- For the constant sequence the early spread is `0`. -/
theorem spread_const_zero (c : Nat) :
    ∀ n, spread (fun _ : Nat => c) c n = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show spread (fun _ : Nat => c) c k + distN c c = 0
      rw [distN_self c, Nat.add_zero]
      exact ih

/-- **Constant-sequence instance.**  `cesaro_converges` applies to `a ≡ c` with
    `L = c`, `N = 0`, spread `0`, giving the trivial computed modulus
    `Nstep m = 1`: every average `S n` (`n ≥ 1`) is within `1/2^m` of `c` at
    every scale — the headline is inhabited (and the average is `c` exactly). -/
theorem inhabited_cesaro_const (c L0 : Nat) :
    ∃ Nstep : Nat → Nat,
      (∀ m, Nstep m = 0 + 2 ^ m * spread (fun _ : Nat => c) c 0 + 1) ∧
      (∀ m, ∀ n, n ≥ Nstep m → closeAvg L0 m n (fun _ : Nat => c) c) :=
  cesaro_converges (fun _ : Nat => c) c L0 0 (const_eventually c)

/-- A genuinely **eventually-constant** witness with nonzero early spread:
    `a 0 = L+1`, `a k = L` for `k ≥ 1`.  Then `N = 1`, `E = |a 0 − L| = 1`, and
    the computed modulus is `Nstep m = 1 + 2^m + 1` — the early bump shrinks as
    `1/n`, exactly the Cesàro content with a *computed* rate. -/
def bumpSeq (L : Nat) : Nat → Nat
  | 0     => L + 1
  | _ + 1 => L

/-- `bumpSeq L` is eventually constant past `N = 1`. -/
theorem bump_eventually (L : Nat) :
    ∀ k, k ≥ 1 → bumpSeq L k = L := by
  intro k hk
  obtain ⟨j, hj⟩ := Nat.le.dest hk   -- 1 + j = k
  rw [← hj]
  -- bumpSeq L (1 + j) = L
  show bumpSeq L (1 + j) = L
  rw [Nat.add_comm 1 j]
  rfl

/-- The early spread of `bumpSeq L` at `N = 1` is `1` (`|a 0 − L| = 1`). -/
theorem bump_spread_one (L : Nat) : spread (bumpSeq L) L 1 = 1 := by
  show spread (bumpSeq L) L 0 + distN (bumpSeq L 0) L = 1
  show (0 : Nat) + distN (L + 1) L = 1
  rw [Nat.zero_add]
  show (L + 1 - L) + (L - (L + 1)) = 1
  -- L + 1 - L = 1  (succ_sub);  L - (L+1) = 0  (sub of larger)
  rw [E213.Tactic.NatHelper.succ_sub L]
  -- L - (L+1) = 0  : induction on L, fully pure
  have hz : ∀ k : Nat, k - (k + 1) = 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        show (k + 1) - ((k + 1) + 1) = 0
        -- (k+1) - (k+2) = succ k - succ (k+1) = k - (k+1)  by succ_sub_succ
        rw [Nat.succ_sub_succ_eq_sub k (k + 1)]
        exact ih
  rw [hz L, Nat.add_zero]

/-- **Genuinely-varying instance.**  `cesaro_converges` applied to `bumpSeq L`:
    `N = 1`, `E = 1`, computed modulus `Nstep m = 1 + 2^m · 1 + 1`.  Every
    average past it is within `1/2^m` of `L` — the early bump `a 0 = L+1`
    averages away at the *computed* rate `~ 2^m`. -/
theorem inhabited_cesaro_bump (L L0 : Nat) :
    ∃ Nstep : Nat → Nat,
      (∀ m, Nstep m = 1 + 2 ^ m * spread (bumpSeq L) L 1 + 1) ∧
      (∀ m, ∀ n, n ≥ Nstep m → closeAvg L0 m n (bumpSeq L) L) :=
  cesaro_converges (bumpSeq L) L L0 1 (bump_eventually L)

end E213.Lib.Math.Analysis.CesaroMean
