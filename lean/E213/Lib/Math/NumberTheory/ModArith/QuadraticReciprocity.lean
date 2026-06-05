import E213.Lib.Math.NumberTheory.ModArith.GaussLemma
import E213.Lib.Math.NumberTheory.ModArith.SecondSupplement
import E213.Lib.Math.Algebra.Linalg213.SumLinear
import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Nat.MulMod213
import E213.Lib.Math.NumberTheory.ModArith.CenteredDivision

/-!
# QuadraticReciprocity — Eisenstein lattice-point route (in progress)

Building on `gauss_mu` (`QR(a) ⟺ μ even`, `μ = #{x∈[1,m] : a·x mod p > m}`) toward
`(p/q)(q/p) = (−1)^(((p−1)/2)((q−1)/2))`.

`floor_mod_split` is the summed division identity `Σ a·x = p·Σ⌊a·x/p⌋ + Σ(a·x mod p)` over the
half-system `[1..m]` (the first analytic step of Eisenstein's `μ ≡ Σ⌊a·x/p⌋ (mod 2)`).
Plan: `research-notes/frontiers/quadratic_reciprocity.md`.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.QuadraticReciprocity

open E213.Lib.Math.NumberTheory.ModArith.GaussLemma (seg mem_seg fold fold_perm fold_lo fold_hi sgFn sgFn_lo sgFn_hi)
open E213.Lib.Math.NumberTheory.ModArith.SecondSupplement (countNeg gauss_mu)
open E213.Lib.Math.Algebra.Linalg213.Permutation (sumZ sumZ_lperm map_lperm iota)
open E213.Lib.Math.Algebra.Linalg213.Laplace (sumZ_append map_append')
open E213.Lib.Math.Algebra.Linalg213.PermClosure (map_map')
open E213.Lib.Math.Algebra.Linalg213.SumLinear (sumZ_map_add sumZ_map_sub sumZ_map_const_mul sumZ_swap)
open E213.Lib.Math.NumberTheory.PolyRoot (natCast_add)
open E213.Lib.Math.NumberTheory.ModArith.NonFixedExists (natCast_mul)
open E213.Lib.Math.NumberTheory.ModArith.EulerConverse (natCast_sub)
open E213.Meta.Nat.AddMod213 (div_add_mod dvd_of_mod_eq_zero add_mod_left_pure zero_mod le_div_iff_mul_le)
open E213.Meta.Nat.NatDiv213 (div_lt_of_lt_mul)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure)
open E213.Lib.Math.NumberTheory.ModArith.CenteredDivision (centered_div_int)
open E213.Lib.Math.NumberTheory.FourSquareSeed (nat_prime_dvd_mul)
open E213.Meta.Nat.AddMod213 (mod_two_zero_or_one)
open E213.Tactic.List213 (map_congr)
open E213.Lib.Math.NumberTheory.PolyRoot (int_euclid int_dvd_to_nat nat_dvd_to_int dvd_sub')
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Meta.Int213.Order (sub_self_zero)
open E213.Meta.Int213.PolyIntM (mul_zeroZ)

/-- Elementwise: `↑(a·x) = ↑p·↑(a·x/p) + ↑(a·x mod p)` (`div_add_mod`, cast). -/
private theorem cast_div_mod (a p x : Nat) :
    ((a * x : Nat) : Int) = (p : Int) * ((a * x / p : Nat) : Int) + ((a * x % p : Nat) : Int) := by
  rw [← natCast_mul p (a * x / p), ← natCast_add (p * (a * x / p)) (a * x % p), div_add_mod (a * x) p]

/-- ★ **Summed division identity.**  `Σₓ∈[1,m] a·x = p · Σₓ ⌊a·x/p⌋ + Σₓ (a·x mod p)` (over `ℤ`). -/
theorem floor_mod_split (a p m : Nat) :
    sumZ ((seg m).map (fun x => ((a * x : Nat) : Int)))
      = (p : Int) * sumZ ((seg m).map (fun x => ((a * x / p : Nat) : Int)))
        + sumZ ((seg m).map (fun x => ((a * x % p : Nat) : Int))) := by
  rw [show (seg m).map (fun x => ((a * x : Nat) : Int))
        = (seg m).map (fun x => (p : Int) * ((a * x / p : Nat) : Int) + ((a * x % p : Nat) : Int))
        from map_congr (fun x _ => cast_div_mod a p x),
      sumZ_map_add (fun x => (p : Int) * ((a * x / p : Nat) : Int))
        (fun x => ((a * x % p : Nat) : Int)) (seg m),
      sumZ_map_const_mul (p : Int) (fun x => ((a * x / p : Nat) : Int)) (seg m)]

/-- ★ **The fold-value sum equals the half-system sum.**  `Σₓ ↑(fold a p m x) = Σₓ ↑x` over `[1..m]`,
    since `fold` permutes `[1..m]` (`fold_perm`). -/
theorem fold_sum (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hnpa : ¬ p ∣ a) :
    sumZ ((seg m).map (fun x => ((fold a p m x : Nat) : Int)))
      = sumZ ((seg m).map (fun x => ((x : Nat) : Int))) := by
  rw [show (seg m).map (fun x => ((fold a p m x : Nat) : Int))
        = ((seg m).map (fold a p m)).map (fun n : Nat => (n : Int)) from
      (map_map' (fold a p m) (fun n : Nat => (n : Int)) (seg m)).symm]
  exact sumZ_lperm (map_lperm (fun n : Nat => (n : Int)) (fold_perm a p m hp hpr h2m hnpa))

/-- Per-element evenness: `(↑(a·x%p) − ↑(fold x)) − ↑p·ind = 2·(if r≤m then 0 else ↑(a·x%p) − ↑p)`.
    Low branch `0`; high branch `↑r − (↑p − ↑r) − ↑p = 2(↑r − ↑p)`. -/
private theorem elem_two (a p m x : Nat) (hp : 1 < p) :
    (((a * x % p : Nat) : Int) - ((fold a p m x : Nat) : Int))
        - (p : Int) * (if (a * x) % p ≤ m then (0 : Int) else 1)
      = 2 * (if (a * x) % p ≤ m then (0 : Int) else (((a * x % p : Nat) : Int) - (p : Int))) := by
  rcases Nat.lt_or_ge ((a * x) % p) (m + 1) with hc | hc
  · have hle : (a * x) % p ≤ m := Nat.le_of_lt_succ hc
    rw [fold_lo a p m x hle, if_pos hle, if_pos hle, sub_self_zero, mul_zeroZ, mul_zeroZ,
        sub_self_zero]
  · have hnle : ¬ (a * x) % p ≤ m := fun h => Nat.not_succ_le_self m (Nat.le_trans hc h)
    have hrlt : (a * x) % p < p := Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp))
    rw [fold_hi a p m x hnle, if_neg hnle, if_neg hnle, natCast_sub p ((a * x) % p) (Nat.le_of_lt hrlt)]
    ring_intZ

/-- ★ **Residue-fold evenness (Eisenstein crux).**  `2 ∣ (Σ↑(a·x%p) − Σ↑(fold x) − ↑p·Σ ind)`,
    where `ind = (if (a·x)%p ≤ m then 0 else 1)` is the μ-indicator.  Elementwise `2·(…)`
    (`elem_two`), summed by `sumZ` linearity. -/
theorem residue_fold_even (a p m : Nat) (hp : 1 < p) :
    (2 : Int) ∣ (sumZ ((seg m).map (fun x => ((a * x % p : Nat) : Int)))
        - sumZ ((seg m).map (fun x => ((fold a p m x : Nat) : Int)))
        - (p : Int) * sumZ ((seg m).map (fun x => if (a * x) % p ≤ m then (0 : Int) else 1))) := by
  refine ⟨sumZ ((seg m).map
      (fun x => if (a * x) % p ≤ m then (0 : Int) else (((a * x % p : Nat) : Int) - (p : Int)))), ?_⟩
  rw [← sumZ_map_const_mul (p : Int) (fun x => if (a * x) % p ≤ m then (0 : Int) else 1) (seg m),
      ← sumZ_map_sub (fun x => ((a * x % p : Nat) : Int)) (fun x => ((fold a p m x : Nat) : Int)) (seg m),
      ← sumZ_map_sub (fun x => ((a * x % p : Nat) : Int) - ((fold a p m x : Nat) : Int))
        (fun x => (p : Int) * (if (a * x) % p ≤ m then (0 : Int) else 1)) (seg m),
      ← sumZ_map_const_mul 2
        (fun x => if (a * x) % p ≤ m then (0 : Int) else (((a * x % p : Nat) : Int) - (p : Int))) (seg m)]
  exact congrArg sumZ (map_congr (fun x _ => elem_two a p m x hp))

/-- `Σ ↑(a·x) = ↑a · Σ ↑x` over `[1..m]`. -/
theorem Sa_eq (a m : Nat) :
    sumZ ((seg m).map (fun x => ((a * x : Nat) : Int)))
      = (a : Int) * sumZ ((seg m).map (fun x => ((x : Nat) : Int))) := by
  rw [show (seg m).map (fun x => ((a * x : Nat) : Int))
        = (seg m).map (fun x => (a : Int) * ((x : Nat) : Int)) from
      map_congr (fun x _ => natCast_mul a x),
      sumZ_map_const_mul (a : Int) (fun x => ((x : Nat) : Int)) (seg m)]

/-- `2` is prime (divisor dichotomy).  Pure: `d ∣ 2 ⟹ d ≤ 2 ⟹ d < 3`, case-split (`cases_lt_three`),
    and `0 ∤ 2` via `0 · c = 0 ≠ 2`. -/
private theorem two_prime : ∀ d, d ∣ 2 → d = 1 ∨ d = 2 := fun d hd => by
  have hle : d ≤ 2 := le_of_dvd_pos d 2 (Nat.zero_lt_succ 1) hd
  rcases E213.Tactic.NatHelper.cases_lt_three (Nat.lt_succ_of_le hle) with h0 | h1 | h2
  · subst h0
    obtain ⟨c, hc⟩ := hd
    rw [Nat.zero_mul] at hc
    exact Nat.noConfusion hc
  · exact Or.inl h1
  · exact Or.inr h2

/-- ★ **Eisenstein parity bridge.**  For an odd unit `a` and odd prime `p`:
    `2 ∣ (Σ⌊a·x/p⌋ + Σ ind)` (the floor sum ≡ μ mod 2).  Combines `floor_mod_split`, `Sa_eq`,
    `fold_sum`, `residue_fold_even`, the oddness of `a` (`↑a−1 = 2↑(a/2)`), and `int_euclid` (`p` odd). -/
theorem floor_mu_even (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hnpa : ¬ p ∣ a) (haodd : a % 2 = 1) (hp2 : 2 < p) :
    (2 : Int) ∣ (sumZ ((seg m).map (fun x => ((a * x / p : Nat) : Int)))
        + sumZ ((seg m).map (fun x => if (a * x) % p ≤ m then (0 : Int) else 1))) := by
  have hsplit := floor_mod_split a p m
  rw [Sa_eq a m] at hsplit
  obtain ⟨k, hk⟩ := residue_fold_even a p m hp
  have hfold := fold_sum a p m hp hpr h2m hnpa
  have hcast0 : (a : Int) = 2 * ((a / 2 : Nat) : Int) + 1 := by
    have hae : a = 2 * (a / 2) + 1 := by
      have h := div_add_mod a 2; rw [haodd] at h; exact h.symm
    generalize hb : a / 2 = b at hae ⊢
    rw [hae, natCast_add, natCast_mul, show ((2 : Nat) : Int) = 2 from rfl,
        show ((1 : Nat) : Int) = 1 from rfl]
  generalize hSf : sumZ ((seg m).map (fun x => ((a * x / p : Nat) : Int))) = Sfloor at hsplit ⊢
  generalize hIm : sumZ ((seg m).map (fun x => if (a * x) % p ≤ m then (0 : Int) else 1)) = Imu at hk ⊢
  generalize hSs : sumZ ((seg m).map (fun x => ((x : Nat) : Int))) = Sseg at hsplit hfold
  generalize hSr : sumZ ((seg m).map (fun x => ((a * x % p : Nat) : Int))) = Sr at hsplit hk
  generalize hSfo : sumZ ((seg m).map (fun x => ((fold a p m x : Nat) : Int))) = Sfold at hk hfold
  -- hsplit : ↑a*Sseg = ↑p*Sfloor + Sr ; hk : Sr - Sfold - ↑p*Imu = 2*k ; hfold : Sfold = Sseg
  have e1 : (p : Int) * Sfloor = (a : Int) * Sseg - Sr := by rw [hsplit]; ring_intZ
  have e2 : (p : Int) * Imu = Sr - Sfold - 2 * k := by rw [← hk]; ring_intZ
  have key : (p : Int) * (Sfloor + Imu) = 2 * (((a / 2 : Nat) : Int) * Sseg - k) := by
    have hdist : (p : Int) * (Sfloor + Imu) = (p : Int) * Sfloor + (p : Int) * Imu := by ring_intZ
    rw [hdist, e1, e2, hfold, hcast0]; ring_intZ
  have hnp2 : ¬ (2 : Int) ∣ (p : Int) := fun hd => by
    have h2p : 2 ∣ p := by have := int_dvd_to_nat 2 (p : Int) hd; rwa [Int.natAbs_ofNat] at this
    rcases hpr 2 h2p with h | h
    · exact absurd h (by decide)
    · exact absurd h (Nat.ne_of_lt hp2)
  exact int_euclid 2 (by decide) two_prime (p : Int) (Sfloor + Imu) ⟨_, key⟩ hnp2

/-- The μ-indicator sum equals the μ-count (cast).  Per-element: `(if (a·x)%p ≤ m then 0 else 1)`
    is `1` exactly when `sgFn a p m x = −1`; `countNeg` counts the `−1`s. -/
private theorem ind_sum_countNeg (a p m : Nat) : ∀ (L : List Nat),
    sumZ (L.map (fun x => if (a * x) % p ≤ m then (0 : Int) else 1))
      = ((countNeg (L.map (sgFn a p m)) : Nat) : Int)
  | [] => rfl
  | x :: xs => by
    show (if (a * x) % p ≤ m then (0 : Int) else 1)
          + sumZ (xs.map (fun y => if (a * y) % p ≤ m then (0 : Int) else 1))
       = ((countNeg (xs.map (sgFn a p m)) + (if sgFn a p m x = -1 then 1 else 0) : Nat) : Int)
    rw [ind_sum_countNeg a p m xs]
    rcases Nat.lt_or_ge ((a * x) % p) (m + 1) with hc | hc
    · have hle : (a * x) % p ≤ m := Nat.le_of_lt_succ hc
      rw [if_pos hle, sgFn_lo a p m x hle,
          show (if (1 : Int) = -1 then (1 : Nat) else 0) = 0 from by decide, Nat.add_zero,
          E213.Meta.Int213.zero_add]
    · have hnle : ¬ (a * x) % p ≤ m := fun h => Nat.not_succ_le_self m (Nat.le_trans hc h)
      rw [if_neg hnle, sgFn_hi a p m x hnle,
          show (if (-1 : Int) = -1 then (1 : Nat) else 0) = 1 from by decide,
          natCast_add, show ((1 : Nat) : Int) = 1 from rfl]
      ring_intZ

/-- ★ **The μ-indicator sum equals the μ-count** (over `[1..m]`, cast to `ℤ`):
    `Σₓ (if (a·x)%p ≤ m then 0 else 1) = ↑(countNeg ((seg m).map (sgFn a p m)))`. -/
theorem imu_eq_countNeg (a p m : Nat) :
    sumZ ((seg m).map (fun x => if (a * x) % p ≤ m then (0 : Int) else 1))
      = ((countNeg ((seg m).map (sgFn a p m)) : Nat) : Int) :=
  ind_sum_countNeg a p m (seg m)

/-- `(2·k) % 2 = 0` (pure: `add_mod_left_pure` induction). -/
private theorem two_mul_mod (k : Nat) : (2 * k) % 2 = 0 := by
  induction k with
  | zero => exact zero_mod 2
  | succ k ih =>
    rw [Nat.mul_succ, Nat.add_comm, add_mod_left_pure 2 (2 * k)]; exact ih

/-- `2 ∣ n → n % 2 = 0` (pure). -/
private theorem two_dvd_to_mod (n : Nat) (h : 2 ∣ n) : n % 2 = 0 := by
  obtain ⟨k, hk⟩ := h; rw [hk]; exact two_mul_mod k

/-- **Generalized Gauss μ-criterion** (coprime, residue `z² ≡ a (mod p)`).  For `p ∤ a`,
    `a` is a QR mod `p` (`∃z, z²%p = a%p`) ⟺ `μ` even.  Reduces to `gauss_mu` at `a % p` since
    `sgFn` depends only on `(a·x) mod p` (`mul_mod_left_pure`).  Lets reciprocity apply the bridge at
    `a = q` (the other prime, possibly `> p`). -/
theorem gauss_mu_gen (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (hnpa : ¬ p ∣ a) :
    (∃ z : Nat, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = a % p)
      ↔ countNeg ((seg m).map (sgFn a p m)) % 2 = 0 := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  have h1 : 1 ≤ a % p := Nat.pos_of_ne_zero (fun h0 => hnpa (dvd_of_mod_eq_zero h0))
  have hmodlt : a % p < p := Nat.mod_lt a hppos
  have hsgeq : ∀ x, sgFn a p m x = sgFn (a % p) p m x := fun x => by
    show (if (a * x) % p ≤ m then (1 : Int) else -1)
       = (if ((a % p) * x) % p ≤ m then (1 : Int) else -1)
    rw [mul_mod_left_pure a x p]
  rw [show (seg m).map (sgFn a p m) = (seg m).map (sgFn (a % p) p m) from
        map_congr (fun x _ => hsgeq x)]
  exact gauss_mu (a % p) p m hp hpr h2m hm1 h1 hmodlt

/-- ★ **The Eisenstein bridge (divisibility form).**  For an odd `a` coprime to an odd prime `p`,
    `a` is a quadratic residue mod `p` (`z² ≡ a mod p`) iff the floor sum `Σₓ∈[1,m] ⌊a·x/p⌋` is even.
    Assembles `gauss_mu_gen` (QR ⟺ μ even), `imu_eq_countNeg` (Imu = ↑μ), and `floor_mu_even`
    (`2 ∣ (Sfloor + Imu)`), with the `2∣·` ↔ `·%2=0` casts. -/
theorem floor_qr (a p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m = p - 1) (hm1 : 1 ≤ m) (hnpa : ¬ p ∣ a) (haodd : a % 2 = 1)
    (hp2 : 2 < p) :
    (∃ z : Nat, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = a % p)
      ↔ (2 : Int) ∣ sumZ ((seg m).map (fun x => ((a * x / p : Nat) : Int))) := by
  have hsum : (2 : Int) ∣ (sumZ ((seg m).map (fun x => ((a * x / p : Nat) : Int)))
      + ((countNeg ((seg m).map (sgFn a p m)) : Nat) : Int)) := by
    rw [← imu_eq_countNeg a p m]; exact floor_mu_even a p m hp hpr h2m hnpa haodd hp2
  have hmid : countNeg ((seg m).map (sgFn a p m)) % 2 = 0
      ↔ (2 : Int) ∣ sumZ ((seg m).map (fun x => ((a * x / p : Nat) : Int))) := by
    constructor
    · intro hcn
      have hd : (2 : Int) ∣ ((countNeg ((seg m).map (sgFn a p m)) : Nat) : Int) :=
        nat_dvd_to_int 2 _ (by rw [Int.natAbs_ofNat]; exact dvd_of_mod_eq_zero hcn)
      have hsub := dvd_sub' hsum hd
      have heq : sumZ ((seg m).map (fun x => ((a * x / p : Nat) : Int)))
          + ((countNeg ((seg m).map (sgFn a p m)) : Nat) : Int)
          - ((countNeg ((seg m).map (sgFn a p m)) : Nat) : Int)
          = sumZ ((seg m).map (fun x => ((a * x / p : Nat) : Int))) := by ring_intZ
      rwa [heq] at hsub
    · intro hsf
      have hd : (2 : Int) ∣ ((countNeg ((seg m).map (sgFn a p m)) : Nat) : Int) := by
        have hsub := dvd_sub' hsum hsf
        have heq : sumZ ((seg m).map (fun x => ((a * x / p : Nat) : Int)))
            + ((countNeg ((seg m).map (sgFn a p m)) : Nat) : Int)
            - sumZ ((seg m).map (fun x => ((a * x / p : Nat) : Int)))
            = ((countNeg ((seg m).map (sgFn a p m)) : Nat) : Int) := by ring_intZ
        rwa [heq] at hsub
      exact two_dvd_to_mod _ (by have := int_dvd_to_nat 2 _ hd; rwa [Int.natAbs_ofNat] at this)
  exact (gauss_mu_gen a p m hp hpr h2m hm1 hnpa).trans hmid

/-- **Floor bound for the rectangle count (step 3 prerequisite).**  With `p = 2m+1`, `q = 2n+1`
    and `1 ≤ x ≤ m`, `⌊q·x/p⌋ ≤ n` — so each column's floor count stays within `[1..n]`.  Key:
    `q·x ≤ q·m < p·(n+1)` since `(2m+1)(n+1) = (2n+1)·m + (m+n+1)`. -/
theorem floor_bound (m n x : Nat) (hx : x ≤ m) : (2 * n + 1) * x / (2 * m + 1) ≤ n := by
  apply Nat.le_of_lt_succ
  apply div_lt_of_lt_mul
  apply Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_refl (2 * n + 1)) hx)
  have hexp : (2 * m + 1) * (n + 1) = (2 * n + 1) * m + (m + n + 1) := by ring_nat
  rw [hexp]
  exact Nat.lt_add_of_pos_right (Nat.succ_pos (m + n))

/-! ## Step 3 — the Eisenstein rectangle lattice double-count -/

/-- `seg (n+1) = seg n ++ [n+1]` (since `iota (n+1) = iota n ++ [n]` definitionally). -/
private theorem seg_succ (n : Nat) : seg (n + 1) = seg n ++ [n + 1] := by
  show (iota (n + 1)).map (· + 1) = (iota n).map (· + 1) ++ [n + 1]
  rw [show iota (n + 1) = iota n ++ [n] from rfl, map_append']
  rfl

/-- `Σ_{y∈[1,n]} 1 = n` (over `ℤ`). -/
private theorem count_all : ∀ (n : Nat), sumZ ((seg n).map (fun _ => (1 : Int))) = (n : Int)
  | 0 => rfl
  | n + 1 => by
    rw [seg_succ, map_append', sumZ_append, count_all n]
    show (n : Int) + ((1 : Int) + 0) = ((n + 1 : Nat) : Int)
    rw [natCast_add, show ((1 : Nat) : Int) = (1 : Int) from rfl]
    ring_intZ

/-- `Σ_{y∈[1,n]} [y ≤ K] = K` when `K ≤ n` (over `ℤ`).  Induction on `n`; the boundary `K = n+1`
    uses `count_all` (every `y ∈ [1,n]` satisfies `y ≤ n < K`).  Avoids `Nat.min` (propext-dirty). -/
private theorem count_le_eq (K : Nat) : ∀ (n : Nat), K ≤ n →
    sumZ ((seg n).map (fun y => if y ≤ K then (1 : Int) else 0)) = (K : Int)
  | 0 => fun h => by rw [Nat.le_antisymm h (Nat.zero_le K)]; rfl
  | n + 1 => fun h => by
    rw [seg_succ, map_append', sumZ_append]
    rcases Nat.lt_or_ge K (n + 1) with hlt | hge
    · have hKn : K ≤ n := Nat.le_of_lt_succ hlt
      have hnle : ¬ (n + 1 ≤ K) := fun hc => Nat.not_succ_le_self n (Nat.le_trans hc hKn)
      rw [count_le_eq K n hKn]
      show (K : Int) + ((if n + 1 ≤ K then (1 : Int) else 0) + 0) = (K : Int)
      rw [if_neg hnle]; ring_intZ
    · have hKeq : K = n + 1 := Nat.le_antisymm h hge
      rw [show (seg n).map (fun y => if y ≤ K then (1 : Int) else 0)
            = (seg n).map (fun _ => (1 : Int)) from
          map_congr (fun y hy => by
            rw [if_pos (Nat.le_trans (mem_seg.mp hy).2 (by rw [hKeq]; exact Nat.le_succ n))]),
          count_all n]
      have hyes : n + 1 ≤ K := Nat.le_of_eq hKeq.symm
      show (n : Int) + ((if n + 1 ≤ K then (1 : Int) else 0) + 0) = (K : Int)
      rw [if_pos hyes, hKeq, natCast_add, show ((1 : Nat) : Int) = (1 : Int) from rfl]
      ring_intZ

/-- Per-column predicate swap: `p·y < q·x ⟺ y ≤ ⌊q·x/p⌋` (when `p ∤ q·x`, so `p·y = q·x` is ruled
    out, collapsing `<` to `≤`).  Indicator form. -/
private theorem elem_col (p q x y : Nat) (hp : 0 < p) (hndvd : ¬ p ∣ q * x) :
    (if p * y < q * x then (1 : Int) else 0) = (if y ≤ q * x / p then (1 : Int) else 0) := by
  rcases Nat.lt_or_ge (p * y) (q * x) with hlt | hge
  · have hyle : y ≤ q * x / p :=
      (le_div_iff_mul_le hp y (q * x)).mpr (by rw [Nat.mul_comm y p]; exact Nat.le_of_lt hlt)
    rw [if_pos hlt, if_pos hyle]
  · have hLneg : ¬ p * y < q * x := fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h hge)
    have hRneg : ¬ y ≤ q * x / p := fun hyle => by
      have h1 : y * p ≤ q * x := (le_div_iff_mul_le hp y (q * x)).mp hyle
      have h2 : p * y ≤ q * x := by rw [Nat.mul_comm p y]; exact h1
      exact hndvd ⟨y, Nat.le_antisymm hge h2⟩
    rw [if_neg hLneg, if_neg hRneg]

/-- ★ **Per-column lattice count.**  For `0 < p`, `p ∤ q·x`, `⌊q·x/p⌋ ≤ n`, the number of
    `y ∈ [1,n]` with `p·y < q·x` is exactly `⌊q·x/p⌋` (over `ℤ`).  `elem_col` + `count_le_eq`. -/
private theorem colCount_eq_floor (p q x n : Nat) (hp : 0 < p) (hndvd : ¬ p ∣ q * x)
    (hbnd : q * x / p ≤ n) :
    sumZ ((seg n).map (fun y => if p * y < q * x then (1 : Int) else 0))
      = ((q * x / p : Nat) : Int) := by
  rw [show (seg n).map (fun y => if p * y < q * x then (1 : Int) else 0)
        = (seg n).map (fun y => if y ≤ q * x / p then (1 : Int) else 0) from
      map_congr (fun y _ => elem_col p q x y hp hndvd)]
  exact count_le_eq (q * x / p) n hbnd

/-- Trichotomy at a lattice point: exactly one of `p·y < q·x`, `q·x < p·y` holds (no equality, since
    `q·x = p·y ⟹ p ∣ q·x`), so the two indicators sum to `1`. -/
private theorem elem_tri (p q x y : Nat) (hndvd : ¬ p ∣ q * x) :
    (if p * y < q * x then (1 : Int) else 0) + (if q * x < p * y then (1 : Int) else 0) = 1 := by
  rcases Nat.lt_or_ge (p * y) (q * x) with hlt | hge
  · have hn2 : ¬ q * x < p * y := fun h => Nat.lt_irrefl _ (Nat.lt_trans hlt h)
    rw [if_pos hlt, if_neg hn2]; ring_intZ
  · have hne : q * x ≠ p * y := fun he => hndvd ⟨y, he⟩
    have hqxlt : q * x < p * y := Nat.lt_of_le_of_ne hge hne
    have hn1 : ¬ p * y < q * x := fun h => Nat.lt_irrefl _ (Nat.lt_trans h hqxlt)
    rw [if_neg hn1, if_pos hqxlt]; ring_intZ

/-- ★★ **Eisenstein rectangle double-count.**  For `p = 2m+1`, `q = 2n+1` with `p ∤ q·x`
    (`x ∈ [1,m]`) and `q ∤ p·y` (`y ∈ [1,n]`):
    `Σ_{x∈[1,m]} ⌊q·x/p⌋ + Σ_{y∈[1,n]} ⌊p·y/q⌋ = m·n` (over `ℤ`).  Both sums count lattice points
    of `[1,m]×[1,n]` on either side of the diagonal `q·x = p·y` (no point ON it).  Columns/rows via
    `colCount_eq_floor`; the cross term swaps by `sumZ_swap` (Fubini); `elem_tri` collapses the grid
    to `Σ_x Σ_y 1 = m·n`. -/
theorem floor_sum_rectangle (m n p q : Nat) (hp : 0 < p) (hq : 0 < q)
    (hpf : p = 2 * m + 1) (hqf : q = 2 * n + 1)
    (hcol : ∀ x, x ∈ seg m → ¬ p ∣ q * x)
    (hrow : ∀ y, y ∈ seg n → ¬ q ∣ p * y) :
    sumZ ((seg m).map (fun x => ((q * x / p : Nat) : Int)))
      + sumZ ((seg n).map (fun y => ((p * y / q : Nat) : Int)))
      = ((m * n : Nat) : Int) := by
  have hColBnd : ∀ x, x ∈ seg m → q * x / p ≤ n := fun x hx => by
    rw [hpf, hqf]; exact floor_bound m n x (mem_seg.mp hx).2
  have hRowBnd : ∀ y, y ∈ seg n → p * y / q ≤ m := fun y hy => by
    rw [hpf, hqf]; exact floor_bound n m y (mem_seg.mp hy).2
  have hCol : sumZ ((seg m).map (fun x => ((q * x / p : Nat) : Int)))
      = sumZ ((seg m).map (fun x =>
          sumZ ((seg n).map (fun y => if p * y < q * x then (1 : Int) else 0)))) :=
    congrArg sumZ (map_congr (fun x hx =>
      (colCount_eq_floor p q x n hp (hcol x hx) (hColBnd x hx)).symm))
  have hRow : sumZ ((seg n).map (fun y => ((p * y / q : Nat) : Int)))
      = sumZ ((seg n).map (fun y =>
          sumZ ((seg m).map (fun x => if q * x < p * y then (1 : Int) else 0)))) :=
    congrArg sumZ (map_congr (fun y hy =>
      (colCount_eq_floor q p y m hq (hrow y hy) (hRowBnd y hy)).symm))
  rw [hCol, hRow, sumZ_swap (fun y x => if q * x < p * y then (1 : Int) else 0) (seg n) (seg m),
      ← sumZ_map_add
        (fun x => sumZ ((seg n).map (fun y => if p * y < q * x then (1 : Int) else 0)))
        (fun x => sumZ ((seg n).map (fun y => if q * x < p * y then (1 : Int) else 0))) (seg m)]
  have hInner : ∀ x, x ∈ seg m →
      sumZ ((seg n).map (fun y => if p * y < q * x then (1 : Int) else 0))
        + sumZ ((seg n).map (fun y => if q * x < p * y then (1 : Int) else 0)) = (n : Int) := by
    intro x hx
    rw [← sumZ_map_add (fun y => if p * y < q * x then (1 : Int) else 0)
          (fun y => if q * x < p * y then (1 : Int) else 0) (seg n),
        show (seg n).map (fun y =>
              (if p * y < q * x then (1 : Int) else 0) + (if q * x < p * y then (1 : Int) else 0))
            = (seg n).map (fun _ => (1 : Int)) from
          map_congr (fun y _ => elem_tri p q x y (hcol x hx)),
        count_all n]
  rw [show (seg m).map (fun x =>
          sumZ ((seg n).map (fun y => if p * y < q * x then (1 : Int) else 0))
            + sumZ ((seg n).map (fun y => if q * x < p * y then (1 : Int) else 0)))
        = (seg m).map (fun _ => (n : Int)) from map_congr hInner,
      show (seg m).map (fun _ => (n : Int)) = (seg m).map (fun _ => (n : Int) * 1) from
        map_congr (fun x _ => (E213.Meta.Int213.mul_one (n : Int)).symm),
      sumZ_map_const_mul (n : Int) (fun _ => (1 : Int)) (seg m), count_all m, natCast_mul]
  ring_intZ

/-! ## Step 4 — assembly into the law of quadratic reciprocity -/

/-- Every integer is even or odd (witness form, via `centered_div_int`). -/
private theorem int_even_or_odd (a : Int) : (∃ k, a = 2 * k) ∨ (∃ k, a = 2 * k + 1) := by
  obtain ⟨q, r, hd, hr⟩ := centered_div_int a 2 (by decide)
  rw [show (2 : Int).natAbs = 2 from rfl] at hr
  have hle : r.natAbs ≤ 1 := by
    rcases Nat.lt_or_ge r.natAbs 2 with h | h
    · exact Nat.le_of_lt_succ h
    · exact absurd (Nat.le_trans (Nat.mul_le_mul_left 2 h) hr) (by decide)
  rcases E213.Tactic.NatHelper.cases_lt_two (Nat.lt_succ_of_le hle) with h0 | h1
  · left; refine ⟨q, ?_⟩
    have hr0 : r = 0 := by rcases Int.natAbs_eq r with he | he <;> rw [he, h0] <;> decide
    rw [hd, hr0, Int.add_zero]; ring_intZ
  · rcases Int.natAbs_eq r with he | he
    · right; exact ⟨q, by rw [hd, he, h1, show ((1 : Nat) : Int) = 1 from rfl]; ring_intZ⟩
    · right; exact ⟨q - 1, by rw [hd, he, h1, show ((1 : Nat) : Int) = 1 from rfl]; ring_intZ⟩

/-- `2·w ≠ 1` over `ℤ`. -/
private theorem two_mul_ne_one (w : Int) : 2 * w ≠ 1 := fun h => by
  have h2 : 2 ∣ (1 : Int).natAbs := int_dvd_to_nat 2 1 ⟨w, h.symm⟩
  rw [Int.natAbs_one] at h2
  exact absurd (le_of_dvd_pos 2 1 (by decide) h2) (by decide)

/-- `↑N = 2·W ⟹ N` even. -/
private theorem even_cast (N : Nat) (W : Int) (h : (N : Int) = 2 * W) : N % 2 = 0 :=
  two_dvd_to_mod N (by have := int_dvd_to_nat 2 (N : Int) ⟨W, h⟩; rwa [Int.natAbs_ofNat] at this)

/-- `↑N = 2·W + 1 ⟹ N` odd. -/
private theorem odd_cast (N : Nat) (W : Int) (h : (N : Int) = 2 * W + 1) : N % 2 = 1 := by
  have hni : ¬ (2 : Int) ∣ (N : Int) := fun ⟨c, hc⟩ =>
    two_mul_ne_one (c - W) (by
      rw [show (2 : Int) * (c - W) = 2 * c - 2 * W from by ring_intZ, ← hc, h]; ring_intZ)
  have hnn : ¬ 2 ∣ N := fun hd => hni (nat_dvd_to_int 2 (N : Int) (by rw [Int.natAbs_ofNat]; exact hd))
  rcases mod_two_zero_or_one N with h0 | h1
  · exact absurd (dvd_of_mod_eq_zero h0) hnn
  · exact h1

/-- Parity of a sum: with `S + T = ↑N`, the indicators `2∣S`, `2∣T` agree iff `N` is even. -/
private theorem parity_sum_iff (S T : Int) (N : Nat) (h : S + T = (N : Int)) :
    ((2 : Int) ∣ S ↔ (2 : Int) ∣ T) ↔ N % 2 = 0 := by
  rcases int_even_or_odd S with ⟨sk, hs⟩ | ⟨sk, hs⟩ <;>
    rcases int_even_or_odd T with ⟨tk, ht⟩ | ⟨tk, ht⟩
  · exact ⟨fun _ => even_cast N (sk + tk) (by rw [← h, hs, ht]; ring_intZ),
      fun _ => ⟨fun _ => ⟨tk, ht⟩, fun _ => ⟨sk, hs⟩⟩⟩
  · have hNodd : N % 2 = 1 := odd_cast N (sk + tk) (by rw [← h, hs, ht]; ring_intZ)
    have hTnot : ¬ (2 : Int) ∣ T := fun ⟨c, hc⟩ =>
      two_mul_ne_one (c - tk) (by
        rw [show (2 : Int) * (c - tk) = 2 * c - 2 * tk from by ring_intZ, ← hc, ht]; ring_intZ)
    exact ⟨fun hiff => absurd (hiff.mp ⟨sk, hs⟩) hTnot,
      fun hN0 => absurd (hN0.symm.trans hNodd) (by decide)⟩
  · have hNodd : N % 2 = 1 := odd_cast N (sk + tk) (by rw [← h, hs, ht]; ring_intZ)
    have hSnot : ¬ (2 : Int) ∣ S := fun ⟨c, hc⟩ =>
      two_mul_ne_one (c - sk) (by
        rw [show (2 : Int) * (c - sk) = 2 * c - 2 * sk from by ring_intZ, ← hc, hs]; ring_intZ)
    exact ⟨fun hiff => absurd (hiff.mpr ⟨tk, ht⟩) hSnot,
      fun hN0 => absurd (hN0.symm.trans hNodd) (by decide)⟩
  · have hNeven : N % 2 = 0 := even_cast N (sk + tk + 1) (by rw [← h, hs, ht]; ring_intZ)
    have hSnot : ¬ (2 : Int) ∣ S := fun ⟨c, hc⟩ =>
      two_mul_ne_one (c - sk) (by
        rw [show (2 : Int) * (c - sk) = 2 * c - 2 * sk from by ring_intZ, ← hc, hs]; ring_intZ)
    have hTnot : ¬ (2 : Int) ∣ T := fun ⟨c, hc⟩ =>
      two_mul_ne_one (c - tk) (by
        rw [show (2 : Int) * (c - tk) = 2 * c - 2 * tk from by ring_intZ, ← hc, ht]; ring_intZ)
    exact ⟨fun _ => hNeven, fun _ => ⟨fun hS => absurd hS hSnot, fun hT => absurd hT hTnot⟩⟩

/-- `p` prime, `x ∈ [1,m]`, `m < p` ⟹ `p ∤ x`. -/
private theorem not_dvd_seg (p m x : Nat) (hmp : m < p) (hx : x ∈ seg m) : ¬ p ∣ x := by
  obtain ⟨hx1, hxm⟩ := mem_seg.mp hx
  exact fun hpx => Nat.lt_irrefl x
    (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hxm hmp) (le_of_dvd_pos p x hx1 hpx))

/-- ★★★★★ **The law of quadratic reciprocity.**  For distinct odd primes `p, q` with
    `m = (p−1)/2`, `n = (q−1)/2`: `q` is a quadratic residue mod `p` iff `p` is a quadratic residue
    mod `q` — agreeing exactly when `m·n` is even (i.e. unless both `p ≡ q ≡ 3 mod 4`).  Eisenstein
    form.  Assembles the generalized `floor_qr` (at residues `q`, `p`) with `floor_sum_rectangle`
    (`Σ⌊qx/p⌋ + Σ⌊py/q⌋ = m·n`) via `parity_sum_iff`. -/
theorem quadratic_reciprocity (p q m n : Nat)
    (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (hp2 : 2 < p) (hpm : 2 * m = p - 1)
    (hm1 : 1 ≤ m) (hpodd : p % 2 = 1)
    (hq : 1 < q) (hqr : ∀ d, d ∣ q → d = 1 ∨ d = q) (hq2 : 2 < q) (hqn : 2 * n = q - 1)
    (hn1 : 1 ≤ n) (hqodd : q % 2 = 1) (hpqne : p ≠ q) :
    ((∃ z : Nat, 1 ≤ z ∧ z < p ∧ z ^ 2 % p = q % p)
        ↔ (∃ z : Nat, 1 ≤ z ∧ z < q ∧ z ^ 2 % q = p % q))
      ↔ (m * n) % 2 = 0 := by
  have hppos : 0 < p := Nat.lt_trans Nat.zero_lt_one hp
  have hqpos : 0 < q := Nat.lt_trans Nat.zero_lt_one hq
  have hpf : p = 2 * m + 1 := by rw [hpm]; exact (Nat.succ_pred_eq_of_pos hppos).symm
  have hqf : q = 2 * n + 1 := by rw [hqn]; exact (Nat.succ_pred_eq_of_pos hqpos).symm
  have hmp : m < p := by
    rw [hpf]
    exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_left m m) (Nat.le_of_eq (Nat.two_mul m).symm))
  have hnq : n < q := by
    rw [hqf]
    exact Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_left n n) (Nat.le_of_eq (Nat.two_mul n).symm))
  have hnpq : ¬ p ∣ q := fun hd =>
    (hqr p hd).elim (fun h => absurd h (Nat.ne_of_gt hp)) (fun h => hpqne h)
  have hnqp : ¬ q ∣ p := fun hd =>
    (hpr q hd).elim (fun h => absurd h (Nat.ne_of_gt hq)) (fun h => hpqne h.symm)
  have hA := floor_qr q p m hp hpr hpm hm1 hnpq hqodd hp2
  have hB := floor_qr p q n hq hqr hqn hn1 hnqp hpodd hq2
  have hcol : ∀ x, x ∈ seg m → ¬ p ∣ q * x := fun x hx hd =>
    (nat_prime_dvd_mul p hp hpr q x hd).elim hnpq (not_dvd_seg p m x hmp hx)
  have hrow : ∀ y, y ∈ seg n → ¬ q ∣ p * y := fun y hy hd =>
    (nat_prime_dvd_mul q hq hqr p y hd).elim hnqp (not_dvd_seg q n y hnq hy)
  have hRect := floor_sum_rectangle m n p q hppos hqpos hpf hqf hcol hrow
  refine Iff.trans ?_ (parity_sum_iff _ _ (m * n) hRect)
  exact ⟨fun hxy => hA.symm.trans (hxy.trans hB), fun hst => hA.trans (hst.trans hB.symm)⟩

end E213.Lib.Math.NumberTheory.ModArith.QuadraticReciprocity
