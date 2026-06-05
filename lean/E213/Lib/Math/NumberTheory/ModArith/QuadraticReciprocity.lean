import E213.Lib.Math.NumberTheory.ModArith.GaussLemma
import E213.Lib.Math.Algebra.Linalg213.SumLinear

/-!
# QuadraticReciprocity — Eisenstein lattice-point route (in progress)

Building on `gauss_mu` (`QR(a) ⟺ μ even`, `μ = #{x∈[1,m] : a·x mod p > m}`) toward
`(p/q)(q/p) = (−1)^(((p−1)/2)((q−1)/2))`.

`floor_mod_split` is the summed division identity `Σ a·x = p·Σ⌊a·x/p⌋ + Σ(a·x mod p)` over the
half-system `[1..m]` (the first analytic step of Eisenstein's `μ ≡ Σ⌊a·x/p⌋ (mod 2)`).
Plan: `research-notes/frontiers/quadratic_reciprocity.md`.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.QuadraticReciprocity

open E213.Lib.Math.NumberTheory.ModArith.GaussLemma (seg fold fold_perm fold_lo fold_hi)
open E213.Lib.Math.Algebra.Linalg213.Permutation (sumZ sumZ_lperm map_lperm)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (map_map')
open E213.Lib.Math.Algebra.Linalg213.SumLinear (sumZ_map_add sumZ_map_sub sumZ_map_const_mul)
open E213.Lib.Math.NumberTheory.PolyRoot (natCast_add)
open E213.Lib.Math.NumberTheory.ModArith.NonFixedExists (natCast_mul)
open E213.Lib.Math.NumberTheory.ModArith.EulerConverse (natCast_sub)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Tactic.List213 (map_congr)
open E213.Lib.Math.NumberTheory.PolyRoot (int_euclid int_dvd_to_nat)
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
    (h2m : 2 * m = p - 1) (ha1 : 1 ≤ a) (halt : a < p) :
    sumZ ((seg m).map (fun x => ((fold a p m x : Nat) : Int)))
      = sumZ ((seg m).map (fun x => ((x : Nat) : Int))) := by
  rw [show (seg m).map (fun x => ((fold a p m x : Nat) : Int))
        = ((seg m).map (fold a p m)).map (fun n : Nat => (n : Int)) from
      (map_map' (fold a p m) (fun n : Nat => (n : Int)) (seg m)).symm]
  exact sumZ_lperm (map_lperm (fun n : Nat => (n : Int)) (fold_perm a p m hp hpr h2m ha1 halt))

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
    (h2m : 2 * m = p - 1) (ha1 : 1 ≤ a) (halt : a < p) (haodd : a % 2 = 1) (hp2 : 2 < p) :
    (2 : Int) ∣ (sumZ ((seg m).map (fun x => ((a * x / p : Nat) : Int)))
        + sumZ ((seg m).map (fun x => if (a * x) % p ≤ m then (0 : Int) else 1))) := by
  have hsplit := floor_mod_split a p m
  rw [Sa_eq a m] at hsplit
  obtain ⟨k, hk⟩ := residue_fold_even a p m hp
  have hfold := fold_sum a p m hp hpr h2m ha1 halt
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

end E213.Lib.Math.NumberTheory.ModArith.QuadraticReciprocity
