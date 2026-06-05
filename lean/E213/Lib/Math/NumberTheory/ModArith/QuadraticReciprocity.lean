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

open E213.Lib.Math.NumberTheory.ModArith.GaussLemma (seg)
open E213.Lib.Math.Algebra.Linalg213.Permutation (sumZ)
open E213.Lib.Math.Algebra.Linalg213.SumLinear (sumZ_map_add sumZ_map_const_mul)
open E213.Lib.Math.NumberTheory.PolyRoot (natCast_add)
open E213.Lib.Math.NumberTheory.ModArith.NonFixedExists (natCast_mul)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Tactic.List213 (map_congr)

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

end E213.Lib.Math.NumberTheory.ModArith.QuadraticReciprocity
