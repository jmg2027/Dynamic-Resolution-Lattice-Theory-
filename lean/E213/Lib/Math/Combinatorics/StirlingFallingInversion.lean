import E213.Lib.Math.IncidenceInversion
import E213.Lib.Math.Combinatorics.StirlingFalling

/-!
# The falling factorial is the signed-Stirling expansion of monomials (∅-axiom)

The classical identity `(x)_n = Σ_{k=0}^{n} s(n,k)·x^k` (the falling factorial expanded in
signed Stirling numbers of the first kind) is exactly the **partition-lattice inversion**
(`IncidenceInversion.stirling_inversion_via_engine`) of the forward expansion
`x^n = Σ_{k=0}^{n} S₂(n,k)·(x)_k` (`StirlingFalling.stirling_falling_sum`).

So the two Stirling expansions — monomials in falling factorials (forward, second kind) and
falling factorials in monomials (inverse, signed first kind) — are the two faces of one
antipode on the partition lattice `Π_n`, the same incidence-algebra engine that gives
binomial / Möbius inversion and (on `(ℕ,≤)`) the derangement formula. This is the partition
counterpart of `DerangementInversion` (binomial face).

Companion essay: `theory/essays/proof_isa/incidence_inversion.md` (the engine and its posets).
-/

namespace E213.Lib.Math.Combinatorics.StirlingFallingInversion

open E213.Lib.Math.Combinatorics.BinomialInversion (sumZ sumZ_congr)
open E213.Lib.Math.Combinatorics.StirlingOrthogonality (s)
open E213.Lib.Math.Combinatorics.Stirling (stirling2)
open E213.Lib.Math.Combinatorics.StirlingFalling (ff stirling_falling_sum)
open E213.Lib.Math.IncidenceInversion (stirling_inversion_via_engine)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)

/-- Bridge: the `Nat` range-sum `sumTo`, cast to `Int`, is the engine's `sumZ` of the cast. -/
private theorem sumTo_binZ (F : Nat → Nat) :
    ∀ M, ((sumTo M F : Nat) : Int) = sumZ M (fun k => ((F k : Nat) : Int))
  | 0 => rfl
  | M + 1 => by
      show ((sumTo M F + F M : Nat) : Int) = sumZ M (fun k => ((F k : Nat) : Int)) + ((F M : Nat) : Int)
      rw [Int.ofNat_add, sumTo_binZ F M]

/-- ★★★ **The falling factorial expanded in signed Stirling numbers**:
    `(x)_n = Σ_{k=0}^{n} s(n,k)·x^k`.  A direct instance of the partition-lattice inversion
    `stirling_inversion_via_engine` applied to the forward expansion
    `x^n = Σ_{k≤n} S₂(n,k)·(x)_k` (`stirling_falling_sum`).  The inverse face of the Stirling
    pair on `Π_n` — the partition counterpart of the derangement formula. -/
theorem falling_eq_signed_stirling_pow (x : Nat) :
    ∀ n, ((ff x n : Nat) : Int) = sumZ (n + 1) (fun k => s n k * ((x ^ k : Nat) : Int)) := by
  apply stirling_inversion_via_engine
    (fun k => ((ff x k : Nat) : Int)) (fun n => ((x ^ n : Nat) : Int))
  intro n
  show ((x ^ n : Nat) : Int) = sumZ (n + 1) (fun k => (stirling2 n k : Int) * ((ff x k : Nat) : Int))
  have hcast : ((sumTo (n + 1) (fun k => stirling2 n k * ff x k) : Nat) : Int)
      = ((x ^ n : Nat) : Int) := congrArg (fun m : Nat => (m : Int)) (stirling_falling_sum x n)
  rw [sumTo_binZ (fun k => stirling2 n k * ff x k) (n + 1)] at hcast
  rw [← hcast]
  exact sumZ_congr (n + 1)
    (fun k => (((stirling2 n k * ff x k : Nat)) : Int))
    (fun k => (stirling2 n k : Int) * ((ff x k : Nat) : Int))
    (fun k _ => by
      show (((stirling2 n k * ff x k : Nat)) : Int) = (stirling2 n k : Int) * ((ff x k : Nat) : Int)
      rw [Int.ofNat_mul])

/-- Smoke: `(5)_3 = 5·4·3 = 60 = Σ_{k≤3} s(3,k)·5^k`. -/
theorem falling_signed_stirling_smoke :
    sumZ 4 (fun k => s 3 k * ((5 ^ k : Nat) : Int)) = ((ff 5 3 : Nat) : Int) :=
  (falling_eq_signed_stirling_pow 5 3).symm

end E213.Lib.Math.Combinatorics.StirlingFallingInversion
