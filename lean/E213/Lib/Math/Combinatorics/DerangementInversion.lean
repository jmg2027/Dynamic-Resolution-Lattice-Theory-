import E213.Lib.Math.IncidenceInversion
import E213.Lib.Math.Combinatorics.DerangementConvolution

/-!
# Derangements are the binomial inverse of the factorial (∅-axiom)

The classical derangement formula `D(n) = Σ_{k=0}^{n} (−1)^{n−k}·C(n,k)·k!` is exactly the
**binomial inversion** (additive-cut antipode, `IncidenceInversion.binomial_inversion_via_engine`)
of the permutation–derangement identity `n! = Σ_{k=0}^{n} C(n,k)·D(k)`
(`DerangementConvolution.TZ_eq_fact`).

So inclusion–exclusion for derangements is **not** a separate technique — it is the Boolean
lattice's Möbius/antipode applied to the forward identity, the same incidence-algebra engine
that gives binomial and (on other posets) Möbius and Stirling inversion. The forward identity
(`Σ C(n,k)D(k) = n!`) and its inverse (`D(n) = Σ sb(n,k)·k!`) are the two faces of one
antipode on `(ℕ,≤)`.

Companion essay: `theory/essays/proof_isa/incidence_inversion.md` (the engine and its posets).
-/

namespace E213.Lib.Math.Combinatorics.DerangementInversion

open E213.Lib.Math.Combinatorics.BinomialInversion (sumZ sb)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.IncidenceInversion (binomial_inversion_via_engine)
open E213.Lib.Math.Combinatorics.DerangementConvolution (TZ_eq_fact)
open E213.Lib.Math.Combinatorics.Derangements (derange)
open E213.Lib.Math.Combinatorics.Permutations (fact)

/-- Bridge: the engine's `sumZ` and the alternating-binomial `sumZ` are the same fold
    (identical definitions, distinct names). -/
private theorem bin_alt_sumZ (f : Nat → Int) :
    ∀ N, sumZ N f
      = E213.Lib.Math.NumberTheory.DyadicFSM.FLT.AlternatingBinomial.sumZ N f
  | 0 => rfl
  | N + 1 => by
      show sumZ N f + f N
         = E213.Lib.Math.NumberTheory.DyadicFSM.FLT.AlternatingBinomial.sumZ N f + f N
      rw [bin_alt_sumZ f N]

/-- ★★★ **Derangements are the binomial inverse of the factorial.**  From the forward
    identity `n! = Σ_{k≤n} C(n,k)·D(k)` (`TZ_eq_fact`), the additive-cut antipode recovers the
    classical derangement formula

      `D(n) = Σ_{k=0}^{n} (−1)^{n−k}·C(n,k)·k!`   (sign carried by `sb n k`).

    A direct instance of `binomial_inversion_via_engine` — inclusion–exclusion for
    derangements is the Boolean-lattice antipode on `(ℕ,≤)`, not a separate technique. -/
theorem derange_eq_binomial_inverse_fact :
    ∀ n, (derange n : Int) = sumZ (n + 1) (fun k => sb n k * (fact k : Int)) := by
  apply binomial_inversion_via_engine (fun k => (derange k : Int)) (fun n => (fact n : Int))
  intro n
  show (fact n : Int) = sumZ (n + 1) (fun k => (choose n k : Int) * (derange k : Int))
  rw [bin_alt_sumZ (fun k => (choose n k : Int) * (derange k : Int)) (n + 1)]
  exact (TZ_eq_fact n).symm

/-- Smoke: `D(4) = Σ_{k≤4} (−1)^{4−k} C(4,k) k! = 9`. -/
theorem derange_binomial_inverse_smoke :
    sumZ 5 (fun k => sb 4 k * (fact k : Int)) = (derange 4 : Int) :=
  (derange_eq_binomial_inverse_fact 4).symm

end E213.Lib.Math.Combinatorics.DerangementInversion
