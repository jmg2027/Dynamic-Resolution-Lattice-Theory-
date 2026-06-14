import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyLattice
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.FiniteOrderSpectrum

/-!
# HolonomyOrderLaw — the general order law for holonomy loops (∅-axiom)

Item (2) of the holonomy-lattice frontier (`research-notes/frontiers/INDEX.md`
"holonomy_lattice"): lift `FiniteOrderSpectrum` onto the holonomy fold.

The two modules use two different folds — `holonomy` right-folds a `List Mat2` to
`I` (`HolonomyLattice`), `pow` left-folds to `I` (`Mat2.Mat2TraceRecurrence`).  On
a *constant* list they coincide: **`holonomy_replicate`** bridges them
(`holonomy (replicate n g) = pow g n`, via `g` commuting with its own powers).
The crystallographic restriction then transfers: a holonomy loop that repeats a
single flat (`det = 1`) state-transition closes only at a length dividing 12
(**`holonomy_pow_order`**), and the fold loop `S` (`[S,S,S,S] = I`) is now a
*corollary* of the order spectrum, not a standalone `decide`.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyOrderLaw

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace.Mat2 (mul I det S)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyLattice
  (holonomy L positive_loop_trivial PositiveWord)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2TraceRecurrence (pow)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Assoc (mul_assoc)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.FiniteOrderSpectrum
  (finite_order_divides_twelve exact_order_four I_mul mul_I)

/-- A transition `g` commutes with its own powers: `g · gⁿ = gⁿ · g`. -/
theorem pow_succ_comm (g : Mat2) : ∀ n, mul g (pow g n) = mul (pow g n) g
  | 0     => by rw [show pow g 0 = I from rfl, I_mul, mul_I]
  | n + 1 => by
      show mul g (mul (pow g n) g) = mul (mul (pow g n) g) g
      rw [← mul_assoc, pow_succ_comm g n]

/-- ★★★ **The bridge: holonomy of an `n`-fold repeat is the `n`-th power.**  The
    right-fold `holonomy` and the left-fold `pow` agree on a constant list — the
    loop that repeats one transition `g` `n` times has holonomy `gⁿ`. -/
theorem holonomy_replicate (g : Mat2) :
    ∀ n, holonomy (List.replicate n g) = pow g n
  | 0     => rfl
  | n + 1 => by
      show mul g (holonomy (List.replicate n g)) = pow g (n + 1)
      rw [holonomy_replicate g n]
      exact pow_succ_comm g n

/-- ★★★★ **General order law for holonomy loops.**  If a loop that repeats a
    single flat (`det = 1`) transition `g` closes at some non-trivial length
    `n+1`, then the 12-fold repeat closes — the crystallographic restriction
    (`order ∣ 12`, spectrum `{1,2,3,4,6}`) read on the holonomy fold. -/
theorem holonomy_pow_order (g : Mat2) (hdet : det g = 1) (n : Nat)
    (h : holonomy (List.replicate (n + 1) g) = I) :
    holonomy (List.replicate 12 g) = I := by
  rw [holonomy_replicate] at h ⊢
  exact finite_order_divides_twelve g hdet n h

/-- The elliptic fold loop `S` closes at 4 — now a corollary of the order
    spectrum (`pow S 4 = I`, `exact_order_four`) through the bridge, rather than a
    standalone `decide` on `[S,S,S,S]`. -/
theorem holonomy_S_loop_closes : holonomy (List.replicate 4 S) = I := by
  rw [holonomy_replicate]; exact exact_order_four.1

/-- Every element of `replicate n a` equals `a` (pure structural `Mem` recursion —
    avoids the propext-tainted core `List.eq_of_mem_replicate`). -/
theorem all_eq_of_replicate {a : Mat2} : ∀ {n} (g : Mat2), g ∈ List.replicate n a → g = a
  | 0,     g, h => by cases h
  | _ + 1, g, h => by
      cases h with
      | head      => rfl
      | tail _ h' => exact all_eq_of_replicate g h'

/-- **The positive generator `L` never closes a loop** (contrast with `S`): the
    Stern–Brocot monoid `⟨L,R⟩` is free, so no `n`-fold `L`-repeat returns to `I`.
    `positive_loop_trivial` through the bridge. -/
theorem holonomy_L_loop_never_closes (n : Nat) :
    holonomy (List.replicate (n + 1) L) ≠ I := by
  refine positive_loop_trivial (fun g hg => Or.inl (all_eq_of_replicate g hg)) ?_
  exact fun hcon => List.noConfusion hcon

end E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyOrderLaw
