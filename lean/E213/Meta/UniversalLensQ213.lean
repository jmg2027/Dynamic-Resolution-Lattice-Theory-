import E213.Meta.UniversalLens
import E213.Kernel.Rat

/-!
# Universal Lens at ℚ × ℚ — using 213-native rational

213's rational arithmetic (`Kernel/Rat.lean`) does NOT define a
separate `ℚ` type — instead, rationals are pairs of `Term`s
(numerator, denominator) with cross-multiplication equivalence:

  p/q ≡ r/s  ⇔  p·s = q·r

So `ℚ` in 213 is `Term × Term`, and `ℚ × ℚ` is
`(Term × Term) × (Term × Term)`.  This gives a true
"ℚ²-discrete" codomain *within 213's native infrastructure*
(no Lean Rat, no Mathlib).

This file constructs `Lens ((Term × Term) × (Term × Term))` using
the same exp-sum encoding, lifted from ℕ × ℕ.
-/

namespace E213.Meta.UniversalLensQ213

open E213.Firmware E213.Hypervisor E213.Kernel

/-- 213-native rational: pair of (numerator, denominator) Terms. -/
abbrev Q213 : Type := Term × Term

/-- Encode Nat as Q213 (n/1). -/
def Q213.ofNat (n : Nat) : Q213 :=
  let rec build : Nat → Term
    | 0 => Term.zero
    | k + 1 => Term.succ (build k)
  (build n, Term.succ Term.zero)

/-- Lens at Q213 × Q213 (= ℚ × ℚ in 213's sense).
    Encoding mirrors `expSumLens` but with Q213 components. -/
def q213Lens : Lens (Q213 × Q213) where
  base_a := (Q213.ofNat 1, Q213.ofNat 0)
  base_b := (Q213.ofNat 2, Q213.ofNat 0)
  combine x y :=
    -- Symmetric combine: encode via (eval-sum, depth)
    let n1 := x.1.1.eval; let m1 := y.1.1.eval
    let n2 := x.2.1.eval; let m2 := y.2.1.eval
    (Q213.ofNat (2 ^ n1 + 2 ^ m1),
     Q213.ofNat (n2 + m2 + 1))

/-- ★★★ Combine is symmetric. -/
theorem q213Lens_symmetric :
    ∀ u v : Q213 × Q213, q213Lens.combine u v = q213Lens.combine v u := by
  intro u v
  show (Q213.ofNat (2^u.1.1.eval + 2^v.1.1.eval),
        Q213.ofNat (u.2.1.eval + v.2.1.eval + 1))
      = (Q213.ofNat (2^v.1.1.eval + 2^u.1.1.eval),
         Q213.ofNat (v.2.1.eval + u.2.1.eval + 1))
  congr 1
  · congr 1; exact Nat.add_comm _ _
  · congr 1; omega

/-- Concrete view: a maps to (1/1, 0/1). -/
theorem q213Lens_view_a :
    q213Lens.view Raw.a = (Q213.ofNat 1, Q213.ofNat 0) := rfl

/-- Concrete view: b maps to (2/1, 0/1). -/
theorem q213Lens_view_b :
    q213Lens.view Raw.b = (Q213.ofNat 2, Q213.ofNat 0) := rfl

/-- ★★★★★ q213Lens distinguishes Raw.a from Raw.b. -/
theorem q213Lens_distinguishes_a_b :
    q213Lens.view Raw.a ≠ q213Lens.view Raw.b := by
  rw [q213Lens_view_a, q213Lens_view_b]
  intro h
  have h1 : Q213.ofNat 1 = Q213.ofNat 2 := (Prod.mk.inj h).1
  have h2 : (Q213.ofNat 1).1 = (Q213.ofNat 2).1 :=
    congrArg Prod.fst h1
  have h3 : Term.eval (Q213.ofNat 1).1 = Term.eval (Q213.ofNat 2).1 := by rw [h2]
  show False
  exact absurd h3 (by decide)

end E213.Meta.UniversalLensQ213
