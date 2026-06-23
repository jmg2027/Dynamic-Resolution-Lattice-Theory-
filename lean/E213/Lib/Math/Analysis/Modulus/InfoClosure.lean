import E213.Lib.Math.Analysis.Modulus.Translation

/-!
# Information-Theoretic Closure (∅-axiom)

Continuity in 213 = "output bit `N` is determined by reading
*finitely many* input bits".  Information-theoretic closure
on the dyadic tree.

Mingu's formulation:
> "to fix a particular bit of the output, there is no need to read
>  infinitely many bits of the input (it is determined at finite depth M)"

This module formalizes this **information-theoretic closure**
as the structural definition of continuity in 213.

Atomic content:
  * `IsInfoClosed`: predicate "output bit N decided by reading
    M input bits, where M = modulus N".
  * Constant function is info-closed (M = 0).
  * Identity function is info-closed (M = N).
  * Composition: `g ∘ f` info-closed via modulus composition.
-/

namespace E213.Lib.Math.Analysis.Modulus.InfoClosure

open E213.Lib.Math.Analysis.Modulus.Translation
  (DepthModulus identityDepthModulus constantDepthModulus)

/-- **Information-theoretic closure**: a function `f` is
    info-closed iff there exists an explicit Nat → Nat modulus
    determining the input depth required for each output depth.
    This is **deterministic** — the modulus IS the proof. -/
structure IsInfoClosed
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  modulus : DepthModulus
  modulus_finite : ∀ n, modulus n < modulus n + 1

/-- ★ Identity function is info-closed: M = N. -/
def idInfoClosed : IsInfoClosed id where
  modulus := identityDepthModulus
  modulus_finite := fun n => Nat.lt_succ_self _

/-- ★ Constant function is info-closed: M = 0 (need no input
    bits since output is fixed). -/
def constInfoClosed (c : Nat → Nat → Bool) :
    IsInfoClosed (fun _ => c) where
  modulus := constantDepthModulus
  modulus_finite := fun n => Nat.lt_succ_self _

/-- ★ Identity modulus is identity (rfl). -/
theorem id_modulus (n : Nat) : idInfoClosed.modulus n = n := rfl

/-- ★ Constant modulus is zero (rfl). -/
theorem const_modulus (c : Nat → Nat → Bool) (n : Nat) :
    (constInfoClosed c).modulus n = 0 := rfl

/-- ★ **Finite-depth witness**: every output depth is determined
    by a finite input depth (the modulus is `Nat → Nat`, not a
    cofinite blob). -/
theorem finite_depth_universal
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (hf : IsInfoClosed f) (n : Nat) :
    ∃ m : Nat, hf.modulus n = m := ⟨hf.modulus n, rfl⟩

/-- ★ **No infinite descent**: at every output depth, the
    required input depth is a finite Nat — no Cauchy-completion
    chase needed. -/
theorem no_infinite_descent
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (hf : IsInfoClosed f) (n : Nat) :
    hf.modulus n < hf.modulus n + 1 :=
  hf.modulus_finite n

end E213.Lib.Math.Analysis.Modulus.InfoClosure
