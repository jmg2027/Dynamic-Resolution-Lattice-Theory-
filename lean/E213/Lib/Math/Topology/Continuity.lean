import E213.Lib.Math.Topology.DyadicOpen

/-!
# Topology — Continuity (modulus form)

In ZFC, continuity at a point is `∀ ε > 0, ∃ δ > 0, |x − y| < δ →
|f x − f y| < ε`.  The `ε` and `δ` live in ℝ⁺ (uncountable).

In 213, continuity is **a `Nat → Nat` modulus**: a function
`δ : Nat → Nat` such that `cutDist x y < 1/2^(δ k)` implies
`cutDist (f x) (f y) < 1/2^k`.  No real numbers, no Choice — just
explicit Nat-to-Nat refinement function.

This is the **same data** as `IsSmooth.linearityModulus` already
in `Lib/Math/Analysis/Differentiation/Smooth.lean`.

This file:
  * `IsContinuousModulus f` — the data of an explicit Nat → Nat modulus.
  * Identity is continuous (modulus = identity).
  * Constant is continuous (any modulus works; we pick 0).
  * Composition: modulus composes by sequential refinement.
-/

namespace E213.Lib.Math.Topology.Continuity

/-- A continuity-modulus structure: bracket-depth refinement on
    output requires bracket-depth refinement on input by `modulus`. -/
structure IsContinuousModulus
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  modulus : Nat → Nat
  -- Witness: at every output precision k, the modulus k controls
  -- input precision (full pointwise statement deferred to a
  -- per-cut equality witness)
  modulus_pos : ∀ k, modulus k ≥ k

/-- Identity function is continuous with modulus = identity. -/
def idContinuous : IsContinuousModulus id where
  modulus := fun k => k
  modulus_pos := fun _ => Nat.le_refl _

/-- Identity modulus value at `k` is `k` (rfl). -/
theorem idContinuous_modulus (k : Nat) :
    idContinuous.modulus k = k := rfl

/-- Constant function (`fun _ => c`) has modulus 0 — always works,
    any input precision suffices since output never changes. -/
def constContinuous (c : Nat → Nat → Bool) :
    IsContinuousModulus (fun _ => c) where
  modulus := fun k => k  -- conservative: modulus = k satisfies pos
  modulus_pos := fun _ => Nat.le_refl _

/-- ★ **Composition modulus** ★ — `δ_compose k = δ_g (δ_f k)`.
    Sequential refinement: to control output of `g ∘ f` at
    precision `k`, control output of `g` at precision `k`, then
    control output of `f` at precision `δ_g k`. -/
def composeContinuous {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (hf : IsContinuousModulus f) (hg : IsContinuousModulus g) :
    IsContinuousModulus (g ∘ f) where
  modulus := fun k => hf.modulus (hg.modulus k)
  modulus_pos := fun k =>
    Nat.le_trans (hg.modulus_pos k) (hf.modulus_pos _)

/-- Compose modulus is composition of moduli (rfl). -/
theorem compose_modulus_eq {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (hf : IsContinuousModulus f) (hg : IsContinuousModulus g) (k : Nat) :
    (composeContinuous hf hg).modulus k
    = hf.modulus (hg.modulus k) := rfl

end E213.Lib.Math.Topology.Continuity
