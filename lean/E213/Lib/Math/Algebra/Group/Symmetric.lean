/-!
# Group Theory 213 — Symmetric group Sₙ (atomic, function-side)

213-native paradigm: Sₙ as `Fin n → Fin n` (we use `Nat → Nat`
restricted, since `Fin` decidable equalities can leak propext).
Composition = function composition.  Identity, transposition,
3-cycle as concrete witnesses.

Atomic content:
  * `composePerm σ τ = σ ∘ τ`.
  * `identityPerm i = i`.
  * Transposition swap on a 2-element pattern.
  * Composition is associative (rfl).
-/

namespace E213.Lib.Math.Algebra.Group.Symmetric

/-- A "permutation" represented as `Nat → Nat`. -/
abbrev Perm := Nat → Nat

/-- Identity permutation. -/
def identityPerm : Perm := id

/-- Composition. -/
def composePerm (σ τ : Perm) : Perm := fun i => σ (τ i)

/-- ★ Identity at any element returns it (rfl). -/
theorem id_at (i : Nat) : identityPerm i = i := rfl

/-- ★ Composition with identity (left) is identity (rfl). -/
theorem id_compose_left (σ : Perm) (i : Nat) :
    composePerm identityPerm σ i = σ i := rfl

/-- ★ Composition with identity (right) is identity (rfl). -/
theorem compose_id_right (σ : Perm) (i : Nat) :
    composePerm σ identityPerm i = σ i := rfl

/-- ★ Composition is associative pointwise (rfl). -/
theorem compose_assoc_pointwise (σ τ ρ : Perm) (i : Nat) :
    composePerm σ (composePerm τ ρ) i
      = composePerm (composePerm σ τ) ρ i := rfl

/-- A transposition swap on `{0, 1}`. -/
def swap01 : Perm
  | 0 => 1
  | 1 => 0
  | n + 2 => n + 2

/-- ★ Transposition is its own inverse: swap01 ∘ swap01 = id. -/
theorem swap01_involutive (i : Nat) :
    composePerm swap01 swap01 i = identityPerm i := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => rfl

end E213.Lib.Math.Algebra.Group.Symmetric
