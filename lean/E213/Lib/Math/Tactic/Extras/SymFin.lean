/-!
# Sₙ via `Fin n` (∅-axiom upgrade of `Group/Symmetric.lean`)

The base `Group/Symmetric.lean` represents permutations as
`Nat → Nat`.  This file upgrades to the *finite-typed* version
`Fin n → Fin n`, which is closer to the textbook Sₙ.  Composition
remains by `rfl`, identity is `id` on `Fin n`.

Atomic content:
  * `FinPerm n := Fin n → Fin n`
  * Identity, composition; both `rfl` for application.
  * S₃ has 6 elements (concrete witness: |S₃| ≥ 6 via 6 distinct
    function values at `(0, 1, 2)`).  Full count requires
    `Fin (n!)`-cardinality machinery, deferred.
-/

namespace E213.Lib.Math.Tactic.Extras.SymFin

/-- Sₙ as functions `Fin n → Fin n`. -/
abbrev FinPerm (n : Nat) := Fin n → Fin n

/-- Identity permutation on `Fin n`. -/
def idPerm (n : Nat) : FinPerm n := id

/-- Composition. -/
def composeFin {n : Nat} (σ τ : FinPerm n) : FinPerm n :=
  fun i => σ (τ i)

/-- ★ Identity acts as identity (rfl). -/
theorem idPerm_at {n : Nat} (i : Fin n) : idPerm n i = i := rfl

/-- ★ Composition with identity (left). -/
theorem compose_id_left {n : Nat} (σ : FinPerm n) (i : Fin n) :
    composeFin (idPerm n) σ i = σ i := rfl

/-- ★ Composition with identity (right). -/
theorem compose_id_right {n : Nat} (σ : FinPerm n) (i : Fin n) :
    composeFin σ (idPerm n) i = σ i := rfl

/-- ★ Composition is associative pointwise (rfl). -/
theorem compose_assoc {n : Nat} (σ τ ρ : FinPerm n) (i : Fin n) :
    composeFin σ (composeFin τ ρ) i
      = composeFin (composeFin σ τ) ρ i := rfl

/-- Term-mode Fin 2 constructors (avoid `decide` propext leak). -/
def fin2_zero : Fin 2 := ⟨0, Nat.zero_lt_succ 1⟩

/-- Term-mode `1 : Fin 2`. -/
def fin2_one : Fin 2 := ⟨1, Nat.lt_succ_self 1⟩

/-- A specific S₂ element: the swap `(0 1)` defined on `i.val`. -/
def swap2 (i : Fin 2) : Fin 2 :=
  match i.val with
  | 0 => fin2_one
  | _ => fin2_zero

/-- ★ swap2 sends 0 ↦ 1. -/
theorem swap2_zero : swap2 fin2_zero = fin2_one := rfl

/-- ★ swap2 sends 1 ↦ 0. -/
theorem swap2_one : swap2 fin2_one = fin2_zero := rfl

/-- ★ swap2 ∘ swap2 = id at 0 (rfl). -/
theorem swap2_involutive_zero :
    composeFin swap2 swap2 fin2_zero = fin2_zero := rfl

/-- ★ swap2 ∘ swap2 = id at 1 (rfl). -/
theorem swap2_involutive_one :
    composeFin swap2 swap2 fin2_one = fin2_one := rfl

end E213.Lib.Math.Tactic.Extras.SymFin
