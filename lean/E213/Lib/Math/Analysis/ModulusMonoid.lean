import E213.Lib.Math.Analysis.CompletionTower
import E213.Lib.Math.Analysis.ResolutionShift

/-!
# ModulusMonoid — the tower's bookkeeping is one graded monoid

`CompletionTower` showed that grouping a sequence of completed cuts into a new
completion creates **no new object** (the level-2 tower collapses to one inner
completion, `tower_is_single_inner`).  The only thing that accumulates up the
tower is the **modulus** — the function saying, at each probe, how deep to read.

This file pins down *what that bookkeeping is*: the moduli form the commutative
monoid

    (Modulus, madd, mzero),   Modulus := ℕ → ℕ → ℕ,
    madd N₁ N₂ := fun m k => N₁ m k + N₂ m k,   mzero := fun _ _ => 0,

— pointwise `(ℕ, +, 0)` — and the completion tower is an action of it: composing
levels adds moduli, the identity level adds `mzero`.  This is the *same* additive
bookkeeping as `Analysis/ResolutionShift`'s `(ℕ, +)`-graded cut transformers, now
carried pointwise: the scalar grade `E : ℕ` embeds as the constant modulus
`fun _ _ => E`, and the embedding is a monoid homomorphism
(`gradeToModulus_add`).  So "grouping the groupings stacks grades, not objects"
is, precisely, that the tower lives over this one monoid.

The monoid laws are stated **pointwise** (`madd … m k = …`) rather than as
function equalities, to stay ∅-axiom — a function-level `=` routes through
`funext`/`Quot.sound`, exactly as in `CauchyCompleteValid.limit_unique`.

All ∅-axiom.
-/

namespace E213.Lib.Math.Analysis.ModulusMonoid

open E213.Lib.Math.Analysis.CauchyComplete
open E213.Lib.Math.Analysis.CompletionTower
open E213.Lib.Math.Analysis.ResolutionShift (IsResolutionShift)

/-! ## §1 — the modulus monoid `(ℕ→ℕ→ℕ, +, 0)` -/

/-- A **modulus** is the per-probe depth function a completion supplies. -/
def Modulus : Type := Nat → Nat → Nat

/-- The identity modulus — read at depth `0` everywhere (the modulus of a constant
    Cauchy sequence, `constCauchyCutSeq.N`). -/
def mzero : Modulus := fun _ _ => 0

/-- Modulus composition: pointwise sum of depths.  Stacking two completions reads
    at the sum of their depths. -/
def madd (N₁ N₂ : Modulus) : Modulus := fun m k => N₁ m k + N₂ m k

/-- ★ Left identity (pointwise). -/
theorem madd_zero_l (N : Modulus) (m k : Nat) : madd mzero N m k = N m k :=
  Nat.zero_add _

/-- ★ Right identity (pointwise). -/
theorem madd_zero_r (N : Modulus) (m k : Nat) : madd N mzero m k = N m k :=
  Nat.add_zero _

/-- ★ Associativity (pointwise). -/
theorem madd_assoc (A B C : Modulus) (m k : Nat) :
    madd (madd A B) C m k = madd A (madd B C) m k := Nat.add_assoc _ _ _

/-- ★ Commutativity (pointwise) — depth bookkeeping is order-independent. -/
theorem madd_comm (A B : Modulus) (m k : Nat) : madd A B m k = madd B A m k :=
  Nat.add_comm _ _

/-! ## §2 — the tower is an action: composing levels adds moduli -/

/-- ★★★ **The composite modulus resolves the level-2 tower.**  To read the
    completed value of a sequence-of-completions at probe `(m,k)`, it suffices to
    read at any index past `madd No Ni`, where `No` is the outer modulus.  The two
    levels' bookkeeping **adds**: `(No + Ni) m k` is a sufficient depth, and the
    value read there is the stable tower value.  (The `Ni` summand is slack the
    caller may use for the inner level; the outer `No` alone already resolves, so
    any larger composite does too — additivity gives a *uniform* sufficient
    depth.) -/
theorem tower_resolves_at_madd (inner : Nat → CauchyCutSeq) (No Ni : Modulus)
    (hc : ∀ m k i j, i ≥ No m k → j ≥ No m k →
        towerOuter inner i m k = towerOuter inner j m k)
    (m k i : Nat) (hi : i ≥ madd No Ni m k) :
    (towerSeq inner No hc).limit m k = (inner i).limit m k := by
  have h1 : i ≥ No m k := Nat.le_trans (Nat.le_add_right (No m k) (Ni m k)) hi
  exact tower_value_stable inner No hc m k i h1

/-- ★★ **The identity level adds `mzero`.**  Grouping a single completed cut as a
    constant sequence (the trivial outer level) and completing again returns it —
    the level it adds is `mzero`, the monoid identity (`constCauchyCutSeq.N =
    mzero` definitionally, and the limit is unchanged). -/
theorem identity_level_is_mzero (ccs : CauchyCutSeq) (m k : Nat) :
    (constCauchyCutSeq ccs.limit).limit m k = ccs.limit m k
    ∧ (constCauchyCutSeq ccs.limit).N = mzero :=
  ⟨congrFun (congrFun (constCauchyCutSeq_limit ccs.limit) m) k, rfl⟩

/-! ## §3 — ResolutionShift grades embed as constant moduli (monoid hom) -/

/-- The embedding of a scalar `ResolutionShift` grade `E : ℕ` into the modulus
    monoid: the constant modulus `fun _ _ => E`.  Reads at the *same* depth at
    every probe — a uniform resolution shift. -/
def gradeToModulus (E : Nat) : Modulus := fun _ _ => E

/-- ★ The embedding sends grade `0` to `mzero` (pointwise). -/
theorem gradeToModulus_zero (m k : Nat) : gradeToModulus 0 m k = mzero m k := rfl

/-- ★★ **The embedding is a monoid homomorphism**: grade addition (the `(ℕ,+)`
    of `ResolutionShift`, e.g. `IsResolutionShift_compose`'s `E₂ + E₁`) maps to
    `madd` of the constant moduli (pointwise).  So the scalar grade monoid sits
    inside the tower's modulus monoid as the constant sub-monoid — the same
    additive bookkeeping, one scalar, one pointwise. -/
theorem gradeToModulus_add (a b m k : Nat) :
    gradeToModulus (a + b) m k = madd (gradeToModulus a) (gradeToModulus b) m k :=
  rfl

/-- ★★★ **The bridge, stated.**  For any resolution-shifter `g` of grade `E`, its
    grade embeds as the constant modulus `gradeToModulus E`, and composition of
    shifters (which adds grades) corresponds to `madd` of the embedded moduli.
    Concretely: if `g₁` has grade `E₁` and `g₂` has grade `E₂`, the composite
    grade `E₂ + E₁` embeds as `madd (gradeToModulus E₂) (gradeToModulus E₁)` — the
    tower's modulus composition.  Grouping-of-groupings and resolution-shifting are
    the same `(ℕ,+)` bookkeeping. -/
theorem shift_grade_embeds (g₁ g₂ : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (E₁ E₂ : Nat) (_h₁ : IsResolutionShift g₁ E₁) (_h₂ : IsResolutionShift g₂ E₂)
    (m k : Nat) :
    gradeToModulus (E₂ + E₁) m k
    = madd (gradeToModulus E₂) (gradeToModulus E₁) m k := rfl

end E213.Lib.Math.Analysis.ModulusMonoid
