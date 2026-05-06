import E213.Math.Real213.CutBisection
import E213.Math.Real213.Dyadic
import E213.Math.Real213.CutFnData
import E213.Kernel.Tactic.Nat213
import E213.Kernel.Tactic.Pow213

/-!
# ResolutionShift — `(Nat, +)`-graded structure on cut transformers

Concrete exploration of the grading uncovered in the CollapseCondition
arc: cut transformers `f : Cut → Cut` carry a *resolution grade* — a
natural number `E_g` describing how `f` shifts dyadic resolution.

## Core definition

`IsResolutionShift g E_g` := pointwise:
  ∀ M E m k, g (dyadicCut M E) m k = dyadicCut M (E + E_g) m k

i.e., `g` zooms dyadic resolution upward by `E_g` (sends `M/2^E` to
`M/2^(E+E_g)`).

## Concrete grades computed in this file

| Function          | Grade | Theorem                                  |
|-------------------|-------|------------------------------------------|
| `id`              | 0     | `IsResolutionShift_id`                   |
| `cutHalf`         | 1     | `IsResolutionShift_cutHalf`              |
| `cutHalf^n`       | n     | `IsResolutionShift_cutHalf_iter`         |
| `g₁ ∘ g₂`         | E₁+E₂ | `IsResolutionShift_compose`              |

## Generation pattern

The single generator `cutHalf` (grade 1) generates every nonzero
grade by iteration; `id` is the zero element.  This makes the graded
monoid `(ℕ, +)` *free on one generator* at the resolution-shift
layer — same algebraic shape as polynomial ring `ℕ[x]` graded by
degree.

## What's NOT IsResolutionShift

  * `constCutFn c` — output independent of input; no shift, but
    not the identity.  A *different* grade-0 element (constant
    cocycle).
  * `cutSum` (curried as `fun x => cutSum x c`) — depends on input
    + constant; produces non-dyadic outputs in general.
  * `negation`-like operations — break dyadicCut shape.

These admit alternative gradings (constant grade, multiplicative
grade, etc.) but don't fit `IsResolutionShift`.
-/

namespace E213.Math.Analysis.ResolutionShift

open E213.Firmware E213.Hypervisor
open E213.Math.Real213.Dyadic (dyadicCut)
open E213.Math.Real213.CutBisection (cutHalf)
open E213.Math.Real213.CutFnData (LocallyDeterminedData composeLDD cutHalfLDD)

/-- **`IsResolutionShift g E_g`**: g sends `dyadicCut M E` to a cut
    pointwise-equal to `dyadicCut M (E + E_g)`.

The shift is *additive* in the dyadic exponent — equivalent to the
operation "scale by 1/2^E_g" on the represented rational.  Pointwise
equality (no funext): `g (dyadicCut M E) m k = dyadicCut M (E + E_g) m k`. -/
def IsResolutionShift
    (g : (Nat → Nat → Bool) → (Nat → Nat → Bool)) (E_g : Nat) : Prop :=
  ∀ M E m k, g (dyadicCut M E) m k = dyadicCut M (E + E_g) m k

/-! ### Grade 0 — the identity -/

/-- **id has grade 0**: identity preserves dyadic resolution.

Direct from `E + 0 = E` by `Nat.add_zero`. -/
theorem IsResolutionShift_id : IsResolutionShift id 0 := by
  intro M E m k
  show dyadicCut M E m k = dyadicCut M (E + 0) m k
  rw [Nat.add_zero]

/-! ### Grade 1 — `cutHalf` -/

/-- **cutHalf has grade 1**: `cutHalf` shifts dyadic resolution by 1.

`cutHalf c m k = c (2*m) k`.  Applied to `dyadicCut M E`:
  `cutHalf (dyadicCut M E) m k = decide(M*k ≤ 2^E * (2*m))`.
The RHS `dyadicCut M (E+1) m k = decide(M*k ≤ 2^(E+1) * m)`.
These are equal because `2^E * (2*m) = 2^(E+1) * m`. -/
theorem IsResolutionShift_cutHalf : IsResolutionShift cutHalf 1 := by
  intro M E m k
  show decide (M * k ≤ 2^E * (2 * m)) = decide (M * k ≤ 2^(E + 1) * m)
  -- 2^E * (2 * m) = 2^(E+1) * m
  have hpow : 2^E * (2 * m) = 2^(E+1) * m := by
    rw [Nat.pow_succ, Nat.mul_comm (2^E) 2,
        E213.Tactic.Nat213.mul_assoc 2 (2^E) m,
        ← E213.Tactic.Nat213.mul_assoc 2 (2^E) m,
        Nat.mul_comm 2 (2^E),
        E213.Tactic.Nat213.mul_assoc (2^E) 2 m]
  rw [hpow]

/-! ### Composition — `(Nat, +)` graded multiplication

The central algebraic fact: composition of two resolution shifters
is a resolution shifter, with grades adding.  This realises the
*graded monoid structure* on cut transformers — the same arithmetic
as cup-product degree, polynomial degree, and simplicial dimension. -/

/-- **★ Composition law (LDD-bridged form)**:
    `IsResolutionShift g₁ E₁` + `IsResolutionShift g₂ E₂` +
    `LocallyDeterminedData g₁` ⇒ `IsResolutionShift (g₁ ∘ g₂) (E₂ + E₁)`.

The LDD on g₁ is the *minimum sufficient hypothesis* to bridge
pointwise equality through composition: g₂'s output is *pointwise
equal* to `dyadicCut M (E + E₂)` but not necessarily equal as a
function (would require funext).  LDD on g₁ propagates pointwise
input agreement to pointwise output agreement at any single query —
exactly what we need.

Grades **add upstream** under composition: g₂ shifts by E₂, g₁
shifts by E₁, total shift = E₂ + E₁.  Order matters: applying g₂
first then g₁ gives upstream-stacking.

This is the pure ∅-axiom form — no funext, no propext. -/
theorem IsResolutionShift_compose
    {g₁ g₂ : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    {E₁ E₂ : Nat}
    (lf₁ : LocallyDeterminedData g₁)
    (hg₁ : IsResolutionShift g₁ E₁) (hg₂ : IsResolutionShift g₂ E₂) :
    IsResolutionShift (g₁ ∘ g₂) (E₂ + E₁) := by
  intro M E m k
  show g₁ (g₂ (dyadicCut M E)) m k = dyadicCut M (E + (E₂ + E₁)) m k
  -- Step 1: by hg₂ pointwise, g₂ (dyadicCut M E) is pointwise equal
  -- to dyadicCut M (E + E₂).  By LDD on g₁, this gives equal g₁-values.
  have heq : ∀ m' k', g₂ (dyadicCut M E) m' k' = dyadicCut M (E + E₂) m' k' :=
    fun m' k' => hg₂ M E m' k'
  have lf₁_bridge : g₁ (g₂ (dyadicCut M E)) m k
                  = g₁ (dyadicCut M (E + E₂)) m k :=
    lf₁.prop m k _ _ (fun m' k' _ _ => heq m' k')
  rw [lf₁_bridge]
  -- Step 2: apply hg₁'s shift on the dyadicCut input.
  rw [hg₁ M (E + E₂) m k]
  -- Step 3: arithmetic — (E + E₂) + E₁ = E + (E₂ + E₁).
  rw [Nat.add_assoc E E₂ E₁]

/-! ### Grade n — `cutHalf^n` iteration

Iterating `cutHalf` n times produces a function of grade `n`.  This
is the canonical "generator" pattern: every nonzero grade arises
from iterated application of the unit generator `cutHalf`. -/

/-- n-fold iterated cutHalf composition. -/
def cutHalfIter : Nat → ((Nat → Nat → Bool) → (Nat → Nat → Bool))
  | 0 => id
  | n+1 => cutHalf ∘ cutHalfIter n

/-- LDD for iterated cutHalf, by structural induction.  Each
    cutHalf is LDD; composition closure (`composeLDD`) propagates. -/
def cutHalfIterLDD : ∀ n, LocallyDeterminedData (cutHalfIter n)
  | 0 =>
    { N := fun m k => max m k
      prop := by
        intro m k cx cy h
        exact h m k (E213.Math.Max213.le_max_left _ _)
                    (E213.Math.Max213.le_max_right _ _) }
  | n+1 => composeLDD cutHalfLDD (cutHalfIterLDD n)

/-- **`cutHalf^n` has grade n**: structural induction on n.

  * n = 0: `cutHalfIter 0 = id`, grade 0 (`IsResolutionShift_id`).
  * n+1: `cutHalfIter (n+1) = cutHalf ∘ cutHalfIter n`.  By
    composition law (`IsResolutionShift_compose`) with grade n
    (IH) and grade 1 (cutHalf), result is grade `n + 1`. -/
theorem IsResolutionShift_cutHalfIter :
    ∀ n, IsResolutionShift (cutHalfIter n) n
  | 0 => IsResolutionShift_id
  | n+1 => by
    show IsResolutionShift (cutHalf ∘ cutHalfIter n) (n + 1)
    have h_compose : IsResolutionShift (cutHalf ∘ cutHalfIter n) (n + 1) :=
      IsResolutionShift_compose cutHalfLDD
        IsResolutionShift_cutHalf (IsResolutionShift_cutHalfIter n)
    exact h_compose

/-! ### Pattern recognition — grade uniqueness

The grade of a resolution shifter is **unique** — different grades
produce *measurably different* dyadic cuts at carefully chosen
queries.  This is the *pattern-recognition theorem*: given a
function g claiming to satisfy `IsResolutionShift`, its grade is
fully determined. -/

/-- `dyadicCut 1 E 1 (2^E') = false` when `E' > E`.

Test query that distinguishes grade `E` from grade `E'`. -/
private theorem dyadicCut_test_lt
    (E E' : Nat) (h : E < E') :
    dyadicCut 1 E 1 (2^E') = false := by
  show decide (1 * 2^E' ≤ 2^E * 1) = false
  rw [Nat.one_mul, Nat.mul_one]
  apply decide_eq_false
  -- 2^E < 2^E' (from E < E')
  exact Nat.not_le_of_lt (E213.Tactic.Pow213.pow_lt_pow_two E E' h)

/-- `dyadicCut 1 E 1 (2^E) = true` (the diagonal — exactly equals). -/
private theorem dyadicCut_test_diag (E : Nat) :
    dyadicCut 1 E 1 (2^E) = true := by
  show decide (1 * 2^E ≤ 2^E * 1) = true
  rw [Nat.one_mul, Nat.mul_one]
  exact decide_eq_true (Nat.le_refl _)

/-- **★ Grade uniqueness**: a function carries *at most one* grade.

If `g` satisfies both `IsResolutionShift g E` and
`IsResolutionShift g E'`, then `E = E'`.  The grade is a *property
of the function*, not a free parameter.

Proof: at the test query `(m, k) = (1, 2^max(E, E'))`, the two
hypotheses force `dyadicCut 1 E` and `dyadicCut 1 E'` to agree —
which by `dyadicCut_test_lt` / `dyadicCut_test_diag` forces
`E = E'`. -/
theorem IsResolutionShift_grade_unique
    {g : (Nat → Nat → Bool) → (Nat → Nat → Bool)} {E E' : Nat}
    (h : IsResolutionShift g E) (h' : IsResolutionShift g E') :
    E = E' := by
  -- Step 1: dispatch on E vs E' trichotomy.
  rcases Nat.lt_or_ge E E' with hlt | hge
  · exfalso
    have h₁ : g (dyadicCut 1 0) 1 (2^E') = dyadicCut 1 E 1 (2^E') := by
      have := h 1 0 1 (2^E')
      rw [Nat.zero_add] at this; exact this
    have h₂ : g (dyadicCut 1 0) 1 (2^E') = dyadicCut 1 E' 1 (2^E') := by
      have := h' 1 0 1 (2^E')
      rw [Nat.zero_add] at this; exact this
    have eq : dyadicCut 1 E 1 (2^E') = dyadicCut 1 E' 1 (2^E') := h₁.symm.trans h₂
    rw [dyadicCut_test_lt E E' hlt, dyadicCut_test_diag E'] at eq
    exact Bool.noConfusion eq
  · rcases Nat.lt_or_ge E' E with hlt' | hge'
    · exfalso
      have h₁ : g (dyadicCut 1 0) 1 (2^E) = dyadicCut 1 E 1 (2^E) := by
        have := h 1 0 1 (2^E)
        rw [Nat.zero_add] at this; exact this
      have h₂ : g (dyadicCut 1 0) 1 (2^E) = dyadicCut 1 E' 1 (2^E) := by
        have := h' 1 0 1 (2^E)
        rw [Nat.zero_add] at this; exact this
      have eq : dyadicCut 1 E 1 (2^E) = dyadicCut 1 E' 1 (2^E) := h₁.symm.trans h₂
      rw [dyadicCut_test_diag E, dyadicCut_test_lt E' E hlt'] at eq
      exact Bool.noConfusion eq
    · exact Nat.le_antisymm hge' hge

/-! ### Generation analysis — `cutHalfIter` is the canonical generator

Combined with grade uniqueness, the data establishes the structure
of `(Nat, +)` as a *graded monoid module* on cut transformers, with
`cutHalfIter n` the canonical witness at grade n.

The structure: `(Nat, +) = Free monoid on {cutHalf}` (one generator).
This is the same algebraic shape as polynomial degrees — `ℕ[x]`
graded by degree, with `cutHalf` playing the role of `x`. -/

/-- **Existence at every grade**: for any `n`, the witness
    `cutHalfIter n` realises grade `n` (Σ-pair). -/
def IsResolutionShift_exists_at_grade (n : Nat) :
    Σ' g : (Nat → Nat → Bool) → (Nat → Nat → Bool), IsResolutionShift g n :=
  ⟨cutHalfIter n, IsResolutionShift_cutHalfIter n⟩

/-- **Grade-0 acts as identity on dyadicCut**: any function with
    grade 0 is pointwise-equal to identity on dyadic inputs.

The grade-0 class is not `id` exclusively — any function that
preserves dyadicCut shape pointwise has grade 0. -/
theorem IsResolutionShift_zero_acts_as_id
    {g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (h : IsResolutionShift g 0) (M E m k : Nat) :
    g (dyadicCut M E) m k = dyadicCut M E m k := by
  rw [h M E m k, Nat.add_zero]

/-- **Canonical action**: any two functions of the same grade act
    *identically on dyadic inputs at every query*.

This is the "free on one generator" payoff: the grade-`n` class
has a *unique pointwise behavior* on dyadicCut inputs, captured by
`dyadicCut M (E + n)`. -/
theorem IsResolutionShift_agree_on_dyadicCut
    {g₁ g₂ : (Nat → Nat → Bool) → (Nat → Nat → Bool)} {n : Nat}
    (h₁ : IsResolutionShift g₁ n) (h₂ : IsResolutionShift g₂ n)
    (M E m k : Nat) :
    g₁ (dyadicCut M E) m k = g₂ (dyadicCut M E) m k := by
  rw [h₁ M E m k, h₂ M E m k]

-- **Concrete grade table** (smoke tests via `decide`):

-- `cutHalf` at depth 0 sends `dyadicCut 1 0 = 1/1` to `dyadicCut 1 1 = 1/2`.
example : cutHalf (dyadicCut 1 0) 1 1 = dyadicCut 1 1 1 1 := by decide

-- `cutHalfIter 2 = cutHalf ∘ cutHalf` sends `dyadicCut 1 0` to `dyadicCut 1 2 = 1/4`.
example : cutHalfIter 2 (dyadicCut 1 0) 1 1 = dyadicCut 1 2 1 1 := by decide

-- `cutHalfIter 3` sends `dyadicCut 1 0` to `dyadicCut 1 3 = 1/8`.
example : cutHalfIter 3 (dyadicCut 1 0) 1 1 = dyadicCut 1 3 1 1 := by decide

end E213.Math.Analysis.ResolutionShift
