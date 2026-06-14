import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.Gcd213

/-!
# A6 FLOW — monovariant-driven convergence to a normal form (∅-axiom)

The sixth finite→uniform lift archetype on the proof-ISA, the **continuous /
well-founded sibling of A2 LOOP**.

A2 LOOP (`flt_primary`, `slashNu_final`) lifts a *finite per-step recurrence*
to a uniform statement by **forward induction**: the per-step relation closes a
recurrence, induction iterates it.  FLOW lifts a *per-step strict descent of a
monovariant* to a **normal form** by **well-founded descent**: a self-map `f`
on presentations carries a `Nat`-valued monovariant `μ` that strictly decreases
off fixed points, so iterating `f` reaches a fixed point (a normal / canonical
form) in finitely many steps.

This is the discrete realization of the geometric-flow shape that
`Lib/Math/Geometry/GeometrizationConjecture/Ricci.lean` records as the open
piece: *"monotonicity functional analogous to Perelman's 𝓕 / 𝓦 … none of these
exist in `lean/E213/`."*  Ricci flow `∂_t g = −2R` drives an arbitrary metric to
a canonical (constant-curvature) geometry, its convergence certified by a
monotone entropy; here `flow_reaches` is exactly that shape with the entropy
replaced by a `Nat`-monovariant — `∅`-axiom, with no metric tensor.

The canonical instance is the **Euclidean GCD flow**: `(a,b) ↦ (b % a, a)` with
monovariant `Prod.fst`; the gcd is the invariant the flow preserves, and the
normal form it converges to is `(0, gcd a b)` — the gcd *is* the canonical form
reached by the descent.  Reuses the `Gcd213` monovariant infrastructure
(`gcd213_rec`, the Euclidean step).

## ISA reading

FLOW = `LOOP` whose termination is a **monovariant**, not a finite recurrence.
It is the *other* completion of in-place monovariant exhaustion that REFRAME
(A4) is the dual of (`reframe_presentation_transport.md`): when the monovariant
*exhausts*, it drives the object to its normal form; when it *cannot* be improved
in place, REFRAME transports to a presentation where it can.

**Lift cost: a monovariant that strictly descends off fixed points.**

## Widening: the relation form is the universal descent schema

`flow_reaches` is stated for a self-map `f`.  The *same* fuel-recursion-on-a-
monovariant is re-proven, independently, in three number-theory domains the
geometry framing does not reach: UFD separation (`Meta/Nat/VpSeparation`
`vp_separation`, monovariant `m+n`), Markov reachability
(`…/Markov/MarkovUniqueness` `markov_ordered_reachable`, monovariant `max`), and
atomic forcing (`Theory/Atomicity/Five` `atomic_implies_five`, bounded Bézout
shift).  Two features push past the self-map archetype: the step is a **reduction
relation** (it may change carrier or permute, not one endo-`f`), and the answer is
an **invariant transported to the normal form**, not a bare fixed point.

`descent_reaches` / `descent_invariant` below are that common generator: a step
relation `R` with a `Nat`-monovariant `μ` that descends off a normal-form
predicate `NF`, carrying any step-invariant `I` to the reached normal form.
`flow_reaches` is the self-map special case (`flow_reaches_of_relation` proves the
A6 statement *from* the relation schema), so A6 FLOW is not a geometry instrument —
it is the universal descent/normal-form lift, and gcd / Ricci / UFD / Markov /
atomicity are its instances.
-/

namespace E213.Lib.Math.Foundations.MonovariantFlow

open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213 (gcd213_rec)

/-- Iterate a self-map from the front: `iter f (n+1) x = iter f n (f x)`
    (definitional). -/
def iter {X : Type _} (f : X → X) : Nat → X → X
  | 0,   x => x
  | n+1, x => iter f n (f x)

/-- `x` is a **normal form** of the flow `f`: a fixed point, `f x = x`. -/
def IsNormalForm {X : Type _} (f : X → X) (x : X) : Prop := f x = x

/-- Fuel-bounded descent.  The disjunction `μ (f x) < μ x ∨ f x = x` is taken as
    `Prop`-data so the case split is **constructive** (`Or`-elimination, no
    decidable equality on `X`, no `Classical`). -/
theorem flow_reaches_fueled {X : Type _} (f : X → X) (μ : X → Nat)
    (descent : ∀ x, μ (f x) < μ x ∨ f x = x) :
    ∀ (fuel : Nat) (x : X), μ x ≤ fuel → ∃ n, IsNormalForm f (iter f n x)
  | 0, x, h => by
      cases descent x with
      | inr hfix => exact ⟨0, hfix⟩
      | inl hlt  => exact absurd (Nat.lt_of_lt_of_le hlt h) (Nat.not_lt_zero _)
  | k+1, x, h => by
      cases descent x with
      | inr hfix => exact ⟨0, hfix⟩
      | inl hlt  =>
          have hk : μ (f x) ≤ k := Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt h)
          obtain ⟨n, hn⟩ := flow_reaches_fueled f μ descent k (f x) hk
          exact ⟨n + 1, hn⟩

/-- ★★★★★ **A6 FLOW archetype** — a self-map with a `Nat`-monovariant that
    strictly descends off fixed points converges to a normal form.

    The finite per-step descent (`descent`) lifts to the uniform existence of a
    reached fixed point.  This is the proof-ISA witness for the FLOW lift, the
    well-founded sibling of A2 LOOP. -/
theorem flow_reaches {X : Type _} (f : X → X) (μ : X → Nat)
    (descent : ∀ x, μ (f x) < μ x ∨ f x = x) (x : X) :
    ∃ n, IsNormalForm f (iter f n x) :=
  flow_reaches_fueled f μ descent (μ x) x (Nat.le_refl _)

/-! ## The relation form — the universal descent schema (A6 FLOW widened)

The step generalises from a self-map `f : X → X` to a reduction **relation**
`R : X → X → Prop`, and the conclusion from "fixed point reached" to "a normal
form is reached, carrying any step-invariant".  See the module header for the
three number-theory instances this subsumes. -/

/-- Reflexive–transitive reachability under a step relation `R`. -/
inductive Reaches {X : Type _} (R : X → X → Prop) : X → X → Prop where
  | refl {x : X} : Reaches R x x
  | head {x y z : X} : R x y → Reaches R y z → Reaches R x z

/-- An invariant preserved by every `R`-step is preserved along reachability. -/
theorem reaches_invariant {X : Type _} {α : Type _} (R : X → X → Prop) (I : X → α)
    (inv : ∀ x y, R x y → I x = I y) {x y : X} (h : Reaches R x y) : I x = I y := by
  induction h with
  | refl => rfl
  | head hxy _ ih => exact (inv _ _ hxy).trans ih

/-- Fuel-bounded relational descent.  At each `x`, `step` gives either a
    normal-form certificate or an `R`-successor with strictly smaller `μ`; the
    `Or`/`Exists` data is eliminated constructively (no `Classical`, no decidable
    equality on `X`). -/
theorem descent_reaches_fueled {X : Type _} (R : X → X → Prop) (μ : X → Nat)
    (NF : X → Prop)
    (step : ∀ x, NF x ∨ ∃ y, R x y ∧ μ y < μ x) :
    ∀ (fuel : Nat) (x : X), μ x ≤ fuel → ∃ y, NF y ∧ Reaches R x y
  | 0, x, h => by
      cases step x with
      | inl hnf => exact ⟨x, hnf, Reaches.refl⟩
      | inr hex =>
          obtain ⟨_, _, hlt⟩ := hex
          exact absurd (Nat.lt_of_lt_of_le hlt h) (Nat.not_lt_zero _)
  | k+1, x, h => by
      cases step x with
      | inl hnf => exact ⟨x, hnf, Reaches.refl⟩
      | inr hex =>
          obtain ⟨y, hxy, hlt⟩ := hex
          have hk : μ y ≤ k := Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt h)
          obtain ⟨z, hz_nf, hz_reach⟩ := descent_reaches_fueled R μ NF step k y hk
          exact ⟨z, hz_nf, Reaches.head hxy hz_reach⟩

/-- ★★★★★ **Relational A6 FLOW** — a step relation with a `Nat`-monovariant that
    strictly descends off a normal-form predicate reaches a normal form from any
    start. -/
theorem descent_reaches {X : Type _} (R : X → X → Prop) (μ : X → Nat)
    (NF : X → Prop) (step : ∀ x, NF x ∨ ∃ y, R x y ∧ μ y < μ x) (x : X) :
    ∃ y, NF y ∧ Reaches R x y :=
  descent_reaches_fueled R μ NF step (μ x) x (Nat.le_refl _)

/-- ★★★★★★ **The descent-with-invariant schema** — the normal form reached by the
    descent carries any `R`-step invariant `I`.  This is the shape the three
    number-theory descents (UFD separation / Markov / atomicity) and the GCD flow
    all instantiate: *the answer is the invariant the descent preserves.* -/
theorem descent_invariant {X : Type _} {α : Type _} (R : X → X → Prop) (μ : X → Nat)
    (NF : X → Prop) (I : X → α)
    (step : ∀ x, NF x ∨ ∃ y, R x y ∧ μ y < μ x)
    (inv : ∀ x y, R x y → I x = I y) (x : X) :
    ∃ y, NF y ∧ Reaches R x y ∧ I y = I x := by
  obtain ⟨y, hy_nf, hy_reach⟩ := descent_reaches R μ NF step x
  exact ⟨y, hy_nf, hy_reach, (reaches_invariant R I inv hy_reach).symm⟩

/-! ### A6 FLOW is the self-map special case -/

/-- A `Reaches` chain under a function's graph is an `iter` index. -/
theorem reaches_graph_iter {X : Type _} (f : X → X) {x y : X}
    (h : Reaches (fun a b => f a = b) x y) : ∃ n, iter f n x = y := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | @head a b c hab _ ih =>
      have hab' : f a = b := hab
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, ?_⟩
      show iter f n (f a) = c
      rw [hab']; exact hn

/-- **`flow_reaches` reproved from the relation schema** — the self-map archetype
    is `descent_reaches` on the graph relation `fun a b => f a = b`, normal form
    `f x = x`.  Witness that A6 FLOW's function form is subsumed by the universal
    descent schema. -/
theorem flow_reaches_of_relation {X : Type _} (f : X → X) (μ : X → Nat)
    (descent : ∀ x, μ (f x) < μ x ∨ f x = x) (x : X) :
    ∃ n, IsNormalForm f (iter f n x) := by
  have step : ∀ a, (f a = a) ∨ ∃ b, (f a = b) ∧ μ b < μ a := by
    intro a
    cases descent a with
    | inl hlt  => exact Or.inr ⟨f a, rfl, hlt⟩
    | inr hfix => exact Or.inl hfix
  obtain ⟨y, hy_nf, hy_reach⟩ :=
    descent_reaches (fun a b => f a = b) μ (fun a => f a = a) step x
  obtain ⟨n, hn⟩ := reaches_graph_iter f hy_reach
  exact ⟨n, by show f (iter f n x) = iter f n x; rw [hn]; exact hy_nf⟩

/-! ## Instance: the Euclidean GCD flow (the canonical normal-form flow) -/

/-- The Euclidean flow on pairs: `(a, b) ↦ (b % a, a)`, with the first
    coordinate `0` as the absorbing normal form. -/
def euclidStep : Nat × Nat → Nat × Nat
  | (0,   b) => (0, b)
  | (a+1, b) => (b % (a+1), a+1)

/-- The monovariant `Prod.fst` strictly descends off fixed points: each
    Euclidean step shrinks the first coordinate, except at `(0, b)` which is
    fixed. -/
theorem euclid_descent :
    ∀ p : Nat × Nat, (euclidStep p).1 < p.1 ∨ euclidStep p = p
  | (0,   _) => Or.inr rfl
  | (a+1, b) => Or.inl (Nat.mod_lt b (Nat.zero_lt_succ a))

/-- The Euclidean flow reaches a normal form from any start (the A6 archetype
    fired). -/
theorem euclid_flow_reaches (a b : Nat) :
    ∃ n, IsNormalForm euclidStep (iter euclidStep n (a, b)) :=
  flow_reaches euclidStep (fun p => p.1) euclid_descent (a, b)

/-- `gcd213 0 b = b` — the gcd at a normal-form pair reads off the second
    coordinate.  ∅-axiom (`rfl`: `gcdFuel (_+1) 0 b = b`). -/
theorem gcd213_zero_left (b : Nat) : gcd213 0 b = b := rfl

/-- The gcd is the **invariant** the Euclidean step preserves
    (`gcd213_rec` per step). -/
theorem euclid_invariant :
    ∀ p : Nat × Nat,
      gcd213 (euclidStep p).1 (euclidStep p).2 = gcd213 p.1 p.2
  | (0,   _) => rfl
  | (a+1, b) => (gcd213_rec (a+1) b (Nat.zero_lt_succ a)).symm

/-- The invariant is preserved along the whole flow. -/
theorem euclid_invariant_iter :
    ∀ (n : Nat) (p : Nat × Nat),
      gcd213 (iter euclidStep n p).1 (iter euclidStep n p).2 = gcd213 p.1 p.2
  | 0,   _ => rfl
  | n+1, p => (euclid_invariant_iter n (euclidStep p)).trans (euclid_invariant p)

/-- A normal form of the Euclidean flow has first coordinate `0`. -/
theorem normal_fst_zero : ∀ p : Nat × Nat, euclidStep p = p → p.1 = 0
  | (0,   _), _ => rfl
  | (a+1, b), h => by
      have hlt : b % (a+1) < a+1 := Nat.mod_lt b (Nat.zero_lt_succ a)
      have h1 : b % (a+1) = a+1 := congrArg Prod.fst h
      rw [h1] at hlt
      exact absurd hlt (Nat.lt_irrefl _)

/-- ★★★★★★ **The GCD is the normal form of the Euclidean flow.**

    From any `(a, b)`, the monovariant flow converges to `(0, gcd213 a b)`:
    the first coordinate hits the absorbing `0`, and the gcd-invariant forces
    the second coordinate to be `gcd213 a b`.  The canonical-form-reached-by-
    descent statement — the discrete A6 FLOW analog of "Ricci flow drives any
    metric to its canonical geometry." -/
theorem euclid_flow_normal_form (a b : Nat) :
    ∃ n, (iter euclidStep n (a, b)).1 = 0
       ∧ (iter euclidStep n (a, b)).2 = gcd213 a b := by
  obtain ⟨n, hn⟩ := euclid_flow_reaches a b
  have hfst : (iter euclidStep n (a, b)).1 = 0 := normal_fst_zero _ hn
  have hinv : gcd213 (iter euclidStep n (a, b)).1 (iter euclidStep n (a, b)).2
                = gcd213 a b := euclid_invariant_iter n (a, b)
  rw [hfst, gcd213_zero_left] at hinv
  exact ⟨n, hfst, hinv⟩

end E213.Lib.Math.Foundations.MonovariantFlow
