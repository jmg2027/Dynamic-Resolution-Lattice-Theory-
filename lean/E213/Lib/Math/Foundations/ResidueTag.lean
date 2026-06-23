import E213.Lens
import E213.Lib.Math.Analysis.BanachFixedPointModulated
import E213.Lib.Math.Algebra.CassiniUnimodular

/-!
# ResidueTag — the `q = ±1` residue tag, one construct exhibiting both poles (∅-axiom)

the decomposition calculus (model v7.1) converged the whole decomposition
calculus on a single invariant: the **residue of a self-applying reading carries a multiplier
bit `q = ±1`**.  Its two values are two ways a self-map's fixed-point structure can sit:

  * **`q = −1` (Escape / fixed-point-free)** — a modifier with no fixed point (`∀ x, f x ≠ x`).
    Built into a self-cover, it forces non-surjectivity: the diagonal residue lies **outside**
    every view's image (`OneDiagonal.no_surjection_of_fixedpointfree`).  Instances:
    Cantor (`cardinality.md`), Gödel/Russell/Liar (`godel.md`), the residue's own non-closure
    (`object1_not_surjective`), non-measurable / Vitali (`measure.md`).

  * **`q = +1` (Converge / has-a-fixed-point)** — a contraction self-map.  It **has** a fixed
    point, reached by no finite iterate, only as the modulus-limit
    (`BanachFixedPoint.banach_fixed_point_modulated`).  Instances: φ
    (`golden_ratio.md`, the Cassini `q=+1` conserved orbit), the Gaussian (`gaussian_clt.md`),
    ODE flows / Picard (`differential_equations.md`).

The `±1` is not decoration: `CassiniUnimodular.det_step` shows it is literally the **multiplier
`q`** of a 2nd-order orbit — `q = +1` conserves the Cassini determinant (golden, `det_golden`),
`q = −1` alternates its sign (period-2 swap, `det_period2_alternates`); `qpow` carries the two
poles' order (`qpow 1 n = 1`; `(-1)` has order `NT = 2`).

## The honest shape of the unification (read this before reading "one theorem")

The two poles are **genuinely asymmetric in type**, and this file does not force a false
symmetry (the `two_cells.md` / `MuNuMirror` discipline):

  * the `q=−1` pole takes a *fixed-point-free* hypothesis (a **universal negation**,
    `∀ x, f x ≠ x`) and yields a **negative** theorem (a self-cover is *not* surjective);
  * the `q=+1` pole takes a *contraction* hypothesis and yields a **positive** theorem
    (a fixed point **exists**, located to every scale).

A `∀…≠` hypothesis + a negative conclusion versus a metric-contraction hypothesis + an
existence conclusion cannot collapse into one `Eq`-shaped theorem without smuggling a decision
of "does `f` have a fixed point" (the excluded middle on the fixed-point predicate — forbidden).
So the unification is **NOT** a single biconditional.  What is genuinely *one* construct:

  1. **one tag** `ResidueTag` with a `multiplier : ResidueTag → Int` whose two values are `±1`
     (the Cassini multiplier), and one fixed-point predicate read at each pole
     (`tagOfSelfMap`);
  2. **one consequence theorem per pole**, each delegating to the canonical engine
     (`escape_residue_outside` ⟵ `no_surjection_of_fixedpointfree`; `converge_residue_fixed`
     ⟵ `banach_fixed_point_modulated`);
  3. **one bundling structure** `TaggedResidue` carrying both, and one capstone
     `residue_tag_two_poles` exhibiting Cantor/Gödel/Vitali and φ/Gaussian/ODE as the two
     *values* of the *same* tag — the shared column, not a forced common map.

This is the same honest "capstone" stance as `DualCollapseCapstone` / `ResidueForm`: it proves
no new content, it names the convergence.  The residue itself stays outside every view (the
`q=−1` conjunct is exactly that fact); the `q=+1` value is reached by none, only the limit.

All zero-axiom.
-/

namespace E213.Lib.Math.Foundations.ResidueTag

open E213.Lens.Foundations.OneDiagonal (no_surjection_of_fixedpointfree)
open E213.Lib.Math.Analysis.BanachFixedPoint
open E213.Lib.Math.Analysis.UniformLimitContinuous (MetricModulus)

/-! ## §1 — the tag and its `±1` multiplier -/

/-- ★★★ **The residue tag.**  The single bit a self-applying reading's residue carries:
    `escape` (fixed-point-free, the diagonal lies outside every view) or `converge`
    (a fixed point exists, reached only as a limit).  Decidable, pure — an inductive, not an
    `Int` (no `propext` risk); its `±1` reading is `multiplier` below. -/
inductive ResidueTag
  | escape    -- q = −1
  | converge  -- q = +1
deriving DecidableEq

/-- The `q = ±1` reading of the tag — the **Cassini multiplier** (`CassiniUnimodular.det_step`):
    `escape ↦ −1` (the swap orbit, determinant alternates), `converge ↦ +1` (the golden orbit,
    determinant conserved). -/
def multiplier : ResidueTag → Int
  | .escape   => -1
  | .converge => 1

/-- The two tags carry the two unimodular multipliers: `|q| = 1` at both poles. -/
theorem multiplier_unimodular (q : ResidueTag) : multiplier q * multiplier q = 1 := by
  cases q <;> rfl

/-- The tag is determined by its multiplier (faithful `±1` reading). -/
theorem tag_inj_multiplier {q₁ q₂ : ResidueTag} (h : multiplier q₁ = multiplier q₂) :
    q₁ = q₂ := by
  cases q₁ <;> cases q₂ <;> first | rfl | (exact absurd h (by decide))

/-! ## §2 — the two fixed-point predicates a self-map can satisfy -/

/-- **`FixedPointFree f`** — the `q = −1` shape: `f` has **no** fixed point.  A universal
    negation; the diagonal `t (f a a)` of any self-cover built from it escapes. -/
def FixedPointFree {X : Type} (f : X → X) : Prop := ∀ x, f x ≠ x

/-- **`HasFixedPoint f`** — the `q = +1` shape: `f` **has** a fixed point.  For a contraction
    this is the located limit, reached by none. -/
def HasFixedPoint {X : Type} (f : X → X) : Prop := ∃ x, f x = x

/-- The tag of a self-map *whose pole is known*: a witness that `f` is fixed-point-free reads
    as `escape`; a witness that `f` has a fixed point reads as `converge`.  (We tag from the
    witness, not by deciding the undecidable fixed-point predicate — `PSum`, not `Bool`-of-EM.) -/
def tagOfSelfMap {X : Type} (f : X → X)
    (w : FixedPointFree f ⊕' HasFixedPoint f) : ResidueTag :=
  match w with
  | .inl _ => .escape
  | .inr _ => .converge

/-- The escape witness reads as `q = −1`. -/
theorem tagOfSelfMap_escape {X : Type} (f : X → X) (h : FixedPointFree f) :
    tagOfSelfMap f (.inl h) = .escape := rfl

/-- The converge witness reads as `q = +1`. -/
theorem tagOfSelfMap_converge {X : Type} (f : X → X) (h : HasFixedPoint f) :
    tagOfSelfMap f (.inr h) = .converge := rfl

/-! ## §3 — pole `q = −1`: fixed-point-free ⟹ the residue lies OUTSIDE every view

The escape consequence is `OneDiagonal.no_surjection_of_fixedpointfree` *verbatim*, re-exported
through the tag vocabulary: a fixed-point-free modifier on the value type forces every self-cover
`A → (A → B)` to miss a row — the diagonal residue is outside the image. -/

/-- ★★★ **Escape residue (`q = −1`): the diagonal lies outside every view.**  If the value
    modifier `t : B → B` is fixed-point-free, then **no** self-cover `f : A → (A → B)` is
    surjective: the diagonal `fun a => t (f a a)` is never a row.  This is
    `no_surjection_of_fixedpointfree` read through `FixedPointFree`; it is the engine behind
    Cantor, Gödel/Russell/Liar (`russell_liar_no_surjection`), the residue's own non-closure
    (`object1_not_surjective`), and the Vitali / non-measurable escape (`measure.md`). -/
theorem escape_residue_outside {A B : Type} (t : B → B) (ht : FixedPointFree t) :
    ¬ ∃ f : A → (A → B), Function.Surjective f :=
  no_surjection_of_fixedpointfree t ht

/-- The canonical decidable escape witness: on a value type that **distinguishes** (`Bool`,
    `true ≠ false`), the negation modifier `not` is fixed-point-free — the `q = −1` pole is
    inhabited, and it is exactly Cantor's modifier. -/
theorem bool_not_fixedPointFree : FixedPointFree (fun b : Bool => !b) :=
  fun b h => E213.Lens.Cardinality.bnot_self_ne b h

/-- Cantor as the named `q = −1` instance: the `Bool`/`not` escape residue. -/
theorem cantor_is_escape {A : Type} : ¬ ∃ f : A → (A → Bool), Function.Surjective f :=
  escape_residue_outside (fun b => !b) bool_not_fixedPointFree

/-! ## §4 — pole `q = +1`: a contraction ⟹ the residue IS a fixed point, reached by none

The converge consequence is `banach_fixed_point_modulated`: a contraction has a located fixed
point `x* = picardLim …`, reached by no finite iterate (only the modulus-limit).  We package it
as `HasFixedPoint`-flavoured: the located equality `∀ m, close m x* (T x*)` is the constructive
form of `T x* = x*`. -/

/-- ★★★ **Converge residue (`q = +1`): the fixed point exists, reached by none.**  A
    contraction `T` over a modulated-complete dyadic metric has the explicit point
    `x* = picardLim …` with `close m x* (T x*)` at **every** scale `m` — the located
    `HasFixedPoint`.  Delegates to `banach_fixed_point_modulated`; the engine behind φ
    (`golden_ratio.md`), the Gaussian (`gaussian_clt.md`), and ODE flows
    (`differential_equations.md`). -/
theorem converge_residue_fixed {X : Type} (C : CompleteMetricModulusMod X) {T : X → X}
    (hT : Contraction C.toMetricModulus T) (x0 : X) (s : Nat)
    (hbase : C.close (s + 1) (picard T x0 0) (picard T x0 1)) :
    ∀ m, C.close m (C.picardLim hT x0 s hbase) (T (C.picardLim hT x0 s hbase)) :=
  C.banach_fixed_point_modulated hT x0 s hbase

/-- The canonical converge witness on the degenerate complete carrier: the identity on `Unit`
    has its located Picard fixed point — the `q = +1` pole is inhabited. -/
theorem unit_id_converges :
    ∀ m, trivCompleteMod.close m
      (trivCompleteMod.picardLim
        (triv_contraction (fun _ : Unit => ())) () 0 trivial)
      ((fun _ : Unit => ())
        (trivCompleteMod.picardLim
          (triv_contraction (fun _ : Unit => ())) () 0 trivial)) :=
  converge_residue_fixed trivCompleteMod (triv_contraction (fun _ : Unit => ())) () 0 trivial

/-- φ / golden as the named `q = +1` instance, via the Cassini multiplier: the golden orbit's
    Cassini determinant multiplies by `q = +1` each step (`det_golden`/`det_step 3 1`), i.e. it
    is **conserved** — the converging unimodular pole, multiplier `multiplier .converge = 1`. -/
theorem golden_is_converge :
    multiplier .converge = 1
    ∧ (∀ n : Nat, E213.Lib.Math.Algebra.CassiniUnimodular.det
        E213.Lib.Math.Algebra.Mobius213.Px.POrbitClosure.L (n + 1)
        = 1 * E213.Lib.Math.Algebra.CassiniUnimodular.det
            E213.Lib.Math.Algebra.Mobius213.Px.POrbitClosure.L n) :=
  ⟨rfl, (E213.Lib.Math.Algebra.CassiniUnimodular.cassini_law_one_at_two_multipliers).1⟩

/-! ## §5 — the bundling structure and the capstone -/

/-- ★★ **A tagged residue at a value type.**  Bundles a self-map `f : X → X` with a witness
    of its pole (fixed-point-free ⊕' has-fixed-point) and reads off the tag.  This is the *one*
    construct under which both poles are values: `tag = escape` (q=−1) or `tag = converge`
    (q=+1), with the matching `±1` multiplier. -/
structure TaggedResidue (X : Type) where
  f : X → X
  pole : FixedPointFree f ⊕' HasFixedPoint f

/-- The tag read off a `TaggedResidue`. -/
def TaggedResidue.tag {X : Type} (r : TaggedResidue X) : ResidueTag :=
  tagOfSelfMap r.f r.pole

/-- The tag of a `TaggedResidue` is `escape` exactly with a fixed-point-free witness, and
    `converge` exactly with a has-fixed-point witness — the two values, faithfully read. -/
theorem TaggedResidue.tag_dichotomy {X : Type} (r : TaggedResidue X) :
    (∃ _ : FixedPointFree r.f, r.tag = .escape)
    ∨ (∃ _ : HasFixedPoint r.f, r.tag = .converge) := by
  cases hp : r.pole with
  | inl hf => exact Or.inl ⟨hf, by simp only [TaggedResidue.tag, hp]; rfl⟩
  | inr hf => exact Or.inr ⟨hf, by simp only [TaggedResidue.tag, hp]; rfl⟩

/-- ★★★ **The `q = ±1` residue tag exhibits both poles as its two values.**  One construct
    (`ResidueTag`, `multiplier`, the two consequence theorems) under which:

    * **`escape` (`multiplier = −1`)** — the fixed-point-free pole forces a self-cover
      non-surjective: the residue lies **outside every view** (Cantor / Gödel / Russell / Liar /
      the residue's own non-closure / Vitali). `escape_residue_outside`.

    * **`converge` (`multiplier = +1`)** — a contraction has a located fixed point **reached by
      none**, only the modulus-limit (φ / Gaussian / ODE / Picard).
      `converge_residue_fixed`.

    The two `multiplier` values are the two **unimodular** Cassini multipliers
    (`multiplier_unimodular`).  This is the honest unity: one tag, one `±1` reading, one
    consequence per pole — NOT a single biconditional (the poles are a universal-negation
    hypothesis with a negative conclusion versus a contraction hypothesis with an existence
    conclusion; collapsing them would decide the fixed-point predicate, forbidden).  The shared
    column is the tag, not a forced common map. -/
theorem residue_tag_two_poles :
    -- the tag's two values carry the two unimodular `±1` multipliers
    (multiplier .escape = -1 ∧ multiplier .converge = 1)
    ∧ (∀ q : ResidueTag, multiplier q * multiplier q = 1)
    -- q = −1 value: the escape pole (residue outside every view) — inhabited by Cantor's `not`
    ∧ (FixedPointFree (fun b : Bool => !b)
        ∧ ∀ {A : Type}, ¬ ∃ f : A → (A → Bool), Function.Surjective f)
    -- q = +1 value: the converge pole (located fixed point reached by none) — inhabited on Unit
    ∧ (∀ m, trivCompleteMod.close m
        (trivCompleteMod.picardLim
          (triv_contraction (fun _ : Unit => ())) () 0 trivial)
        ((fun _ : Unit => ())
          (trivCompleteMod.picardLim
            (triv_contraction (fun _ : Unit => ())) () 0 trivial))) :=
  ⟨⟨rfl, rfl⟩,
   multiplier_unimodular,
   ⟨bool_not_fixedPointFree, fun {_A} => cantor_is_escape⟩,
   unit_id_converges⟩

end E213.Lib.Math.Foundations.ResidueTag
