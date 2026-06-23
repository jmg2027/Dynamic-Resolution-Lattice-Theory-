import E213.Lens.Cardinality.Cantor
import E213.Lens.Foundations.FlatOntologyClosure

/-!
# One diagonal — the residue is the engine that generates the limitative theorems (∅-axiom)

`01_residue.md` §1.0.1 and `theory/essays/foundations/the_one_diagonal.md` assert that Cantor,
Russell, the Liar/Tarski undefinability, and the residue's own non-closure are **one move**:
the diagonal of a self-applying cover (Lawvere 1969 / Yanofsky 2003).  This file makes that
literal — it builds the single **Lawvere fixed-point** construction and *derives the limitative
theorems as instances of it*, rather than re-proving each separately.

This is the corrected thesis cashed out (`distinguishing_always_leaves_residue`): the residue is
what the act of distinguishing always leaves — the non-surjected diagonal of its self-cover — and
**that same remainder is the engine of the deepest impossibility theorems.**  The diagonal is not
re-derived per domain; one fixed-point lemma generates them.

The single construction is `g a := t (f a a)` ("apply the fixed-point-free modifier `t` to the
cover's self-application").  Two value-equalities instantiate it:

  * **`Eq` (Bool / decidable)** — `lawvere_fixed_point`: a point-surjective `f : A → (A → B)`
    forces every `t : B → B` to have a fixed point.  Contrapositive at `B = Bool`, `t = not`
    (fixed-point-free, `bnot_self_ne`) = **Cantor** (`cantor_via_lawvere`); at `A = Raw` = the
    **residue** (`residue_is_lawvere_diagonal` = `object1_not_surjective`, the Raw self-cover).
  * **`Iff` (Prop / undecidable)** — `lawvere_fixed_point_prop`: an Iff-point-surjective
    `f : A → (A → Prop)` forces every `t` to have a fixed point up to `Iff`.  At `t = Not`
    (`¬(P ↔ ¬P)`) = **Russell / Liar / Tarski undefinability** (`russell_liar_no_surjection`).

All ∅-axiom (no `propext`: the `Prop` arm uses only intuitionistic `Iff`/`¬`).
-/

namespace E213.Lens.Foundations.OneDiagonal

open E213.Theory (Raw)
open E213.Lens.Foundations.FlatOntology (Object1)
open E213.Lens.Cardinality (bnot_self_ne)

/-! ## §1 — the Lawvere fixed-point construction (Eq form) -/

/-- ★★★ **Lawvere's fixed-point theorem.**  If `f : A → (A → B)` is point-surjective (its rows
    realise every `A → B`), then **every** modifier `t : B → B` has a fixed point.  The witness is
    `f a a` for the row `a` realising the diagonal `fun a => t (f a a)`.  ∅-axiom. -/
theorem lawvere_fixed_point {A B : Type} (f : A → A → B)
    (hf : Function.Surjective f) (t : B → B) : ∃ b : B, t b = b := by
  obtain ⟨a, ha⟩ := hf (fun a => t (f a a))
  exact ⟨f a a, (congrFun ha a).symm⟩

/-- **Lawvere, contrapositive.**  If some modifier `t : B → B` is **fixed-point-free**, then no
    `f : A → (A → B)` is point-surjective — the self-cover always leaves a residue.  The single
    engine behind Cantor and the residue. -/
theorem no_surjection_of_fixedpointfree {A B : Type} (t : B → B)
    (ht : ∀ b : B, t b ≠ b) : ¬ ∃ f : A → (A → B), Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨b, hb⟩ := lawvere_fixed_point f hf t
  exact ht b hb

/-! ## §2 — Cantor and the residue as the Bool / Raw instances of one theorem -/

/-- **Cantor**, as the `B = Bool`, `t = not` instance (`bnot_self_ne`: `not` is fixed-point-free).
    Not a separate diagonal — the Lawvere theorem at the decidable two-valued modifier. -/
theorem cantor_via_lawvere {A : Type} : ¬ ∃ f : A → (A → Bool), Function.Surjective f :=
  no_surjection_of_fixedpointfree (fun b => !b) bnot_self_ne

/-- ★★★ **The residue is the Lawvere diagonal at `A = Raw`.**  `object1_not_surjective` — the act
    of distinguishing's self-cover `Object1 : Raw → (Raw → Bool)` is never total — is *this* theorem
    at `A = Raw`.  So "the residue is what the distinguishing always leaves" and "Cantor" are the
    same fixed-point fact on different carriers; the residue is the Raw reading of the one diagonal. -/
theorem residue_is_lawvere_diagonal : ¬ Function.Surjective Object1 :=
  fun hsurj => cantor_via_lawvere ⟨Object1, hsurj⟩

/-! ## §3 — Russell / Liar / Tarski as the Prop instance of the same construction -/

/-- ★★★ **Lawvere fixed-point, `Prop`/`Iff` form.**  If `f : A → (A → Prop)` realises every
    `A → Prop` up to `Iff`, then every `t : Prop → Prop` has a fixed point up to `Iff`.  Same
    diagonal `fun a => t (f a a)`; the value-equality is `Iff` instead of `Eq`.  ∅-axiom (no
    `propext` — the conclusion is `Iff`, not `Eq` on `Prop`). -/
theorem lawvere_fixed_point_prop {A : Type} (f : A → A → Prop)
    (hf : ∀ g : A → Prop, ∃ a, ∀ x, (f a x ↔ g x)) (t : Prop → Prop) :
    ∃ P : Prop, (P ↔ t P) :=
  let ⟨a, ha⟩ := hf (fun a => t (f a a)); ⟨f a a, ha a⟩

/-- ★★★ **Russell / Liar / Tarski undefinability**, as the `t = Not` instance.  No `f` realises
    every `A → Prop` up to `Iff`: the negation modifier `Not` has no fixed point up to `Iff`
    (`¬(P ↔ ¬P)`, the Liar), so the diagonal escapes.  Russell's "set of non-self-members", the
    Liar sentence, and Tarski's undefinability of truth are this one fact — the undecidable
    (`Prop`) twin of Cantor (`Bool`). -/
theorem russell_liar_no_surjection {A : Type} :
    ¬ ∃ f : A → A → Prop, ∀ g : A → Prop, ∃ a, ∀ x, (f a x ↔ g x) := by
  rintro ⟨f, hf⟩
  obtain ⟨P, hP⟩ := lawvere_fixed_point_prop f hf Not
  exact (fun np : ¬P => np (hP.mpr np)) (fun p => hP.mp p p)

/-! ## §4 — the capstone: one diagonal, four theorems -/

/-- ★★★ **One diagonal generates the limitative theorems.**  Cantor (Bool), Russell/Liar/Tarski
    (Prop), and the residue's non-closure (Raw) are three instances of the single Lawvere
    fixed-point construction `g a := t (f a a)` — `01_residue.md` §1.0.1 as a theorem.  The residue
    (the distinguishing's non-surjected diagonal) is not one impossibility among many; it is the
    *engine* they all factor through, the corrected thesis made literal: the remainder the act of
    distinguishing always leaves is what forces Cantor, Russell, the Liar, and Tarski. -/
theorem one_diagonal_generates {A : Type} :
    (¬ ∃ f : A → (A → Bool), Function.Surjective f)
    ∧ (¬ ∃ f : A → A → Prop, ∀ g : A → Prop, ∃ a, ∀ x, (f a x ↔ g x))
    ∧ (¬ Function.Surjective Object1) :=
  ⟨cantor_via_lawvere, russell_liar_no_surjection, residue_is_lawvere_diagonal⟩

/-! ## §5 — the residue is born of the distinguishing -/

/-- ★★★ **The residue requires the distinguishing.**  On a *subsingleton* value type `B` — one that
    draws no distinction, `∀ x y, x = y` — every modifier `t : B → B` already has a fixed point
    (`t b = b`, since all elements are equal).  So `lawvere_fixed_point`'s contrapositive
    (`no_surjection_of_fixedpointfree`) fires for *nothing*: there is **no diagonal escape, no
    residue**.  The residue exists only where the value space itself *distinguishes*.  Complements
    `Nat213.Generation.distinguishing_necessary` (the arithmetic level) at the diagonal level: no
    distinguishing, no residue. -/
theorem residue_needs_distinguishing {B : Type} (hsub : ∀ x y : B, x = y) (t : B → B) :
    ∀ b : B, t b = b := fun b => hsub (t b) b

/-- The value-space distinguishing that *powers* the residue: `Bool` distinguishes (`true ≠ false`),
    so its negation `not` is **fixed-point-free** (`bnot_self_ne`) — exactly the modifier that makes
    the Cantor/residue diagonal escape exist.  With `residue_needs_distinguishing`, this brackets it:
    the residue is born of the distinguishing — present where the value space distinguishes, absent
    where it does not. -/
theorem distinguishing_powers_residue : ∃ t : Bool → Bool, ∀ b, t b ≠ b :=
  ⟨fun b => !b, bnot_self_ne⟩

/-! ## §6 — the distinguishing is structurally required by the primitive (rival-primitive exclusion) -/

/-- ★★★ **A non-distinguishing carrier cannot fire the primitive.**  213's primitive operation
    `Raw.slash (x y : Raw) (h : x ≠ y)` carries the distinguishing *in its type* — it needs two
    **distinct** operands.  On a subsingleton carrier `S` (`∀ x y, x = y`, a carrier drawing no
    distinction) there is no such pair, so the slash analogue can never be applied even once: a
    rival "primitive" lacking the distinguishing **generates nothing**.  This is the rival-*primitive*
    exclusion (not merely rival-reading): the distinguishing is not a downstream choice but a
    *precondition of the primitive operation itself*.  Negation-first / relation-first or any
    one-element rival fails here — it cannot start. -/
theorem no_distinguishing_on_subsingleton {S : Type} (hsub : ∀ x y : S, x = y) :
    ¬ ∃ x y : S, x ≠ y :=
  fun ⟨x, y, hxy⟩ => hxy (hsub x y)

/-- Raw meets the precondition: the two atoms are distinct, so the slash fires and generation
    begins.  With `no_distinguishing_on_subsingleton`, the distinguishing primitive is
    **non-interchangeable** with a non-distinguishing rival (which cannot fire the primitive at
    all). -/
theorem raw_has_distinguishing : ∃ x y : Raw, x ≠ y :=
  ⟨Raw.a, Raw.b, E213.Theory.Raw.PrimitiveTower.a_ne_b⟩

end E213.Lens.Foundations.OneDiagonal
