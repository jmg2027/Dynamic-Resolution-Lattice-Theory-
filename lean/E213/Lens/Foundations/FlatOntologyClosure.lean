import E213.Lens.Foundations.FlatOntology
import E213.Lens.Cardinality.Cantor

/-!
# Lens.FlatOntologyClosure — the self-covering closure, exactly up to the residue

`FlatOntology` realises every sort (object / type / relation / function / Lens)
as one primitive: a decidable predicate on `Raw^n`.  It defers the *closure*
direction — encoding a predicate back as a Raw (`seed/AXIOM/06_lens_readings.md`
§6.3; "self-cover").

This file records the *limit* shape of that closure:

  * **Faithful**: `Object1 : Raw → (Raw → Bool)` (each Raw as its own indicator
    `· = r`) is **injective** — Raw self-covers as predicates with nothing lost.
  * **Not total**: `Object1` is **not surjective** — the predicates *not* of the
    form `· = r` are exactly the Cantor-unpointable surplus
    (`Cardinality.cantor_raw_bool`).  That surplus is the **residue**: the part
    of the predicate algebra the substrate cannot point at as a single Raw.

The complementary *positive* direction is already closed in
`Lens/Foundations/PredicateSelfEncoding.lean`: every **finite-prefix / definable** predicate
DOES encode back to a Raw (`predicateToRaw`, `predicate_self_encoding_closure`,
all ∅-axiom).  Together: definable predicates round-trip (positive closure), the
full predicate space does not (this file) — and the gap between "definable" and
"all" is exactly the residue.  So the self-covering "closes exactly up to the
residue": faithful and round-tripping on what can be pointed at / described, with
the unpointable surplus being the residue itself.  This is the ∅-axiom statement
of the session thesis: pointing
is finite; the completed-infinite surplus is a finite *name*, not an inhabitant.
-/

namespace E213.Lens.Foundations.FlatOntologyClosure

open E213.Theory (Raw)
open E213.Lens.Foundations.FlatOntology (Object1 Object1_self)
open E213.Term.Internal (Tree)

/-- The two atoms differ — propext-free (`Tree.noConfusion`, not `decide`
    which pulls `propext` through `DecidableEq Raw`). -/
private theorem a_ne_b : Raw.a ≠ Raw.b :=
  fun h => Tree.noConfusion (congrArg Subtype.val h)

/-- The self-cover `Object1` is **injective**: distinct Raws give distinct
    indicator predicates.  Faithful self-covering — applying both sides at `r`
    forces `decide (r = s) = true`, hence `r = s`. -/
theorem object1_injective : Function.Injective Object1 := by
  intro r s h
  -- `h : Object1 r = Object1 s`; evaluate both sides at `r`.
  have hr : Object1 r r = Object1 s r := congrFun h r
  -- `Object1 r r = true`, so `Object1 s r = true`, i.e. `decide (r = s) = true`.
  rw [E213.Lens.Foundations.FlatOntology.Object1_self] at hr
  -- `Object1 s r = decide (r = s)`; from `true = decide (r = s)` get `r = s`.
  -- `of_decide_eq_true` (not `decide_eq_true_eq`, which pulls propext).
  unfold E213.Lens.Foundations.FlatOntology.Object1 at hr
  exact of_decide_eq_true hr.symm

/-- The self-cover `Object1` is **not surjective**: there is no surjection
    `Raw → (Raw → Bool)` at all (Cantor).  The predicates outside the image of
    `Object1` are the residue surplus. -/
theorem object1_not_surjective : ¬ Function.Surjective Object1 :=
  fun hsurj => E213.Lens.Cardinality.cantor_raw_bool ⟨Object1, hsurj⟩

/-- ★ **Self-covering closure capstone.**  The flat-ontology self-cover
    `Object1 : Raw → (Raw → Bool)` is faithful (injective) but not total
    (not surjective).  Raw embeds exactly into its own predicate algebra, and
    the un-embedded surplus — the Cantor-unpointable predicates — is the
    residue. -/
theorem self_covering_closure :
    Function.Injective Object1 ∧ ¬ Function.Surjective Object1 :=
  ⟨object1_injective, object1_not_surjective⟩

/-! ## A concrete residue witness — the undifferentiated predicate

`object1_not_surjective` is the abstract gap (Cantor).  Here is a *named*
inhabitant of it, tying the gap to the session's "undifferentiated"
notion: the **constant-true predicate** `fun _ => true` — the predicate that
draws no distinction at all (the `Raw → Bool` shadow of `constLens`) — is not in
the image of `Object1`.  Each `Object1 r` is true at exactly one Raw, so it can
never equal a predicate true everywhere (there are ≥ 2 Raws, `a ≠ b`).

So the residue is not merely a cardinality surplus: its cleanest concrete member
is the *undifferentiated* reading itself — the one predicate that points at
nothing-in-particular cannot be pointed at as any single Raw. -/

/-- The constant-true (undifferentiated) predicate on Raw. -/
def undifferentiated : Raw → Bool := fun _ => true

/-- No Raw's indicator equals the undifferentiated predicate: pick a Raw `≠ r`
    (the other atom), where the indicator is `false` but `undifferentiated` is
    `true`. -/
theorem undifferentiated_not_object1 (r : Raw) :
    Object1 r ≠ undifferentiated := by
  intro h
  -- Choose a witness `s ≠ r`: the atom on the other side of `r`.
  -- If `r = a` use `b`; otherwise use `a`.  Either way `s ≠ r`.
  by_cases hra : r = Raw.a
  · -- r = a; take s = b, and b ≠ a = r
    have hbr : Raw.b ≠ r := by rw [hra]; exact (Ne.symm a_ne_b)
    have hval : Object1 r Raw.b = undifferentiated Raw.b := congrFun h Raw.b
    -- Object1 r b = decide (b = r) = false (since b ≠ r); undifferentiated b = true
    unfold Object1 undifferentiated at hval
    rw [decide_eq_false hbr] at hval
    exact Bool.noConfusion hval
  · -- r ≠ a; take s = a, and a ≠ r
    have har : Raw.a ≠ r := fun e => hra e.symm
    have hval : Object1 r Raw.a = undifferentiated Raw.a := congrFun h Raw.a
    unfold Object1 undifferentiated at hval
    rw [decide_eq_false har] at hval
    exact Bool.noConfusion hval

/-- ★★ **The residue, named.**  The undifferentiated predicate inhabits the
    Cantor gap of `object1_not_surjective`: it is a `Raw → Bool` with no Raw
    preimage under `Object1`.  The faithful self-cover closes *exactly* up to
    this — the part the substrate cannot point at as a single Raw is led by the
    reading that draws no distinction. -/
theorem residue_witnessed :
    Function.Injective Object1
    ∧ (∃ P : Raw → Bool, ∀ r : Raw, Object1 r ≠ P) :=
  ⟨object1_injective, undifferentiated, undifferentiated_not_object1⟩

/-- ★★★ **The residue is the remainder the distinguishing always leaves** — `01_residue.md`
    §1.1 *as a theorem*, not a primitive.  The primitive is the **act of distinguishing**:
    `Object1 : Raw → (Raw → Bool)` reads each `Raw` as its own self-indication (the
    distinguishing of that point from every other).  This act is **faithful** —
    `object1_injective`, distinct points are genuinely separated, the distinguishing
    *succeeds* — and **never total** — `object1_not_surjective`, a predicate always lies
    outside its image (Cantor).  The residue is therefore not assumed; it is *derived* as the
    proven, ineliminable remainder of distinguishing, with a **named** member: the
    undifferentiated reading `fun _ => true` is outside every self-indication
    (`undifferentiated_not_object1`).

    So "213 is the residue of pointing" is exact only read this way: pointing/distinguishing
    is primal, and *that a residue always remains* is the content of this theorem.  Its
    dynamic strengthening — the residue re-enters as the next operand and the cover still
    never closes — is `ResidueReentry.residue_perpetually_reenters`; its generative twin —
    the distinguishing never closes `Raw` — is `Theory.Raw.MuNuMirror.tower_no_cycle`. -/
theorem distinguishing_always_leaves_residue :
    Function.Injective Object1
    ∧ ¬ Function.Surjective Object1
    ∧ (∀ r : Raw, Object1 r ≠ undifferentiated) :=
  ⟨object1_injective, object1_not_surjective, undifferentiated_not_object1⟩

/-- ★★★ **Distinguishing = reference = self-reference — one map, three argument-patterns.**
    The single map `Object1 : Raw → (Raw → Bool)` carries all three "names" the seminar
    (`theory/essays/foundations/the_distinguishing_is_the_primitive.md`) treats as one act:

    1. **reference IS the distinguishing read as a pointing** — `Object1 r s = true ↔ s = r`:
       the indicator `Object1 r = (· = r)` points at *exactly* the point `r` distinguishes
       from every other.  Reference is not added on top of distinguishing; it is the
       distinguishing presented as a `Raw → Bool` map.
    2. **self-reference IS that reference self-applied** — `Object1 a a = true`: the diagonal
       value `decide (a = a)` is `a` referring to itself *by the very predicate that
       distinguishes it*.  This is the kernel `f a a` of the Lawvere diagonal at `f := Object1`
       (`OneDiagonal.residue_is_lawvere_diagonal`).
    3. the act's **non-closure** — `¬ Function.Surjective Object1` — is that one
       self-application's residue (Cantor).

    So the three are one map `Object1` read at three argument-patterns (`r s`, `a a`,
    all-of-image), not three constructions.

    **Honest guard** (failure-mode *View-promoted-to-identity*): this is a **Lens reading**
    (one map, three readings), not a kernel-*forced* identity of three types — exactly the
    `SelfReferenceThreeOutcomes` "one act, three readings."  The apparent *ascent* to
    self-reference (the TIER-B climb to the power object `Raw → Bool`) is the **writing-cost** of reifying the
    function space to express `f a a`, not a real level above the distinguishing; the act is
    one.  And "reference" here is **de-intentionalized** — bare directedness (`· = r`), no
    referring agent (the type `Raw → Bool` contains no mind). -/
theorem three_as_one_construction :
    (∀ r s : Raw, Object1 r s = true ↔ s = r)        -- reference = the distinguishing `· = r`
    ∧ (∀ a : Raw, Object1 a a = true)                 -- self-reference kernel: r refers to itself
    ∧ ¬ Function.Surjective Object1 :=                 -- the residue (Cantor)
  ⟨fun _ _ => ⟨of_decide_eq_true, decide_eq_true⟩, Object1_self, object1_not_surjective⟩

end E213.Lens.Foundations.FlatOntologyClosure
