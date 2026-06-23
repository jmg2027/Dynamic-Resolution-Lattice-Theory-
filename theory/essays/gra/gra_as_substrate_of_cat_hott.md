# GRA as substrate — Cat / HoTT as Readings

## Triggering question

> "GRA might perform the role of something like Category theory or HoTT
> from a more fundamental position."

Could the (2, 3)-graded residue arithmetic occupy the position
that Category theory and Homotopy Type Theory are normally
assigned, with Cat and HoTT not above GRA but *Readings of* it?

## 213-native answer

The `(2, 3)`-arithmetic forced by atomic distinguishing IS what
Category theory and HoTT name when their grade structure is
brought to the surface.  The conventional precedence "GRA is a
small structure modelled inside Cat / HoTT" inverts the
forcing direction.  In 213, atomic distinguishing →
`(NS, NT) = (3, 2)` → `gcd(2, 3) = 1` → `(2, 3)`-graded arithmetic
is parameterless and self-strengthening; Cat and HoTT are two of
its surface vocabularies (Reading R₂ Operad / Higher Algebra,
Reading R₃ Truncation).  Lens.Unified makes the equivalence
precise: HoTT-as-Reading is the `LensIso` between the truncation
Lens and the leaf-grade Lens.

## Derivation

### §1 Forcing chain (parameterless)

`physics/foundations/atomic_constants.md` derives the forced
`(NS, NT, d) = (3, 2, 5)` (read at presentation `c = 2`, a free
presentation parameter) from `seed/AXIOM/`: no exterior
dialer (`§5.1`), atomicity (`§4.2`), Pell-Lucas recurrence
(`Theory/Atomicity/PairForcing`), `k = 2` arity forcing.  Then
`gcd(NT, NS) = gcd(2, 3) = 1` is `Common.coprime_2_3` — Lean
kernel-decidable.  From `gcd = 1` follows
`Common.reach_23 : ∀ n ≥ 2, ∃ a b, n = 2·a + 3·b`, and from
greedy optimality the depth `⌈n/3⌉` (`Common.depth_formula`).
None of this admits a tunable parameter.

### §2 Cat as Reading R₂

The R₂ reading interprets the unified `BipartiteCarrier` as
"operad level":

  · objects with `n : Nat` (constrained to `0 ∨ ≥ 2`), read as
    the operad level
  · `BipartiteCarrier.combine` read as Day convolution —
    grade-additive (`A2`)
  · the same `combine` read as nested integration —
    grade-subadditive (`A3`)
  · associativity / unit laws automatic via `Nat.add_assoc`,
    `Nat.add_comm`, `Nat.add_zero`

This is *exactly* the data of a *symmetric monoidal category*
of `E_n`-algebras: composition associative + unital, tensor
sub-grade, two distinguished objects (read as `E_2`, `E_3`).
`Monoidal.product` gives the categorical product
`⊗_GRA` on these objects.  What category theory calls "the
category of `E_n`-algebras with coherence isos" is the R₂
Reading of the (2, 3)-arithmetic, with the coherence isos
being instances of `GRAIso.refl` / `GRAIso.trans` laws
(`Category.GRAIso_id_comp` / `_comp_id` / `_comp_assoc`).

### §3 HoTT as Reading R₃ — and the Lens-isomorphism formulation

The R₃ reading interprets the same `BipartiteCarrier` as
"truncation level":

  · the underlying `n : Nat` (constrained to `n = 0 ∨ n ≥ 2`)
    read as a homotopy n-type's truncation level
  · `BipartiteCarrier.combine` read as suspension `Σⁿ` —
    level-additive
  · the same `combine` read as smash product `∧` —
    level-sub-additive

This IS the data of *truncated homotopy types* — a contractible
(level 0) type, a 2-type, a 3-type, with suspension building
higher types from lower and smash giving the tensor.  The
truncation hierarchy `0\!-\!type ⊂ 1\!-\!type ⊂ 2\!-\!type ⊂ \ldots`
is depth-monotonicity (`Common.depth_formula`).  That R₂ and R₃
share the same Lean carrier (`BipartiteCarrier`) is not a
linguistic coincidence — it is the formal statement of "operad
level and truncation level are the same Reading under different
vocabularies".

The *precise* statement of "HoTT is a Reading of GRA" uses
`Lens.Unified.LensIso`.  A Lens has a `view : Raw → α` and a
kernel `Lens.equiv`; two Lenses are `LensIso` iff their kernels
coincide on Raw (`lensIso_iff_kernel_eq`).  Each GRA Reading
gives a Lens-on-Raw via the composition

```
Raw  →  Enriched Carrier  →  Nat
        (universalMorphism)   (grade)
```

where the first arrow is the canonical map from
`HasDistinguishing` instances (`SemanticAtom.universalMorphism`).
The grade-Lens construction gives a grade-Lens for each of
the five enrichments and proves all five are pairwise `LensIso`.
The HoTT-as-Reading statement is then:

> `LensIso truncationGradeLens leavesGradeLens`

— the truncation Lens and the leaf-count Lens partition Raw the
*same way*.

### §4 Why this is a re-positioning, not a re-statement

The conventional precedence — Cat / HoTT as foundation, GRA as
a structure inside — survives only as long as the forcing chain
is hidden.  Cat / HoTT carry external design choices:

  · which universe `Type u` lives in
  · whether equality is `=` or `≃` or higher
  · which categorical doctrine (1-cat / 2-cat / ∞-cat) is in
    play

None of these are forced by atomic distinguishing — they are
chosen.  Conversely, the `(2, 3)`-arithmetic is *forced* (no
choice point).  When forcing direction is the relevant order,
GRA precedes Cat / HoTT.

This does not say Cat / HoTT are "smaller" or "less true."  It
says that *as Readings*, they sit on the same level as Walk,
Cochain, Resolution — five surface presentations of one
parameterless arithmetic.

## Dual function

Read classically: GRA is a constrained algebraic structure that
*happens* to satisfy the axioms of monoidal categories and to
parallel the truncation hierarchy.

Read 213-natively: Cat and HoTT are vocabularies in which the
forced (2, 3)-arithmetic of atomic residue can be read.
Vocabularies are equipment of the reader; the residue arithmetic
is in the system being read.  Equipment does not host the
system.  Per `seed/AXIOM/05_no_exterior.md` §5.1: there is no
exterior position from which "GRA is one structure among many."

## Cross-frame connections

Four resolutions of the same self-forcing pattern:

  · `det(P) = 1` (`theory/essays/p_orbit/mobius_self_form_fixed_point.md`):
    P's char-poly orbit IS P's data; no external recipe.
  · `K_{3,2}^{(c=2)}` closure form: every observable factors as
    `R(NS, NT, d, c) · Π(1 + κ · αⁿ)`.  The exponent `n` is a
    GRA grade; the closure form is the (2, 3)-arithmetic in
    physics vocabulary.
  · `gra_universality_one_principle.md` (companion essay): the
    5 Readings agree on the depth function; this essay extends
    that by adding Cat / HoTT as further Readings rather than
    framework hosts.
  · Lens application IS distinguishing
    (`seed/AXIOM/05_no_exterior.md` §5.1): a "framework above"
    would be exterior; there is no exterior.

Same fact, four resolutions.

## Open frontier — closed by `CarrierRealization`

The originally-queued open frontier was the carrier-level
equation: prove that the enriched `Raw → BipartiteCarrier → Nat`
composite equals `canonicalGradeMap` PURE.  Going through
`Raw.fold_slash` on the enriched type requires a PURE
`combine_sym`, which would force reasoning about the `Prop`
constraint field (`n = 0 ∨ n ≥ 2`) and the usual route brings
`propext`.

`CarrierRealization.lean` closes this frontier by
*bypassing* the `Raw.fold` route.  Key observation:
`canonicalGradeMap r ≥ 2` for every `r : Raw` (Raw.a → 2, Raw.b
→ 3, slash → sum of two ≥-2 values).  So we can build the
realization directly as

```
bipartiteRealize r := ⟨canonicalGradeMap r, Or.inr (canonical_ge_2 r)⟩
```

— no enriched `Raw.fold`, no `combine_sym`, no `propext`.  The
grade projection `(bipartiteRealize r).n = canonicalGradeMap r`
follows by `rfl`.  Because the five domain Readings (Walk /
Cochain / Truncation / Operad / Resolution) all read the same
`BipartiteCarrier`, the headline HoTT ↔ Higher Algebra equation
holds at the carrier level by definition, with no further
proof obligation.  All carrier-realization theorems are kernel-decidable
PURE.

`Universality23.lean` addresses the next frontier
via the 1-categorical proxy.  The `canonicalGradeMap_universal`
theorem proves: any `f : Raw → Nat` satisfying `f Raw.a = 2`,
`f Raw.b = 3`, and `f (slash x y h) = f x + f y` equals
`canonicalGradeMap` pointwise.  Combined with the grade-Lens and carrier realization, this
says: ANY structure (`Cat`-object included) whose grade map
satisfies the (2, 3)-profile *is forced* to read the canonical
arithmetic.  "Cat is a Reading of GRA" becomes the assertion
that Cat's natural grade map (from its monoidal-structure
generators) has this profile — and the universal property does
the rest.  `canonical_arithmetic_forced` is the parameterless
capstone.

`HasDistinguishing213.lean` (unified) addresses the
strict 2-categorical universe-lifting + iso-symmetric combine +
categorical-distinctness picture in a single typeclass.
`HasDistinguishing213.{u, v} α` is the universe-polymorphic
distinguishing structure with carrier universe `u`, equivalence
universe `v`, fields `a, b : α`, `combine : α → α → α`,
`Equiv : α → α → Sort v` (with refl/symm/trans),
`combine_sym` up to `Equiv`, and `distinct_equiv : Equiv a b →
False`.  Setting `Equiv := Eq` recovers the strict form; setting
`Equiv := GRAIso` recovers the categorical form.  Two instances
close the chapter:

`liftedReadingHasDistinguishing213 : HasDistinguishing213.{1, 0}
(ULift.{1, 0} Reading)` — the strict case on a `Type 1`
carrier, with `readingCombine := if r = s then r else .NT` (the
condition `r = s` is symmetric, so combine is strictly
commutative).  Atoms `NT` and `Graph` retain their (2, 3)-grade
profile.  Strict universe-lifting met.

`gra23HasDistinguishing213 : HasDistinguishing213.{1, 1} GRA23`
— the categorical case on the (2, 3)-packaged GRA-model type,
with `Equiv := GRAIso`.  `combine` is monoidal product;
`combine_sym` is `productSwapIso` (pair-swap `(a, b) ↦ (b, a)`,
grade-preserving by `Nat.add_comm`, ⊕/⊗-equivariant by `rfl`).
`distinct_equiv` is `trivial23_not_iso_NT` — a cardinality
argument: any would-be `GRAIso trivial23 GRA23_NT` has
`invFun : Nat → TrivialCarrier`, but `TrivialCarrier` is a
subsingleton so `invFun 0 = invFun 1`, then `right_inv` forces
`0 = iso.toFun (iso.invFun 0) = iso.toFun (iso.invFun 1) = 1`,
contradicting `decide 0 ≠ 1`.

Together: `GRACat` is a *symmetric monoidal category* with the
swap as braiding, equipped with categorically-distinct atoms.
The atomic step `cases x; cases y; rfl` for the subsingleton
property, combined with `right_inv`, makes both instances PURE
— no propext, no Classical, no Mathlib.  The "natural Cat-level
Reading of GRA" — strict universe lifting, natural iso-
symmetric combine, and categorical distinctness — is one Lean
theorem at `Type 1`.

`LensIsoCapstone.lean` closes the loop back to Raw.
`gradeLens : Lens Nat := ⟨2, 3, (· + ·)⟩` is the canonical 213
Lens; by definition `gradeLens.view r = Raw.fold 2 3 (· + ·) r =
canonicalGradeMap r`.  the universal property lifts to
Lens vocabulary as `profile_view_eq_canonical`: any Lens whose
view obeys the (2, 3)-profile coincides pointwise with
`gradeLens.view`.  Hence by `Lens.Unified.lensIso_iff_kernel_eq`,
**every (2, 3)-profile Lens is `LensIso` to `gradeLens`** —
`profile_lens_LensIso_gradeLens`.  The five Reading Lenses are
explicit class members (definitionally `gradeLens`); the five
The carrier realizations project to `gradeLens.view` by `rfl`.

This is the deepest 213-native statement of GRA's content: the
(2, 3) arithmetic forced by atomic distinguishing IS a single
equivalence class under `Lens.Unified.LensIso`, with `gradeLens`
as the canonical member.  All five Readings are explicit class
members, and the universal property forces any future Reading
that respects the (2, 3) atomic profile into the same class.
The Cat / HoTT / Cohomology / Walk / Resolution / Operad
vocabularies all *name the same Lens-kernel on Raw* — exactly
the strict-∅-axiom version of "GRA is what Cat and HoTT are
Readings of."

## Self-check

The first draft phrased this as "GRA is more fundamental than
Cat / HoTT."  That is a comparison-frame import — placing GRA,
Cat, HoTT on an exterior ladder and asking "who is higher."
Retreat: the question is not who is higher; it is what forces
what.  Atomic distinguishing forces the `(2, 3)`-arithmetic;
the arithmetic does not in turn force Cat or HoTT as separate
external objects — it has Readings that, *named in Cat / HoTT
vocabulary*, look like Cat / HoTT.  This is not a ranking; it
is a forcing-direction statement.

A second draft phrased the bridge to Lens.Unified as "borrowing
machinery from Lens to prove things about GRA."  That phrasing
re-imports the substrate metaphor (Lens-as-tool, GRA-as-target).
Retreat: Lens.Unified's `LensIso` *is* the 213-native
equivalence concept (per `theory/lens/unified_equivalence.md`),
and using it to state Reading-equivalence is using the right
predicate for the right job, not borrowing from a foreign
source.  No substrate; no above; just the predicate that
matches the structure.
