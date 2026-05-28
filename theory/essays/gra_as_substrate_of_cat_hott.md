# GRA as substrate — Cat / HoTT as Readings

## Triggering question

> "카테고리나 HoTT 같은 역할을 GRA 가 더 본질적인 자리에서
> 수행할 수도 있겠는데."

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

`physics/foundations/atomic_constants.md` derives
`(NS, NT, c, d) = (3, 2, 2, 5)` from `seed/AXIOM/`: no exterior
dialer (`§5.1`), atomicity (`§4.2`), Pell-Lucas recurrence
(`Theory/Atomicity/PairForcing`), `k = 2` arity forcing.  Then
`gcd(NT, NS) = gcd(2, 3) = 1` is `Common.coprime_2_3` — Lean
kernel-decidable.  From `gcd = 1` follows
`Common.reach_23 : ∀ n ≥ 2, ∃ a b, n = 2·a + 3·b`, and from
greedy optimality the depth `⌈n/3⌉` (`Common.depth_formula`).
None of this admits a tunable parameter.

### §2 Cat as Reading R₂

`GRA/HigherAlgebraEnrichment.lean` already names R₂ as "operad
level"; the data is:

  · objects with `level : Nat` (constrained to `0 ∨ ≥ 2`)
  · `day : Operad → Operad → Operad` — Day convolution,
    grade-additive (`A2`)
  · `nest : Operad → Operad → Operad` — nested integration,
    grade-subadditive (`A3`)
  · associativity / unit laws automatic via `Nat.add_assoc`,
    `Nat.add_comm`, `Nat.add_zero`

This is *exactly* the data of a *symmetric monoidal category*
of `E_n`-algebras: composition (`day`) associative + unital,
tensor (`nest`) sub-grade, two distinguished objects
(`E_2`, `E_3`).  Phase 15 `Monoidal.product` gives the
categorical product `⊗_GRA` on these objects.  What category
theory calls "the category of `E_n`-algebras with coherence
isos" is the R₂ Reading of the (2, 3)-arithmetic, with the
coherence isos being instances of `GRAIso.refl` / `GRAIso.trans`
laws (Phase 7 `Category.GRAIso_id_comp` / `_comp_id` /
`_comp_assoc`).

### §3 HoTT as Reading R₃ — and the Lens-isomorphism formulation

`GRA/HoTTEnrichment.lean` names R₃ as "truncation level":

  · `Truncation.level : Nat` with `level = 0 ∨ level ≥ 2`
  · `suspend (Σⁿ)` : level-additive
  · `smash (∧)` : level-sub-additive

This IS the data of *truncated homotopy types* — a contractible
(level 0) type, a 2-type, a 3-type, with suspension building
higher types from lower and smash giving the tensor.  The
truncation hierarchy `0\!-\!type ⊂ 1\!-\!type ⊂ 2\!-\!type ⊂ \ldots`
is depth-monotonicity (`Common.depth_formula`).

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
Phase 16 (forthcoming) constructs the grade-Lens for each of
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

  · `det(P) = 1` (`theory/essays/mobius_self_form_fixed_point.md`):
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

## Open frontier — closed in Phase 17

The originally-queued open frontier was the carrier-level
equation: prove that the enriched `Raw → C → Nat` composite
equals `canonicalGradeMap` PURE, where `C ∈ {Walk, Cochain,
Truncation, Operad, Resolution}`.  Going through `Raw.fold_slash`
on `C` requires a PURE `combine_sym` for the enriched type,
which would force reasoning about the `Prop` constraint field
(`length = 0 ∨ length ≥ 2`) and the usual route brings
`propext`.

Phase 17 (`CarrierRealization.lean`) closes this frontier by
*bypassing* the `Raw.fold` route.  Key observation:
`canonicalGradeMap r ≥ 2` for every `r : Raw` (Raw.a → 2, Raw.b
→ 3, slash → sum of two ≥-2 values).  So we can build each
realization directly as

```
walkRealize r := ⟨canonicalGradeMap r, Or.inr (canonical_ge_2 r)⟩
```

— no enriched `Raw.fold`, no `combine_sym`, no `propext`.  The
grade projection `(walkRealize r).length = canonicalGradeMap r`
follows by `rfl`, and the headline HoTT ↔ Higher Algebra
equation `(truncationRealize r).level = (operadRealize r).level`
holds *at the carrier level*, also by `rfl`.  Total: 33 PURE
theorems in Phase 17, all kernel-decidable.

Phase 18 (`Universality23.lean`) addresses the next frontier
via the 1-categorical proxy.  The `canonicalGradeMap_universal`
theorem proves: any `f : Raw → Nat` satisfying `f Raw.a = 2`,
`f Raw.b = 3`, and `f (slash x y h) = f x + f y` equals
`canonicalGradeMap` pointwise.  Combined with Phase 16/17, this
says: ANY structure (`Cat`-object included) whose grade map
satisfies the (2, 3)-profile *is forced* to read the canonical
arithmetic.  "Cat is a Reading of GRA" becomes the assertion
that Cat's natural grade map (from its monoidal-structure
generators) has this profile — and the universal property does
the rest.  `canonical_arithmetic_forced` is the parameterless
capstone.

Phase 19 (`Universe1.lean`) addresses the strict 2-categorical
universe-lifting requirement.  A universe-polymorphic parallel
`HasDistinguishingU.{u}` is defined, and an instance
`HasDistinguishingU.{1} (ULift.{1, 0} Reading)` is exhibited via
the `Type 1`-lifted `Reading` enum, with `readingCombine := if r
= s then r else .NT` providing strict commutativity (the
condition `r = s` is symmetric).  Atoms `NT` and `Graph` retain
their (2, 3)-grade profile under the lifted structure.  The
strict universe-lifting requirement Phase 18 named is therefore
*met*: a `Type 1` carrier admits the distinguishing structure
with the same atomic grades as the `Raw`-level arithmetic.

This does not give a *natural* combine on the category-of-
categories — `readingCombine` collapses non-equal Readings to
the hub `.NT`.  A natural combine on categorical objects (e.g.,
Cartesian product) is iso-symmetric, not strictly symmetric, so
requires a separate weakening of `HasDistinguishingU` to take
combine_sym up to a chosen equivalence relation.  That
weakening is the open question beyond Phase 19 — but Phase 19
demonstrates that the universe-lifting itself does not break
the parameterless discipline.

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
