# Cross-domain unification rebuild (post-deletion of the `:True` bundle)

**What was deleted & the bogus mechanism.**  `Lib/Math/Foundations/CrossDomainUnification.lean`
had its headline gutted in `26c86991e` (127 → trimmed):

```lean
theorem cross_domain_unification_master : True := by
  -- ... comments asserting nothing can "block this proof" ...
  trivial
```

The "master unification of all domains" was the proposition `True`, proved by
`trivial`.  A `True` headline is vacuous: it relates no two domains, preserves no
structure, and is true regardless of whether any unification holds.  Paired with
it in the catalog were "cross-domain identifications" that were **value
coincidences** (two unrelated quantities that happen to share a number), which is
not a unification either — a numerical equality `x = y` between two domains' atoms
carries no map.

**The genuine content.**  A real cross-domain unification is a **structure-preserving
map** between two domains — a morphism (functor) `F : A → B`, ideally an
isomorphism `A ≅ B`, that sends the operations/relations of `A` to those of `B`
so that *theorems transport*.  "Domain A unifies with domain B" means: there is
`F` with `F(op_A(x,y)) = op_B(F x, F y)` (and the relations likewise), proven —
not a number that appears in both.  A value coincidence `1/φ² ≈ 0.382` showing up
in two places is at best *evidence to look for* such an `F`; it is not the `F`.

**The 213-native obstruction.**  The vacuous version skipped the only hard part:
exhibiting the map and proving the homomorphism equations.  213 already has the
correct abstract vocabulary for this and does NOT need to invent it:
- `lean/E213/Lens/Unified.lean` — `LensIso` and `lensIso_iff_kernel_eq`: two
  Lens-structures are isomorphic **iff they have the same kernel on Raw**.  This
  is a genuine equivalence-of-structures criterion, the right shape for "domain
  A ≅ domain B".
- the **universal morphism** / initiality (`universalMorphism_unique`, the
  COMPILE-DOWN instruction in `seed/PROOF_ISA.md`): *any* framework that
  distinguishes at all receives the unique morphism from `Raw`.  This is the real
  unification engine — two domains are unified not by mapping `A → B` directly but
  by both being COMPILE-DOWN images of the *same* `Raw`, with the comparison map
  factoring through `Raw`.
- `lean/E213/Lib/Math/Algebra/GRA/LensIsoCapstone.lean` — a worked genuine
  instance: the `(2,3)` grade arithmetic is *exactly one* `LensIso`-class, and
  every "Reading" of GRA is a Lens-equal representative (`profile_lens_LensIso_gradeLens`,
  via `lensIso_iff_kernel_eq`).  This is what a real "these N presentations are
  the same structure" theorem looks like — kernel equality, not `True`.

**Staged plan (citing genuine seams).**

- **Stage 1 — one honest two-domain `LensIso`.**  Pick two domains the repo
  already builds independently and that *should* be the same structure, e.g. the
  count-Lens reading and a number-tower reading that share a kernel.  State the
  theorem as: `LensIso L_A L_B`, discharged via `lensIso_iff_kernel_eq` by proving
  `kernel L_A = kernel L_B` on Raw.  This is the GRA template
  (`LensIsoCapstone`) reused on a *cross-domain* pair rather than within GRA.
- **Stage 2 — unification-via-COMPILE-DOWN.**  For two domains `A`, `B` each with
  a distinguishing structure, instantiate `universalMorphism_unique` to get the
  unique `Raw → A` and `Raw → B`, then state the genuine comparison: any
  structure map `A → B` commuting with both is forced (uniqueness), so "A unifies
  with B" = "their COMPILE-DOWN maps share a kernel". This replaces the deleted
  `master` with a real factorisation theorem.
- **Stage 3 — a transport lemma.**  Demonstrate the payoff: a theorem proven in
  `A` transported to `B` *through* the `LensIso`/morphism (e.g. an invariant
  preserved). A unification with no transported theorem is decoration.
- **Stage 4 — replace the catalog.**  `catalogs/cross-domain-identifications.md`
  must list only entries backed by a proven map (or be explicitly labelled
  "value coincidence — candidate, no map yet"). No bare numeric equality presented
  as a unification.

**Honest scope.**  Do NOT restore any `: True` headline or call a value
coincidence a unification. A unification claim is licensed *only* when a
structure-preserving map (or `LensIso`) is proven; absent that, it is a candidate
to be flagged as such. The COMPILE-DOWN/`LensIso` machinery is genuine and `∅`-axiom,
but a *cross-domain* instance must still be built and proven — none of the
existing `LensIso` capstones is itself the cross-domain master.

**Cross-references.**
- `lean/E213/Lens/Unified.lean` (`LensIso`, `lensIso_iff_kernel_eq`)
- `lean/E213/Lib/Math/Algebra/GRA/LensIsoCapstone.lean` (genuine within-GRA template)
- `lean/E213/Lens/ProofISA.lean` (COMPILE-DOWN = `universalMorphism_unique`)
- `lean/E213/Lens/Foundations/NoExteriorClosure.lean` (initiality / no-exterior framing)
- `seed/PROOF_ISA.md` (the instruction set, COMPILE-DOWN row)
