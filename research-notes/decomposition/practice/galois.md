# Decomposition: the Galois correspondence

*213-decomposition of "the Galois correspondence", per `../README.md` (model v3) and the
sharpened hypothesis: Galois is an **order-reversing iso between two composition-closed
reading-families** — the lattice of sub-constructions (intermediate fields) and the lattice of
Aut-subgroups (the readings fixing them). A `LensIso`-style mirror: "fix more of the construction
⟺ fewer automorphism-readings survive". The fundamental theorem = the two fibre-maps are mutually
inverse, i.e. a **Galois connection = an adjoint pair of readings**.*

This entry is deliberately split into a **grounded core** and a **flagged conceptual leg**: the
*connection / adjoint-pair / order-reversing-iso machinery* is fully in the repo and ∅-axiom; the
*field-theoretic content* (splitting fields, intermediate fields as Aut-subgroup fixed points,
solvability) is **not** — it is conceptual-only here, and said so plainly.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a construction with a distinguishing-history and a **composition-closed
  family of `C`-preserving self-readings** `Aut(C)` (the model-v3 promotion from `groups.md`: the
  reading slot may be a family closed under `∘`). Galois adds *one structure on top*: `C` carries a
  **lattice of sub-constructions** — partial distinguishing-histories, each "fix this much, forget
  the rest". The Galois data is the pair (lattice of sub-constructions, `Aut(C)` and its
  sub-families).

- **Reading `L`** — here `L` is not one projection but **two mutually-defined family-readings**:
  - `Fix` : sub-construction `H` ↦ "the automorphism-readings that leave `H` un-moved"
    (a sub-family of `Aut(C)`);
  - `Inv` : sub-family `G ⊆ Aut(C)` ↦ "the largest sub-construction every reading in `G` fixes".

  Both are **order-reversing**: fix *more* of the construction ⟹ *fewer* readings survive, and vice
  versa. The order on each side is the refinement/containment order — and in the repo that order is
  literally `Lens.refines` = kernel-containment = **divisibility** (see core below).

- **Residue** — what `Inv ∘ Fix` (resp. `Fix ∘ Inv`) leaves is the **closure**: the closed
  sub-constructions and closed sub-families. The Galois *correspondence* (the bijection) is exactly
  the statement that the residue collapses on the closed elements — the closure operator becomes the
  identity. So "the fundamental theorem" = *the adjunction's closure is trivial on the relevant
  lattices*, the residue vanishes there. The general residue (where closure ≠ id) is the
  not-Galois / not-normal case.

## Re-seeing — `⟨C | L⟩`

```
   the Galois data       =  ⟨ C with a sub-construction lattice  |  the pair (Fix, Inv) ⟩
                            two order-REVERSING readings between two composition-closed lattices

   Fix(H)                =  { σ ∈ Aut(C) | σ fixes H }          (sub-family-reading)
   Inv(G)               =  largest H fixed by all of G          (sub-construction-reading)
   the correspondence    =  Fix, Inv are mutually inverse on closed elements
                          =  a Galois CONNECTION  Fix ⊣ Inv  whose closure = id there
   order-reversing iso   =  the LensIso of two reading-lattices, one with the order flipped
```

The adjoint-pair shape is the repo's `GaloisConnection`: `leB (f a) b ↔ leA a (g b)`
(`gc : ∀ a b, ...`), with `gc_unit` (`a ≤ g (f a)`), `gc_counit` (`f (g b) ≤ b`), `gc_monotone_f/g`,
the triangle identities `gc_fgf`/`gc_gfg` (`f∘g∘f = f`, pointwise — no `funext`), the induced
**closure** `clo = g ∘ f` (extensive/monotone/idempotent), and `gc_unique_right` (the right adjoint
is unique). Order-*reversal* is obtained by running one of the two relations backwards — the
machinery is relation-parametric, so a contravariant pair is just `leA`/`leB` with the inclusion
flipped on one side. The "iso" half (closure = id, mutual inverse) is the residue-collapse on closed
elements.

## Revelation — which legs are grounded, which are conceptual

**Grounded (∅-axiom, verified):** *the adjoint-pair / order-reversing-iso skeleton of Galois is a
real, proven object in this repo* — and there is a **concrete Galois-connection-shaped lattice
that IS the correspondence in miniature.** The `leavesModNat` reading-lattice has
`refines = ∣` proven **both ways** (`divides_refines`: `k ∣ m ⟹ L_m ⊑ L_k`; `refines_implies_divides`:
the converse for `k,m ≥ 2`) — so the order on reading-families is *literally the divisibility lattice*,
with meet = lcm (`leavesModNat_lcm`: `L_{lcm(m,k)} ≈ prodLens(L_m,L_k)` as a `LensIso`) and the dual
gcd-lattice (`GcdLcmLattice`). The full adjoint apparatus (unit, counit, both monotonicities,
triangle identities, closure, right-adjoint uniqueness) is `Order/GaloisConnection.lean`, with a
genuine non-trivial witness (`(·*p) ⊣ (·/p)` on `Nat`, `mulDiv_gc`). So **the load-bearing claim —
"Galois = an adjoint pair of mutually-refining reading-lattices, order-reversing, with the
correspondence = residue-collapse-to-closure" — is grounded as a *general order/lattice fact*, not
asserted.** The `divides ⟺ refines` biconditional is exactly an order-reversing dictionary between a
number-lattice and a reading-lattice — the *shape* of the fundamental theorem.

**Conceptual-only (flagged honestly):** *the field-theoretic content of Galois is not in the repo.*
There is **no** splitting-field construction, **no** intermediate-field-as-fixed-set theorem, **no**
"automorphism group of a field extension", **no** solvability-by-radicals. The token `galois` appears
only as an `AutGroup` **enum label** in `Mobius213/Px/SymmetrySpecies.lean` (the `char_poly` species
is tagged `.galois`) — a *catalogue tag*, not a proven group action, exactly the kind of label
`groups.md` already flagged as "not theorem-level". Field extensions exist only as **quadratic rings**
(`Tactic/QuadExtension.lean` is a normalization tactic for `a+b√d`; `GoldenFieldBridge.lean` is ℤ[φ]
arithmetic) — there is no Aut-of-extension / fixed-field machinery on them. So the *specific* Galois
correspondence (intermediate fields ⟷ subgroups for a given extension) is **conceptual here**; what
is grounded is the *abstract correspondence-shape* it is an instance of.

Net Revelation (the honest collapse): **the Galois correspondence is one instance of a single
repo-grounded object — an order-reversing Galois connection between two refinement lattices whose
closed elements are in bijection (residue-collapse).** The repo proves that object abstractly
(`GaloisConnection`: `gc_fgf`/`gc_gfg`/`clo_idempotent`/`gc_unique_right`) *and* exhibits a concrete
number-theoretic instance of "two mutually-refining reading-lattices = a divisibility/lcm lattice
mirrored as a Lens lattice" (`divides_refines` + `refines_implies_divides` + `leavesModNat_lcm`). The
field-theoretic instance is the missing leg; everything it would need *structurally* is present.

## Note for the technique — does Galois force a new construct?

**Verdict: Galois EXTENDS the model — it forces one explicit promotion, and the repo already
contains the construct, so the extension is grounded, not speculative.**

`groups.md` promoted the reading slot to a **composition-closed family** `Aut(C)`. `equivalence.md`
fixed the comparison layer as the **`Lens.refines` kernel preorder**. Galois forces the *next* step:
a reading can be a **pair of order-reversing maps between two such ordered reading-families that form
an adjunction** — a **Galois connection of reading-lattices**. Concretely:

> **Add to the map an adjoint-pair operator between reading-lattices.** Given two
> refinement-ordered reading-families `A` (sub-constructions of `C`) and `B` (sub-families of
> `Aut(C)`), a **Galois connection** is a pair `Fix : A → Bᵒᵖ`, `Inv : Bᵒᵖ → A` with
> `Inv(G) ⊑ H ⟺ G ⊑ Fix(H)` — `Order/GaloisConnection.lean`'s `gc`, with one order reversed. It is
> *forced* (the laws are `gc_unit`/`gc_counit`/`gc_fgf`/`gc_gfg`, pure order-chases), it *pays* (the
> "correspondence" = the closure `clo = Inv∘Fix` being the identity on closed elements,
> `clo_idempotent` + the residue-collapse), and it **subsumes the earlier slots**: a single
> `LensIso` (kernel-equality, `lensIso_iff_kernel_eq`) is the *degenerate* Galois connection where
> `Fix`/`Inv` are mutually inverse *everywhere* (closure already trivial) — i.e. **a `LensIso` is the
> top-of-the-lattice case of a Galois connection**, and a general Galois connection is the proper
> generalization: an *adjoint pair* where the iso holds only after closure.

So the answer to the two pointed questions:

1. **Does Galois force an ADJOINT-PAIR / order-reversing-iso construct between reading-families?**
   *Yes* — and it is the genuine generalization of `equivalence.md`'s `LensIso`. `LensIso` is the
   *symmetric* (mutual-refinement, kernel-equal) special case; Galois needs the *asymmetric* adjoint
   pair `Fix ⊣ Inv` where one direction is `unit` (over-shoot, `a ≤ g(f a)`) and the other is
   `counit` (under-shoot, `f(g b) ≤ b`), reconciled only on the **closure-fixed** (= "closed"
   sub-fields / "closed" subgroups) elements. This is the model's first *non-invertible* reading-pair
   — a real extension, not a re-skin.

2. **Is a "Galois connection" = a pair of mutually-refining reading-lattices?** *Yes, with one
   sharpening*: it is a pair of reading-lattices joined by an **adjunction whose closure operator
   measures the residue**. "Mutually-refining" is right *only on the closed elements* (there the
   closure is `id`, residue vanishes, and you get the order-reversing **iso** = the fundamental
   theorem); off the closed elements the two lattices are *adjoint*, not iso, and the gap is exactly
   `Residue(L,C)` = `clo a` vs `a`. So the calculus gains: **`Residue` of a reading-pair is named by
   its closure operator; the "correspondence/iso" is the locus where that residue is zero.** This
   ties Galois back to the model's residue-first normal form `⟨C | L⟩ ⊕ Residue(L,C)`: Galois is the
   reading-pair whose residue is governed by a closure, and the fundamental theorem is the *vanishing
   of that residue on closed elements*.

A `q = ±1` note (model v3's residue multiplier): the Galois closure here is the **converging /
fixed-point pole** (`q = +1` in the README map) — `clo` is *idempotent* (`clo_idempotent`), it
*asymptotes to a fixed sub-construction* rather than oscillating outside every reading. So Galois
sits on the same `q = +1` side as φ (`golden_ratio.md`), not the Cantor-diagonal `q = −1` side — the
correspondence is a residue that *settles*, which is exactly why a bijection (not a diagonal escape)
is available.

## Verified Lean anchors (all ∅-axiom-style; grep-checked)

The order/adjunction skeleton:
- `Lib/Math/Order/GaloisConnection.lean`:
  - `gc_unit` (`a ≤ g(f a)`), `gc_counit` (`f(g b) ≤ b`) — the over/under-shoot of the adjoint pair
  - `gc_monotone_f`, `gc_monotone_g` (both adjoints monotone)
  - `gc_fgf` (`f∘g∘f = f`), `gc_gfg` (`g∘f∘g = g`) — triangle identities, pointwise (no `funext`)
  - `clo` (def, the closure `g∘f`), `clo_extensive`, `clo_monotone`, `clo_idempotent`
  - `gc_unique_right` (right adjoint unique — the "Inv is determined by Fix" half)
  - `mulDiv_gc` (★ concrete non-trivial witness `(·*p) ⊣ (·/p)` on `Nat`), `mulDiv_unit`,
    `mulDiv_counit`
- `Lib/Math/Order/GaloisConnectionComposition.lean`: `gc_comp`, `closed_iff_image`,
  `gc_idempotent_closure`, `gc_le_closed` (connections compose; closed-element characterization)
- `Lib/Math/Order/KnasterTarski.lean` (fixed-point side of the closure story — present, not load-bearing here)

The concrete "two mutually-refining reading-lattices" = divisibility/CRT lattice (the in-repo
miniature of the correspondence shape):
- `Lens/Instances/Leaves/ModNat.lean`:
  - `divides_refines` (★ `k ∣ m ⟹ L_m.refines L_k` — order one way)
  - `refines_implies_divides` (★ converse for `k,m ≥ 2` — the **biconditional**: `refines ⟺ divides`,
    the order-reversing dictionary number-lattice ⟷ reading-lattice)
  - `common_divisor_upper_bound`, `common_multiple_lower_bound` (the lattice bounds)
- `Lib/Math/NumberTheory/ModArith/LensLcmMeet.lean`:
  - `leavesModNat_lcm` (★ `LensIso (leavesModNat (lcm m k)) (prodLens (leavesModNat m) (leavesModNat k))`
    — the meet IS the lcm; the reading-lattice mirrors the divisibility lattice as a `LensIso`)
  - `lcm_unique`, `leavesModNat_refines_prod_lcm`, `prod_refines_leavesModNat_lcm`
- `Lib/Math/NumberTheory/GcdLcmLattice.lean`: `gcd_lcm_absorb`, `lcm_gcd_absorb`, `lcm_self`,
  `gcd_self_law` (the dual gcd-lattice axioms — the lattice both readings live in)

The reading-iso layer (the degenerate / closed-element case of the connection):
- `Lens/Unified.lean`: `LensIso` (def), `lensIso_refl`, `lensIso_symm`, `lensIso_trans` (groupoid),
  `lensIso_iff_kernel_eq` (iso = kernel coincidence — the symmetric special case of `Fix ⊣ Inv`)
- `Lens/LensCore.lean`: `Lens.refines` (the order = kernel containment), `Lens.refines_refl`,
  `Lens.refines_trans`
- `Lib/Math/Algebra/Linalg213/PermGroup.lean`: `composeList`, `composeList_assoc`,
  `composeList_invPerm_left`, `composeList_iota_left/right` (the `Aut(C)` realisation, from
  `groups.md`)

## Conceptual-only legs (honest — these are NOT grounded in repo Lean)

- **Splitting fields / normal extensions** — absent. No construction of a splitting field, no
  normality predicate. Conceptual.
- **Intermediate fields as Aut-subgroup fixed sets** — absent. There is *no* "fixed field of a
  subgroup" theorem on any field extension in the repo. The fixed-point/closure *machinery* exists
  generically (`clo`, `KnasterTarski`), but it is **not instantiated to a field extension**. The
  field-side of the correspondence is conceptual.
- **`galois` as a real object** — the token is an `AutGroup` **enum label** in
  `Mobius213/Px/SymmetrySpecies.lean` (`char_poly ↦ .galois`), a catalogue tag, **not** a proven
  group action or fixed-field theorem. Flagged exactly as `groups.md` flagged the `AutGroup` enum:
  corroborates the *form*, certifies *nothing*.
- **Field extensions beyond quadratic rings** — `Tactic/QuadExtension.lean` is a normalization tactic
  for `a + b√d`; `GoldenFieldBridge.lean` / `FP2SqrtD.lean` are ℤ[φ] / `𝔽_{p²}` arithmetic. There is
  arithmetic *in* quadratic extensions but no automorphism-group / Galois-group theorem *of* them.
  Conjugation `a+b√d ↦ a−b√d` is the obvious `q=−1` swap-bit reading (cf. `integers.md`'s sign), but
  no theorem packages it as "the order-2 Galois group of the quadratic extension" — so even the
  simplest real Galois group is **conceptual** in this repo.
- **Solvability by radicals / the insolvability of the quintic** — entirely absent. Conceptual.

## Verdict: EXTENDS (with a real, grounded promotion)

Galois **extends** the model and does **not** break it. The new construct it forces — a
**Galois-connection / adjoint-pair of order-reversing reading-lattices, with the correspondence =
residue-collapse-to-closure** — is *already a proven ∅-axiom object* in `Order/GaloisConnection.lean`,
and its number-theoretic shadow (`refines ⟺ divides`, meet = lcm) is proven in `ModNat.lean` +
`LensLcmMeet.lean`. The promotion is: **`LensIso` (symmetric, `equivalence.md`) is the closed/iso
special case of a Galois connection (asymmetric adjoint, residue = closure).** The *field-theoretic
instance* of the correspondence is the one conceptual-only leg — honestly absent — but the structure
it would inhabit is wholly present and certified.
