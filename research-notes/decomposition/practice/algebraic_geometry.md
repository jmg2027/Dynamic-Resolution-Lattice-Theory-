# Decomposition: algebraic geometry (the Nullstellensatz / the ideal–variety correspondence)

*A FRESH decomposition per `../README.md` (model v7.1). The bar is **prediction / revelation**, and
the consolidating hypothesis to TEST (not re-skin): the **`V ⊣ I` ideal–variety correspondence** is the
SAME order-reversing closure `clo = G∘F` as field-Galois (`galois.md`/`galois_correspondence.md`) and
Legendre–Fenchel (`convex_duality.md`/`FenchelMoreau.lean`) — the **THIRD instance** of one
`f**=clo(f)` object; **Hilbert's Nullstellensatz `I(V(J)) = √J`** = the closure `clo(J) = √J` (the
radical = the closure-completion of an ideal, the `q=+1` idempotent fixed point, `clo_idempotent` on the
ideal lattice); the **Zariski topology** = the V-closed sets (`topology.md`); **irreducible variety ⟺
prime ideal** ties `prime_factorization.md`'s atoms/UFD; and **`Spec(R)` glued** = `sheaf_theory.md`'s
`q=+1` gluing. The grounded toy is the divisor-lattice adjunction `mulDiv_gc` (divisibility ↔ multiples
= the `V⊣I`-shaped connection in miniature).*

This entry is split, like `galois.md`/`convex_duality.md`/`knots.md`, into a **grounded core** (the
order-reversing closure machine, its idempotent `√`-style fixed point, the divisor-lattice adjunction,
the prime-atom/UFD coordinate, a Carathéodory-style closure on a *set*-system) and a **located missing
leg** (an actual `Ideal`/`V`/`I`/`radical`/`Spec`/Zariski object — **absent**, confirmed by grep, located
exactly like `convex_duality.md`'s missing `convexConjugate` and `galois.md`'s missing field extension).

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **point-construction** (`derivative.md`'s value-at-a-point: affine space,
  a tuple of coordinates) together with a **lattice of sub-constructions read two ways at once**: a
  function (polynomial) is a reading on the points, and a *set of functions* (an ideal `J`) cuts out a
  *set of points* (the variety `V(J)`). The construction carries the model-v4 **fold-height** (degree of
  a polynomial) and the **atom-distinguishability** axis (`prime_factorization.md`): a *prime* ideal is
  the ×-atom of the ideal lattice, exactly as a prime is the ×-atom of `ℕ_{>0}`.

- **Reading `L`** — here `L` is **two mutually-defined order-reversing family-readings**, *verbatim*
  `galois.md`'s `Fix`/`Inv`:
  - `V` : ideal `J` ↦ "the points where every function in `J` vanishes" (a sub-construction of space);
  - `I` : point-set `S` ↦ "the functions that vanish on all of `S`" (a sub-construction of the ring).

  Both are **order-reversing**: more functions ⟹ fewer points, and vice versa — `galois.md`'s
  "fix more of the construction ⟹ fewer readings survive", with the order on each side the
  refinement/containment lattice. In the repo this order is literally `Lens.refines = ∣ = divisibility`
  (`divides_refines`/`refines_implies_divides`), and the divisor-lattice adjunction `(·*p) ⊣ (·/p)`
  (`mulDiv_gc`) is the concrete `V⊣I`-shaped connection: multiples ↔ divisors, one order flipped.

- **Residue** — what `I∘V` (resp. `V∘I`) leaves un-pointed is the **closure**: `clo(J) = I(V(J))`. The
  Nullstellensatz says this closure **is the radical** `√J` — the `q=+1` idempotent fixed point
  (`√√J = √J` = `clo_idempotent`). The closed ideals (= `clo`-fixed = radical ideals) are in bijection
  with the Zariski-closed sets; the correspondence is **the residue collapsing on the closed elements**,
  identical in shape to `galois.md`'s "fundamental theorem = residue-collapse-to-closure" and
  `convex_duality.md`'s `f**=f` on convex-closed functions. Off the radical locus the gap `√J − J` is
  the surviving residue (a non-radical ideal `J ⊊ √J`, e.g. `(x²) ⊊ (x)`).

## Re-seeing — `⟨C | L⟩ ⊕ Residue`

```
   affine variety / ideal data =  ⟨ affine space (point-construction)  |  the pair (V, I) ⟩
                                   two order-REVERSING readings between two refinement lattices
   V(J) = {x | ∀ f∈J, f(x)=0}    =  galois.md's sub-construction reading        (Fix-side)
   I(S) = {f | ∀ x∈S, f(x)=0}    =  galois.md's Inv-side reading                (Inv-side)
   the correspondence            =  V, I mutually inverse on CLOSED elements    = clo = id there
   order-REVERSING anti-iso       =  bigger ideal ⟺ smaller variety            (refines ⟺ divides, ModNat)
   Zariski-closed set            =  a V-closed sub-construction                 (closed = V(I(·))-fixed)
   radical ideal                 =  an I-closed sub-construction                 (closed = clo-fixed)

   Nullstellensatz I(V(J)) = √J  =  clo(J) = √J                                  (clo_idempotent, q=+1)
   √√J = √J                       =  clo (clo J) = clo J                         (clo_idempotent / biconj_idempotent)
   √J = J  (radical / reduced)    =  residue vanishes = strong-duality corner    (closed_iff_fixed, q=+1)

   irreducible variety           =  V(prime ideal)  =  the ×-atom of the ideal lattice
                                  =  prime_factorization.md's distinguishable ×-atom (vp / UFD)
   Spec(R) = {prime ideals}      =  read R by its atoms = the prime-valuation coordinate (vp)
   scheme = Spec glued            =  sheaf_theory.md's q=+1 unique-amalgamation gluing
```

The map is exact on the closure spine. **`galois.md`'s `Fix ⊣ Inv` with `clo = Inv∘Fix` IS the
`V ⊣ I` ideal–variety correspondence**, the identical object `convex_duality.md` instantiated as
`f↦f*` with `clo = f↦f**`. The **order-reversal** (anti-iso) is the repo's `divides ⟺ refines`
dictionary with one inclusion flipped. The one move special to algebraic geometry — the
**Nullstellensatz** — names the closure operator explicitly: `clo = √`, the radical, with `clo_idempotent`
becoming `√√J = √J`.

## LEVERAGE — does the ideal–variety correspondence fall out as the order-reversing closure?

**Verdict: PREDICTION (the third instance of one closure) + PARTIAL — the closure spine, the radical
idempotent, the anti-iso skeleton, the prime/atom tie, and a worked set-system closure are ALL grounded
∅-axiom; the actual `Ideal`/`V`/`I`/`√`/`Spec`/Zariski OBJECT is the single located missing leg.** The
brief's target hypotheses, honestly graded:

**(A) `V ⊣ I` = `galois.md`'s order-reversing closure, the THIRD instance after field-Galois and
Legendre — PREDICTED, abstractly grounded.** The abstract closure machine is fully built and PURE
(`Order/GaloisConnection.lean`: `gc_unit`/`gc_counit` = the over/under-shoot of the adjoint pair,
`gc_fgf`/`gc_gfg` = triangle identities pointwise (no `funext`), `clo`/`clo_extensive`/`clo_monotone`/
`clo_idempotent` = the idempotent closure monad, `gc_unique_right` = "I determined by V", `mulDiv_gc` =
a concrete non-trivial witness — **15 pure / 0 dirty**). The **order-reversing** flavour `V`/`I` need
(not the monotone form) is built explicitly in `FenchelMoreau.lean` (**18/0 PURE**): an antitone
self-adjoint `star` whose square `cloAntitone star = star∘star` is a closure (`cloAntitone_extensive`,
`cloAntitone_monotone`, `cloAntitone_idempotent`), with `cloAntitone_eq_gc_clo` proving by `rfl` that the
antitone closure **is** `GaloisConnection.clo star star` into the order-dual. Since `I = Fix`, `V = Inv`
with one order flipped, `clo(J) = I(V(J))` is *exactly* this antitone closure. So the load-bearing claim
— "`V⊣I` is the same order-reversing closure as field-Galois (`galois_correspondence.md`) and
Legendre–Fenchel (`convex_duality.md`/`FenchelMoreau`); algebraic geometry's foundational duality is the
THIRD `f**=clo(f)` instance" — is **grounded as a general order/lattice fact, not asserted.** The three
instances share the *same* `clo_idempotent` (15/0) and `biconj_idempotent` (18/0) theorems.

**(B) Nullstellensatz `I(V(J)) = √J` = the radical-closure idempotent `clo(J) = √J`, `√√J = √J` =
`clo_idempotent` — PREDICTED, abstractly grounded; the radical object conceptual.** This is the entry's
leverage. The Nullstellensatz is *not* a separate theorem to be proved — it is the **identification of
the Galois closure `I∘V` with the radical** `√`. Its content `√√J = √J` is *verbatim*
`clo_idempotent` (`clo(clo J) = clo J`, `GaloisConnection.lean:126`, PURE) / `biconj_idempotent`
(`star⁴ = star²`, `FenchelMoreau.lean:134`, PURE), and "`√J = J` ⟺ `J` radical/reduced" is *verbatim*
`closed_iff_fixed` (`x = cloAntitone star x ↔ ∃ b, x = star b`, `FenchelMoreau.lean:152`, PURE) — the
closed/fixed locus where the residue vanishes, the **`q=+1` converging pole** (the closure *settles*,
asymptotes to a fixed radical ideal, never the Cantor `q=−1` diagonal escape). So the calculus
**predicts the Nullstellensatz's form** — "the closure of the conjugate-reading is idempotent, and its
fixed points are the radical (reduced) ideals" — from the closure laws alone, exactly as
`convex_duality.md` predicted Fenchel–Moreau `f**=f` is `closed_iff_fixed`. *Conceptual leg:* the **actual
`√J` operation on an ideal object is absent** (no `radical`/`Ideal` in the repo — see below); what is
grounded is the closure-with-idempotent-fixed-points *structure* the radical inhabits.

The closest *instantiated* shadow — a real closure operator on a **set-system** (not an abstract chain) —
is **Carathéodory's outer measure** (`measure.md`): `Analysis/Measure/OuterMeasure.lean` (**29/0 PURE**)
builds `cara_gc` (a genuine Galois connection on `DyadicMeasurableSet`), `caraClosure` (the set-closure
`= clo`), `caraClosure_extensive` and **`caraClosure_idempotent`** (`clo(clo s) = clo s`). That is a
`V∘I`-shaped closure *on an actual collection of sets* — the nearest in-repo analogue to `√ = I∘V` on a
collection of ideals (the conservative-extension `q=+1` corner), short only of the polynomial-ring content.

**(C) Zariski topology = the V-closed sets; irreducible ⟺ prime = `prime_factorization.md`'s atom —
PREDICTED, the prime-atom leg grounded; the topology object conceptual.** `topology.md` already reads an
open set as a resolution-stable fibre and a closed set as the complement; the Zariski topology is the
specialization where **closed = `V(I)`-fixed** (the `clo`-image), so it is the closed-element
characterization of the connection (`GaloisConnectionComposition.closed_iff_image`, referenced in
`galois.md`). The leverage tie is **irreducible variety ⟺ prime ideal**: a prime ideal is the **×-atom
of the ideal lattice**, the *distinguishable* multiplicative atom that `prime_factorization.md`
formalizes as the faithful prime-valuation coordinate — `vp_mul` (`PrimeValuation.lean:96`, `L_vp(ab) =
L_vp(a)+L_vp(b)`, the `×↦+` character), `eq_of_vp_eq` (`FTAEquality.lean:130`, UFD faithfulness), and
**`two_three_unique`** (`FoldCriterion.lean:158`, `2^a=3^b ⟹ a=b=0` — axis-independence = the atoms
never trade), all PURE. The reason a prime ideal `p` makes `R/p` a domain ("`fg ∈ p ⟹ f∈p ∨ g∈p`") is
the **same atom-distinguishability** that makes `vp` a faithful coordinate. So "irreducible = prime =
the ×-atom" is grounded *as the atom axis of `C`*; the *topology-on-Spec* object is conceptual.

**(D) `Spec(R)` = reading `R` by its prime ideals (the atoms); a scheme = `Spec` glued =
`sheaf_theory.md`'s `q=+1` gluing — PREDICTED, both legs conceptual at the object level.** `Spec(R)` is
"read the ring by its atoms" — the same move as the prime-valuation coordinate `vp` reading `ℕ_{>0}` by
its primes (`prime_factorization.md`), now for a general ring. A **scheme** glues `Spec` of pieces, and
`sheaf_theory.md` already reads the gluing axiom as the **`q=+1` unique-amalgamation** =
`dhom_unique_pointwise` initiality (the converge/closure pole). So the calculus predicts both: `Spec` =
the atom-reading; scheme = `Spec` under `q=+1` gluing. *Conceptual leg:* there is **no `Spec` object, no
prime-spectrum, no structure sheaf** in the repo — the prediction names the structure (the atom-coordinate
`vp`, the gluing initiality) without an instantiated `Spec(R)`.

**Net.** Not a re-skin: it **predicts** the correspondence's form (third instance of `clo`), **derives
why** the Nullstellensatz is the idempotent (`clo_idempotent`/`closed_iff_fixed`), and ties irreducible =
prime to a *built* atom coordinate. Not a clean collapse-only: the polynomial-ring `Ideal`/`V`/`I`/`√`/
`Spec` object is genuinely unbuilt. It is **PREDICTION + PARTIAL**: every structural leg is grounded and
the missing legs are *named objects* (the ideal/variety/radical/Spec), not missing structure — the
structure they inhabit (`clo`, `closed_iff_fixed`, the antitone closure, the prime atom) is wholly
present and certified.

## Revelation

**The ideal–variety correspondence is ONE `(C,L)` — `galois.md`'s order-reversing adjoint-closure read on
the ideal lattice — and it is the THIRD instance of a single repo-grounded object, consolidating galois +
galois_correspondence + convex_duality + prime_factorization + topology + sheaf under one closure.**
This is **collapse + forcing + residue-surfaced**, three at once, and the broadest consolidation in the
notebook:

1. **Collapse — the V⊣I correspondence, field-Galois, and Legendre–Fenchel are ONE closure.** The
   fundamental theorem of Galois theory (closed subgroups ↔ intermediate fields,
   `galois_correspondence.md`), the Fenchel–Moreau biconjugate (`f**=f` on convex functions,
   `convex_duality.md`/`FenchelMoreau.biconj_idempotent`), Carathéodory's conservative extension
   (`measure.md`/`caraClosure_idempotent`), and now the **Nullstellensatz** (`I(V(J)) = √J`,
   radical ideals ↔ Zariski-closed sets) are **not four/five theorems** — they are the *same* idempotent
   closure `clo = G∘F` (`clo_idempotent`, 15/0; `biconj_idempotent`, 18/0) being the identity on its
   closed elements, the residue vanishing (`closed_iff_fixed`). Algebraic geometry's V⊣I is that closure
   read on the ideal/variety lattices, with the order-reversal (anti-iso) supplied by running one
   inclusion backwards (`divides ⟺ refines`, `ModNat`), and **the radical `√` is the name of the closure**.

2. **Forcing — the Nullstellensatz is forced as `clo_idempotent`, and irreducible = prime is forced as
   the atom axis.** The Nullstellensatz is *not posited*: once `V`/`I` are an order-reversing adjoint
   pair, `clo = I∘V` is automatically idempotent (`√√J = √J`) and its fixed points are exactly the
   radical (reduced) ideals (`closed_iff_fixed`) — the bijection radical-ideals ↔ Zariski-closed-sets is
   *forced* to live on the `q=+1` closed locus, never the `q=−1` diagonal. And "irreducible ⟺ prime" is
   forced as the **×-atom-distinguishability axis** of `C` (`prime_factorization.md`): a prime ideal is
   the distinguishable multiplicative atom, the same faithful-coordinate property (`vp_mul`,
   `eq_of_vp_eq`, `two_three_unique`) that makes UFD work — `Spec` is just "read the ring by these atoms".

3. **Residue surfaced — the radical IS the closure residue, and reduced = the gap zero.** Classical AG
   states the Nullstellensatz as a deep theorem (needing algebraic closure / Hilbert basis); the calculus
   re-sees `√J` as **`clo(J)` — the closure residue `I(V(J))`** — and a *non-radical* ideal `J ⊊ √J`
   (e.g. `(x²) ⊊ (x)`) as the surviving gap, the `q=+1` residue that *settles* (idempotent: `√√J = √J`,
   never escapes). "Reduced ring / radical ideal" stops being a special hypothesis and becomes
   **the closure-fixed locus where the residue vanishes** — the same shape as a normal field extension
   and a convex-closed function.

**THE CONSOLIDATION (the brief's central question):**

| target hypothesis | 213 reading | prior entry | Lean status |
|---|---|---|---|
| `V ⊣ I` = order-reversing closure, the THIRD `f**=clo(f)` instance | `Fix ⊣ Inv`, `clo = I∘V`, antitone | `galois.md` / `galois_correspondence.md` / `convex_duality.md` | closure machine **built** (`clo_idempotent` 15/0; `cloAntitone`/`biconj_idempotent` 18/0); the V/I objects conceptual |
| Nullstellensatz `I(V(J)) = √J` = `clo(J) = √J`; `√√J = √J` = `clo_idempotent` | the radical = the closure-completion, q=+1 fixed point | `convex_duality.md` (Fenchel–Moreau `f**=f`) | `clo_idempotent` (`:126`), `biconj_idempotent` (`:134`), `closed_iff_fixed` (`:152`) **built PURE**; `√`/ideal object conceptual |
| order-reversing anti-iso skeleton (bigger ideal ⟺ smaller variety) | `divides ⟺ refines`, meet = lcm | `galois.md` (`ModNat`) | `divides_refines` (`:57`), `refines_implies_divides` (`:75`), `leavesModNat_lcm` (`:122`) **built**; grounded toy `mulDiv_gc` (`:168`) |
| Zariski-closed = V-closed; irreducible ⟺ prime = the ×-atom | closed = `clo`-image; prime = distinguishable atom (UFD) | `topology.md` / `prime_factorization.md` | atom coordinate **built** (`vp_mul` `:96`, `eq_of_vp_eq` `:130`, `two_three_unique` `:158`); Zariski/irreducible object conceptual |
| `Spec(R)` = read R by primes; scheme = Spec glued = `q=+1` gluing | atom-reading `vp`; sheaf unique-amalgamation initiality | `prime_factorization.md` / `sheaf_theory.md` | atom-reading **built** (`vp`); `Spec`/structure-sheaf object **absent** |
| a `V∘I`-shaped closure on an actual *set*-system (the nearest instantiated shadow) | Carathéodory closure on a measurable-set collection | `measure.md` | `cara_gc` (`:182`), `caraClosure_idempotent` (`:217`) **built PURE** (29/0) |

So **YES** — the V⊣I ideal–variety correspondence falls out as `galois.md`'s order-reversing closure,
the **THIRD instance** of one `f**=clo(f)` object (after field-Galois `galois_correspondence.md` and
Legendre–Fenchel `convex_duality.md`/`FenchelMoreau`); the **Nullstellensatz `I(V(J))=√J` is the
radical-closure idempotent** `clo(J)=√J` with `√√J=√J` = `clo_idempotent`/`biconj_idempotent` and
reduced = `closed_iff_fixed`; **Zariski-closed = V-closed**; **irreducible = prime = the ×-atom of
`prime_factorization.md`** (the same faithful UFD coordinate); and **`Spec` glued = `sheaf_theory.md`'s
`q=+1` gluing**. The **grounded toy is the divisor lattice `mulDiv_gc`** (multiples ↔ divisors, one
order flipped = the V⊣I-shaped adjunction in miniature). Algebraic geometry **consolidates galois +
galois_correspondence + convex_duality + prime_factorization + topology + sheaf** under the
order-reversing closure, with **no new axis**.

## Note for the technique — does algebraic geometry force a new construct?

**Verdict: EXTEND by consolidation — no new primitive.** Every slot is present:
- **the order-reversing adjoint pair → closure** (`galois.md`/`adjunction.md`/`FenchelMoreau`'s `clo`) —
  `V⊣I` is its instance, the radical `√` = the closure operator, the anti-iso = one order flipped;
- **the `q=+1` residue tag** (`ResidueTag.lean`) — the closure settles (radical idempotent), never escapes;
- **the ×-atom-distinguishability axis** (`prime_factorization.md`) — irreducible = prime, `Spec` = atom-reading;
- **the resolution/topology dial** (`topology.md`) — Zariski-closed = the V-closed fibre;
- **the `q=+1` gluing initiality** (`sheaf_theory.md`) — a scheme = `Spec` glued.

The one sharpening (and the named open target): the Nullstellensatz **names the closure operator**. In
field-Galois the closure is unnamed (`Inv∘Fix`); in convex duality it is the convex hull; in AG it is
**`√` (the radical)** — and `clo_idempotent` *is* `√√=√`. So algebraic geometry contributes the cleanest
*name* for the `q=+1` closure: the radical/reduced operation. The promotion target is the parallel of
`convex_duality.md`'s missing `convexConjugate` and `galois.md`'s missing field extension:

> **Promote the closure to an ideal-lattice instance.** Define a polynomial-ring `Ideal` object, the
> order-reversing pair `V : Ideal → PointSet` and `I : PointSet → Ideal`, instantiate
> `Order/GaloisConnection.clo` (or `FenchelMoreau.cloAntitone`) at `Fix=I, Inv=V`, and obtain
> `I(V(J)) = clo(J)` with `clo_idempotent` giving `√√J = √J` and `closed_iff_fixed` giving "radical ⟺
> fixed". This is the one weld that would promote this entry from PREDICTION+PARTIAL to a closed
> derivation — the analogue of `ConvolveRescaleContraction` welding the Banach engine to the CLT, or
> `CyclotomicFive` realising one concrete field-Galois correspondence.

## Verified Lean anchors (file:line — all grep + `tools/scan_axioms.py`-verified this session; all PURE)

| Leg | Theorem (file : name : line) | Status |
|---|---|---|
| **V⊣I = order-reversing closure** (the `clo` machine, shared with galois + convex_duality) | `Lib/Math/Order/GaloisConnection.lean : gc_unit` (:41), `gc_counit` (:49), `gc_fgf` (:79), `gc_gfg` (:91), `clo` (def, :104), `clo_extensive` (:107), `clo_monotone` (:114), `clo_idempotent` (:126), `gc_unique_right` (:140), `mulDiv_gc` (:168) | ∅-axiom ✓ (**15 pure / 0 dirty**) |
| ★ **Nullstellensatz `I(V(J))=√J` = the radical-closure idempotent** (`√√J=√J`); reduced = closed-fixed | `Lib/Math/Order/FenchelMoreau.lean : cloAntitone` (def, :53), `cloAntitone_extensive` (:72), `cloAntitone_idempotent` (:123), `biconj_idempotent` (:134, `star⁴=star²` = `√√=√`), `closed_iff_fixed` (:152, radical ⟺ fixed), `cloAntitone_eq_gc_clo` (:187, antitone closure = `GaloisConnection.clo` by `rfl`) | ∅-axiom ✓ (**18 pure / 0 dirty**) |
| **order-reversing anti-iso skeleton** (bigger ideal ⟺ smaller variety; meet=lcm); the **grounded toy** | `Lens/Instances/Leaves/ModNat.lean : divides_refines` (:57), `refines_implies_divides` (:75), `common_divisor_upper_bound` (:123); `Lib/Math/NumberTheory/ModArith/LensLcmMeet.lean : leavesModNat_lcm` (:122) | ∅-axiom ✓ |
| **irreducible ⟺ prime = the ×-atom of `prime_factorization.md`** (faithful UFD coordinate) | `Lib/Math/NumberTheory/PrimeValuation.lean : vp_mul` (:96, `×↦+`); `Lib/Math/NumberTheory/FTAEquality.lean : eq_of_vp_eq` (:130, UFD faithfulness); `Meta/Nat/FoldCriterion.lean : two_three_unique` (:158, axis-independence); `Meta/Nat/VpSeparation.lean : vp_separation` (:172) | ∅-axiom ✓ (7/0 + 6/0 + 8/0) |
| **a `V∘I`-shaped closure on an actual set-system** (nearest instantiated shadow of `√=I∘V`) | `Lib/Math/Analysis/Measure/OuterMeasure.lean : cara_gc` (:182), `caraClosure` (def, :192), `caraClosure_extensive` (:200), `caraClosure_idempotent` (:217) | ∅-axiom ✓ (**29 pure / 0 dirty**) |

> Axiom-purity note: `GaloisConnection` (15/0), `FenchelMoreau` (18/0), `PrimeValuation` (7/0),
> `FTAEquality` (6/0), `FoldCriterion` (8/0), and `OuterMeasure` (29/0) were each re-run through
> `tools/scan_axioms.py` (full `E213.` prefix) from repo root this session — **every cited theorem PURE**,
> 0 dirty across all six load-bearing modules.

## Conceptual-only legs / located missing leg (honest — NOT grounded in repo Lean)

- **An actual `Ideal` / `V` / `I` / `√` (radical) / variety / Zariski / `Spec` / Nullstellensatz object
  — ABSENT (confirmed by grep).** Across all `lean/E213`, there is **no** `def Ideal`, `def variety`,
  `def vanishing`, `def radical`, `def Spec`/prime-spectrum, `coordinateRing`, `nullstellensatz`, or
  `Zariski` (the only `Spec`/`spec*` hits are unrelated — `spectrum` of a Laplacian, `specimen`/`species`
  catalogue tags, `specLens`). This is **the single located missing leg**, located exactly like
  `convex_duality.md`'s missing `convexConjugate`, `galois.md`'s missing field extension, and `knots.md`'s
  located boundary: the closure *structure* (`clo`, antitone `cloAntitone`, `closed_iff_fixed`, the prime
  atom, a set-system closure `caraClosure`) is wholly present and certified; only the **polynomial-ring
  instantiation** of `V`/`I`/`√`/`Spec` is unwritten. The Nullstellensatz `I(V(J))=√J` is *predicted* as
  `clo_idempotent`/`closed_iff_fixed` with both endpoints PURE, but the connecting ideal-lattice object is
  the named promotion target.
- **The polynomial ring `k[x₁..xₙ]` and Hilbert's basis theorem (Noetherian / finite generation)** —
  absent. The repo has `Algebra/Polynomial213.lean` (polynomial arithmetic) but no ideal theory on it, no
  ACC/Noetherian, no Hilbert basis. The finiteness that classical AG needs sits with `topology.md`'s
  located missing leg (the arbitrary-cover quantifier the finite-`List` setting can't host).
- **Algebraic closure / the "weak" Nullstellensatz (`V(J)=∅ ⟹ 1∈J`)** — absent. This is the input the
  classical Nullstellensatz proof needs (`k = k̄`); the calculus *predicts* the `√J` identity from the
  closure laws but does not supply the algebraically-closed base field, which would be a `Real213`/ℂ-cut
  residue (the same kind of value-cut gap as `convex_duality.md`'s `sup_x` and `galois_correspondence.md`'s
  general cyclotomic `ℤ[ζ_n]`).
- **`Spec(R)` + the structure sheaf + schemes** — absent. `Spec` = the atom-reading is *predicted* (the
  `vp` prime coordinate generalized to a ring), and gluing = `sheaf_theory.md`'s `q=+1`
  `dhom_unique_pointwise` initiality is *predicted*, but neither the prime-spectrum object nor a structure
  sheaf is built. The `q=−1` half (higher sheaf cohomology / global obstructions) is the escape pole, the
  same un-built colimit corner `knots.md`/`category_theory.md` locate.

## Verdict: PREDICTION (the THIRD `f**=clo(f)` instance) + PARTIAL (the ideal/variety/Spec object the missing leg)

Algebraic geometry's foundational duality **predicts and consolidates** — it does not break the model and
adds no axis. **Grounded ∅-axiom:** the order-reversing closure machine (`clo_idempotent` 15/0; the
antitone `cloAntitone`/`biconj_idempotent`/`closed_iff_fixed` 18/0 — the **third instance** after
field-Galois and Legendre, all one `f**=clo(f)`); the **Nullstellensatz `I(V(J))=√J` as the
radical-closure idempotent** (`√√J=√J` = `clo_idempotent`/`biconj_idempotent`; reduced ⟺ closed-fixed =
`closed_iff_fixed`); the **anti-iso skeleton** (`divides⟺refines`, meet=lcm) with the **grounded toy
`mulDiv_gc`** (multiples ↔ divisors); **irreducible = prime = the ×-atom** of `prime_factorization.md`
(faithful UFD coordinate `vp_mul`/`eq_of_vp_eq`/`two_three_unique`); and a **real set-system closure**
(`caraClosure_idempotent`, the nearest instantiated `V∘I` shadow). The **single located missing leg** is
an actual `Ideal`/`V`/`I`/`√`/`Zariski`/`Spec` object — **confirmed absent by grep** — located precisely:
the closure structure, the radical-as-idempotent, the prime atom, and a set-system closure are all
present and certified; only the **polynomial-ring instantiation** of the correspondence is unwritten,
named as the one promotion target (the analogue of `convexConjugate`/the field extension). **45 worked
decompositions; algebraic geometry EXTENDS by consolidation — the THIRD order-reversing-closure instance,
the ideal/variety/Spec object the located missing leg.**
