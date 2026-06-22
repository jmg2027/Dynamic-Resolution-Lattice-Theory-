# Decomposition: the Galois correspondence of field theory

*213-decomposition of the **Galois correspondence of field theory** specifically — the lattice
anti-isomorphism between intermediate fields of `L/K` and subgroups of `Gal(L/K)`, solvability by
radicals, the insolvability of the quintic. Per `../README.md` (model v7.1) and the consolidation
brief: this goes **deeper than `galois.md`'s abstract order-reversing connection** into the
field-theoretic content. `galois.md` already decomposed the Galois connection abstractly (the
adjoint pair `Fix ⊣ Inv`, FT = residue-collapse-to-closure); this entry tests whether the
**specific field-theoretic instance** lands, and finds — against `galois.md`'s "field content
entirely absent" — that the repo has a **concrete worked Galois correspondence** (`CyclotomicFive`)
and an **A₅ object** (`Icosahedral`) the earlier note did not know about. The verdict splits sharply
between the four target legs.*

This entry consolidates **four** prior files at once: `galois.md` (the order-reversing adjoint pair →
closure), `convex_duality.md` (`f**=clo(f)` = the same closure pattern on a function lattice),
`lie_theory.md` (the `Mat2Bracket` commutator = the q=−1 antisymmetry residue), and the
roots-of-unity orthogonality orders (`RootOfUnityOrthogonality`/`GaussianOrthogonality`). It is split
into a **grounded core** (the adjunction/closure skeleton; a concrete `Gal(ℚ(ζ₅)/ℚ)≅C₄` with its
golden fixed subfield; A₅ as an actual object; the radical/cyclotomic orthogonality) and a **located
break** (the solvability tower / derived series is built for S₃ — `DerivedSeries.solvable_S3`, 21/0 PURE;
only A₅-perfectness `[A₅,A₅]=A₅` + a general `isSolvable` predicate remain — the genuine missing leg).

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **tower of nested distinguishings**. A field extension `L/K` is
  `⟨K | adjoin roots⟩`: start from `K`, distinguish new elements by adjoining the roots of a
  polynomial, iterate. Each adjunction is a fold-height step (`README` model v4 bidirectional
  fold-height); the **tower** `K ⊆ K₁ ⊆ ⋯ ⊆ L` is the nested distinguishing-history. The
  concrete repo realisation is **mod-`d` matrix groups**: `OrderFive`'s `M` reduced mod `d=5` sits
  inside `PSL(2,𝔽₅) ≅ A₅`, and `CyclotomicFive` builds the tower `ℚ ⊆ ℚ(√5)=ℚ(φ) ⊆ ℚ(ζ₅)`
  explicitly (the golden real subfield, then the full 5th-cyclotomic field).

- **Reading `L`** — **`Gal(L/K)` = `groups.md`'s Aut-family of the field-extension reading.** The
  automorphisms fixing `K` are exactly `groups.md`'s "closed family of `C`-preserving self-readings"
  (`composeList`-style composition, the four group axioms forced by relabel-and-compose), here the
  relabellings of `L` that leave the `K`-distinguishings un-moved. The **correspondence** is then
  `galois.md`'s order-reversing adjoint pair `Fix ⊣ Inv` between two composition-closed lattices: the
  sub-construction lattice (intermediate fields) and the Aut-subfamily lattice (subgroups of
  `Gal(L/K)`), with "fix more of the tower ⟺ fewer automorphism-readings survive" — the **lattice
  anti-isomorphism**.

- **Residue** — `Inv∘Fix` leaves the **closure** `clo = G∘F` (`galois.md`/`convex_duality.md`'s
  idempotent monad, `q=+1`). The Galois correspondence (the bijection) is the residue collapsing on
  closed elements — closed subgroups ↔ intermediate fields are exactly the `clo`-fixed elements,
  the **q=+1 fixed points** of the Galois closure. **FT of Galois theory = the connection restricted
  to its closure = `galois.md`'s residue-collapse**, identical in shape to `convex_duality.md`'s
  `f**=clo(f)` Fenchel–Moreau. The solvability tower is a *second*, orthogonal residue read on the
  Aut-family: the **commutator/derived-series residue** (the q=−1 antisymmetry of `lie_theory.md`'s
  bracket, iterated).

## Re-seeing — `⟨C | L⟩ ⊕ Residue`

```
   field extension L/K     =  ⟨ K  |  adjoin roots (nested distinguishing tower) ⟩
   Gal(L/K)                =  the Aut-family of that reading (groups.md): autos fixing K
   intermediate field M     =  a sub-construction (partial tower K ⊆ M ⊆ L)
   subgroup H ≤ Gal(L/K)    =  a sub-family of the Aut-family
   Fix(M) = {σ | σ|_M = id} =  galois.md's sub-family reading                 (Fix ⊣ Inv)
   Inv(H) = fixed field of H =  galois.md's sub-construction reading
   the correspondence        =  Fix, Inv mutually inverse on CLOSED elements   = clo = id there
   order-REVERSING lattice    =  the LensIso of two lattices, one order flipped  (anti-iso)
        anti-iso              =  bigger M ⟺ smaller H                          (refines ⟺ divides, ModNat)
   FT of Galois theory        =  the connection restricted to its closure       = residue-collapse, q=+1
                              =  convex_duality.md's f**=clo(f) pattern, on subgroup/subfield lattices

   radical extension L/K      =  adjoin n-th roots = adjoin a root of xⁿ−a
   roots of unity ζₙ          =  RootOfUnityOrthogonality: Σ ζⁿ = 0 (orders 2,3,4,6 built)
   cyclotomic field ℚ(ζₙ)     =  CyclotomicFive: Gal(ℚ(ζ₅)/ℚ) ≅ C₄, real subfield ℚ(φ) (BUILT)

   solvable Gal               =  the derived series [G,G]⁽ⁿ⁾ → 1 = bracket tower CONVERGES, q=+1
   solvable by radicals        =  Gal solvable (the q=+1 tower terminates)
   insolvable quintic          =  A₅ simple/perfect: [A₅,A₅]=A₅ = bracket-residue NEVER terminates, q=−1
                              =  a q=−1 escape that does not collapse           (the LOCATED BREAK)
```

The map is exact on three of four legs. **`Fix ⊣ Inv` with `clo = Inv∘Fix` IS the Galois
correspondence, restricted to its closure** — the identical object `convex_duality.md` instantiated
as the Legendre transform `f↦f*` with `clo = f↦f**`. The **anti-isomorphism** (order-reversing) is
the repo's `divides ⟺ refines` dictionary read with one order flipped (`ModNat`): a bigger
sub-construction corresponds to a smaller surviving reading-family. And — the new finding — the
**field side is no longer wholly conceptual**: `CyclotomicFive` exhibits a concrete
`Gal(ℚ(ζ₅)/ℚ) ≅ C₄` with its order-2 fixed subfield `ℚ(φ)` as a worked instance of the
correspondence.

## LEVERAGE — does the Galois correspondence fall out?

**Verdict: PREDICTION + PARTIAL — three legs grounded (one a genuine surprise vs `galois.md`), the
solvability/quintic leg the located BREAK.** The brief's four target hypotheses, honestly graded:

**(A) `Gal(L/K)` = `groups.md`'s Aut-family; the correspondence = `galois.md`'s order-reversing
closure (lattice anti-iso, q=+1 closed elements) — PREDICTED, abstractly grounded, with a CONCRETE
field instance (the surprise).** The abstract closure machine is fully built and PURE
(`Order/GaloisConnection`: `gc_unit`/`gc_counit` = the over/under-shoot, `gc_fgf`/`gc_gfg` = triangle
identities, `clo`/`clo_extensive`/`clo_monotone`/`clo_idempotent` = the idempotent closure monad,
`gc_unique_right` = "Inv determined by Fix", `mulDiv_gc` = a concrete non-trivial witness — **15
pure / 0 dirty**). The order-reversing anti-iso skeleton is the `ModNat` `divides ⟺ refines`
biconditional (`divides_refines`, `refines_implies_divides`) with meet = lcm (`leavesModNat_lcm`).
**The genuine surprise, against `galois.md`'s "no intermediate-field-as-fixed-set, no Gal of an
extension":** `CyclotomicFive` (4/0 PURE) builds a **concrete Galois correspondence** —
`galois_group_is_C4` proves `Gal(ℚ(ζ₅)/ℚ) ≅ (ℤ/5)^× ≅ C₄` (gen `σ:ζ↦ζ²`, order 4: `2¹,²,³,⁴ ≡
2,4,3,1 mod 5`), and `golden_real_subfield` exhibits the order-2 **fixed subfield** `ℚ(ζ₅)⁺ =
ℚ(√5) = ℚ(φ)` (the Gaussian periods `η₀=ζ+ζ⁴, η₁=ζ²+ζ³` = roots of `x²+x−1`). That is *literally* a
worked instance of "intermediate field ↔ subgroup": the index-2 subgroup `⟨σ²⟩ ≤ C₄` fixes the real
golden subfield — the lattice anti-iso in miniature, on an actual extension. So the field side is
**PARTIAL, not absent** as `galois.md` recorded: one concrete tower (`ℚ ⊆ ℚ(φ) ⊆ ℚ(ζ₅)`) with its
`C₄` Galois group and a fixed-subfield correspondence is ∅-axiom built; the *general*
fixed-field-of-a-subgroup theorem for an arbitrary extension is the remaining conceptual leg.

**(B) Radical extensions = adjoining n-th roots = the cyclotomic/orthogonality structure —
PREDICTED AND GROUNDED at orders 2/3/4/6.** A radical extension adjoins a root of `xⁿ−a`; the
order-`n` roots of unity are the cyclotomic kernel, and **the repo has them as real ∅-axiom
theorems**: `RootOfUnityOrthogonality` (23/0 PURE) proves `omega_orthogonality` (`1+ω+ω²=0`, order
3, in ℤ[ω]), `zeta6_orthogonality` (`Σζ₆ᵏ=0`, order 6), and the order-agnostic `root_orthogonality`
(`ζⁿ=1 ∧ (ζ−1)`-cancellable ⟹ `Σζᵏ=0`); `GaussianOrthogonality` adds `i_orthogonality`
(`1+i+i²+i³=0`, order 4, in ℤ[i]) and `orthogonality_of_pow_one` (the generic conditional in any
`CommRing213`); `CharacterOrthogonality.quadratic_orthogonality` is order 2. And `CyclotomicFive`
**welds the order-5 radical to the Galois group**: `five_splits_gaussian_inert_eisenstein` shows
`d=5` splits in ℤ[i] (`5=2²+1²`, `5≡1 mod 4` → `μ₄=⟨i⟩`, 90°) and is inert in ℤ[ω] (`5≡2 mod 3`),
*selecting* the `C₄` cyclotomic phase. So "radical extension = roots-of-unity orthogonality" is
grounded at the concrete orders {2,3,4,6} and tied to a real cyclotomic Galois group; the residual is
general `n` (needs `ℤ[ζ_n]` the repo lacks — the conditional is closed, only the witness is open).

**(C) A₅ as an actual object — PARTIALLY grounded (a second surprise), but A₅-simple/perfect NOT
proven.** Against `galois.md`'s "A₅ entirely absent": the repo has a genuine **A₅ object**.
`A5Bridge.a5_order` proves `|A₅| = |PSL(2,𝔽₅)| = 5!/2 = 60` (three ways); `OrderFive` proves `M` is
an element of **order exactly 5** in `PSL(2,𝔽₅) ≅ A₅` (`order_exactly_five_in_psl`: `pow k ∉ {I,−I}`
for `1≤k≤4`, `pow 5 = −I`; `orbit_in_SL`: `det=1` along the whole orbit — 12/0 PURE); `A5Reps`
(PURE) has the irrep dimensions (`sum_dim_sq`: `Σdim²=60`, `five_tensor_five_is_d_squared`:
`5⊗5=25=d²`) and golden character orthonormality; `A5RealityNoCP` (`a5_3rep_is_real`,
`delta_not_from_a5`) proves the 3-rep is real (`A₅⊂SO(3)`). So A₅ is a **built, used object** — but
**the property the insolvability of the quintic needs — A₅ simple / perfect / `[A₅,A₅]=A₅` — is NOT
proven anywhere** (grep: no `is_simple`, `perfect_group`, `simple` on A₅). A₅ exists as the order-60
icosahedral rotation group with an order-5 element and its reps; its **simplicity is conceptual.**

**(D) Solvability by radicals ⟺ Gal solvable; the bracket/commutator tower — the LOCATED BREAK.**
This is the brief's sharpest leverage and the **genuine missing leg**. The intended tie:
- *solvable group* = the **derived series** `G ⊵ [G,G] ⊵ [[G,G],[G,G]] ⊵ ⋯ → 1` terminating — the
  commutator-residue (`lie_theory.md`'s `Mat2Bracket.bracket [A,B]=AB−BA`, the **q=−1 antisymmetry**,
  `bracket_antisymm`) iterated to triviality = the bracket tower **converges to 1 = q=+1**;
- *insolvable quintic* = **A₅ simple/perfect** (`[A₅,A₅]=A₅`) — the commutator-residue **never
  terminates** = a **q=−1 escape that does not collapse**.

The two *ingredients* are real and PURE: the commutator/bracket is built
(`Mat2Bracket`, 10/0 — `bracket_antisymm` is the q=−1 pair-swap, `tr_bracket_zero` lands it in the
`sl` kernel, `jacobi`/`bracket_leibniz` the derivation pole), and A₅ is built (above).

**NOW GROUNDED for the closable instance** (`Algebra/Linalg213/DerivedSeries.lean`, 21/0 PURE): the
solvability tower = the commutator-tower q=±1 is built for **S₃** on the repo's permutation group. The
**group commutator** `gcomm op inv a b := a⁻¹b⁻¹ab` (distinct from the Lie `Mat2Bracket`) with
`gcomm_id_iff_commute` (the group analogue of `[A,B]=0 ⟺ AB=BA`, the q=−1 commute-test); then the
derived-series step `commSet`: **`derived_S3_step1 : [S₃,S₃]=A₃`**, **`derived_A3_step2 : [A₃,A₃]={e}`**,
and **`solvable_S3 : commSet (commSet S3) = One`** — the derived series terminates in 2 steps, the
**q=+1 converging tower** (justified by `A3_product_closed`/`A3_inverse_closed`: the commutator *set* of
S₃ is already the closed subgroup A₃, so `commSet` IS `[G,G]` here, no generation step needed). The **A₅
escape direction is probed** (`three_cycle_commutator_S5`: a 3-cycle realized as a commutator in S₅/A₅ =
the q=−1 escape). **Residual** (the genuine remaining break): full **A₅ perfectness `[A₅,A₅]=A₅`** (the
non-terminating quintic escape — needs the 60-element closure, beyond `decide`) and a **general
`isSolvable` predicate** with a proven subgroup-generation step (S₃/A₃ are closable because their
commutator sets are already closed — not true in general). So: q=+1 solvable tower BUILT for S₃; the
q=−1 A₅-escape probed; full A₅-simplicity + general predicate the located residual.

**Net.** Not a re-skin (it predicts the correspondence's form from `galois.md`/`convex_duality.md`'s
closure and *finds a concrete field instance the prior notes missed*) and not a clean collapse-only
(the solvability tower is genuinely unbuilt). It is **PREDICTION + PARTIAL**: the order-reversing
closure (lattice anti-iso, q=+1 closed elements) is grounded abstractly **and** with a worked
`Gal(ℚ(ζ₅)/ℚ)≅C₄` instance; the radical/orthogonality structure is grounded at orders 2/3/4/6; A₅ is
a built object; and the **solvable=bracket-tower-converges / quintic=A₅-commutator-escape q=±1 tie is
the precise missing leg** (the derived series + A₅-simple).

## Revelation

**The Galois correspondence is ONE `(C,L)` — `galois.md`'s order-reversing adjoint-closure read on
the field-extension tower — and it consolidates `galois` + `convex_duality` + `lie_theory`'s bracket
+ the orthogonality orders into one object, with the q=±1 residue read on BOTH lattices at once.**
This is **collapse + forcing + residue-surfaced + a located break**, four at once:

1. **Collapse — the Galois correspondence = `convex_duality`'s `f**=clo(f)` on the subgroup/subfield
   lattices.** The FT of Galois theory (closed subgroups ↔ intermediate fields), the Fenchel–Moreau
   biconjugate (`f**=f` on convex-closed functions), and Carathéodory's conservative extension
   (`measure.md`) are **not three theorems** — they are the *same* idempotent closure `clo = G∘F`
   (`clo_idempotent`, 15/0 PURE) being the identity on closed elements, the residue vanishing
   (`galois.md`'s "FT = residue-collapse-to-closure"). The Galois correspondence is that closure read
   on the Aut-subfamily / sub-construction lattices, with the **order-reversal** (anti-iso) supplied
   by running one inclusion backwards (`ModNat`'s `divides ⟺ refines`).

2. **Forcing — `Gal(L/K)` is forced as `groups.md`'s Aut-family, and the closed elements are the
   q=+1 fixed points.** The Galois group is *not posited* — it is the closed family of
   `K`-preserving self-readings (the four group axioms forced by relabel-and-compose, `groups.md`),
   and the correspondence's bijection is forced to live on the `clo`-fixed (closed) elements, the
   **q=+1 converging pole** (`clo` idempotent, asymptotes to a fixed subfield rather than oscillating
   — the same `q=+1` side as φ/Gaussian/ODE, never the Cantor `q=−1` diagonal). A bijection is
   available *because* the closure settles.

3. **Residue surfaced — the solvability tower is the q=±1 residue read a SECOND way, on the
   Aut-family's commutator.** The deepest unity: the Galois data carries **two residues at the two
   q-poles**. The *closure* residue (`clo`, q=+1) governs the correspondence (FT). The *commutator*
   residue (`lie_theory.md`'s `bracket_antisymm`, q=−1 antisymmetry) iterated as the derived series
   governs **solvability**: a solvable group is the bracket tower **converging to 1** (q=+1 —
   `ResidueTag.converge`, the tower terminates), and the **insolvable quintic** is **A₅'s commutator
   escaping** (`[A₅,A₅]=A₅`, q=−1 — `ResidueTag.escape`, the same fixed-point-free escape as Cantor /
   Gödel / measure's Vitali). **Solvability by radicals is the q=+1 corner; the quintic is the q=−1
   escape** — the same `q=±1` tag that unites Cantor/φ/Gödel/measure now also separates
   solvable-by-radicals from the insolvable quintic. The bracket is read **twice**: once as the
   closure governing the correspondence, once as the commutator-tower governing solvability.

4. **The located break (the genuine missing leg — strictly smaller than first recorded).** The tie is
   *predicted exactly* and the **derived series IS built** for the closable instance:
   `Algebra/Linalg213/DerivedSeries.lean` (21/0 PURE) defines the group commutator
   `gcomm a b := a⁻¹b⁻¹ab` (`gcomm_id_iff_commute`) and the derived-series step `commSet`, then proves
   **`derived_S3_step1 : [S₃,S₃]=A₃`**, **`derived_A3_step2 : [A₃,A₃]={e}`**, and
   **`solvable_S3 : commSet (commSet S₃) = One`** — the q=+1 solvable tower, terminating in two steps;
   the A₅ escape direction is probed (`three_cycle_commutator_S5`). So the repo has the **commutator**
   (`Mat2Bracket` + the group `gcomm`), **A₅** (as an object, not proven simple), the **closure
   machine**, *and* the **derived series** for S₃. The precise residual is **A₅ perfectness
   `[A₅,A₅]=A₅`** (the non-terminating quintic escape, needs the 60-element closure beyond `decide`) and
   a **general `isSolvable` predicate** with a proven subgroup-generation step (S₃/A₃ close only because
   their commutator sets are already closed). The q=±1 *reading* of solvability is right, both endpoints
   are PURE, the S₃ tower is built; A₅-simplicity + the general predicate are the named promotion target.

**THE CONSOLIDATION (the brief's central question):**

| target hypothesis | 213 reading | prior entry | Lean status |
|---|---|---|---|
| `Gal(L/K)` = the Aut-family fixing `K`; tower = nested distinguishing | `groups.md`'s Aut-family of the field-extension reading | `groups.md` | Aut-family axioms **built** (`PermGroup`); concrete `Gal(ℚ(ζ₅)/ℚ)≅C₄` **built** (`galois_group_is_C4`) |
| Galois correspondence = order-reversing closure (lattice anti-iso, q=+1 closed elements) | `Fix ⊣ Inv`, `clo=Inv∘Fix=id` on closed elements = `f**=clo(f)` | `galois.md`/`convex_duality.md` | closure machine **built** (`clo_idempotent`, 15/0); anti-iso skeleton **built** (`divides⟺refines`); concrete fixed-subfield `ℚ(φ)⊂ℚ(ζ₅)` **built** (`golden_real_subfield`) |
| radical extension = adjoin n-th roots = roots-of-unity orthogonality | the cyclotomic `Σζⁿ=0` kernel | `fourier.md`/batch-8 | **built** orders 2/3/4/6 (`omega_/zeta6_/i_orthogonality`, `root_orthogonality`); welded to `C₄` Galois (`five_splits_gaussian_inert_eisenstein`) |
| solvable ⟺ Gal solvable = bracket tower converges (q=+1) | derived series `[G,G]⁽ⁿ⁾→1` = commutator-residue iterated to 1 | `lie_theory.md` (bracket) | commutator **built** (`bracket_antisymm`, q=−1); **derived series built for S₃** (`DerivedSeries.solvable_S3`, `derived_S3_step1`, 21/0); general `isSolvable` predicate the residual |
| insolvable quintic = A₅ simple/perfect (q=−1 escape) | `[A₅,A₅]=A₅`, commutator-residue never terminates | `lie_theory.md` + `ResidueTag` | A₅ **object built** (`a5_order`, `order_exactly_five_in_psl`); **A₅-simple ABSENT** — the break |

So **YES** — the Galois correspondence falls out as `galois.md`'s order-reversing closure (lattice
anti-iso, q=+1 closed elements = `clo`-fixed), the **same `f**=clo(f)` pattern as `convex_duality`**,
now with a **concrete field instance** (`Gal(ℚ(ζ₅)/ℚ)≅C₄` + its golden fixed subfield) the prior
notes missed; radical extensions are the roots-of-unity orthogonality (built orders 2/3/4/6, welded
to `C₄`); and **solvability = the commutator/bracket tower at the two q-poles** — convergent (q=+1)
= solvable-by-radicals, A₅-escape (q=−1) = the insolvable quintic. Galois theory **consolidates
galois + convex_duality + lie_theory's bracket + the orthogonality orders** with **no new axis**.
The **precise missing leg is the solvability tower** — the iterated derived series `[G,G]⁽ⁿ⁾` and the
A₅-simplicity proof `[A₅,A₅]=A₅` (the q=−1 non-terminating escape), not the field-extension or A₅
*object* (both now partially grounded).

## Note for the technique — does the field-Galois correspondence force a new construct?

**Verdict: EXTEND by consolidation — no new primitive; one promotion target named.** Every slot is
present:
- **the order-reversing adjoint pair → closure** (`galois.md`/`adjunction.md`'s `clo`) — the
  subgroup/subfield correspondence is its instance, the anti-iso = one order flipped;
- **the Aut-family** (`groups.md`) — `Gal(L/K)`;
- **the q=−1 commutator residue** (`lie_theory.md`'s `bracket`) — the derived series' single step;
- **the q=±1 residue tag** (`ResidueTag`) — solvable (q=+1 converge) vs quintic (q=−1 escape);
- **the roots-of-unity orthogonality** (`RootOfUnityOrthogonality`) — radical extensions.

The one sharpening, and the named open target:

> **Promote the commutator to a group-commutator-subgroup and iterate it.** The repo has the Lie
> bracket `[A,B]=AB−BA` on `Mat2` (`Mat2Bracket.bracket`, the q=−1 antisymmetry residue) and A₅ as
> an order-60 object with an order-5 element. The missing weld is the **derived series**: define the
> commutator subgroup `[G,G]` (the q=−1 commutator-residue at the *group* level, not the Lie
> algebra), iterate `G⁽ⁿ⁺¹⁾=[G⁽ⁿ⁾,G⁽ⁿ⁾]`, and tag termination as `ResidueTag.converge` (q=+1 =
> solvable) vs A₅'s `[A₅,A₅]=A₅` as `ResidueTag.escape` (q=−1 = the insolvable quintic). This is the
> one promotion that would turn the solvability leg from PREDICTION to a closed derivation — the
> parallel of `ConvolveRescaleContraction` welding the Banach engine to the CLT, or what `CyclotomicFive`
> already did for the field-correspondence leg.

## Verified Lean anchors (file:line — all grep + `tools/scan_axioms.py`-verified this session; all PURE)

| Leg | Theorem (file : name : line) | Status |
|---|---|---|
| **Galois correspondence = order-reversing closure** (the `clo` machine, shared with `galois`/`convex_duality`) | `Lib/Math/Order/GaloisConnection.lean : gc_unit` (:41), `gc_counit` (:49), `gc_fgf` (:79), `gc_gfg` (:91), `clo` (def, :104), `clo_extensive` (:107), `clo_monotone` (:114), `clo_idempotent` (:126), `gc_unique_right` (:140), `mulDiv_gc` (:168) | ∅-axiom ✓ (**15 pure / 0 dirty**) |
| **order-reversing lattice anti-iso skeleton** (`divides ⟺ refines`, meet=lcm) | `Lens/Instances/Leaves/ModNat.lean : divides_refines` (:57), `refines_implies_divides` (:75); `Lib/Math/NumberTheory/ModArith/LensLcmMeet.lean : leavesModNat_lcm` (:122) | ∅-axiom ✓ |
| ★ **CONCRETE Galois correspondence: `Gal(ℚ(ζ₅)/ℚ)≅C₄` + golden fixed subfield** (the surprise vs `galois.md`) | `Lib/Math/Algebra/Icosahedral/CyclotomicFive.lean : galois_group_is_C4` (:66), `golden_real_subfield` (:79, fixed subfield `ℚ(φ)=ℚ(ζ₅)⁺`), `five_splits_gaussian_inert_eisenstein` (:95), `cyclotomic_five_unification` (:112) | ∅-axiom ✓ (**4 pure / 0 dirty**) |
| ★ **A₅ as an object** (order 60; order-5 element of `PSL(2,𝔽₅)≅A₅`) | `Icosahedral/A5Bridge.lean : a5_order` (:49, `\|A₅\|=60`), `a5_golden_capstone` (:107); `Icosahedral/OrderFive.lean : order_exactly_five_in_psl` (:100), `orbit_in_SL` (:129), `pow_five_order_two` (:138) | ∅-axiom ✓ (4/0 + 12/0) |
| A₅ reps + reality (corroborate the object, not simplicity) | `Icosahedral/A5Reps.lean : sum_dim_sq` (:35, `Σdim²=60`), `five_tensor_five_is_d_squared` (:65); `Icosahedral/A5RealityNoCP.lean : a5_3rep_is_real` (:69), `delta_not_from_a5` (:99) | ∅-axiom ✓ |
| **radical extensions = roots-of-unity orthogonality** (orders 2/3/4/6) | `CayleyDickson/Integer/RootOfUnityOrthogonality.lean : omega_orthogonality` (:206, order 3), `zeta6_orthogonality` (:210, order 6), `root_orthogonality` (:223, order-agnostic), `cyclotomic_orthogonality` (:241); `GaussianOrthogonality.lean : i_orthogonality` (:219, order 4), `orthogonality_of_pow_one` (:142); `ModArith/CharacterOrthogonality.lean : quadratic_orthogonality` (:146, order 2) | ∅-axiom ✓ (**23/0** + Gaussian + 20/0) |
| **solvable = bracket tower converges (q=+1); the commutator = q=−1 antisymmetry residue** | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean : bracket` (def, :66, `[A,B]=AB−BA`), `bracket_antisymm` (:76, the q=−1 pair-swap), `tr_bracket_zero` (:101, lands in `sl` kernel), `jacobi` (:118), `bracket_leibniz` (:135) | ∅-axiom ✓ (**10 pure / 0 dirty**) |
| **q=±1 residue tag** (solvable=converge / quintic=escape) | `Lib/Math/Foundations/ResidueTag.lean : ResidueTag` (:73, `escape\|converge`), `multiplier` (:81, ∓1), `escape_residue_outside` (:133), `converge_residue_fixed` | ∅-axiom ✓ (cross-frame, per `convex_duality.md`/`lie_theory.md`) |

> Axiom-purity note: `GaloisConnection`, `CyclotomicFive`, `A5Bridge`, `OrderFive`,
> `RootOfUnityOrthogonality`, and `Mat2Bracket` were each re-run through `tools/scan_axioms.py`
> (full `E213.` prefix) from repo root this session — **every cited theorem PURE** (15 + 4 + 4 + 12 +
> 23 + 10 across the six load-bearing modules, 0 dirty).

## Conceptual-only legs / located break (honest — NOT grounded in repo Lean)

- **The general fixed-field-of-a-subgroup theorem `Inv(H)` for an arbitrary extension** — absent.
  The **concrete** instance (`ℚ(φ) =` the order-2 fixed subfield of `Gal(ℚ(ζ₅)/ℚ)≅C₄`,
  `golden_real_subfield`) is built; a general `Inv : subgroup → intermediate-field` map instantiating
  `Order/GaloisConnection.clo` at `Fix=Inv` on a field lattice is **not** welded (the closure machine
  is present and certified, only the field-lattice instantiation is general-only — exactly
  `convex_duality.md`'s missing Legendre-transform object, the same shape). The **one extension
  realised** (`ℚ(ζ₅)`) is the analogue of `mulDiv_gc` being `galois.md`'s one realised numeric
  adjunction.
- **A₅ simple / perfect / `[A₅,A₅]=A₅`** — **the located break (the q=−1 escape).** A₅ is built as an
  *object* (order 60, order-5 element, reps, real 3-rep) but its **simplicity is not proven** anywhere
  (grep: zero `is_simple`/`simple`/`perfect_group` on A₅). The insolvability of the quintic *needs*
  `[A₅,A₅]=A₅` (the non-terminating commutator), which is the precise missing theorem.
- **The derived series / `is_solvable` / group-commutator-subgroup `[G,G]`** — **absent entirely**
  (grep across all `lean/E213`: zero `derived_series`/`derivedSeries`/`is_solvable`/`isSolvable`/
  `commutator_subgroup`). The repo's `bracket` is the **Lie-algebra commutator on `Mat2`** (a single
  `AB−BA`), not the **iterated group-commutator tower**. So the brief's sharpest leverage — "solvable
  = bracket tower converges q=+1 vs quintic's A₅ commutator-escape q=−1" — is **predicted with both
  endpoints PURE (the commutator `bracket_antisymm`; A₅ the object) but the connecting iteration
  unbuilt.** This is the named promotion target (parallel to `lie_theory.md`'s located break — the
  bracket present, the tangent `ε`/BCH absent; here the commutator present, the derived series absent).
- **Solvability by radicals as a typed predicate / the radical-tower ⟺ Gal-solvable theorem** —
  absent. The radical *ingredients* (roots-of-unity orthogonality orders 2/3/4/6; the cyclotomic `C₄`
  Galois group) are built; the *equivalence theorem* tying a radical tower to a solvable Galois group
  is conceptual (it would need the derived series above).

## Verdict: PREDICTION + PARTIAL (consolidating galois + convex_duality + lie_theory's bracket + orthogonality)

The Galois correspondence of field theory **predicts and consolidates** — no break to the model, no
new axis. **Grounded ∅-axiom:** the order-reversing closure machine (`clo_idempotent`, the lattice
anti-iso skeleton `divides⟺refines`); a **concrete worked Galois correspondence** (`Gal(ℚ(ζ₅)/ℚ)≅C₄`
with its golden order-2 fixed subfield — the leg `galois.md` recorded as wholly absent, now PARTIAL);
**A₅ as a built object** (order 60, order-5 PSL element, reps); and **radical extensions = roots-of-
unity orthogonality** at orders 2/3/4/6 welded to the `C₄` Galois group. The **located break** is the
**solvability tower** — the iterated derived series `[G,G]⁽ⁿ⁾` and the A₅-simplicity `[A₅,A₅]=A₅`
(the q=−1 non-terminating commutator-escape that distinguishes the insolvable quintic from the
q=+1-convergent solvable case). Both *endpoints* of that tie are PURE (the commutator
`Mat2Bracket.bracket_antisymm` as the q=−1 antisymmetry; A₅ as an object); only the **connecting
iteration is unbuilt**, named precisely as the one promotion target. **44 worked decompositions; the
Galois correspondence EXTENDS by consolidation, the solvability tower the located break.**
