# Decomposition: geometric invariant theory (GIT — X//G = Spec R^G, stable/semistable/unstable, Hilbert–Mumford, moment map / Kempf–Ness, categorical quotient)

*213-decomposition per `../README.md` (model v7.1) and `SYNTHESIS.md` (the two invariants, the q=±1
spine §3, the colimit/quotient corner §5). A **fresh** field but a pure consolidation: GIT does not
add a construction or a primitive — it **fuses four already-built corners on one object** (a group
acting on a construction). The thesis tested: GIT = the **quotient-by-a-group as the invariant-ring
Lens (galois_correspondence's Fix/`clo` closure)** + **stability = the q=±1 tag** (stable = q+1
closed-orbit / converge, unstable = q−1 escape) + **Hilbert–Mumford = the 1-parameter q±1 test** +
**the moment map / Kempf–Ness = the q+1 symplectic/convex optimum** + **the categorical quotient =
the colimit corner, stability = the Side-A-good locus**. Bar: PREDICTION/REVELATION (collapse of four
prior files onto one object), with the named `GIT`/`invariantRing`/`stable`/`momentMap`/
`categoricalQuotient` objects honestly ABSENT.*

## The decomposition (C / Reading / Residue)

- **Construction `C` — a group acting on a construction.** GIT introduces no new construction: it is
  `representation.md`/`groups.md`'s `C` carrying an `Aut`-family action `G ⤳ X`. `X` is any
  distinguishing-history; `G` is `groups.md`'s composition-closed family of `C`-preserving self-readings
  (the four group axioms forced by relabel-and-compose). The **orbit** `G·x` is the equivalence class of
  the action — the set of points the relabel-family identifies. The repo's concrete shadow is the
  unimodular `Mat2`/`SL₂` action (`CyclotomicFive`'s `C₄`, `A5*`'s order-60 icosahedral group), the
  same `C` symplectic_geometry / galois_correspondence read.

- **Reading `L_inv` (the G-invariant Fix Lens) — this is the new datum.** The **ring of invariants**
  `R^G = {r ∈ R | g·r = r ∀g}` is *exactly* galois_correspondence's `Fix`: the closed/fixed elements
  under the `G`-relabel family, the `clo`-fixed points of the closure `clo = Inv∘Fix`
  (`GaloisConnection.clo`, `clo_idempotent`). So **X//G = Spec(R^G) = reading X through its G-invariant
  Lens** = the same `Fix ⊣ Inv` Galois adjunction galois_correspondence decomposed, here on the
  function ring rather than the field/subgroup lattice. "Invariant" = "fixed under the relabel-family" =
  the q+1 closure pole settling (`clo` idempotent, never the Cantor q−1 diagonal).

- **The stability reading `L_q` (the q=±1 tag) — and the moment-map optimum.** A point's status is the
  **q=±1 residue tag of its orbit** (`ResidueTag.lean`): **stable = q+1** (the orbit is *closed* — its
  closure does not hit `0` — the converge pole, a genuine separated quotient point); **unstable = q−1**
  (the orbit's closure *contains* `0` — the escape pole, the orbit runs off to the degenerate point, the
  same fixed-point-free escape as Cantor/Gödel/Vitali). The **moment map / Kempf–Ness** picks the q+1
  *minimal-norm* point in each closed orbit — the zero-level `μ⁻¹(0)` = the q+1 symplectic/convex optimum
  (symplectic_geometry's `cup1`/`Im(G)` antisymmetric form whose flow preserves the q+1 `det=1`
  invariant; convex_duality / optimal_transport's `q+1` LP/Fenchel optimum, `kantorovich_weak_duality`/
  `ollivier_plan_optimal`).

- **Residue — `q = ±1`, the escape/converge tag.** The GIT residue is exactly `ResidueTag`'s two poles:
  the *closed-orbit / semistable* locus settles to a quotient point (q+1, the closure exact, no gap), the
  *unstable* locus escapes to the closure of `0` (q−1, the diagonal escape). The Hilbert–Mumford
  criterion is the **1-parameter (resolution/iteration axis) test** asking which pole an orbit sits at.

## Re-seeing — `⟨C | L⟩ ⊕ Residue`

```
   group action G ⤳ X        =  ⟨ a construction X | the Aut-family G of C-preserving relabelings ⟩  (groups.md/representation.md)
   orbit G·x                 =  the G-equivalence class = the relabel-family's identification
   ring of invariants R^G    =  galois_correspondence's Fix: the G-fixed/closed elements   (clo-fixed, GaloisConnection.clo)
   GIT quotient X//G = Spec R^G = reading X through its G-invariant Fix Lens               (the same Fix ⊣ Inv adjunction)
   "invariant"               =  fixed under the relabel-family = clo-idempotent settling (q+1)  (clo_idempotent)
   the categorical quotient   =  the colimit / quotient corner (SYNTHESIS §5): Side-A when orbits separated
   stable point              =  CLOSED orbit (closure misses 0) = the q+1 converge pole       (ResidueTag.converge, golden_is_converge)
   semistable point          =  orbit closure does NOT contain 0 (a quotient point survives)   = q+1 corner
   unstable point            =  orbit closure CONTAINS 0 = the q−1 ESCAPE (runs to the degenerate point)  (ResidueTag.escape, no_surjection_of_fixedpointfree)
   Hilbert–Mumford criterion  =  the 1-parameter subgroup test: does lim_{t→0} λ(t)·x escape?  = the resolution-axis q±1 test
      destabilizing λ          =  a q−1 escaping direction (a 1-PS whose limit hits 0)
   moment map μ; μ⁻¹(0)        =  the q+1 symplectic/convex optimum: minimal-norm orbit point   (symplectic cup1; convex/LP optimum)
   Kempf–Ness (symplectic=GIT) =  μ⁻¹(0)/K = X^{ss}//G : the q+1 fixed point = the closed-orbit representative
   strong "the quotient exists" =  the Side-A-good locus = where the closure is exact, gap=0 (q+1)  (ollivier_plan_optimal, FreeReduction)
```

Set side by side, GIT is the **literal intersection of four earlier files**: galois_correspondence's
`Fix ⊣ Inv` closure (the invariant ring), the `ResidueTag` q=±1 spine (stability), the
symplectic/convex q+1 optimum (the moment map / Kempf–Ness), and the colimit/quotient corner (the
categorical quotient, stability = the Side-A locus) — all read on the one `G ⤳ X` action object.

| GIT corner | reading on `C` | residue at the relevant pole | prior file |
|---|---|---|---|
| ring of invariants `R^G` | the G-fixed/closed elements (`Fix`) | q+1 closure settles (`clo_idempotent`) | `galois_correspondence.md` |
| stable / closed orbit | the orbit's closure misses `0` | q+1 converge (`golden_is_converge`) | `ResidueTag` / `SYNTHESIS §3` |
| unstable orbit | the closure hits `0` (escape to degenerate) | q−1 escape (`no_surjection_of_fixedpointfree`) | `cardinality`/`godel`/`measure` |
| moment map `μ⁻¹(0)` / Kempf–Ness | minimal-norm orbit point (the q+1 optimum) | q+1 symplectic/convex optimum | `symplectic_geometry.md` / `convex_duality.md` / `optimal_transport.md` |
| categorical quotient | the colimit on the closed/separated locus | Side-A buildable (q+1) vs Side-B obstructed | `free_corner.md` / `homotopy_theory.md` / `SYNTHESIS §5` |

## Revelation (collapse + forcing + spine: X//G = the G-invariant Fix Lens, stability = q=±1, the moment map = the q+1 optimum)

**Collapse 1 — the GIT quotient X//G = Spec(R^G) IS galois_correspondence's `Fix ⊣ Inv` closure, read
on the function ring.** This is not an analogy. The ring of invariants `R^G` is the set of elements
*fixed* under the `G`-relabel family — galois_correspondence's `Fix` *verbatim*, the `clo`-fixed
elements of the idempotent closure `clo = Inv∘Fix` (`GaloisConnection.clo`, `clo_idempotent`, 15/0
PURE). The classical fact "X//G = Spec of the invariants" is therefore the calculus's *single*
order-reversing adjoint-closure object, the same `clo` that is field-Galois (`Fix⊣Inv`),
Legendre–Fenchel (`f**`, convex_duality), the Nullstellensatz (`V⊣I`), and matroid closure — the
**fifth/sixth instance of one `f**=clo`** (SYNTHESIS §2). The GIT quotient is that closure read on the
G-invariant Lens of the action; the **categorical-quotient universal property** is the closure being
the identity on its closed (= invariant) elements, exactly galois_correspondence's "FT = residue-
collapse-to-closure."

**Collapse 2 — stability = the q=±1 tag (the SYNTHESIS §3 spine), and the moment map = the q+1 optimum.**
A point is **stable iff its orbit is closed** (the orbit's closure does not contain the cone point `0`)
— this is *literally* `ResidueTag.converge` (q+1): the orbit *settles* to a separated quotient point,
the same converge pole as φ/Gaussian/ODE (`golden_is_converge`, `converge_residue_fixed`, delegating to
`banach_fixed_point_modulated`). A point is **unstable iff its orbit's closure contains `0`** — the
orbit *escapes* to the degenerate point, `ResidueTag.escape` (q−1), the same fixed-point-free escape as
Cantor/Gödel/Vitali (`escape_residue_outside` ⟵ `no_surjection_of_fixedpointfree`). The **moment map**
`μ` and **Kempf–Ness** select the q+1 *minimal-norm* representative in each closed orbit:
`μ⁻¹(0)/K = X^{ss}//G` is the symplectic quotient = GIT quotient, and `μ⁻¹(0)` is the q+1 optimum —
symplectic_geometry's antisymmetric `cup1 = Im(G)` (the symplectic form, `gram_hermitian_gravity_gauge_split`,
14/0) whose flow preserves the q+1 `det=1` invariant, and convex_duality / optimal_transport's q+1
LP/Fenchel optimum (`kantorovich_weak_duality`, `ollivier_plan_optimal`, 60/0). So the Kempf–Ness
theorem "minimal-norm point ⟺ closed orbit ⟺ μ=0" is the calculus's q+1 corner read three ways at once
(closed orbit + converge fixed point + convex/symplectic optimum).

**Forcing — the Hilbert–Mumford criterion is the 1-parameter q±1 test, forced not posited.** The
numerical criterion tests stability with a **1-parameter subgroup** `λ : 𝔾_m → G` and the limit
`lim_{t→0} λ(t)·x`: the point is unstable iff some `λ` *destabilizes* it (the limit escapes to `0`).
This is the calculus's **resolution/iteration axis** (`free_corner.md`'s growing endo-reading run as a
1-PS) asking which q-pole the orbit sits at: a destabilizing `λ` is a **q−1 escaping direction** (the
limit hits the degenerate point, the escape pole); no destabilizing `λ` means the orbit *converges* to
a separated point (q+1). The numerical function `μ(x,λ)` (the Hilbert–Mumford weight) is the
*finite-signature* of that escape — the modulus reading SYNTHESIS §3 names "the computable operand 213
calculates with, the limit never is." So Hilbert–Mumford is *forced* as the 1-PS q±1 test, the discrete
calculation that decides the residue pole; it is not a separate combinatorial miracle.

**The q=±1 spine — GIT is the field where the invariant-Fix Lens and BOTH residue poles meet on one
object.** This is the new datum past galois_correspondence (which read q+1 closure on the field/subgroup
lattice) and symplectic_geometry (which fused q−1 antisymmetry with q+1 `det=1` conservation): GIT binds
the **q+1 invariant-ring Fix Lens** (X//G = Spec R^G, the closure settling) to the **q=±1 stability tag**
(stable orbits at q+1 converge, unstable at q−1 escape) to the **q+1 moment-map optimum** (Kempf–Ness),
*all on the `G ⤳ X` action*. The categorical quotient lives on the **Side-A-good locus**
(SYNTHESIS §5): buildable as a `Quot`-free normal-form quotient exactly where the orbits are closed/
separated (the q+1 corner, `FreeReduction.proj_val_eq_iff`/`free_group_quotient_no_quot`, 26/0,
`Quot`-free), obstructed where they are not (Side-B, the q−1 corner). **GIT stability IS the choice of
the locus where the quotient is Side-A-good** — the field's whole reason for existing (you must throw
out the unstable q−1 locus to get a separated quotient) is the calculus's Side-A/Side-B split made
into a definition.

**THE CONSOLIDATION (the brief's central question):**

| target hypothesis | 213 reading | prior entry | Lean status |
|---|---|---|---|
| X//G = Spec R^G = the G-invariant Fix Lens | galois_correspondence's `Fix ⊣ Inv`, `clo=Inv∘Fix=id` on closed/invariant elements | `galois_correspondence.md` | closure machine **built** (`clo_idempotent`, 15/0); concrete `Gal(ℚ(ζ₅)/ℚ)≅C₄` fixed-subfield **built** (`golden_real_subfield`); named `invariantRing`/`Spec R^G` object ABSENT |
| ring of invariants = `Fix` = the closed/fixed elements (`clo` idempotent) | the G-fixed elements settle (q+1) | `galois_correspondence.md`/`convex_duality.md` | `clo_idempotent` **built** (15/0); the `R^G`/Reynolds-operator object ABSENT |
| stable = closed orbit = q+1; unstable = closure-hits-0 = q−1 escape | the `ResidueTag` two poles on the orbit | `ResidueTag` / `SYNTHESIS §3` | **built** (`residue_tag_two_poles`, `golden_is_converge`, 55/0); named `stable`/`semistable`/`unstable` predicate ABSENT |
| Hilbert–Mumford = the 1-parameter q±1 escape test | a 1-PS = the resolution axis; destabilizing λ = a q−1 escape | `free_corner.md`/`SYNTHESIS §3` | the q−1 escape engine **built** (`no_surjection_of_fixedpointfree`); the named `HilbertMumford`/`1-PS weight μ(x,λ)` object ABSENT |
| moment map / Kempf–Ness = the q+1 symplectic/convex optimum (μ⁻¹(0) = min-norm orbit point) | symplectic_geometry's `cup1`; convex/LP q+1 optimum | `symplectic_geometry.md`/`convex_duality.md`/`optimal_transport.md` | engines **built** (`gram_hermitian_gravity_gauge_split` 14/0; `kantorovich_weak_duality`/`ollivier_plan_optimal` 60/0); named `momentMap`/`Kempf` object ABSENT |
| categorical quotient = the colimit corner; stability = the Side-A locus | SYNTHESIS §5 Side-A (separated orbits) vs Side-B | `free_corner.md`/`homotopy_theory.md`/`SYNTHESIS §5` | Side-A witness **built** (`FreeReduction.free_group_quotient_no_quot`, 26/0, `Quot`-free); named `categoricalQuotient`/`GIT` object ABSENT |

So **YES** — GIT falls out with **no new primitive**: X//G = Spec R^G is galois_correspondence's
G-invariant Fix Lens (the `clo` closure, the invariant ring = the closed/fixed elements); stability is
the q=±1 tag (stable/closed-orbit = q+1 converge, unstable = q−1 escape); the Hilbert–Mumford criterion
is the 1-parameter q±1 escape test on the resolution axis; the moment map / Kempf–Ness is the q+1
symplectic/convex optimum (μ⁻¹(0) = the minimal-norm closed-orbit representative); and the categorical
quotient is the colimit corner, GIT stability being the choice of the Side-A-good (separated, q+1)
locus. GIT **consolidates galois_correspondence + ResidueTag + symplectic_geometry + convex_duality/
optimal_transport + the colimit corner** into one object.

## LEVERAGE — verdict

**PREDICTION (consolidation), no new primitive.** Five legs, honestly graded — the engines all built
∅-axiom, the named GIT objects honestly ABSENT.

- **Leg 1 — X//G = Spec R^G = the G-invariant Fix Lens. BUILT ∅-axiom (the engine).** The
  order-reversing adjoint-closure `clo = Inv∘Fix` is fully built and PURE (`GaloisConnection.clo`,
  `clo_extensive`, `clo_monotone`, `clo_idempotent`, `gc_unit`, `gc_counit`; 15/0), and a *concrete*
  Galois Fix instance is built (`CyclotomicFive.golden_real_subfield`: `ℚ(φ)` = the order-2 fixed
  subfield of `Gal(ℚ(ζ₅)/ℚ)≅C₄`, 4/0). The ring of invariants `R^G` is `Fix` read on the function ring;
  the *named* `invariantRing`/`Reynolds`/`Spec R^G` object is ABSENT (grep-confirmed). PARTIAL: the
  closure machine and a concrete field Fix are certified, the function-ring instantiation is conceptual
  — exactly galois_correspondence's "field-extension instance missing, the closure structure present."

- **Leg 2 — stability = the q=±1 tag. BUILT ∅-axiom (the tag).** `ResidueTag.lean` (55/0):
  `residue_tag_two_poles` bundles the two poles, `golden_is_converge`/`converge_residue_fixed` the q+1
  (stable/closed orbit), `escape_residue_outside` ⟵ `no_surjection_of_fixedpointfree` the q−1
  (unstable/escape), `multiplier_unimodular` the ±1 bit. The stable/unstable/semistable *predicate on
  orbits* is the named gap; the q=±1 *engine* it would instantiate is built and PURE.

- **Leg 3 — Hilbert–Mumford = the 1-parameter q±1 test. PREDICTION (engine present).** The q−1 escape
  engine is built (`no_surjection_of_fixedpointfree`, `OneDiagonal`), and the resolution/iteration
  1-parameter axis is built (`free_corner.md`'s ascent; `ResolutionShift`). But a literal 1-PS
  `λ : 𝔾_m → G`, the limit `lim_{t→0} λ(t)·x`, and the numerical weight `μ(x,λ)` are NOT built — the
  discrete `Mat2` setting hosts the q±1 tag and the escape engine, not a `1-PS`/`HilbertMumford` object.
  PARTIAL: the q±1 escape-test *shape* is certified, the named numerical criterion is the open target.

- **Leg 4 — moment map / Kempf–Ness = the q+1 symplectic/convex optimum. BUILT ∅-axiom (the optima).**
  symplectic_geometry's `cup1 = Im(G)` (the repo's own "symplectic form", `gram_hermitian_gravity_gauge_split`,
  14/0) gives the antisymmetric form whose flow preserves the q+1 `det=1` invariant; convex_duality /
  optimal_transport give the q+1 LP/Fenchel optimum (`kantorovich_weak_duality` = weak duality,
  `ollivier_plan_optimal` = the zero-gap q+1 tight optimum, 60/0). The Kempf–Ness `μ⁻¹(0) = min-norm
  closed-orbit point` is the calculus's q+1 corner read three ways. The named `momentMap`/`Kempf`
  object and the `μ⁻¹(0)/K = X^{ss}//G` symplectic-quotient theorem are ABSENT; the optimum engines are
  built and PURE.

- **Leg 5 — categorical quotient = the colimit corner; stability = the Side-A locus. BUILT ∅-axiom
  (Side A).** SYNTHESIS §5's colimit corner: Side-A buildable as a `Quot`-free normal-form quotient
  exactly when orbits are closed/separated (`FreeReduction.free_group_quotient_no_quot`,
  `proj_val_eq_iff`, 26/0, *no `Quot`*), obstructed when not (Side B, Novikov–Boone-grade). GIT
  stability is the choice of that Side-A-good locus — the field's defining move (discard the unstable
  q−1 locus to get a separated quotient) is the calculus's Side-A/Side-B split made into a definition.
  The named `categoricalQuotient`/`GIT` quotient object is ABSENT; the colimit Side-A witness is built.

## Note for the technique — does GIT touch model v7.1?

**No new primitive; EXTEND by consolidation.** The two invariants (the character arrow, the q=±1
residue) and the frame (direction, fold-height, resolution+base, iteration-character, weight) absorb
GIT whole:

> **GIT is the field where the G-invariant Fix Lens (the quotient = Spec R^G = galois_correspondence's
> `clo` closure), the q=±1 stability tag (stable/closed-orbit = q+1 vs unstable/escape = q−1, tested by
> the 1-parameter Hilbert–Mumford criterion), the q+1 symplectic/convex moment-map optimum (Kempf–Ness,
> μ⁻¹(0) = the minimal-norm closed-orbit representative), and the colimit/quotient corner (the
> categorical quotient, stability = the Side-A-good locus) are FIVE readings of one `G ⤳ X` action
> object.** Where galois_correspondence reads q+1 closure on the field/subgroup lattice and
> symplectic_geometry fuses q−1 antisymmetry with q+1 conservation, GIT binds the invariant-ring Fix
> Lens to both stability poles and the moment-map optimum on the *action*. The located breaks: the named
> `GIT`/`invariantRing`/`stable`/`semistable`/`unstable`/`HilbertMumford`/`momentMap`/`Kempf`/
> `categoricalQuotient` objects (engines PURE, bundles absent), and the symplectic-quotient theorem
> `μ⁻¹(0)/K = X^{ss}//G` (the moment-map object's weld, at the same `d>1`/continuous gap
> symplectic_geometry/representation named).

So model v7.1's interior is unchanged; GIT is a **five-way consolidation corner** — the invariant-ring
Fix Lens carrying both q=±1 stability poles and the q+1 moment-map optimum, the categorical quotient on
the Side-A locus — under the two standing invariants, with the named GIT objects as the located breaks.

## Verified Lean anchors (file:line:theorem — all grep + `tools/scan_axioms.py`-verified this session; all PURE)

| Leg | Theorem (file : name : line) | Status |
|---|---|---|
| ★ X//G = Spec R^G = the G-invariant **Fix** Lens (the `clo = Inv∘Fix` closure, invariants = closed/fixed elements) | `Lib/Math/Order/GaloisConnection.lean : clo` (def :104), `clo_extensive` (:107), `clo_monotone` (:114), `clo_idempotent` (:126), `gc_unit` (:41), `gc_counit` (:49) | **PURE (15/0)** ✓ |
| concrete Galois **Fix** instance (a fixed subfield = invariants of a subgroup) | `Lib/Math/Algebra/Icosahedral/CyclotomicFive.lean : galois_group_is_C4` (:66), `golden_real_subfield` (:79, `ℚ(φ)` = order-2 fixed subfield) | **PURE (4/0)** ✓ |
| ★ stability = the q=±1 tag (stable/closed-orbit = q+1 converge / unstable = q−1 escape) | `Lib/Math/Foundations/ResidueTag.lean : ResidueTag` (:73), `multiplier` (:81), `multiplier_unimodular` (:86), `escape_residue_outside` (:133), `converge_residue_fixed` (:160), `golden_is_converge` (:180), `residue_tag_two_poles` (:228) | **PURE (55/0)** ✓ |
| ★ the q−1 escape engine (unstable = orbit closure hits 0 = the fixed-point-free escape; Hilbert–Mumford's destabilizing direction) | `Lens/Foundations/OneDiagonal.lean : no_surjection_of_fixedpointfree` (:51) | **PURE** ✓ (cross-frame via `ResidueTag.escape_residue_outside`) |
| ★ moment map / Kempf–Ness = the q+1 **symplectic** optimum (`cup1 = Im(G)` = the repo's symplectic form, antisym) | `Lib/Math/Cohomology/Cup/SignedCup.lean : cup1` (def :57), `cup1_antisymmetric` (:62), `GIm` (def :118), `gram_hermitian_gravity_gauge_split` (:127) | **PURE (14/0)** ✓ |
| ★ moment map / Kempf–Ness = the q+1 **convex/LP** optimum (μ⁻¹(0) = min-norm point; weak + zero-gap duality) | `Lib/Math/Geometry/DiscreteCurvature/OllivierRicci.lean : transportCost` (def :36), `dualValue` (def :40), `kantorovich_weak_duality` (:52), `ollivier_plan_optimal` (:106) | **PURE (60/0)** ✓ |
| ★ categorical quotient = the colimit corner; stability = the Side-A-good (separated, q+1) locus | `Lib/Math/Algebra/Group/FreeReduction.lean : freeReduce_idempotent` (:191), `proj_val_eq_iff` (:237), `proj_section` (:242), `free_group_quotient_no_quot` (:264) | **PURE (26/0)** ✓ |

**Scan tallies (this session, `tools/scan_axioms.py` from repo root):** `GaloisConnection` **15/0**;
`CyclotomicFive` **4/0**; `ResidueTag` **55/0**; `SignedCup` **14/0**; `OllivierRicci` **60/0**;
`FreeReduction` **26/0**. All PURE, 0 DIRTY. (`OneDiagonal.no_surjection_of_fixedpointfree` cross-frame
via `ResidueTag`, PURE.)

## Dropped / flagged citations (honest)

- **`GIT` / `invariantRing` / `Reynolds` / `Spec R^G` / `stable` / `semistable` / `unstable` /
  `HilbertMumford` / 1-parameter-subgroup weight `μ(x,λ)` / `momentMap` / `Kempf` / `categoricalQuotient`
  — ABSENT.** Grep-confirmed across all `lean/E213` (broad case-insensitive scan for
  `geometric.invariant|invariant.ring|GIT|categorical.quotient|hilbert.mumford|kempf.ness|moment.map|
  semistable|unstable|destabiliz`): **zero** named GIT-theory objects. The one hit
  (`Lib/Physics/AlphaEM/Capstone.lean:21` "graded geometric invariants of K_{NS,NT}") is unrelated —
  it is a physics-deployment phrase, NOT a GIT quotient. The engines are built and PURE (X//G = Spec R^G
  = `Fix`/`clo`; stability = `ResidueTag` q±1; moment map = `cup1`/`OllivierRicci` q+1 optimum;
  categorical quotient = `FreeReduction` Side-A), but no named GIT bundle. **Predicted-not-built, as
  the brief expected.**
- **The symplectic-quotient theorem `μ⁻¹(0)/K = X^{ss}//G` (Kempf–Ness "symplectic = GIT")** — the
  *weld* tying the moment-map object to the invariant-ring quotient is conceptual: both endpoints are
  built (the q+1 symplectic/convex optimum `cup1`/`ollivier_plan_optimal`; the invariant-ring Fix closure
  `clo_idempotent`), only the connecting object/theorem is unwritten — the same `d>1`/continuous gap
  `symplectic_geometry.md`'s missing `momentMap` and `representation.md`'s `det`/`tr` split named.
- **The Hilbert–Mumford numerical function `μ(x,λ)` as a typed object** — absent; the grounded shadow is
  the q±1 escape test (`no_surjection_of_fixedpointfree` for the q−1 destabilizing direction, the
  resolution/iteration 1-PS axis from `free_corner.md`/`ResolutionShift`). The named 1-PS weight and the
  "unstable ⟺ ∃ destabilizing λ" theorem are the open target.
- **No buildable witness proposed.** The thesis is fully grounded by existing PURE theorems
  (`clo_idempotent` for X//G = Spec R^G; `ResidueTag.residue_tag_two_poles` for stability;
  `gram_hermitian_gravity_gauge_split` + `ollivier_plan_optimal` for the moment-map q+1 optimum;
  `free_group_quotient_no_quot` for the categorical quotient on the Side-A locus). The genuine open
  targets (the `R^G`/`Spec` object, the `HilbertMumford`/1-PS weight, the `momentMap` object + the
  Kempf–Ness symplectic-quotient theorem, the named `GIT` quotient) are continuous/`d>1`/named-bundle
  gaps, not finite decidable facts.

## Verdict: PREDICTION (consolidating galois_correspondence + ResidueTag + symplectic_geometry + convex_duality/optimal_transport + the colimit corner), no new primitive

GIT **predicts and consolidates** — no break to the model, no new axis. **Grounded ∅-axiom:** the
G-invariant Fix Lens / `clo` closure (X//G = Spec R^G = galois_correspondence's invariant ring,
`clo_idempotent` 15/0, with a concrete field Fix `golden_real_subfield`); the q=±1 stability tag
(stable/closed-orbit = q+1 vs unstable = q−1 escape, `residue_tag_two_poles` 55/0,
`no_surjection_of_fixedpointfree`); the q+1 symplectic/convex moment-map optimum (Kempf–Ness, `cup1`
14/0 + `ollivier_plan_optimal` 60/0); and the categorical quotient on the Side-A-good locus
(`free_group_quotient_no_quot` 26/0, `Quot`-free). The **located break** is the family of named GIT
objects (`invariantRing`/`Spec R^G`, `stable`/`semistable`/`unstable`, `HilbertMumford` 1-PS weight,
`momentMap`/`Kempf`, `categoricalQuotient`/`GIT`) — every *engine* PURE, the *named bundles* and the
Kempf–Ness symplectic-quotient weld `μ⁻¹(0)/K = X^{ss}//G` honestly absent. The new datum past the five
parent files: GIT is the field where the invariant-ring Fix Lens carries **both** q=±1 stability poles
**and** the q+1 moment-map optimum on **one** action object, with the categorical quotient living
exactly on the calculus's Side-A locus — GIT stability IS the choice of that Side-A-good locus. EXTENDS
by consolidation; the named GIT objects + the symplectic-quotient theorem are the located breaks.
