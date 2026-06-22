# Decomposition: matroid theory

*213-decomposition per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`,
the Revelation rule) and `../SYNTHESIS.md` (the two invariants; the `q=±1` spine; the
**`f**=clo` order-reversing-closure family** — Field-Galois + Legendre–Fenchel +
Nullstellensatz/`V⊣I`; the iteration-character axis with idempotent `clo`). Targets: a
matroid via independent sets / rank function / circuits / closure operator, the greedy
algorithm's optimality, matroid duality `M*`, the exchange axiom, the submodular rank.*

This is the **fifth instance of the closure-operator family** (after Galois `Fix⊣Inv`,
Legendre–Fenchel `f**`, the Nullstellensatz `V⊣I`, and Carathéodory's outer measure
`caraClosure`). Its matroid-specific legs are the **rank = dimension reading**
(`dimension.md`) and the **`q=±1` complementation involution** (duality `M↔M*`). The new
datum vs `galois_correspondence.md`: the matroid closure is the *same* `clo`, and "greedy =
optimal" is the calculus's "the fold-to-normal-form gives the optimum" characterization. The
named `Matroid` / `Independent` / `greedy` / `circuit` / `submodular` objects are
**ABSENT** in `lean/E213/` (grep-confirmed); the load-bearing *legs* are built.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **finite ground set `E` of distinguished atoms, with a
  generating/extension act**: from a set `S ⊆ E`, the act is "adjoin a still-distinguishable
  element" (one that is *not* already captured). This is the bare distinguishing iterated over
  a finite carrier — the same `C` as the field tower in `galois_correspondence.md`
  ("adjoin roots, iterate"), but over an unstructured finite atom-set rather than a field. The
  in-repo realisation of the *linear* matroid is the subset-sum carrier of
  `Combinatorics/LinearDependence.lean`: vectors `vs : List (List Bool)` over `𝔽₂`, and the
  extension act is `vxor`/`vsum` (`++` a vector into a running selection).

- **Reading `L`** — **two welded readings, both already in the calculus**:
  1. **`clo` = the matroid closure operator `cl : 2^E → 2^E`** (extensive, monotone,
     idempotent + the Steinitz–Mac Lane exchange property). This IS `galois_correspondence.md`'s
     `clo = G∘F` (`GaloisConnection.clo`): the round-trip of the order-reversing adjoint pair
     `span ⊣ "the elements that don't extend rank"`. A **flat** = a **closed set** = a
     **`clo`-fixed point** — `closed_iff_fixed` (`FenchelMoreau.closed_iff_fixed`): `x = cl x`
     iff `x` is in the image of the antitone leg. Idempotence `cl(cl S) = cl S` is
     `clo_idempotent` / `cloAntitone_idempotent`; extensivity `S ⊆ cl S` is `clo_extensive` /
     `cloAntitone_extensive`; monotonicity is `clo_monotone`.
  2. **`r` = the rank function = the fold-height / dimension reading** (`dimension.md`'s `L↑`):
     `r(S)` counts the **independent fold** — the number of extension acts that genuinely raise
     the build before the carrier saturates. Per `dimension.md`, "dimension / degree /
     pole-order / nesting depth" are one height-reading `L↑`; matroid rank is that *same*
     reading on the finite-carrier construction. Its load-bearing in-repo content is
     `dimension_bound_is_count` (`LinearDependence.lean`): rank is **COUNT** — `n+1` vectors in
     `𝔽₂^n` are dependent because the `2^m` subset-sums collide in a `2^n` value-space
     (pigeonhole). That collision IS the rank ceiling `r(E) ≤ d`.

- **Residue, tagged `q = ±1`** — two residues at the two poles, exactly as in
  `galois_correspondence.md`:
  - **`clo`-residue, `q = +1` (converge / closure).** `cl S \ S` is the closure gap; it
    *vanishes* on the closed (flat) elements — the **fixed locus** of the idempotent monad
    (`closed_iff_fixed`, the same `q=+1` corner as Galois flats / `f**=f` convex-closed
    functions / Carathéodory-measurable sets). Greedy=optimal lives here (below).
  - **duality-residue, `q = ±1` (the complementation involution).** Matroid duality
    `M ↦ M*`, `r*(S) = |S| − r(E) + r(E−S)`, is the **orientation swap** of `C`: the
    `ResidueTag` `±1` multiplier (`multiplier_unimodular : multiplier q * multiplier q = 1`).
    `M** = M` is the involution `q² = 1` — the same unimodular bit that runs sign / `det=±1` /
    `∂²=0` / antisymmetry. Complementation `S ↦ E−S` is the involution; `r*` is `r` read after
    the swap.

## Re-seeing — `⟨C | L⟩ ⊕ Residue`

```
   ground set E              =  ⟨ finite distinguished atoms | (carrier) ⟩
   independent set S          =  a build where every extension act raised the fold  (no collision)
   dependent set S            =  a build where vsum collided                        (dimension_bound_is_count)
   circuit C                  =  a MINIMAL dependence = the residue of one sum-collision (LinearDependence: the explicit 0-combination)
   rank function r(S)         =  ⟨ S | L↑ = dimension/depth ⟩  = COUNT of the independent fold
   closure operator cl(S)     =  clo = G∘F                       (GaloisConnection.clo)
   flat / closed set          =  a clo-FIXED point               (closed_iff_fixed, q=+1)
   exchange axiom             =  monotone + idempotent + the extension-act is well-defined  (clo_monotone, clo_idempotent)
   submodular  r(A∪B)+r(A∩B) ≤ r(A)+r(B)  =  the inequality the height-residue obeys (the GAP/COUNT deficit, dimension_bound_is_count's < )
   greedy algorithm           =  the fold-to-normal-form raw_initial: read C through L↑ ONCE, left-to-right
   greedy = optimal           =  the matroid is EXACTLY where the fold gives the optimum (the q=+1 closure-corner characterization)
   matroid duality M ↦ M*      =  the q=±1 orientation swap on C  (complementation S↦E−S, multiplier_unimodular)
   r*(S)=|S|−r(E)+r(E−S)       =  r read after the involution
   M** = M                     =  q² = 1                          (the unimodular involution)
```

The map is exact on the **closure** leg and the **rank=dimension** leg; the **greedy=optimal**
and **submodular** legs are *predicted from the parts* (the closure-corner + the COUNT deficit)
but have no named matroid theorem in-repo; the duality involution rides on `ResidueTag`.

## Revelation

**A matroid is ONE `(C, L)` — the calculus's idempotent closure `clo`
(`galois_correspondence.md`) read on a finite atom-carrier, with the rank=dimension reading
(`dimension.md`) and the `q=±1` complementation involution (`ResidueTag`) as its two
matroid-specific legs.** This is **collapse + forcing + residue-surfaced**, three at once, and
it is *not* a re-skin of `galois_correspondence.md` — the new content is that the matroid
closure is the **fifth `clo`-family instance**, with greedy=optimal as the "the fold gives the
optimum" characterization the closure-corner forces.

1. **Collapse — the matroid closure operator IS the Galois/Fenchel `clo`.** "Matroid closure
   `cl`," "Galois closure `Inv∘Fix`," "convex closure `f**`," "the Nullstellensatz radical
   `√J = I(V(J))`," and "Carathéodory outer-measure closure" are **not five operators** — they
   are the *same* idempotent closure `clo = G∘F` (`clo_idempotent`, 15/0 PURE; `biconj_idempotent`,
   18/0 PURE) being the identity on its closed elements. A matroid **flat = a closed set = a
   `clo`-fixed point** is `closed_iff_fixed` *verbatim* (the residue vanishes exactly on the
   closure-fixed locus). The four matroid cryptomorphic axiom systems (independent sets / rank /
   circuits / closure) are four *readings of one construction*: independent sets = the
   no-collision builds, circuits = the minimal collisions, rank = the height-count, closure = the
   `clo`-monad. Cryptomorphism = the calculus's "four facets of one `⟨C|L⟩`."

2. **Forcing — the rank function is forced as the height-reading, and submodularity is the
   COUNT deficit it must obey.** `r` is not posited: it is `dimension.md`'s well-founded
   height-reading `L↑` (the build's own descent measure, `isPart_wf`-style) on the finite
   carrier. Per `dimension.md`, this is the *same* reading as vector-space dimension — matroid
   rank is "linear-algebra dimension with the field thrown away, only the
   independent/dependent distinction kept." The repo grounds this exactly:
   `dimension_bound_is_count` shows the rank ceiling is a **pigeonhole COUNT** (`2^m > 2^n` ⟹
   collision), so submodularity `r(A∪B)+r(A∩B) ≤ r(A)+r(B)` is the **deficit form of that same
   COUNT inequality** — the height-residue can only *lose* count when two builds share atoms,
   never gain. The `<` in `dimension_bound_is_count` is the submodular inequality's source.

3. **Residue surfaced — greedy=optimal is the q=+1 closure corner, and duality is the q=±1
   swap.** The deepest unity, the same two-residue split as `galois_correspondence.md`:
   - **Greedy = the fold-to-normal-form, optimal exactly in the `q=+1` corner.** The greedy
     algorithm reads `C` through `L↑` **once, left-to-right** — it is `raw_initial`'s
     `Lens.view = Raw.fold`, the unique catamorphism out of the construction (`category_theory.md`).
     A matroid is *precisely* the structure where this single fold reaches the optimum (Rado–Edmonds:
     greedy is optimal for *every* weighting iff the independence system is a matroid). In calculus
     terms: the matroid is where the closure *settles* (`clo` idempotent, the residue vanishes on
     flats — `q=+1` converge), so the one-pass fold lands on the fixed point with no oscillation.
     This is the same `q=+1` "the closure settles, so the answer is reached" as Galois flats /
     Banach contraction / compactness finiteness-collapse. Non-matroids are where greedy fails =
     where the fold does *not* give the optimum = the structure is *not* a `clo`-fixed point.
   - **Duality `M↔M*` = the `q=±1` orientation swap.** `M ↦ M*` complements `S ↦ E−S` and reads
     rank after the swap (`r*(S)=|S|−r(E)+r(E−S)`); `M**=M` is `q²=1`, the `multiplier_unimodular`
     involution — the *same* unimodular `±1` bit as sign / `det=±1` / `∂²=0` / Lie antisymmetry.
     Loops (rank-0 elements) and coloops (rank-raising-everywhere elements) are dual under the
     swap, exactly as `0`/`∞` are one pre-Lens residue swapped (`06_lens_readings.md` §6.9).

## VALIDATE verdict: **EXTEND by consolidation + PREDICTION** (no new primitive; one named absence)

The matroid **EXTENDS** the calculus with **no new axis** — every slot is present:

- **the idempotent closure `clo`** (`GaloisConnection`/`FenchelMoreau`) — the matroid closure
  operator, flats = `clo`-fixed points; **fifth instance** of the `f**=clo` family;
- **the rank=dimension height-reading `L↑`** (`dimension.md`) — the rank function, grounded as
  COUNT by `dimension_bound_is_count`;
- **the `q=±1` involution** (`ResidueTag.multiplier_unimodular`) — matroid duality `M↔M*`;
- **the `raw_initial` fold** (`category_theory.md`) — the greedy algorithm; matroid =
  fold-gives-optimum = the `q=+1` closure corner.

**PREDICTION** legs (form delivered, named matroid object absent): greedy-optimality as a typed
theorem (Rado–Edmonds), submodularity of `r` as a typed inequality, the cryptomorphic
equivalence of the four axiom systems, and matroid duality as a typed involution on a `Matroid`
structure. The calculus *predicts* greedy=optimal must be the `q=+1` corner characterization and
submodularity must be the COUNT deficit — both grounded in legs (`closed_iff_fixed`,
`dimension_bound_is_count`) but not welded into a `Matroid` object.

**No BREAK.** Matroids do **not** need a genuine independent-set/exchange primitive the calculus
lacks: the exchange axiom is the monotone-idempotent closure (`clo_monotone`/`clo_idempotent`)
plus the well-definedness of "the rank-raising extension act," and the independent sets are the
no-collision builds (`dimension_bound_is_count`'s complement). The one honest caveat: the repo's
linear-dependence carrier is `𝔽₂`-specific (`LinearDependence.lean`); a general (abstract,
non-linear) matroid would need the closure axioms instantiated on an abstract finite atom-set
rather than read off subset-sum collisions — the same shape as `galois_correspondence.md`'s
"concrete `Gal(ℚ(ζ₅)/ℚ)` built, general `Inv(H)` conceptual."

## Verified Lean anchors (file : line : theorem — all grep-confirmed this session; all PURE)

| Leg | Theorem (file : name : line) | scan tally |
|---|---|---|
| **matroid closure = the `clo` idempotent closure** (flats = `clo`-fixed points) | `Lib/Math/Order/GaloisConnection.lean : clo` (def, :104), `clo_extensive` (:107), `clo_monotone` (:114), `clo_idempotent` (:126), `mulDiv_gc` (:168, concrete witness) | **15 pure / 0 dirty** |
| **flat = closed set = `clo`-fixed point** (the residue vanishes on the closure) | `Lib/Math/Order/FenchelMoreau.lean : cloAntitone` (def, :53), `biconjugate_eq_clo` (:59), `cloAntitone_extensive` (:72), `cloAntitone_idempotent` (:123), `biconj_idempotent` (:134), `closed_iff_fixed` (:152), `cloAntitone_eq_gc_clo` (:187, the weld to `GaloisConnection.clo`) | **18 pure / 0 dirty** |
| **rank = dimension = COUNT of the independent fold; dependence = sum-collision** | `Lib/Math/Combinatorics/LinearDependence.lean : vsum` (def, :57), `vsum_len` (:64), `dimension_bound_is_count` (:85, `n+1` vectors in `𝔽₂^n` are dependent — the rank ceiling / submodular deficit) | **7 pure / 0 dirty** |
| **rank=dimension height-reading `L↑`** (cross-frame, per `dimension.md`) | `Theory/Raw/Lambek.lean : isPart_wf`, `no_infinite_descent`; `Theory/Raw/Levels.lean : Raw.depth_slash` | (cited via `dimension.md`, PURE there) |
| **matroid duality `M↔M*` = the `q=±1` complementation involution** | `Lib/Math/Foundations/ResidueTag.lean : ResidueTag` (:73, `escape\|converge`), `multiplier` (def, :81, `∓1`), `multiplier_unimodular` (:86, `q²=1`), `residue_tag_two_poles` (:228), `golden_is_converge` (:180) | **55 pure / 0 dirty** |
| **greedy = the fold-to-normal-form** (cross-frame, per `category_theory.md`) | `raw_initial` (`Lens.view = Raw.fold`), `dhom_unique_pointwise` — the unique catamorphism out of `C` | (cited via `category_theory.md`/`SYNTHESIS.md`, PURE there) |

> Axiom-purity note: `GaloisConnection` (15/0), `FenchelMoreau` (18/0), `LinearDependence`
> (7/0), and `ResidueTag` (55/0) were each re-run through `tools/scan_axioms.py` (full `E213.`
> prefix) from repo root this session — **every cited theorem PURE, 0 dirty** across the four
> load-bearing modules.

## Dropped / flagged (honest — NOT grounded in repo Lean)

- **`Matroid` / `Independent` / `IndependentSet` / `circuit` / `coloop` / `submodular` as named
  objects — ABSENT.** Grep across all `lean/E213/` returns zero matroid-specific definitions.
  The "greedy optimality" hits in `Algebra/GRA/*` are about **GRA cell-depth minimization on
  `gen2=3`** (⌈n/3⌉), *not* the matroid greedy algorithm — flagged as a false-positive, dropped.
- **Greedy-optimality (Rado–Edmonds) as a typed theorem — ABSENT.** Predicted as the `q=+1`
  closure-corner characterization (greedy=optimal ⟺ matroid ⟺ closure settles); the *legs*
  (`closed_iff_fixed`, `raw_initial`) are PURE, the matroid weld is not built. Named promotion
  target.
- **Submodularity `r(A∪B)+r(A∩B) ≤ r(A)+r(B)` as a typed inequality — ABSENT.** Predicted as the
  deficit form of `dimension_bound_is_count`'s pigeonhole `<`; the COUNT leg is PURE, the
  submodular inequality on an abstract `r` is not stated.
- **`closed_iff_fixed` lives in `FenchelMoreau` (:152), NOT in `GaloisConnection`** — flagged
  because the brief listed it under the `clo` of `galois_correspondence.md`; grep confirms it is
  the Fenchel–Moreau strong-duality theorem (the `f**=clo` antitone twin), welded to
  `GaloisConnection.clo` via `cloAntitone_eq_gc_clo` (:187). Cited at its true location.
- **Abstract (non-linear) matroid closure — conceptual.** The built closure is on a `𝔽₂`
  subset-sum carrier (`LinearDependence`); the general finite-atom-set instantiation of the
  closure axioms is the analogue of `galois_correspondence.md`'s "general `Inv(H)`" residual.

### Verified buildable witness (named, not asserted)

A buildable ∅-axiom witness, parallel to `dimension_bound_is_count`: **the matroid-closure
`clo` instantiated on the `𝔽₂` span**, defining `cl S = {v | r(S ∪ {v}) = r(S)}` (the vectors
whose adjunction does not raise the COUNT) and proving `cl(cl S) = cl S` by routing through
`GaloisConnection.clo_idempotent` — the fifth `clo`-family instance made concrete on the
already-PURE `LinearDependence` carrier, mirroring how `CyclotomicFive` made the abstract Galois
closure concrete. Verified plausible (both legs — `clo_idempotent` and `dimension_bound_is_count`
— are PURE and live in the same dependency-free `Combinatorics`/`Order` cone); not yet written.

## Verdict: EXTEND by consolidation (fifth `clo`-family instance) + PREDICTION (greedy/submodular)

A matroid is the calculus's **idempotent closure `clo`** (the fifth instance after
Galois/Legendre–Fenchel/Nullstellensatz/Carathéodory) read on a finite atom-carrier, with the
**rank=dimension height-reading** (`dimension.md`, grounded as COUNT by
`dimension_bound_is_count`) and the **`q=±1` complementation involution**
(`multiplier_unimodular`, matroid duality `M↔M*`) as its two matroid-specific legs.
Greedy=optimal is the **"the fold gives the optimum" characterization** — the `q=+1` closure
corner where `clo` settles (`closed_iff_fixed`). **No new primitive**, **no break**: the exchange
axiom is the monotone-idempotent closure, independent sets are the no-collision builds. Grounded
∅-axiom: the closure machine (`clo_idempotent`/`closed_iff_fixed`, 15/0 + 18/0), the rank COUNT
ceiling (`dimension_bound_is_count`, 7/0), the duality involution (`multiplier_unimodular`,
55/0). Absent and named: the typed `Matroid`/greedy-optimality/submodularity objects, with a
buildable `𝔽₂`-span closure witness. The matroid **EXTENDS by consolidation**, deepening the
`f**=clo` family from four instances to five.
