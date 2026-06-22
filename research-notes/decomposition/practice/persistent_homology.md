# Decomposition: persistent homology / TDA (a filtration K₀⊆K₁⊆…, the persistence module, the barcode / persistence diagram, the structure theorem ⊕ interval-modules, stability, Betti numbers as a function of scale)

*A FRESH decomposition per `../README.md` (model v7.1), the NEXT step from `homology.md` and
`spectral_sequences.md`. `homology.md` found homology = `Residue(L↓,C) = ker∂/im∂` read at ONE scale;
`spectral_sequences.md` found the residue operation is closed under iteration, indexed by the resolution
dial `r`, converging to a `q=+1` fixed point. The thesis to TEST, not re-skin: **persistent homology is
the homology residue read ACROSS the resolution axis — the Betti number as a function of scale, with the
barcode = each residue-class's lifetime.** Ordinary homology reads the residue `ker∂/im∂` at one scale;
persistent homology reads it across a FILTRATION (a one-parameter family indexed by scale = the resolution
axis, `IsResolutionShift`): the persistence module = homology + the inclusion-induced maps = the residue
tracked along the resolution dial. Concretely:
(i) the **persistence module** (homology with the inclusion maps `H(K_i) → H(K_j)`) is `homology.md`'s
`Residue(L↓,C)` carried along the resolution dial — not a fresh object, the SAME `ker δ/im δ`
(`reduced_betti_d4_contractible`) with the inclusion-induced maps = the resolution shift
(`IsResolutionShift`);
(ii) the **barcode** (birth–death intervals) = each residue-class's LIFETIME along the resolution axis = the
modulus made a lifetime — a class is born at one resolution, dies at another; long bars = real features =
the `q=+1` stable residue (`golden_is_converge`), short bars = noise = the `q=−1` transient
(`residue_reentry_never_closes`);
(iii) the **structure theorem** (a persistence module over the resolution line = ⊕ interval modules) = the
residue DECOMPOSES into intervals — the SAME `⊕`-of-graded-pieces semisimple splitting the
spectral-sequence/Decomposition-Theorem degeneration uses;
(iv) **stability** (close inputs ⟹ close diagrams) = the `q=+1` continuity in scale (`continuity.md`, the
reading is Lipschitz in the resolution).
So persistent homology = (the homology residue `ker∂/im∂`) + (read across the resolution axis = the
filtration, `IsResolutionShift`) + (the barcode = each residue's lifetime = the modulus) + (structure
theorem = the residue splits into interval modules, semisimple) + (stability = the `q=+1` continuity in
scale) — NO new primitive; the homology residue tracked along the resolution dial, the barcode its
lifetime-modulus. This is the deepest test yet of whether the resolution axis (`spectral_sequences.md`'s
indexing dial) and the homology residue (`homology.md`) compose into a one-parameter family.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **filtered simplicial complex** `K₀ ⊆ K₁ ⊆ … ⊆ K_N`: the *same* graded
  simplex/cochain nesting `homology.md`/`spectral_sequences.md` read — a build-tree of iterated
  distinguishing, an `n`-cell = `n+1` distinguished vertices, the `Cochain n k` complex with boundary
  `delta` (`Delta/Core.lean:54`) — now carrying a **second grading**: the **filtration index** `i` (the
  scale), an ascending chain of sub-constructions glued by inclusions `K_i ↪ K_{i+1}`. `C` carries the
  README's two read-off axes, with the fold-height used *twice*: a **fold-height** (the cell dimension `k`,
  the homology degree) and the **resolution axis** (the filtration index `i` = the scale at which a cell is
  born). The filtration index is the README's resolution parameter (`continuity.md`/`derivative.md`,
  `IsResolutionShift`) used as a *grading*: where the degree counts cell-dimension, the filtration counts
  the scale-step at which the sub-complex acquires the cell. There is **no Vietoris–Rips/Čech metric
  construction, no point cloud, no diagram category** in `C` — the construction is the filtered combinatorial
  complex + its `delta` + the inclusion maps; **no `persistentHomology`, no `PersistenceModule`, no
  `Barcode`, no `Filtration` object enters** (grep-confirmed ABSENT, see verdict).

- **Reading `L↓ across the resolution dial` — the homology residue `ker∂/im∂`, read as a FUNCTION of the
  scale.** This is the genuinely new framing the field supplies, and the precise extension of `homology.md`:
  that note read `Residue(L↓,C) = ker δ/im δ` *at one scale* (a single complex). Persistent homology reads it
  **at every scale `i`, together with the inclusion-induced maps between scales**:
  - **At each scale `i`**: the homology residue `H(K_i) = ker ∂_i / im ∂_i` is `homology.md`'s
    `Residue(L↓,C)` verbatim (`reduced_betti_d4_contractible`, `kerSizeDelta`). The **Betti number** `b_k(i)`
    = `dim H_k(K_i)` is the residue-dimension as a function of the scale `i` — `homology.md`'s single Betti
    number turned into a *sequence indexed by the resolution dial*.
  - **Between scales**: the inclusion `K_i ↪ K_{i+1}` induces `H(K_i) → H(K_{i+1})` — a **resolution shift**
    on the residue, `IsResolutionShift` (`ResolutionShift.lean:73`). The persistence module is exactly
    "the homology residue + these shift maps". The shifts **compose additively**:
    `IsResolutionShift_compose` (`:130`) — passing from scale `i` to scale `i+r` is the `r`-fold iterate of
    the unit shift (`cutHalfIter`, `:158`), cumulative grade `r`. So the resolution dial supplies the
    one-parameter indexing.
  - So the reading is: **take the homology residue (`ker∂/im∂`), and read it across the resolution axis,
    tracking each class through the inclusion-induced shift maps.** The reading IS the homology residue made
    a function of scale.

- **Residue — the barcode: each homology class's LIFETIME along the resolution axis, tagged `q=±1` by
  whether the bar is long (stable) or short (transient).** Each scale gives a residue; the *new* residue
  this note surfaces is the **lifetime** of each residue-class — a birth scale and a death scale, the
  interval `[birth, death)`:
  - **`q=+1` (long bars = real features = the residue STABILIZES).** A class born early and dying late (or
    never) persists across the resolution dial — a fixed point of the residue tracked along scale, the
    README's `q=+1` converging pole (`converge_residue_fixed`, `ResidueTag.lean:160`; `golden_is_converge`,
    `:180`) — the SAME modulated-completion convergence as `DyadicCompletion.orbit_to_center_completion`
    (`:366`). **The bar's length is the convergence modulus** — the resolution-range over which the class
    survives, exactly the role the dyadic exponent plays in `banach_fixed_point_modulated`'s `N(m)`. The
    nonzero stable witness is `NonzeroBetti.betti_one_cycle`/`cycle_vs_contractible_qpm`
    (`NonzeroBetti.lean:111,173`): the hollow triangle `S¹`'s `b₁=1` is a genuine un-fillable cycle = a long
    bar that does NOT die — the `q=+1` survivor against the `q=+1`-trivial contractible (`b̃=0`).
  - **`q=−1` (short bars = noise = the class re-enters and dies).** A class born and dying within a tiny
    resolution-range is the `q=−1` transient: the residue re-enters at one scale and the cover closes it at
    the next — `residue_reentry_never_closes` (`ResidueReentry.lean:63`), "naming the residue yields a fresh
    object, leaving a fresh residue", read here as a feature that appears and is immediately filled. The
    contractible case (`reduced_betti_d4_contractible`, `ker=im`, residue empty) is the limit where every bar
    has died: no surviving feature.
  - **The barcode IS the modulus made a lifetime.** `continued_fractions`/`DyadicCompletion`'s modulus
    `M(k)` (the never-closing approximant bracket) becomes, here, a *per-class* interval: birth = the scale
    the class enters, death = the scale it is filled. The whole barcode = the collection of these
    lifetime-moduli, one per residue-class, the `q=±1` tag distinguishing the long (stable) from the short
    (transient).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   filtered complex C          =  ⟨ graded cells + an ascending filtration | the boundary delta + the scale index ⟩
                                  = homology.md's C with a SECOND grading (the filtration index i = the resolution dial)
   H(K_i) = ker ∂_i / im ∂_i   =  homology.md's Residue(L↓,C) AT SCALE i  (reduced_betti_d4_contractible, kerSizeDelta)
   Betti number b_k(i)         =  the residue-dimension as a FUNCTION of scale  =  homology.md's b_k indexed by i
   inclusion map H(K_i)→H(K_j) =  the resolution shift on the residue  =  IsResolutionShift (grades ADD: compose)
   persistence module          =  the homology residue + the shift maps  =  Residue(L↓,C) tracked along the resolution dial
   barcode / persistence diag  =  each residue-class's LIFETIME [birth, death)  =  the modulus made a per-class lifetime
   "long bar" (real feature)   =  q=+1 STABLE residue (survives the dial)  =  golden_is_converge / orbit_to_center_completion
   "short bar" (noise)         =  q=−1 TRANSIENT (re-enters & dies)  =  residue_reentry_never_closes
   structure thm: module = ⊕ interval-modules =  the residue SPLITS into intervals (semisimple over the resolution line)
   stability (close in ⟹ close diagram) =  q=+1 CONTINUITY in scale  =  continuity.md (the reading Lipschitz in resolution)
   "f contractible ⟹ all bars die" =  q=+1 empty-residue limit  (reduced_betti_d4_contractible)
```

Set against `homology.md` (the residue at ONE scale) and `spectral_sequences.md` (the residue ITERATED over
the dial), persistent homology is the *middle* construction — the residue read across the dial as a
one-parameter family, the inclusion maps the shift `spectral_sequences.md` used for the page index:

| classical persistent-homology object | = the 213 reading | already in note | Lean anchor |
|---|---|---|---|
| `H(K_i) = ker ∂_i / im ∂_i` at scale `i` | `Residue(L↓,C)` at one scale | `homology.md` | `reduced_betti_d4_contractible`, `kerSizeDelta` |
| Betti number `b_k(i)` as a function of scale | the residue-dimension indexed by the resolution dial | `homology.md` + resolution | `kerSizeDelta`; `IsResolutionShift` |
| inclusion-induced map `H(K_i) → H(K_j)` | the resolution SHIFT on the residue (grades add) | `spectral_sequences.md` (the shift), `continuity.md` | `IsResolutionShift`, `IsResolutionShift_compose`, `cutHalfIter` |
| persistence module | the homology residue tracked along the dial | NEW (the residue as a one-parameter family) | `reduced_betti_d4_contractible` + `IsResolutionShift_compose` |
| barcode / persistence diagram | each residue-class's lifetime `[birth,death)` = the modulus | NEW (the modulus as a per-class lifetime) | `orbit_to_center_completion` (modulus); `residue_reentry_never_closes` |
| long bar (real feature) | `q=+1` STABLE residue (survives the dial) | `golden_ratio.md`/`gaussian_clt.md` (`q=+1`) | `golden_is_converge`, `converge_residue_fixed`, `betti_one_cycle` |
| short bar (noise) | `q=−1` TRANSIENT (re-enters, dies) | `cardinality.md` (`q=−1`) | `residue_reentry_never_closes`, `object1_not_surjective` |
| structure thm: module = ⊕ interval-modules | the residue SPLITS into intervals (semisimple) | `spectral_sequences.md` (degeneration = ⊕-split) | (interval-module object ABSENT; ⊕-split = `chain_finite`-style) |
| stability (bottleneck) | `q=+1` continuity in scale (Lipschitz in the dial) | `continuity.md` | `continuous_preimage_dyadicopen`, `preimage_dyadicopen_uniform_continuous_of_modulus` |
| `∂²=0` (each `K_i` is a complex) | the `q=±1` orientation sign-cancel, SAME as `∂²=0` | `homology.md` | `dsq_zero_universal_delta4` |

Persistent homology consumes BOTH of `C`'s axes, with the resolution dial promoted to the *primary* index:
the fold-height as the homology degree `k` (`∂` raises/lowers it), the resolution as the filtration index `i`
(the inclusion maps shift it) — exactly because it is the homology residue `homology.md` named, *read as a
function over the resolution dial `spectral_sequences.md` introduced*.

## LEVERAGE — does persistent homology = the homology residue read across the resolution axis, the barcode its lifetime-modulus?

**Verdict: PREDICTION + PARTIAL — the homology residue (`homology.md`) and the resolution dial
(`spectral_sequences.md`/`continuity.md`) compose into a one-parameter family, and every load-bearing leg is
already ∅-axiom and PURE; the *named* `PersistenceModule`/`Barcode`/`PersistenceDiagram`/`IntervalModule`/
`Filtration`/`bottleneck` objects are ABSENT (grep-confirmed: zero Lean declarations) — the same shape as
`spectral_sequences.md`'s missing `SpectralSequence`/`E_r` object and `homology.md`'s missing graded
`Ext^n`.** Persistent homology is not a new edifice; it is `homology.md`'s `ker∂/im∂` residue read across the
filtration, the barcode = each class's lifetime-modulus. Leg by leg, honest.

**(1) ★ The persistence module IS the homology residue read across the resolution axis — the NEW datum, not a
re-skin of `homology.md`.** `homology.md` read `Residue(L↓,C) = ker δ/im δ` *at one scale* and stopped (a
single Betti number). Persistent homology's defining move is to read that residue at *every* scale `i` and
glue the readings by the inclusion-induced maps `H(K_i) → H(K_{i+1})`. The residue mechanism is built and
PURE — `reduced_betti_d4_contractible` (`BettiKernel.lean:63`, scanned 11/0): `kerSize 5 0 = 1 ∧
kerSize 5 1 = 2` ⇒ reduced Betti `b̃₀=b̃₁=0` on the contractible Δ⁴, `ker=im`, residue empty. The
between-scale glue map is exactly the resolution shift `IsResolutionShift` (`ResolutionShift.lean:73`,
scanned 17/0), whose grades **add under composition** — `IsResolutionShift_compose` (`:130`): grade-`E₁` ∘
grade-`E₂` = grade-`(E₂+E₁)`, the `r`-fold iterate `cutHalfIter` (`:158`). So the persistence module =
`reduced_betti_d4_contractible`'s residue + `IsResolutionShift_compose`'s shift maps. **This is the
load-bearing new finding: the homology residue is a function of scale, the inclusion maps are the resolution
shift, and the shifts compose additively (the one-parameter indexing is well-defined).**

**(2) ★ The barcode IS each residue-class's lifetime = the modulus made a per-class lifetime, tagged `q=±1`
long/short — the SECOND new datum.** A bar `[birth, death)` records the resolution-range over which a
homology class survives. The README's residue tag is the formal home of "survives vs dies":
- *Long bar (`q=+1`, real feature).* A class persisting across the dial is the converging pole —
  `converge_residue_fixed` (`ResidueTag.lean:160`, scanned 55/0) delegating to `banach_fixed_point_modulated`,
  and `golden_is_converge` (`:180`) tying `+1` to the literal stabilizing orbit; the completion-limit
  instance `orbit_to_center_completion` (`DyadicCompletion.lean:366`, scanned 32/0) is an orbit reaching its
  center, **narrowed only by a modulus** — the bar's length IS that modulus, the resolution-range the class
  occupies (exactly `banach_fixed_point_modulated`'s explicit `N(m)`). The genuine nonzero survivor is
  `NonzeroBetti.betti_one_cycle`/`nonzero_cohomology_class`/`cycle_vs_contractible_qpm`
  (`NonzeroBetti.lean:111,143,173`, scanned 56/0): the hollow triangle `S¹=∂Δ²`'s `b₁=1` is an un-fillable
  cycle = a long bar with no death, the `q=+1` survivor.
- *Short bar (`q=−1`, noise).* A class born and filled within a tiny range is the escape transient —
  `residue_reentry_never_closes` (`ResidueReentry.lean:63`, scanned 14/0), "naming the residue yields a fresh
  object, leaving a fresh residue, the cover never closes" (`escape_residue_outside`/`object1_not_surjective`,
  `ResidueTag.lean:133`/`FlatOntologyClosure.lean:61`) — read as a feature appearing then immediately filled.
- The tag is one formal object: `residue_tag_two_poles` (`:228`), `multiplier_unimodular` (`:86`). **So the
  barcode is the `q=±1` residue tag read on the lifetime of each class along the resolution axis** — long =
  `q=+1` stable, short = `q=−1` transient — the modulus (`continued_fractions`/`DyadicCompletion`'s
  never-closing bracket) localized to a per-class birth–death interval.

**(3) ★ The structure theorem (persistence module = ⊕ interval modules) IS the residue splitting into
intervals, semisimple over the resolution line — the SAME `⊕`-of-graded-pieces as the spectral-sequence
degeneration.** A persistence module over the (totally-ordered) resolution line is semisimple: it decomposes
uniquely as a direct sum of interval modules, one per bar. This is structurally the
`spectral_sequences.md`/Decomposition-Theorem semisimple splitting — a graded object over a one-parameter
index splits into its graded pieces. The fold-height grading and its per-level `ker/im` residue are built
(`kerSizeDelta`, `reduced_betti_d4_contractible`); the *named* interval-module/`⊕`-decomposition object is
ABSENT (the chain-finiteness that makes the splitting hold over a finite filtration is the
`Connectedness.chain_finite`-style finiteness the topology cluster uses, but no `IntervalModule` Lean type
exists — see boundary). **Honest: the ⊕-into-intervals is grounded as the residue-per-scale data, NOT as a
named decomposition theorem.**

**(4) ★ Stability (close inputs ⟹ close diagrams) IS the `q=+1` continuity in scale — GROUNDED at the
reading level.** The bottleneck-stability theorem says the persistence diagram is Lipschitz (1-Lipschitz in
the sup norm) in the input filtration: a small perturbation of the scale function moves the bars only a
little. This is exactly `continuity.md`'s resolution-dial continuity — the reading commutes with refinement,
its fibre is resolution-stable. The Lean witness is `continuous_preimage_dyadicopen`
(`ContinuityOpenSet.lean:83`, scanned 11/0) — continuity ⟺ open-preimage at the dyadic resolution — and the
uniform/modulus form `preimage_dyadicopen_uniform_continuous_of_modulus` (`:173`): continuity *as a modulus*,
the explicit Lipschitz-in-resolution data. So stability is the `q=+1` continuity pole read on the
barcode-as-a-function-of-input: the diagram is a continuous (modulus-carrying) reading of the filtration, not
a fresh analytic theorem. **Honest: the bottleneck *metric on diagrams* is conceptual (no `Barcode` type to
metrize); the continuity *mechanism* it would instantiate is built and PURE.**

**(5) `∂²=0` at every scale = `homology.md`'s `q=±1` sign-cancel.** Each `K_i` is a chain complex, so
`∂²=0` holds at every scale by the SAME pairwise orientation-bit cancellation `dsq_zero_universal_delta4`
(`V4Capstone.lean:41`, scanned 5/0: `∀ σ, ∀ i, δ(δσ) i = false` on Δ⁴), threading through the whole
filtration. Persistent homology is the statement that this `q=−1` direction-bit cancellation holds at every
scale, so `H(K_i)` is well-defined for each `i`.

**Honest boundary — Lean-built vs conceptual.**
- *Lean-built (∅-axiom, scanned PURE this session):* (a) the **homology residue `ker δ/im δ`** each scale
  computes — `delta` (`Delta/Core.lean:54`), `dsq_zero_universal_delta4` (`V4Capstone.lean:41`, 5/0),
  `reduced_betti_d4_contractible`/`kerSizeDelta` (`BettiKernel.lean:63,42`, 11/0), and the nonzero-residue
  (long-bar) witness `betti_one_cycle`/`nonzero_cohomology_class`/`cycle_vs_contractible_qpm`
  (`NonzeroBetti.lean:111,143,173`, 56/0); (b) ★ the **resolution dial indexing the scale, grades add** —
  `IsResolutionShift`/`IsResolutionShift_compose`/`cutHalfIter` (`ResolutionShift.lean:73,130,158`, 17/0);
  (c) ★ the **`q=+1` long-bar convergence / `q=−1` short-bar escape** —
  `converge_residue_fixed`/`golden_is_converge`/`residue_tag_two_poles`/`escape_residue_outside`/
  `multiplier_unimodular` (`ResidueTag.lean:160,180,228,133,86`, 55/0), `orbit_to_center_completion`
  (`DyadicCompletion.lean:366`, 32/0), `residue_reentry_never_closes` (`ResidueReentry.lean:63`, 14/0),
  `object1_not_surjective`/`object1_injective`/`self_covering_closure` (`FlatOntologyClosure.lean:61,47,69`,
  7/0); (d) ★ the **stability = `q=+1` continuity in scale** — `continuous_preimage_dyadicopen`/
  `preimage_dyadicopen_uniform_continuous_of_modulus` (`ContinuityOpenSet.lean:83,173`, 11/0).
- *Conceptual-only / the precise missing leg (the `spectral_sequences.md`/`homology.md`-style gap):* the
  **`PersistenceModule`/`Barcode`/`PersistenceDiagram`/`IntervalModule`/`Filtration`/`bottleneck`/
  Vietoris–Rips OBJECTS are ABSENT.** Grep over `lean/E213` for `persistentHomology`/`persistence`/`barcode`/
  `filtration`/`persistence_diagram`/`interval_module`/`bottleneck`/`PersistenceModule`/`PersistenceDiagram`
  returns **zero Lean declarations**; the only `filtration` hits are incidental docstring comments (e.g. the
  *physics* "Filtration spectral sequence" interpretive comment in
  `Lib/Physics/AlphaEM/LoopVertexGraduation.lean:44`, which itself flags the object as recorded "at the
  interpretive level, NOT a derivation"). There is **no** filtered complex object indexed by a scale, **no**
  `H(K_i) → H(K_j)` inclusion-map persistence module as a Lean def, **no** `Barcode`/`PersistenceDiagram`,
  **no** interval-module decomposition theorem, **no** bottleneck metric, **no** Vietoris–Rips/Čech
  construction. This is the SAME shape as `spectral_sequences.md`'s missing `SpectralSequence`/`E_r` object
  and `homology.md`'s missing graded `Ext^n`: the *residue mechanism* (`ker δ/im δ`), the *resolution-dial
  index* (`IsResolutionShift_compose`), the *`q=±1` long/short tag* (`ResidueTag`, `golden_is_converge` /
  `residue_reentry_never_closes`), and the *stability continuity* (`continuous_preimage_dyadicopen`) are each
  built and PURE; the **filtered complex + inclusion-map persistence module + barcode object** that would weld
  them into named persistent homology is the precise open leg.

So: **PREDICTION on the consolidation (persistent homology = the homology residue read across the resolution
axis; the persistence module = `Residue(L↓,C)` + the inclusion-induced resolution shift; the barcode = each
class's lifetime-modulus, long = `q=+1` stable / short = `q=−1` transient; the structure theorem = the
residue splitting into intervals; stability = the `q=+1` continuity in scale), cashed at the
residue-mechanism / resolution-dial / `q=±1`-tag / continuity level; PARTIAL because the
`PersistenceModule`/`Barcode`/`IntervalModule` OBJECTS are absent — the named open legs, not hand-waves.**

## Revelation (consolidation: persistent homology = the homology residue read across the resolution axis, the barcode its lifetime-modulus)

**Collapse — the persistence module, the barcode, the structure theorem, and stability are ONE machine: the
homology residue `Residue(L↓,C)` read as a function of the scale, glued by the resolution shift.**
`homology.md`'s deepest find was that homology = `Residue(L↓,C) = ker∂/im∂` (the residue at one scale).
`spectral_sequences.md` found the resolution dial `IsResolutionShift` indexes a family of residues with
additive grades. Persistent homology is what the calculus produces when those two compose: read the homology
residue at *every* scale, glue by the inclusion-induced resolution shift, and ask how long each class
survives. The single forcing sentence, read at both poles:

- **`q=+1` (long bar = real feature = the class survives the dial).** A homology class persisting across the
  filtration is a fixed point of the residue tracked along scale — the converging/closure pole
  (`converge_residue_fixed`, `golden_is_converge`, `orbit_to_center_completion`). The bar's length IS the
  convergence modulus (`banach_fixed_point_modulated`'s `N(m)`) — the resolution-range the feature occupies;
  the un-fillable cycle (`betti_one_cycle`, the hollow `S¹`) is the canonical survivor. The `q=+1` corner:
  "the residue persists; the feature is real."
- **`q=−1` (short bar = noise = the class re-enters and dies).** A class born and filled within a tiny range
  is the escape transient: the residue re-enters at one scale, the cover closes it at the next —
  `residue_reentry_never_closes`, "naming the residue yields a fresh object, leaving a fresh residue"
  (`object1_not_surjective`). The `q=−1` pole, now read as topological noise on the resolution axis.

This passes the re-skin guard, and it does NOT restate `homology.md` or `spectral_sequences.md`:
`homology.md` read the residue at one scale; `spectral_sequences.md` iterated the residue operation on its own
output (the page recursion `E_{r+1}=H(E_r)`). **This note's new datum is that persistent homology reads the
SAME homology residue as a *one-parameter family over the scale* (not iterated on its own output — read at
each scale of a fixed filtration, glued by inclusion), that the inclusion-induced maps ARE the resolution
shift (`IsResolutionShift_compose`, grades add), and that the barcode is the `q=±1` residue tag read on each
class's LIFETIME — long = `q=+1` stable, short = `q=−1` transient — the modulus localized to a birth–death
interval.** Where `spectral_sequences.md`'s residue re-enters as its own operand (a dynamical system on
residues), persistent homology's residue is read *across an external scale parameter* (a function of the dial)
— two distinct uses of the resolution dial on the homology residue, both `q=±1`-tagged. The deepest line: a
barcode is the homology residue's lifetime-modulus along the resolution axis, the long bars its `q=+1`
survivors and the short bars its `q=−1` transients. **EXTEND by consolidation + the function-of-scale datum;
no new axis; interior model v7.1 holds.** The one genuine absence — the `PersistenceModule`/`Barcode`/
`IntervalModule` object — is located precisely: the filtered-complex twin of `spectral_sequences.md`'s missing
`E_r` and `homology.md`'s missing `Ext^n`, the named one-parameter-family-of-residues object that would weld
the (all-built) residue + resolution-shift + `q=±1`-tag + continuity mechanism.

## Note for the technique

- **Persistent homology is the sharpest confirmation that the resolution axis is a *reading parameter on the
  homology residue*, not just on number-readings.** `continuity.md`/`derivative.md` earned the resolution dial
  on number-readings (`Δ`/`d`, `Σ`/`∫`); `spectral_sequences.md` showed it indexes the residue *iterated*;
  persistent homology shows it indexes the residue *as a one-parameter family* — the Betti number becomes a
  function of scale, the barcode the per-class lifetime. The fact that "Betti-as-a-function-of-scale" is the
  homology residue read across `IsResolutionShift` is the cleanest vindication that the resolution axis is
  reading-agnostic: it dials a number-reading (`derivative.md`), a residue-iteration (`spectral_sequences.md`),
  and a residue-family (here) identically.

- **The barcode reveals the modulus is a PER-CLASS object, not a single global bracket.** Earlier notes read
  the modulus as one never-closing bracket `M(k)` (`continued_fractions`/`DyadicCompletion`). The barcode is
  *many* moduli at once — one birth–death interval per homology class — the modulus distributed over the
  residue's generators. This is the same move `probability.md` made (a single ratio-reading becomes a
  distribution); here the single lifetime-modulus becomes a distribution of lifetimes = the barcode. The
  long/short `q=±1` split is then the modulus's two poles read per-class: a long modulus (survives) = `q=+1`,
  a short modulus (dies) = `q=−1`.

- **Stability ties the `q=+1` continuity pole to the residue-as-a-function-of-input.** The bottleneck
  stability theorem is `continuity.md`'s resolution-continuity applied to the *map input-filtration ↦
  barcode*: small perturbation of the scale ⟹ small perturbation of the bars, i.e. the barcode is a
  modulus-continuous reading of the filtration (`preimage_dyadicopen_uniform_continuous_of_modulus`). So
  stability is not a separate analytic miracle — it is the `q=+1` continuity of the homology-residue reading
  in its scale argument. This is the same resolution-agnosticism `integration.md` found for `Σ⊣Δ`/`∫⊣d`.

- **The break is `spectral_sequences.md`'s, not `knots.md`'s.** Persistent homology hits NO topological-quotient
  break (no isotopy, no ambient identification — the filtration is a chain of honest inclusions, the
  confluent/terminating `q=+1` corner). Its only absence is the *named one-parameter-family object* — a
  filtered complex with scale-indexed homology, the inclusion-map persistence module, the barcode, and the
  interval-module decomposition — the SAME shape as the missing `SpectralSequence`/`E_r`
  (`spectral_sequences.md`) and `Ext^n` (`homology.md`): every leg (residue, resolution shift, `q=±1` tag,
  continuity) PURE, only the bundle naming them open. The metric (Vietoris–Rips/Čech) construction of the
  filtration from a point cloud is the additional `Real213`-cut residue shared with the whole geometry cluster
  — not a structural gap in the discrete reading.

---

### Verified Lean anchors (file:line:theorem — all grep/Read-verified on `lean/E213`; purity via `tools/scan_axioms.py`, run from repo root this session)

| Leg | Theorem / structure (file:line : name) | Status |
|---|---|---|
| ★ **each scale `H(K_i)=ker ∂_i/im ∂_i` = `Residue(L↓,C)`** (the empty/contractible case; Betti-per-scale data) | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 reduced_betti_d4_contractible`, `:42 kerSizeDelta`, `:47 kerSize_5_0`, `:52 kerSize_5_1` | **∅-axiom PURE, scanned 11/0** ✓ |
| ★ **long-bar survivor (nonzero residue): `q=−1` cycle vs `q=+1` contractible** | `Lib/Math/Cohomology/Examples/NonzeroBetti.lean:111 betti_one_cycle`, `:143 nonzero_cohomology_class`, `:134 loopClass_not_coboundary`, `:173 cycle_vs_contractible_qpm` | **∅-axiom PURE, scanned 56/0** ✓ |
| ★ **the resolution dial indexing the scale; inclusion maps = the shift, grades ADD** | `Lib/Math/Analysis/ResolutionShift.lean:73 IsResolutionShift`, `:130 IsResolutionShift_compose`, `:158 cutHalfIter`, `:179 IsResolutionShift_cutHalfIter` | **∅-axiom PURE, scanned 17/0** ✓ |
| ★ **long bar = `q=+1` stable; short bar = `q=−1` transient (the barcode lifetime-tag)** | `Lib/Math/Foundations/ResidueTag.lean:160 converge_residue_fixed`, `:180 golden_is_converge`, `:228 residue_tag_two_poles`, `:133 escape_residue_outside`, `:86 multiplier_unimodular` | **∅-axiom PURE, scanned 55/0** ✓ |
| the bar length = the convergence modulus (reached-by-none, modulus-narrowed) | `Lib/Math/Probability/Limit/DyadicCompletion.lean:366 orbit_to_center_completion` | **∅-axiom PURE, scanned 32/0** ✓ |
| short bar = the residue re-enters and dies (the `q=−1` escape) | `Lens/Foundations/ResidueReentry.lean:63 residue_reentry_never_closes`, `:85 residue_perpetually_reenters` | **∅-axiom PURE, scanned 14/0** ✓ |
| the escape / faithful residue (the `q=−1` pole's kernel) | `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective`, `:47 object1_injective`, `:69 self_covering_closure` | **∅-axiom PURE, scanned 7/0** ✓ |
| ★ **stability = `q=+1` continuity in scale** (Lipschitz/modulus in the resolution) | `Lib/Math/Geometry/Topology/ContinuityOpenSet.lean:83 continuous_preimage_dyadicopen`, `:173 preimage_dyadicopen_uniform_continuous_of_modulus`, `:191 continuous_uniform_open_witness_shift` | **∅-axiom PURE, scanned 11/0** ✓ |
| `∂²=0` at every scale = the `q=±1` orientation sign-cancel | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 dsq_zero_universal_delta4`, `:62 leibniz_universal_delta4` | **∅-axiom PURE, scanned 5/0** ✓ |
| the boundary `∂`/`δ` (`H(K_i)` is built from this) | `Lib/Math/Cohomology/Delta/Core.lean:54 delta`, `:42 deltaAt` | **∅-axiom PURE, scanned 10/0** ✓ |
| cross-frame | `homology.md` (`ker δ/im δ` at one scale, `∂²=0`, `Residue(L↓,C)`), `spectral_sequences.md` (the residue + the resolution dial `IsResolutionShift_compose`), `continuity.md`/`derivative.md` (the resolution axis), `golden_ratio.md`/`gaussian_clt.md`/`differential_equations.md` (`q=+1` Banach fixed point), `cardinality.md` (`q=−1` escape) | prior, ∅-axiom ✓ |

**Fresh purity scan (this session, `tools/scan_axioms.py` from repo root with the `E213.` module prefix):**
`E213.Lib.Math.Cohomology.Examples.BettiKernel` **11/0**; `E213.Lib.Math.Cohomology.Examples.NonzeroBetti`
**56/0**; `E213.Lib.Math.Analysis.ResolutionShift` **17/0**; `E213.Lib.Math.Foundations.ResidueTag` **55/0**;
`E213.Lib.Math.Probability.Limit.DyadicCompletion` **32/0**; `E213.Lens.Foundations.ResidueReentry` **14/0**;
`E213.Lens.Foundations.FlatOntologyClosure` **7/0**;
`E213.Lib.Math.Geometry.Topology.ContinuityOpenSet` **11/0**; `E213.Lib.Math.Cohomology.Delta.V4Capstone`
**5/0**; `E213.Lib.Math.Cohomology.Delta.Core` **10/0** — all pure, 0 dirty. The purity claim rests on the
fresh scan, not docstrings.

### Dropped / flagged (predicted-not-built — honest, grep-confirmed absent)

- **No named persistent-homology object in `lean/E213`.** Grep for `persistentHomology`/`persistence`/
  `PersistenceModule`/`PersistenceDiagram`/`barcode`/`Barcode`/`intervalModule`/`IntervalModule`/`bottleneck`/
  `persistence_diagram` returns **zero Lean declarations**. The grep for `filtration` returns only incidental
  docstring comments — the load-bearing one being the *physics* interpretive comment
  `Lib/Physics/AlphaEM/LoopVertexGraduation.lean:44` ("Filtration spectral sequence … recorded at the
  interpretive level, NOT a derivation"), which itself flags the object as unbuilt. Flagged predicted-not-built,
  exactly as `spectral_sequences.md`/`homology.md` flag their absent named objects.
- **No filtered complex `K₀⊆K₁⊆…` with scale-indexed homology, no inclusion-induced persistence module
  `H(K_i)→H(K_j)`, no barcode/persistence-diagram object, no interval-module decomposition theorem, no
  bottleneck metric.** The homology groups exist (`Cochain`, `delta`, `kerSizeDelta`, Betti via `BettiKernel`/
  `NonzeroBetti`) but at a *single* complex, not graded by a filtration scale; there is no chain of inclusions
  assembled into a one-parameter family, and no `dim H_k(K_i)`-as-a-sequence object. This is the precise missing
  leg — the filtered-complex twin of `spectral_sequences.md`'s missing `E_r`-with-`d_r` and `homology.md`'s
  missing graded `Ext^n`. The *residue* (`reduced_betti_d4_contractible`, `kerSizeDelta`), the *resolution
  shift* (`IsResolutionShift_compose`), the *`q=±1` long/short tag* (`ResidueTag`, `golden_is_converge` /
  `residue_reentry_never_closes`), the *continuity/stability* (`continuous_preimage_dyadicopen`), and the
  *`∂²=0` per scale* (`dsq_zero_universal_delta4`) are each built and PURE; only the named filtered-family object
  is open.
- **The structure theorem (module = ⊕ interval-modules) — ABSENT as a theorem.** The per-scale `ker/im`
  residue data is built (`kerSizeDelta`, `reduced_betti_d4_contractible`); the statement that a persistence
  module over the resolution line splits uniquely into interval modules is conceptual at the named-object level
  (no `IntervalModule`/`⊕`-decomposition Lean def). Same shape as `spectral_sequences.md`'s missing
  `E_∞ ≅ gr_F(H*)` abutment isomorphism.
- **The Vietoris–Rips / Čech construction of the filtration from a point cloud** (a metric-thresholded complex
  `K_ε = {simplices with diameter ≤ ε}`) is the additional `Real213`-cut / metric residue shared with the whole
  geometry cluster (no metric point cloud, no continuous threshold `ε`) — not a structural gap in the discrete
  reading, the same reached-by-none completion the geometry cluster shares.

### Named buildable witness (for the orchestrator)

**A two-step filtration on the built Δ⁴/`NonzeroBetti` cochain complex exhibiting one birth–death bar** — the
persistent-homology analogue of `NonzeroBetti`'s nonzero-`H¹` witness, decidable and `Quot`-free. Take the
hollow triangle `S¹=∂Δ²` (where `NonzeroBetti.betti_one_cycle` gives `b₁=1`, PURE 56/0) as `K₁`, and the
filled triangle Δ² (contractible, `BettiKernel`-style `b₁=0`, PURE 11/0) as `K₂ ⊇ K₁`. The inclusion
`K₁ ↪ K₂` fills the 2-cell, so the `H₁` class **born** at `K₁` (`b₁=1`) **dies** at `K₂` (`b₁=0`): one bar
`[1,2)`, a `q=−1` short transient that the structure-theorem witness would record as a single interval module.
Both endpoints' Betti data are already PURE (`NonzeroBetti` 56/0, `BettiKernel` 11/0); the missing piece is a
small `Filtration`/`Barcode` def welding the inclusion-induced map `H₁(K₁) → H₁(K₂)` (the `IsResolutionShift`
of grade 1, `ResolutionShift` 17/0) into a named birth–death pair — buildable from the existing PURE data, the
exact `IsResolutionShift_compose`/`kerSizeDelta` join, not a one-line `decide`. Pairs with the `q=±1` lifetime
tag (`ResidueTag` 55/0): this bar is `q=−1` (short, dies); a non-filled `K₂` would leave it `q=+1` (long,
survives). The structure theorem (full ⊕-decomposition) and bottleneck stability metric remain open, the named
one-parameter-family bundle leg.
