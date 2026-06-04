# G189 — The geodesic-Lens view of the Markov frontier: where stable-norm / Christoffel sits

Tier-1 frontier analysis (not a closed result).  Applies the Raw/Lens + mediant-engine viewpoint
(`theory/essays/the_modular_geodesic_lens.md`, `Real213/ModularGeodesicLens`) to the open Markov
uniqueness kernel `H` (`markovMaxUnique_iff_orbitRealizabilityH`, the frontier `(C)` of
`theory/math/analysis/markov_uniqueness.md`).  Goal: locate *exactly* which part of the classical
stable-norm / Christoffel route is `∅`-axiom-reachable and which is genuine import, by reading the
Markov tree through three Lenses of one Raw/Stern-Brocot object.

## Three Lens readings of one tree

The Markov tree is one object — a `Raw`/Stern-Brocot tree, paths `p : List Bool` — read three ways:

| reading | Lens | Lean | what it is |
|---|---|---|---|
| **slope** | mediant / difference | `markovRes p = (mNode p).d − (mNode p).c`, `slopeEq` | the geodesic's *direction* `u/c` (the rational it codes) |
| **word** | cutting-sequence | the path `p : List Bool` itself (`mInterval`) | the geodesic's *symbolic coding* = the Christoffel word |
| **size** | trace | `markovNum p = (mNode p).c = tr(mNode p)/3` | the geodesic's *length* = (the discrete shadow of) the **stable norm** |

The mediant engine `ModularGeodesicLens.mediantLens_view_reachable` is the Raw-level source of the
**word/slope** pair: a Raw tree reads to a Stern-Brocot position; its path is the cutting sequence, its
fraction is the slope.  `markovNum`/`markovRes` are the Markov-tree refinement carrying the **size**.

## Where the kernel sits, in this decomposition

What is `∅`-axiom (closed):

  * **slope reading is injective** — `slope_path_inj` (`slopeEq (mNode p) (mNode q) → p = q`), powered by
    the Frobenius determinant identity (`§6`, "the monotonicity engine": `markovRes` cross-determinant
    `= m_l`) + strict slope monotonicity (`§7–§8`, `u_t·m_r < u_r·m_t`, both halves).  *Equal direction
    ⟹ same geodesic.*
  * **mediant is the strict max** — `mNode_max` (`(mInterval p).i.c < (mNode p).c`).  *Size grows down
    the tree.*
  * **word reading lands in the Farey set** — `mediantLens_view_reachable`.

What is open (`H`): the **size reading is injective** — two paths with the same `markovNum` (max value)
coincide.  Crucially this is *not* slope-injectivity: `slope_path_inj` gives "equal slope ⟹ same path,"
but the conjecture is "equal **size** ⟹ same path," and a single `c` could a priori sit at two
*different* slopes.  In the orbit language (`markovMaxUnique_iff_orbitRealizabilityH`): the `2^{ω−1}`
windowed `±`-suborbits are distinct slopes, and `H` asks that at most one carries a realised size-`c`
triple.  So **the kernel is precisely the missing link between the slope reading (closed) and the size
reading (open)** — and that link is exactly what the stable-norm / Christoffel literature supplies
classically.

## The stable-norm / Christoffel content, read 213-natively

Classical (Lee–Li–Rabideau–Schiffler and the Markov-spectrum tradition): the Markov number is the
**stable norm** of the cohomology class of the geodesic of slope `u/c` on the once-punctured torus; the
uniqueness conjecture is the statement that the stable norm is **strictly monotone along Stern-Brocot
directions** (equivalently, the Christoffel-word ↦ Markov-number map is injective).

In the three-reading frame this says: the **size reading is a monotone function of the slope reading
along each Stern-Brocot line**.  That monotonicity, *if* it held strictly, would upgrade
`slope_path_inj` (slope injective) to `markovNum` injective and close `H`.

Two layers of this content — but NOT a "analytic = import, discrete = native" boundary (that boundary
is itself the conventional reflex this project exists to test):

1. **The stable norm itself is already native.**  The stable-norm *value* of the primitive class of
   slope `u/c` is the Markov number — `markovNum p = (mNode p).c`, an integer continuant, present in the
   repo.  What is conventionally real-analytic is not the value but one *proof method* for its
   monotonicity (convexity of the stable-norm unit ball on `H¹(torus; ℝ)`).  "The stable norm needs
   analysis" classifies a *proof method* as a *theorem requirement* — the External-classification
   reflex, not a verified `∅`-axiom ceiling.  The internal precedent is exactly this tree: the
   *slope*-monotone recovery (Zhang Lemma 2), framed analytically in the literature, was done `∅`-axiom
   by discrete slope-separation (`slope_path_inj` + `§6–§8`, one Frobenius determinant identity).  So
   whether the *size*-monotone analog has a discrete (continuant) proof is **open, not ruled out**;
   labelling it "import" imports the reflex.  (Where the honesty bites instead: slope-separation is a
   *local* determinant inequality, while size-monotonicity across slopes is *global* — genuinely harder,
   no discrete proof known to anyone yet.  "Route unknown, suspect discrete structure" — per the repo's
   algebraic-priority principle — not "out of reach," and not "almost there.")

2. **The discrete shadow is in hand.** — the size reading `markovNum p = (mNode p).c` is a **continuant**:
   an integer entry of a product of the generators `genL = [[2,1],[1,1]]`, `genR = [[3,4],[2,3]]`.  Its
   monotonicity along a Stern-Brocot coordinate line is an **integer-recurrence** statement on
   continuants — the same arithmetic `slope_path_inj` already runs.  This shadow is `∅`-axiom-shaped.

## The formalizable brick (and its honest ceiling)

The `∅`-axiom-reachable target is **continuant monotonicity along Stern-Brocot lines** — the discrete
shadow of (1), i.e. the Aigner constant-numerator / constant-denominator / constant-sum monotonicity
statements, whose classical proofs run on continued fractions / continuants (integer recurrences), not
on the metric stable norm.  The repo already carries the engine (the Frobenius determinant identity, the
`genL`/`genR` products, `mNode_max`).

**Landed (the descent half, `§30` of `SternBrocotMarkov`).**  `markovNum_lt_extend` (`(mNode p).c <
(mNode (b::p)).c`) and `markovNum_lt_append` (strict increase along any descent) — the size reading is
strictly monotone *down* the tree, `∅`-axiom, *immediately* from `mNode_max`.  This is the honest
measure of how far the discrete machinery reaches alone: **all the way down a line, none of the way
across lines.**  Descent monotonicity is essentially `mNode_max` repackaged; the cross-line comparison
(different slopes, related positions) is a *global* statement `mNode_max` does not see — it is the
Aigner content proper, and the open kernel.

**Honest ceiling (do not misread this as a path to `H`).**  Aigner monotonicity along the three line
families is *weaker* than uniqueness — it constrains collisions only *within* a Stern-Brocot line, and
is already a classical theorem; it does **not** imply `H`.  The residual after it is the same kernel
isolated before: which `ℤ` lift of a mod-`c` residue survives the full Vieta descent (the `mod c ↔ ℤ`
gap), i.e. collisions *across* lines.  So the brick is a genuine `∅`-axiom result *adjacent* to the
frontier and a clean test of the size-reading machinery — not a reduction of the conjecture.

## Verdict

The geodesic-Lens viewpoint does not move `H`; it **names its position sharply**: `H` is the
size-reading's injectivity, the one reading of the three not yet closed.  The classical route to it
(stable-norm monotonicity) is conventionally proved by real analysis (convexity of the norm ball), but
the stable-norm *value* is already the native integer `markovNum`, and — by the precedent of
`slope_path_inj` discretising the analytically-framed Zhang Lemma 2 — whether the monotonicity itself
admits a discrete/continuant proof is **open, not out of reach**.  Aigner's within-line monotonicity is
the `∅`-axiom-reachable piece (continuants), classically proven but weaker than `H`.

Acting on it (this round) landed the **descent half** (`§30`: `markovNum_lt_extend`,
`markovNum_lt_append`) — size strictly monotone down the tree, free from `mNode_max`.  That is the
honest boundary the discrete machinery reaches alone: descent is `mNode_max`; the *cross-line* Aigner
comparison (the within-line monotonicity across the `(p,q)` grid, and beyond it the across-line kernel)
is a global statement `mNode_max` does not supply — the genuine wall, still the open `H`.  So the
discrete structure goes exactly as far as the tree's order relation and no further on its own; closing
the cross-line gap needs a new global argument (continuant comparison across incomparable nodes), not a
repackaging of what is here.

## Cross-domain tool inventory (broad survey — what each area gives the cross-line wall)

A sweep of Real213/Analysis, Cohomology, GRA, and Algebra213, asking *which existing machinery is the
right type of tool for comparing the size of two **incomparable** Stern-Brocot nodes*.  Verdict per
area — candidates, not proofs (the cross-node argument remains unbuilt; no domain hands it over free):

- **Casoratian / C-finite (`Cauchy/`) — the genuine candidate.**  `casoratian_step`, `telescope`
  (`CasoratianStep`), `second_casoratian` / `hankel3` (`SecondCasoratian`, the order-3 Casorati
  determinant conserved at SL₃), `CFiniteZ` + orbit dimension (`OrbitDimension`), and the Cassini
  ladder `cassini_general : L(n)·L(n+2) − L(n+1)² = d` (`Mobius213/Px/CharPolySelf`).  This is the
  *discrete-Wronskian* apparatus — comparing two solutions of a linear recurrence by a determinant.
  **Key identification**: the tree's own monotonicity engine `markovRes_cross`
  (`u_r·m_t − u_t·m_r = m_l`, `§6`) and `markovRes_cross_left` *are* a Casoratian — the Wronskian of the
  number-sequence `m` and the residue-sequence `u`, both solutions of the order-2 residue recurrence
  (`markoff_res_vieta`, `tr·· − ··`).  A Stern-Brocot **line** is a fixed transfer-matrix iterated, so
  `markovNum` along it is `C-finite` (an entry of `M·T^n`); comparing two *incomparable* lines is two
  different transfer products — exactly what a Casoratian *can express*, and exactly the argument not
  yet written.

- **Cohomology mediant functor — a parallel, not a transfer.**  `MediantCohomologyFunctor` splits cell
  counts under the mediant by a **Vandermonde-2** law (`binom(a+b,2) = binom a 2 + binom b 2 + a·b`;
  `edgeCount_mediant` 4-term, `faceCount_mediant_factored` 9-product).  The mediant recursion is the
  *same* operation, but the invariant is a *count*, not the node *size* — structurally suggestive (the
  mediant has a determinantal/Vandermonde shadow), not a size-comparison tool.  `CrossProductAxes`
  (`CrossAddress` = bipartite × tripartite × P-orbit depth) gives a triple *address* but no size order.

- **GRA — the `P`-backbone, no order.**  Graded residue arithmetic on the coprime grades `(NT,NS)=(2,3)`,
  forced by `det P = 1` (`gradeLens = ⟨2,3,+⟩`, `canonicalGradeMap_universal`, five-Reading
  universality).  This is *why* the Markov coefficient is `NS = 3` and why the whole cluster is one `P`
  — the structural context, but GRA carries only the depth `⌈n/3⌉`, no ordering/recurrence for the
  cross-line comparison.

- **Algebra213 — a norm parallel, a different norm.**  `normSq_mul : N(uv) = N(u)·N(v)` (Hurwitz
  multiplicativity, generic across the Cayley-Dickson tower).  The Markov number *is* a norm value (the
  golden/silver forms `m²−mk−k²`, `x²−2y²` are `ℤ[φ]`/`ℤ[√2]` norms, `GoldenFormMarkov`), so norm
  multiplicativity is conceptually adjacent — but Algebra213's norm is the division-algebra norm, not
  the stable norm on `H¹(torus)`; a structural rhyme, not a direct tool.

**Net.**  The broad survey confirms the earlier verdict precisely: the repo *has* the right *type* of
instrument for the cross-line wall — the Casoratian/C-finite determinant apparatus — and the tree's
existing Frobenius identities are already Casoratians.  What no area supplies is the *aiming*: an actual
determinant comparison between two incomparable transfer products (the constant-sum Aigner line and
beyond).  That is the one new argument; everything around it is in hand.

### Pointers
- engine: `Real213/ModularGeodesicLens` (`mediantLens`, `mediantLens_view_reachable`)
- slope reading closed: `Real213/SternBrocotMarkov` `slope_path_inj`, `§6–§8` (`markovRes_cross` = the tree Casoratian)
- size reading: `markovNum`, `§30` (`markovNum_lt_extend`, `markovNum_lt_append`, descent done), open kernel
  `markovMaxUnique_iff_orbitRealizabilityH`, `OrbitRealizabilityH`
- candidate cross-line tools: `Cauchy/{CasoratianStep, SecondCasoratian, OrbitDimension}`,
  `Mobius213/Px/CharPolySelf` (`cassini_general`), `Linalg213/FibCassiniDet`
- structural parallels: `Cohomology/MediantCohomologyFunctor` (Vandermonde-2 mediant), `GRA/` (the
  `(2,3)=P` backbone), `Meta/Algebra213` (`normSq_mul`, the norm rhyme)
- narrative: `theory/essays/the_modular_geodesic_lens.md`, `theory/math/analysis/markov_uniqueness.md`
- prior frontier notes: G167 (geodesic-flow framing, out of scope), G173/G174 (Markov uniqueness)
