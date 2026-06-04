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

The `∅`-axiom-reachable next target is **continuant monotonicity along Stern-Brocot lines** — the
discrete shadow of (1), i.e. the Aigner constant-numerator / constant-denominator / constant-sum
monotonicity statements, whose classical proofs run on continued fractions / continuants (integer
recurrences), not on the metric stable norm.  The repo already carries the engine (the Frobenius
determinant identity, the `genL`/`genR` products, `mNode_max`); a continuant-monotonicity lemma is the
natural extension of `§7–§8`'s slope monotonicity from the *direction* entry to the *size* entry.

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
the `∅`-axiom-reachable piece (continuants), classically proven but weaker than `H`.  The concrete next move, if a
frontier session wants a real brick rather than the conjecture: **formalize continuant monotonicity
along one Stern-Brocot line** (extend `§7–§8` from slope to size), banked honestly as adjacent-to-frontier,
not as progress on the kernel.

### Pointers
- engine: `Real213/ModularGeodesicLens` (`mediantLens`, `mediantLens_view_reachable`)
- slope reading closed: `Real213/SternBrocotMarkov` `slope_path_inj`, `§6–§8`
- size reading (open kernel): `markovNum`, `markovMaxUnique_iff_orbitRealizabilityH`, `OrbitRealizabilityH`
- narrative: `theory/essays/the_modular_geodesic_lens.md`, `theory/math/analysis/markov_uniqueness.md`
- prior frontier notes: G167 (geodesic-flow framing, out of scope), G173/G174 (Markov uniqueness)
