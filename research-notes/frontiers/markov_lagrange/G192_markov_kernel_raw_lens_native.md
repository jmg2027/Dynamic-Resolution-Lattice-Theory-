# G192 — The Markov kernel in Raw/Lens-native terms: where the geodesic engine reaches, and where it structurally stops

Tier-1 deep investigation (companion to `G191`, the classical/continuant side).  Two parallel surveys —
the Markov frontier objects and the Raw/Lens self-reference machinery — assembled into a precise
213-native reading of the open kernel.  **Discipline (load-bearing):** a 213-native *restatement* of `H`
is renaming, not leverage, unless it produces an actual constraint on *which residue realizes*.  Every
item below carries an explicit leverage-vs-renaming verdict; the central result is a **boundary**, and no
213-native "theorem" is manufactured where only renaming is available — the restraint is the result.

## A. The Markov tree as one Raw object, read three ways (all grounded in code)

The matrix tree is one `Raw`-flavoured binary-distinguishing object (paths `List Bool`).  Three readings,
with their *exact* Lens status:

| reading | object | Lens status (proven) |
|---|---|---|
| **slope** = `mediantLens.view` (the rational `p/q`, the geodesic *direction*) | `mediantLens : Lens (ℕ×ℕ) = ⟨(0,1),(1,0),(·+·,·+·)⟩` | **genuine Raw-Lens** — mediant combine commutative (`mediant_sym`), homomorphic (`mediantLens_view_slash` via `Raw.fold_slash`), image ⊆ Stern-Brocot (`mediantLens_view_reachable`).  **Injective** (`slope_path_inj`). |
| **size** = `markovNum p = (mNode p).c` (the geodesic *length*, the trace shadow) | matrix-product entry on the **oriented free monoid** `{L,R}* = List Bool` | **NOT a Raw-Lens** — combine = matrix product, non-commutative (`markovGen_noncommutative : mul genL genR ≠ mul genR genL`); by `combine_sym_on_image_of_homomorphism` a non-symmetric combine cannot be a homomorphic Raw-Lens. |
| **residue** = `markovRes p = (mNode p).d − (mNode p).c` (the `√(−1)` mod-`c` shadow) | a **difference** reading | difference-flavoured (cf. the ℤ difference-Lens `diffView`/`signedLens`, `Lens/Number/`); satisfies `markovRes_cross` (the Frobenius/Casoratian within-line identity). |

This makes the user's *"geodesic = 213's one engine"* intuition **precise and partly confirmed**: the
slope (the geodesic projection) is *the* residue-native (Raw-Lens) reading; everything else is an oriented
overlay above the direction-free substrate.

## B. `H` in 213-native form, and the leverage-vs-renaming ledger

Since slope determines size (`slope_determines_size`) and slope is injective, the kernel is

> **`H` = "the direction-free residue projection (slope = `mediantLens`) injectively determines the
> orientation-dependent overlay (size = `markovNum`)."**  (`markovMaxUnique_iff_markovNum_injective`, §34.)

The Raw/Lens machinery that *touches* this (exact signatures, honest verdict):

| machinery | what it fixes | decides *which residue realizes*? |
|---|---|---|
| **`object1_not_surjective`** (`Lens/FlatOntologyClosure`) — self-cover injective, non-surjective; residue = the un-pointable Cantor surplus | a **hard** cardinality gap every kernel must respect | **No** — names the gap, not who fills it |
| **difference-Lens additivity** (`difference_lens_founds_on_count`, `signedLens`) — ℤ as the count-Lens on a directed pair, slash-additive | a **hard** group law on any integer reading | **No** — fixes addition, not which integers realize |
| **`SqrtUnity` torsor + free action** (`sqrtUnity_acts_on_root`, `root_orbit_inj{,_neg}`, `nontrivial_unit_root_exists`) — the windowed `√(−1)` roots are a torsor; action free; `2^(ω−1)` disjoint ±-suborbits | a **hard** count + disjointness | **No** — fixes *how many* competitors, not *which* realizes |
| **`kernel_correspondence`** (`Lens/Algebra/Corresp`) — {slash-congruences} ↔ {Lens kernels} | the **form** of all possible quotients | **No** — *enumerates* kernels, selects none (permissive) |
| **`Raw.slash_comm` + `Raw.fold_slash` + `combine_sym_on_image_of_homomorphism`** | the **form** of readings: residue-native ⟹ direction-free | **No** — a structural gate (Raw vs non-Raw), not a selection gate |
| **`mediantLens_view_reachable`** | slope image ⊆ Farey reachable (feeds the tree) | **No** — feeds, does not exhaust |
| **cohomology δ²=0 rhyme** (`Cohomology/Delta/Core`, ℤ/2 cochains) — the ω-prime sign pattern *has the shape* of a 1-cochain; "realized by one global triple" *has the shape* of a coboundary condition | nothing yet — a **rhyme**, aligned with classical `H¹(torus)` stable norm | **No** — would need the realizability map to *be* a δ; unbuilt; rhyme, not constraint |

## C. The central finding — a boundary, not a key

Every hard 213-native constraint **fixes the structure** (the cardinality gap, the group law, the count
`2^(ω−1)`, direction-freedom) and the permissive ones **set the stage** (kernel enumeration, mediant
feeding).  **None decides the selection.**  They *narrow* the kernel — from "which Markov residues exist"
to "which of the explicit `2^(ω−1)` competitors realizes" — a genuine reduction, already captured by
`WindowRealizedUnique`/`OrbitRealizabilityH`.  But the selection itself is the residual freedom, and it is
exactly `H`.

This is **the same verdict as the classical side** (`G191`: Aigner orderings necessary-not-sufficient): the
slope ordering / the torsor structure pin everything *except* realizability.  The convergence of the two
independent analyses is a strong consistency check, **not progress** — and saying so is the honest output.

### The geodesic-engine boundary (sharp, and somewhat negative for the 1-engine bet)

The user's geodesic-as-one-engine bet is **confirmed where it can be and refuted where it can't**, with the
`DirectionFree` theorem as the *precise* boundary:

  - **Reaches** (everything direction-free): the slope reading *is* the genuine Raw-Lens (`mediantLens`),
    it lands on Stern-Brocot (`mediantLens_view_reachable`), and it is **injective** (`slope_path_inj`).
    The geodesic engine closes the entire direction-free layer.
  - **Structurally stops** (at the orientation): `H` is whether the slope pins the *size*, and size is
    **provably not direction-free** (`markovGen_noncommutative` + `combine_sym_on_image_of_homomorphism`)
    — it needs exactly the orientation the residue discards (`Raw.slash_comm`).  So the geodesic engine,
    *by its own defining direction-freedom*, cannot by itself reach the orientation-dependent
    realizability selection.  The engine's success condition (direction-free) is the engine's reach limit.

So the geodesic engine is real and maximal on its layer; `H` lives one structural level up (the oriented
free monoid `{L,R}*`), reachable only by an argument that *uses* the orientation — which is precisely what
the continuant/CF program (`G191`, the Christoffel word = the oriented run-length encoding) supplies, and
precisely why Aigner monotonicity (oriented) is the necessary-but-not-sufficient layer between them.

### The "no exterior selector" reading (methodological, not a lemma)

`05_no_exterior.md` §5.1: there is no exterior dialer.  The realized suborbit is a *point of a torsor*
(`SqrtUnity` acting freely), and a torsor has no canonical point.  So uniqueness `H` is the statement that
realizability **breaks the torsor symmetry to exactly one point** — and, by no-exterior, the symmetry-
breaker cannot be an external label; it must be the residue-internal Vieta descent.  The window already
breaks the `±1` symmetry (the `2u < c` representative choice); realizability is the residual
symmetry-breaking over the remaining `2^(ω−1)`.  This is a **steer** (consistent with the repo's
algebraic-priority / counting-first methodology), **not** a theorem, and is logged as such.

## D. Why no new ∅-axiom lemma this round (the restraint is the result)

Each candidate 213-native "theorem" — `H` as a Lens-image/realizability statement (via
`kernel_correspondence`/`object1_not_surjective`), `H` as a torsor-symmetry-breaking, `H` as a δ-coboundary
— reduces, on inspection, to **renaming** `OrbitRealizabilityH`: none adds a constraint on the selection.
Building one would be the catalogued failure mode *"View promoted to identity / renaming as explanation."*
The boundary result (C) *is* the genuine finding: the 213-native frame **locates** `H` exactly (the
orientation/realizability level, above the direction-free geodesic engine) and **explains the engine's
reach limit** structurally (direction-freedom), without pretending to cross it.

## E. Where the concrete code goes next (unchanged by this investigation)

The boundary says the kernel needs an *oriented* argument; the cheapest oriented apparatus is the
continuant/Christoffel program (`G191` E2–E5).  The next clean ∅-axiom code step remains **E2**:
`continuant K[a₁..aₙ] = (∏[[aᵢ,1],[1,0]]).(1,1)` — connecting the new `Real213/Continuant` to `Mat2`
products — the first rung of the oriented bridge `markovNum p = K(CF-shape of slope p)`.

### Pointers
- frontier objects: `Real213/SternBrocotMarkov` (`mediantLens`/`slope_path_inj`/`markovGen_noncommutative`/`SqrtUnity`/`OrbitRealizabilityH`/§34 iff)
- Raw/Lens native: `Lens/FlatOntologyClosure` (`object1_not_surjective`), `Lens/Number/DifferenceLensFounding` + `Int213/Raw` (`signedLens`), `Lens/Algebra/Corresp` (`kernel_correspondence`), `Lens/DirectionFree`, `Theory/Raw/{Slash,Fold}`, `seed/AXIOM/05_no_exterior.md` §5.1
- cohomology rhyme: `Cohomology/{Delta,Cochain}/Core` (ℤ/2 δ²=0)
- classical companion: `research-notes/G191_continuant_aigner_program.md`
