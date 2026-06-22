# Decomposition: Ramsey theory / extremal combinatorics (R(s,t), pigeonhole, Turán, Szemerédi/vdW, the probabilistic-method lower bound)

*213-decomposition of "order is unavoidable in large structures" — Ramsey's theorem, the pigeonhole
principle, the extremal threshold (Turán / Sperner-LYM / Bollobás), monochromatic arithmetic
progressions (van der Waerden / Szemerédi), and the probabilistic lower bound — per `../README.md`
(model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`, the REVELATION rule) and `../SYNTHESIS.md` (the two
invariants, the q=±1 spine). Honest grounding note up front: this field is **substantially BUILT**
∅-axiom — Pigeonhole (`exists_collision`), the probabilistic method (`erdos_schema`), the named Ramsey
lower bound (`ramsey_lower : R(k,k) > N`), and the extremal-boundary corpus (Sperner / LYM / Bollobás)
all ship PURE. The single missing named object is **Turán's `ex(n,K_r)`** and the **van der
Waerden / Szemerédi monochromatic-AP** statements; the pigeonhole *base* and the union-bound *engine*
they run on are built.*

## The thesis

Ramsey theory is the calculus's **q=±1 unavoidability threshold — the forced-structure pole read at
finite size.** The count-reading (`cardinality.md`) has two poles. Below a finite threshold its residue
**escapes** (q=−1): a coloring exists that dodges all monochromatic structure — disorder is available.
At and above the threshold the escape is **closed off** (q=+1): every coloring is forced to contain the
structure — order is unavoidable. Ramsey's theorem names the threshold; pigeonhole is its base case;
Turán/Sperner-LYM is the extremal boundary between the poles; the probabilistic lower bound is the
below-threshold escape made quantitative.

## The decomposition

- **Construction `C`** — distinguishing, the bare act, iterated into a **finite labelled family**: a
  complete graph `K_n` is the family of all pairs of `n` distinguishables (each pair an edge), and a
  **2-coloring** is a `Bool`-reading on those edges. In the repo's COUNT carrier this is *literal*: an
  edge-coloring of `K_N` is a `Bool` vector over the `C(N,2)` edges, `allBoolLists (binom N 2)`
  (`RamseyNamedBound.lean`), and the `C(N,k)` candidate cliques are `Sperner.kLayer N k`. Pigeonhole's
  `C` is the same family read one level down: `n+1` items distinguished, dropped into `n` boxes — a map
  `Fin (N+1) → Fin N` (`Pigeonhole.lean`). The directed/arithmetic variant (vdW) is the same family
  carrying an *order* sub-structure (an arithmetic progression = a swap-stable directed sub-family).

- **Reading `L_count`** — the **count-reading**, the same count-Lens `cardinality.md` rides, read at
  **finite resolution against a threshold**. `L_count` tallies how many of the `2^{C(N,2)}` colorings
  avoid every monochromatic clique. The decisive parameter is the **threshold comparison** `t·c < 2ⁿ`
  (`erdos_schema`): a *deficit* (bad events occupy fewer than all colorings) leaves a good coloring; a
  *surfeit* (bad events cover everything) forces the structure. This is precisely the resolution dial of
  the count-reading promoted to a **condition**, exactly as `topology.md`'s open-set dial and
  `measure.md`'s weight dial were.

- **Residue `Residue(L_count, C)` — q=±1, read at finite size:**
  - **q=−1 (escape, below threshold)** — the count-reading forces a coloring *outside* the union of all
    "monochromatic-on-S" events: a structure-dodging witness. This is `cardinality.md`'s escaping
    diagonal (`no_surjection_of_fixedpointfree`, `object1_not_surjective`) read at **finite resolution**
    — the bad events miss something, so a good object is left over (`deficit_exists`). The probabilistic
    lower bound `R(k,k) > 2^{k/2}` *is* this escape, certified: `ramsey_lower` (a 2-coloring of `K_N`
    with no monochromatic `K_k`).
  - **q=+1 (converge/unavoidable, above threshold)** — past the threshold the escape is closed: every
    coloring is forced to contain the monochromatic clique. The reading cannot dodge — the residue
    *converges* onto the forced structure, the finite cousin of the q=+1 fixed-point pole
    (`golden_is_converge`). Pigeonhole's `exists_collision` is this pole at the base: `N+1` into `N`
    forces a collision, no coloring escapes.

## Re-seeing — `⟨C | L_count⟩ ⊕ Residue(q=±1)` at the finite threshold

```
  K_n 2-coloring        =  ⟨ pairs of n distinguishables | Bool-edge-reading ⟩    (C; allBoolLists (binom n 2))
  pigeonhole (base)     =  ⟨ N+1 items | count into N boxes ⟩ ⊕ forced collision  (exists_collision; q=+1 at base)
  threshold t·c < 2ⁿ    =  the count-reading's resolution dial, as a CONDITION    (erdos_schema hypothesis)
  below threshold       =  Residue q=−1 ESCAPE: a structure-dodging coloring EXISTS (ramsey_lower; deficit_exists)
  R(k,k) > 2^{k/2}      =  the q=−1 escape, named & CLOSED                         (ramsey_lower)
  above threshold       =  Residue q=+1: NO coloring escapes — structure forced     (the unavoidability pole)
  extremal boundary     =  the threshold itself: max structure-free size            (Turán/Sperner/LYM/Bollobás)
  Sperner C(n,⌊n/2⌋)    =  the extremal antichain bound = the dual double-count      (sperner_theorem; lym_antichain)
  Bollobás C(a+b,a)     =  the cross-intersecting extremal bound                     (bollobas_uniform)
  Erdős–Szekeres        =  forced monotone subsequence = pigeonhole on (inc,dec)     (erdos_szekeres)
  van der Waerden / Sz. =  the threshold on the DIRECTED (AP) sub-family            (ABSENT — predicted)
```

The proof-ISA records the same split independently and prior to this decomposition: the Ramsey **lower**
bound is COUNT's *union-bound face* (escape), Sperner's **upper** bound is its *dual double-count face*
(boundary) — `Combinatorics/INDEX.md` §"COUNT" states both named bounds closed ∅-axiom. That the
field's two halves land on the two faces of one instruction is the collapse, not a re-skin.

## Revelation (collapse + forcing + the q=±1 spine)

**Ramsey theory is one reading — the count-reading at a finite threshold — read at its two poles, with
no new primitive.** Three classically-separate theorems fuse:

1. **Pigeonhole = the q=+1 forcing base, the count-reading's own diagonal at finite resolution.**
   "`N+1` items in `N` boxes force a collision" is `cardinality.md`'s "the count-reading forces a value
   outside its image" run *finitely*: where Cantor's diagonal escapes to an uncountable residue
   (`no_surjection_of_fixedpointfree`), the finite carrier folds the escape *back in* — there is no room
   for an injection, so a coincidence is forced. The repo proves *both* the negative (no injection,
   `no_inj_succ`/`no_inj_lt`) and the **constructive positive** (`exists_collision` *exhibits* the
   colliding pair via a decidable `scan` + `shiftAround`, no `Classical`). Pigeonhole is therefore the
   *converging* (q=+1) face of the very engine whose *escaping* (q=−1) face is the uncountable: same
   `(C, L_count)`, the residue folded back at finite size. `DividesPairPigeonhole.exists_dvd_pair`
   ("among `n+1` numbers in `[1,2n]`, one divides another") is the same theorem with the boxes = the `n`
   odd parts — pigeonhole forcing a *number-theoretic* coincidence, the witness computed.

2. **Ramsey's threshold = the resolution dial promoted to the unavoidability condition.** The whole
   field is the count-reading's resolution parameter made a *condition* `t·c < 2ⁿ` — exactly the move
   `topology.md` (open set), `measure.md` (measurable), and `continuity.md` (continuous map) each made
   with the *same* dial. Below the threshold the residue **escapes** (q=−1) — a coloring dodging all
   structure exists (`deficit_exists`, `count_existence`, `erdos_schema`); above it the escape is closed
   and structure is **unavoidable** (q=+1). The threshold `R(s,t)` is the *exact finite size at which the
   q=−1 escape flips to the q=+1 forced pole* — the new datum: Ramsey theory is not a new field but the
   **flip-locus** of the count-reading's residue tag, read at finite size.

3. **The probabilistic lower bound = the q=−1 escape, named and CLOSED.** Erdős' `R(k,k) > 2^{k/2}` is
   the deficit-existence residue made quantitative: a *random* coloring avoids monochromatic cliques with
   positive probability ⟺ the bad events occupy `t·c < 2ⁿ` of the colorings ⟺ a good coloring is *left
   over* and *found by finite search*. The repo cashes the full chain ∅-axiom: `erdos_schema` (the
   probabilistic method as one theorem, the uniform union bound), the per-event count
   `mono_event_count`/`matchesC_count` (free edges double — `count_factor` — the constrained block
   constant in 2 ways), and the named `ramsey_lower`. The "probability" here is `probability.md`'s
   composite weight-reading `ratio ∘ count` at its purest: a *uniform* count over `allBoolLists`, no
   `Ω`/σ-algebra — the weight axis is the count itself. Independence (free edges multiply, `2^r`) is the
   `×↦·` character (`SYNTHESIS.md` Invariant A) read on the colouring count.

4. **The extremal boundary = the threshold itself, the dual double-count face (q=+1 saturation).**
   Turán's "max edges with no `K_r`" is the *boundary value* between the two poles — the largest
   structure-free configuration, i.e. the threshold read from below. The repo does not have Turán's
   `ex(n,K_r)` *by name*, but it has the **same extremal-threshold shape proven for the set-system
   siblings**: Sperner's `|F| ≤ C(n,⌊n/2⌋)` (max antichain — the extremal *antichain* bound,
   `sperner_theorem`), its per-term refinement LYM (`lym_antichain`, with the tightness/equality case
   `lym_tight_layer` = the extremal configurations are the middle layers), and Bollobás'
   cross-intersecting `|F| ≤ C(a+b,a)` (`bollobas_uniform`). These are all the **q=+1 saturation pole**:
   a maximum forced by the dual double-count (each maximal chain meets the antichain ≤ once), the
   *contrapositive* of the union-bound escape — the same duality `topology.md` records (compactness =
   the contrapositive of the cardinality escape). The proof-ISA names this explicitly: Ramsey-lower =
   union bound, Sperner-upper = its dual double count.

**The q=±1 spine, instanced.** `cardinality.md` (Cantor) sits at the q=−1 escape on an *infinite*
carrier; Ramsey theory is the *same residue at finite size*, where the threshold makes the sign
**switchable**: below it the escape survives (q=−1, `ramsey_lower`), above it the escape is folded back
and structure converges (q=+1, the unavoidability pole — pigeonhole `exists_collision` is its base). So
Ramsey theory adds to the spine the reading where **both signs of the one residue are visible at once**,
separated by a finite number — the threshold. "Order is unavoidable in large structures" = "the
count-reading's q=−1 escape has a finite ceiling, above which it flips to q=+1." This is the count-Lens
diagonal read on the *forced* side, exactly the brief's thesis, and it is the load-bearing new datum
distinguishing this note from `cardinality.md` (which read only the q=−1/infinite pole) and from
`game_theory.md`'s `mex` (which read the bounded diagonal but not the threshold flip).

## VALIDATE — verdict

**EXTEND (by consolidation) + PARTIAL, strongly BUILT.** Ramsey theory introduces **no new axis and no
new primitive**: it is the count-reading (`cardinality.md`) + its q=±1 residue tag (`ResidueTag`) +
the resolution dial promoted to the threshold condition (the same move topology/measure/continuity
made) + the `×↦·` independence character on the colouring count. Reasons it is confirmation, not stress:

1. **Pigeonhole = the count-diagonal at finite resolution**, the q=+1 fold-back of `cardinality.md`'s
   q=−1 escape — built both negatively (`no_inj_lt`) and constructively (`exists_collision`), and reused
   number-theoretically (`exists_dvd_pair`).
2. **The probabilistic method is one ∅-axiom theorem** (`erdos_schema` / `count_existence`), the
   deficit-existence residue = q=−1 escape at finite size, with the named bound `ramsey_lower` closed.
3. **The extremal boundary is built for the set-system siblings** (Sperner/LYM/Bollobás) as the q=+1
   saturation pole = the dual double-count, with the equality/tightness case (`lym_tight_layer`).
4. **Erdős–Szekeres** (`erdos_szekeres`) is forced-monotonicity = pigeonhole on the `(inc,dec)` label
   box — the threshold flip on the *ordered* sub-family, the structural rehearsal vdW would complete.

**The PARTIAL / honest residual — precisely located:**
- **Turán's theorem by name (`ex(n,K_r)`, the K_r-free max-edge graph) is ABSENT** — grep over
  `lean/E213` for `turan`/`turán`/`extremal graph` returns nothing (the only `Extremal` file is
  `Real213/Minkowski/MinkowskiGoldenExtremal.lean`, unrelated). The *extremal-threshold shape* is built
  for antichains and set-pairs (Sperner/LYM/Bollobás), and the graph-edge carrier `allBoolLists (binom
  N 2)` is in hand (`RamseyNamedBound`), so Turán is a **predicted-buildable** target on existing infra,
  not a structural gap — but it is not yet a stated theorem.
- **Van der Waerden / Szemerédi (monochromatic arithmetic progressions) are ABSENT** — grep for
  `vanderWaerden`/`van der Waerden`/`Szemeredi`/`Szemerédi`/`monochromatic` returns no field file. This
  is the *directed/order sub-structure* variant of the threshold (an AP = a swap-stable directed
  sub-family); the order sub-structure of `C` is built (`integers.md`, `ErdosSzekeres`), but no AP /
  density-threshold statement exists. The hardest leg (Szemerédi's density regularity) would face the
  same arbitrary-cover/infinite-quantifier wall `topology.md`/`measure.md` located — a calibrated
  residual, not a finite COUNT object.

**No BREAK.** The normal form `⟨C | L_count⟩ ⊕ Residue(q=±1)` covers every built leg; the absences are
*named field objects on existing infra* (Turán) and the *density/order variant* (vdW/Szemerédi), the
same predicted-not-built shape as `game_theory.md` (the `Game` object) and `surreal.md` — not the
isotopy/colimit-quotient break (`knots.md`) nor the propext ceiling. The two invariants and four axes
are unchanged in the interior.

---

## Verified Lean anchors (file : line : theorem) — all grep-confirmed + scan-tallied

All scans run `python3 tools/scan_axioms.py <module>` from repo root.

**Pigeonhole — the count-forcing base (q=+1 fold-back), `Pigeonhole.lean` (5/0 PURE):**
- `Lib/Math/Combinatorics/Pigeonhole.lean:81` `no_inj_succ` — no injection `Fin (N+1) → Fin N` (the
  negative/forcing form).
- `:112` `no_inj_lt` — generalized: no injection `Fin k → Fin N` when `N < k`.
- `:136` `scan` — decidable bounded membership scan (no `Classical`), the constructive engine.
- `:166` **`exists_collision`** — *exhibits* the colliding pair for any `g : Fin (N+1) → Fin N`
  (constructive pigeonhole — the q=+1 forced coincidence, witness computed).
- `:198` `exists_collision_lt` — the `N < k` constructive form.

**Pigeonhole forcing a number-theoretic coincidence, `DividesPairPigeonhole.lean` (7/0 PURE):**
- `Lib/Math/NumberTheory/DividesPairPigeonhole.lean:109` **`exists_dvd_pair`** — among `n+1` numbers in
  `[1,2n]`, one divides another; pair *computed* (odd-part map collides via `exists_collision`, `:57`
  `same_oddpart_dvd` reads off divisibility). The count-reading forcing a coincidence on a non-graph
  carrier.

**The probabilistic method = the q=−1 escape engine, `CountExistence.lean` (10/0 PURE):**
- `Lib/Math/Combinatorics/CountExistence.lean:93` `union_bound` — `bcount(anyBad) ≤ Σ bcount` (the
  union bound).
- `:114` **`deficit_exists`** — deficit ⟹ a good object EXISTS, by finite search (no `Classical`) — the
  q=−1 escape made constructive.
- `:136` `count_existence` — the COUNT instruction: `Σ bcount < 2ⁿ ⟹ ∃ colouring avoiding all`.
- `:192` **`erdos_schema`** — the probabilistic method as one theorem: `t·c < 2ⁿ ⟹` a dodging colouring
  exists. (The threshold condition = the resolution dial promoted to a condition.)

**Ramsey lower bound — the named q=−1 escape, CLOSED:**
- `Lib/Math/Combinatorics/RamseyLowerBound.lean` (5/0 PURE): `:42` `count_factor` (free edges double —
  the `×↦·` independence character on the count), `:64` `mono_event_count` (per-event `2·2^{E−m}`),
  `:101` `matchesC_count` (arbitrary-subset count, permutation-free).
- `Lib/Math/Combinatorics/RamseyNamedBound.lean` (13/0 PURE): `:50` `pairsCount_eq` (#internal edges of
  `S` = `C(|S|,2)`), `:130` `monoEvent_count` (per-event ≤ `2·2^{C(N,2)−C(k,2)}`), `:174` ★★
  **`ramsey_lower`** — `2·C(N,k) < 2^{C(k,2)} ⟹` a 2-colouring of `K_N` with **no monochromatic
  `K_k`** (i.e. `R(k,k) > N`; instantiating `N < 2^{k/2}` gives `R(k,k) > 2^{k/2}`). The named
  probabilistic Ramsey bound, ∅-axiom.

**The extremal boundary = the q=+1 saturation pole (dual double-count):**
- `Lib/Math/Combinatorics/Sperner.lean` (47/0 PURE): `:89` `layer_size` (#k-subsets = `C(n,k)`), `:235`
  `kLayer` (the `k`-subsets, reused as the Ramsey clique events), `sperner_upper_bound` (abstract
  reduction).
- `Lib/Math/Combinatorics/SpernerChains.lean` (50/0 PURE): `:522` `sperner`, `:534` **`sperner_theorem`**
  — Sperner's `|F| ≤ C(n,⌊n/2⌋)` proven unconditionally (the extremal antichain bound).
- `Lib/Math/Combinatorics/LymInequality.lean` (5/0 PURE): `:97` **`lym_antichain`** (`Σ |A|!(n−|A|)! ≤
  n!`), `:119` `lym_tight_layer` (the equality case — extremal configs = middle layers), `:142`
  `sperner_via_lym`.
- `Lib/Math/Combinatorics/BollobasSetPair.lean` (21/0 PURE): `:257` `bollobas` (named bound `|F| ≤
  C(a+b,a)`), `:325` `bollobas_of_count`.
- `Lib/Math/Combinatorics/BollobasCount.lean` (36/0 PURE): `:725` `favourCount_lower`, ★★★ **`bollobas_uniform`**
  — `|F| ≤ C(a+b,a)`, `n`-independent, unconditional ∅-axiom.

**Forced monotonicity (threshold flip on the ordered sub-family):**
- `Lib/Math/Combinatorics/ErdosSzekeres.lean` (26/0 PURE): `:587` **`erdos_szekeres`** — `>(r−1)(s−1)`
  distinct values force a length-`r` increasing or length-`s` decreasing subsequence (pigeonhole on the
  `(inc,dec)` label box, `exists_collision_lt`; subsequence extracted choice-free).

**The q=±1 spine the threshold rides:**
- `Lib/Math/Foundations/ResidueTag.lean` (55/0 PURE): `:133` `escape_residue_outside` (q=−1, ⟵
  `no_surjection_of_fixedpointfree` — the below-threshold escape pole), `:160` `converge_residue_fixed`
  (q=+1 — the above-threshold unavoidability pole), `:180` `golden_is_converge`, `:86`
  `multiplier_unimodular`, `:228` `residue_tag_two_poles`.
- `Lens/Foundations/OneDiagonal.lean:51` `no_surjection_of_fixedpointfree`, `:43` `lawvere_fixed_point`
  — the count-diagonal engine; pigeonhole = this at finite resolution (fold-back), Ramsey-lower = its
  escape (deficit) at finite resolution.
- `Lens/Foundations/FlatOntologyClosure.lean:61` `object1_not_surjective`, `:47` `object1_injective` —
  the residue the threshold reads at finite size.

**Cross-references (prior decompositions this note consolidates):**
- `../practice/cardinality.md` (the count-reading + its escaping diagonal — q=−1 on the infinite
  carrier; Ramsey = the same residue at finite size with a switchable sign).
- `../practice/probability.md` (the composite weight-reading `ratio ∘ count`; the probabilistic method
  is its uniform-count purest case), `../practice/graph_theory.md` (the K_n family carrier),
  `../practice/game_theory.md` (the bounded diagonal `mex`, the finite cousin without the threshold).
- `lean/E213/Lib/Math/Combinatorics/INDEX.md` §"COUNT": records Ramsey-lower = union-bound face,
  Sperner-upper = dual double-count face, both closed ∅-axiom; `theory/essays/proof_isa/probabilistic_method.md`,
  `.../lym_inequality.md`, `.../sperner_double_counting.md`, `seed/PROOF_ISA.md` (the COUNT instruction).

## Dropped / flagged (could not verify / predicted-not-built)

- **Turán's theorem `ex(n,K_r)` (max K_r-free edges) — ABSENT** (grep `turan`/`turán`/`extremal
  graph`/`K_r-free`/`max edges` over `lean/E213` → no field file; only the unrelated
  `Real213/Minkowski/MinkowskiGoldenExtremal.lean`). Flagged **predicted-buildable**: the
  extremal-threshold shape is built for antichains/set-pairs (Sperner/LYM/Bollobás), and the graph-edge
  COUNT carrier `allBoolLists (binom N 2)` already exists in `RamseyNamedBound`. No verified witness
  proposed (a Turán inequality on the edge carrier is plausible but I did not check a concrete `decide`
  bound — not asserting one).
- **Van der Waerden / Szemerédi (monochromatic arithmetic progressions) — ABSENT** (grep
  `vanderWaerden`/`van der Waerden`/`Szemeredi`/`Szemerédi`/`monochromatic`/`arithmetic progression`
  over `lean/E213` → no field file). Flagged predicted-not-built: the order sub-structure of `C` exists
  (`integers.md`, `ErdosSzekeres`), but no AP / density-threshold object; Szemerédi's density-regularity
  leg would meet the same arbitrary-cover/infinite-quantifier residual `topology.md`/`measure.md`
  located (calibrated, not a finite COUNT object).
- The named `Ramsey`/`R(s,t)`-as-a-function object is not built (only the *bound* `ramsey_lower : R(k,k)
  > N` as an existence statement); the exact Ramsey *numbers* `R(s,t)` are not a defined Lean object —
  the threshold is read as an inequality, not a computed value, the honest ceiling.
- No verified false-witness was produced; every cited theorem was grep-confirmed at the stated
  `file:line` and every cited module scanned `N/0` PURE this pass.
