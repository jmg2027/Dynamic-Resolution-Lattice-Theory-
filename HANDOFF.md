# Session handoff

Branch: `claude/tower-research-analysis-3uWqd`

## This session — tower analysis → Raw branching → the residue → self-covering

Started as a "tower" research audit; became a foundational thread on what the
residue (the "1" in 2-1-3) is.  All commits ∅-axiom where Lean; pushed.

### Constructive deliverables (all PURE)

  - **`Theory/Raw/PrimitiveTower.lean`** (8 PURE) — the most primitive tower:
    `rawTower n = a/(a/(…/b))`, the single `slash` (self-pointing) arrow
    iterated; `depth = level`, `depth < leaves` every rung.
  - **`Lens/FlatOntologyClosure.lean`** (6 PURE) — the self-covering closure
    *limit* half: `object1_injective` (Raw self-covers as predicates,
    faithful) ∧ `object1_not_surjective` (Cantor: the predicate space is not
    in the image = the residue surplus).  `residue_witnessed` names a concrete
    inhabitant of the gap: `undifferentiated := fun _ => true` (the `Raw→Bool`
    shadow of `constLens`) — no Raw's indicator equals it.  Complements the
    pre-existing *positive* half `Lens/PredicateSelfEncoding.lean` (7 PURE,
    definable/finite-prefix predicate → Raw round-trip).
  - **`research-notes/G152_residue_self_covering.md`** — synthesis note (the
    full intellectual thread; file map; this open problem).
  - **`research-notes/data/probes/raw_branching_shape.py`** (+png) — Raw
    branching simulation, self-checks SET-EQUAL to Lean `RawDepth3.depthLe3List`.
    Findings: residue ratio → 1 (structure recedes from the complete-graph
    "void" in proportion); 1D Lens collapses |S_n| onto 2^n+1 dyadic positions;
    growth exponent = 2 = NT.
  - **`theory/essays/tower_atlas.md`** — boundary section (which repo "towers"
    are P-orbit readings vs distinct constructions); dropped deprecated N_U.
  - **`algebra_tower.md`** frontier fixed; **`G150`** trimmed.

### Where the discussion landed (for the next session)

The driving question "is the residue a GAP between 2 and 3 or the UNDIVIDED
thing both are?" dissolved, not answered:

  - "gap" is the *separation-view* reading; "undifferentiated" is the
    *non-separation-view* reading; **the residue is neither — it is what both
    views read.**  Raw has no "separation/non-separation" predicate either;
    both are Lens readings (per `seed/AXIOM/05_no_exterior.md` §5.4, §6.5).
  - Formally, only `object1_not_surjective` touches the residue *itself*: it is
    the surplus outside *every* pointing-view's image.  `object1_injective` /
    `distinct_equiv` / `residue_witnessed` are each one **view's survey**, not
    the residue.
  - The "1" (`Mobius213OneAsGlue`): `det(P) = NS − NT` proves gap = glue = the
    same 1 — the **rotation axis** 2 and 3 interconvert around, not an interval.
    0 = collapse (swap-fixed diagonal); 1 = the undivided unit.  Originator's
    own words: "1이 회전축, 2-1-3 불가분."
  - Method (Mingu): to investigate the "몰루" (the indeterminate — what cannot
    be seen as any single state) you must survey **all** sides — separation and
    non-separation views both.  Every view is a variation of the most primitive
    act = **pointing (지칭)**; "Raw = the residue of pointing" is itself the
    *most primitive view*, not a final description.

## Follow-up bricks this session (open problem RESOLVED + marathon)

  - **"One closure or two?" — answered: TWO, mutually supporting.**
    `Theory/Raw/Lambek.lean` (8 PURE): `decompose` (Lambek forward, the pointing
    act is a fixed point of its constructor shape — holds for μF and νF alike)
    + `depth_drops`/`atoms_are_floor` (well-founded, selects the LEAST fixed
    point); `two_closures` bundles them — neither implies the other, Raw = μF is
    their conjunction.  Also `self_similar_peel`/`self_similar_floor` (the floor
    = fixed shape under refinement, not a stipulated stop).
  - **Method note** `research-notes/G153_method_labelling_toward_residue.md` —
    why one slips (distributional gravity toward a fixed standpoint; 213 has
    none) + the positive method (labelling is the limit and the only method;
    many labels' common shadow narrows the residue's outline; never promote a
    shadow to identity).  CLAUDE.md gained the "View promoted to identity"
    failure mode.
  - **Marathon (3 continuations of G153, all closed):**
    · #2 `Lib/Math/Real213/ObjectIsReadingScaleInvariant.lean` (4 PURE) —
      object = reading is scale-invariant (atom `Object1 : Raw→(Raw→Bool)`;
      limit `RealAsLensOutput = Nat→(Nat→Bool)`); one shape `Index→Bool`.
    · #1 `Lib/Math/SelfSimilarityBridge.lean` (3 PURE) —
      `self_similarity_two_readings`: the form reading (Raw `self_similar_floor`)
      and the count reading (`numV(m+n) = numV m · numV n`, the `5^L`
      level-replication) are one self-similarity, two Lenses.
    · #3 `Lib/Math/DualCollapseCapstone.lean` (1 PURE) —
      `every_dual_is_one_shape`: four duals (decompose/build, object/morphism,
      object/reading, difference/identity) each one shape under the pointing
      view; the shared column made explicit (convergence evidence, not capture).

## φ-side CLOSED — self-similarity now has all three readings

`Lib/Math/SelfSimilarityBridge.lean` (5 PURE) — `self_similarity_three_readings`:
"same shape under descent" is one self-similarity from the (NS,NT)=(3,2)
signature read three ways —
  · **form** (Raw `self_similar_floor`): constructor shape invariant, atomic floor;
  · **count** (`self_similar_count`): level count replicates by `d = 5 = disc P`
    (`numV (m+n) = numV m · numV n`);
  · **limit-ratio** (`self_similar_ratio_is_phi`): the P-orbit consecutive-term
    ratio settles on the irrational fixed point φ (`tower_growth_phi_squared_bracket`
    ∈ (2,3)=φ², `phi_bracket_via_pell` brackets φ as a Cut).
The rational factor `5` and irrational `φ` are invariants of the *same* matrix P,
so the three are one self-similarity, not three coincidences.  This also realises
"걸림 = the self-fixed-point, which is why φ appears": the descent that keeps the
same shape converges to φ because φ is P's fixed point.

## φ limit-ratio PINNED (this session)

`Real213/PhiConvergence.lean` (4 PURE) + `SelfSimilarityBridge.self_similar_ratio_pins_phi`
(6 PURE in bridge): the Pell convergents form a **nested** sequence of rational
brackets (`convergents_nest`: cross-products ±1) whose widths **strictly shrink**
(`bracket_width_shrinks` via `pellDen_strictly_increasing`), pinning a *unique*
value in `[3/2, 5/3]` — φ (`phi_is_unique_nested_limit`).  Upgrades the
limit-ratio reading from "bracketed" to "pinned": a strictly-shrinking nested
rational sequence determines at most one real, and that real is φ.

## φ as a single ValidCut — DONE (this session)

`Real213/PhiAsCut.lean` (5 PURE): φ has a **closed-form decidable cut** — no
Cauchy-completion needed.  `phiCut m k := decide (k ≤ 2m ∧ 5k² ≤ (2m−k)²)` (from
`x² = x+1`: `m/k ≥ φ ⟺ (2m−k)² ≥ 5k²` with sign guard), and `phiCut_valid :
ValidCut phiCut` (both monotonicities, direct Nat arithmetic).  So the
residue's irrational limit-ratio signature is one 213-native Cut object, built
with no completion machinery.  `phiCut_brackets` cross-checks it against the
Pell convergents (8/5 < φ, 5/3 > φ, 13/8 > φ, 21/13 < φ).

The full self-similarity arc is now closed: form (`self_similar_floor`) / count
(`self_similar_count`, factor `5 = disc P`) / limit-ratio (φ, pinned by
`PhiConvergence` and realised as a Cut by `PhiAsCut`) — one self-similarity,
three readings, irrational signature a concrete object.

## φ-norm ∀n DONE; phiCut=false ∀n mechanism in place (this session)

`Real213/PhiNormInvariant.lean` (3 PURE): the φ-norm `num_n² − num_n·den_n −
den_n² = −1` for **all n** (`phi_norm_eq_neg_one`), generalising
`PhiCutConvergents.convergent_norm_form`'s layers-0..8 `decide`.  Route:
`coupling` (the `P = [[2,1],[1,1]]` matrix action `num_{n+1} = 2·num_n + den_n`,
`den_{n+1} = num_n + den_n`, by induction on the shared recurrence) →
`norm_eq_pell_unit` (single-layer φ-norm = consecutive cross-product
`pell_unit_at n`, the Int identity `qid`) → `pell_unit = −1`
(`mobius_213_pell_unit_invariant_forall`).  All manual `Int213` rewrites, no
`ring`/`omega`/Mathlib.

## OPEN (next targets — pick up here)

  - **`phiCut (pellNum n) (pellDen n) = false` for all n** — partially built:
    · **mechanism DONE**: `PhiAsCut.phiCut_false_of_norm (m k)
      (hid : (2m−k)²+4 = 5k²) : phiCut m k = false` (PURE) — the single-layer
      reason a convergent reads below φ.
    · **coupling exposed**: `PhiNormInvariant.{seq_coupling_num, seq_coupling_den}`
      restate the `P`-action on `P_{num,den}.seq` directly (the abbrev-stated
      `coupling` pulls `propext` when cast — use these to `rw` cleanly).
    · **⚠ CRITICAL CONSTRAINT (discovered, verified)**: in this Lean/Int setup,
      **`Int` `≤` pulls `propext`** — even `(0:Int) ≤ 1 := by decide`, and
      `Int.add_le_add`, `Int.add_le_add_left/right` all do.  So **any positivity
      done in `Int` is DIRTY** (a whole Int-positivity attempt was written, hit
      the purity gate, and was reverted).  By contrast **`Nat` `≤` is PURE**
      (`(0:Nat) ≤ 1 := by decide`, `Nat.add_le_add`, `Nat.mul_le_mul_right` all
      clean).  Also `omega` pulls propext+Quot.sound — do not use.
    · **remaining (must be done in Nat)**: prove a **Nat coupling**
      `pellNum (n+1) = 2·pellNum n + pellDen n`, `pellDen (n+1) = pellNum n +
      pellDen n` (from the Int `seq_coupling_*` via `toNat`, or by re-deriving the
      Nat recurrence directly — watch `toNat_add`/`toNat_mul` for propext).  From
      that, in Nat: positivity (`1 ≤ pellNum/pellDen`), `pellDen ≤ 2·pellNum`,
      and the Nat norm identity `(2·pellNum − pellDen)² + 4 = 5·pellDen²` ∀n
      (the Nat shadow of `phi_norm_eq_neg_one`).  Then `phiCut_false_of_norm`
      closes it, upgrading `PhiCutConvergents.convergents_below_phi` from
      layers-0..8 to ∀n.  Everything Nat-side, no Int `≤`, no `omega`.
  - **GRA-tower ↔ CD-tower duality** (conceptual only, `tower_atlas.md` open
    frontier): level `n` of property-loss ↔ level `5−n` of Reading-iso gain.
  - **Flexibility over a non-associative base** (`CDDoubleFlexible.lean`
    cross-pair crux) — the long-standing Cayley-Dickson open item.

## Notes / hygiene

  - N_U = d^(d²) is **deprecated** (audit branch `claude/full-file-audit-ChymR`
    `bbd07b5`); `seed/RESOLUTION_LIMIT_SPEC.md` does not exist (stale ref).
    Don't cite N_U as a constant; don't use "ℝ = final boss" framing (AI-introduced).
  - `decide` on `Subtype`/`Raw` equality pulls `propext` via `DecidableEq Raw`;
    use `Tree.noConfusion` (for `a≠b`) and `of_decide_eq_true` (NOT
    `decide_eq_true_eq`) to stay strict ∅-axiom.  Bit me twice this session.
  - Repo-first: `PredicateSelfEncoding` already existed; I nearly rebuilt it.
    Grep + INDEX before coding a "missing" cell.
