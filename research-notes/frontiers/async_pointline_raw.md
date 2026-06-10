# The asynchronous point–line system ≅ Raw — boundary ladder, scales, agenda

**Origin.**  `seed/ORIGIN_RAW.md` (originator: Mingu Jeong) — the Raw
axiom rebuilt from "difference" alone, then read as an asynchronous
event system; closing question (§10 there): *if strata are assigned
above level 2, which number scale (or scales) is appropriate?*

**Provenance.**  First draft 2026-06-10; same day revised after a
four-expert multi-agent debate (concurrency/order theory, number
theory, Lean formalization, physics foundations) + an adversarial
referee round.  All numeric claims below were machine-verified twice
(independent enumerations / exact bigint + modular tracking).  The
first draft's errors are *corrected silently here*; the ladder in §2
and the base-2 sandwich in §3(b) are the corrected forms.

## 1. The system is Raw

The limit object of the point–line process is the direction-free,
no-self-pair magma on two atoms — `Raw`
(`lean/E213/Theory/Raw/Core.lean`).  Canonical formalization: **state
= points-list only** (lines derived, not stored): `State` = Nodup
list ⊇ {a,b}, subtree-closed; one event kind
`fire x y (h : x ≠ y)` inserting `Raw.slash x y h` when absent.  The
line/point two-event split (origin §8) is a Lens on this one
constructor — the line is the pair caught, the point the same pair
reified.  Under the occurrence-net Lens the reading is conflict-free
(points are read-arcs, lines one-shot) and coincides with its own
unfolding; confluence is a one-step diamond — no fairness, no limit
machinery.  Any two reachable snapshots are joinable (union of
subtree-closed sets is subtree-closed).

## 2. The boundary ladder (semantics-tagged)

Event-indexed boundaries depend on the split/fused Lens choice, so
they carry tags; only the invariant clauses are residue-level.

- **Fused** (one fire = contrast + resolve): step 1 forced (`a/b`);
  any two step-2 snapshots are swap-equal; step 3 reaches **4**
  swap-inequivalent classes (the D₂-completion 5-set + three
  depth-3-bearing snapshots).
- **Split** (line, point separate events): reachable states mod swap
  = 1, 1, 1, **2**, 4, 10 for events 1..6 — events 1–2 forced, event
  3 swap-rescued, event 4 already diverges beyond swap (*within*
  level-2 work: both-lines-pending vs drawn-and-resolved); depth-3
  lines drawable from event 5, before D₂ completes.
- **Semantics-invariant**: (i) determinism ends exactly at the first
  composite; (ii) exactly one further firing is swap-canonical; the
  next diverges beyond swap; (iii) **no run is forced through the
  5-snapshot** — e.g. `{a,b} → ab → a(ab) → a/(a(ab))` never visits
  it; (iv) all snapshots joinable; (v) per-object folds and the
  ancestor order are run-invariant.

**What distinguishes depth ≤ 2 is order-internal, not run-internal:
past-completeness.**  D₂ (population 5, `Raw.level2_total_card`,
`Theory/Raw/Levels.lean:133`) is the largest depth-downset in which
every term's causal past contains the whole previous downset; at
depth 3 this fails for 6 of 7 terms (sole exception: the full join
`(a(ab))/(b(ab))`).  The contrast graph of any reachable snapshot
with a composite is connected, so its coordinate count
(`dim im δ⁰`) is `|S| − 1`; at D₂ that reads 5 − 1 = **4** — the
same 5→4 readout as G121's chart-Lens omitting the self-pointing
axis (knot M2), now anchored to the past-completeness boundary.  It
is *not* an observer-independent invariant (every snapshot reads
`|S|−1`), and "depth = the universe's resolution" stays dead twice
over (privileged level + global depth-clock; the N_U lesson,
`RERESEARCH_n_u_removal.md`).

## 3. Scales — the answer to origin §10

**(a) Per-object stratum: one fold structure, three algebras.**
`Raw.fold` with: max-plus algebra → depth (`Raw.fold_eq_depth`),
additive algebra → leaves (`Raw.fold_eq_leaves`), and the
subterm-**set** algebra (union∘insert) followed by the cardinality
Lens → `dagSize` = #distinct composite subterms.  History is a DAG,
not a tree: each term is created once, so `leaves` has no event-cost
meaning; the event cost of `t` is `dagSize t` (fused) / `2·dagSize t`
(split).  Verified on all 12 depth-≤3 terms:
`depth ≤ dagSize ≤ leaves − 1`, refining `Raw.depth_lt_leaves`;
sharing (dagSize < composite-multiplicity) first occurs at depth 3,
at exactly the 3 terms reusing `ab`.  The event-poset height
recomputes the same fold: `height(pt t) = 2·depth(t) − 1` — the
grading is order-canonical and **never dies**; what is conventional
above the ladder is only its *simultaneity reading* ("all stage-k
together") and run-respect of ranks.  (A grading is not a linear
extension; runs are.)

**(b) Per-layer width: already in the repo + new structure.**  The
recursion `T(n+1) = 2 + C(T(n),2)` exists as `rawCount`/`choose2`
(`Lib/Math/Foundations/UniverseChain/RawRecurrence.lean`, table to
T(5)=2280; generic-N `RawCountGeneric.lean`; depth-graded enumeration
`RawEnumeration.lean` with `(enumTreeDepth n).length = rawCount n`;
5-census `RawDepthCount.lean`; (3,2) split `RawBipartition.lean:46`).
New, debate-found:

- *Normal form*: `8·T(n+1) = (2·T(n) − 1)² + 15` — conjugate to the
  pure quadratic map `w ↦ w² + 11/16`.
- *Asymptotics*: `T(n) ~ 2·K^(2^n)`, `K = 1.24602083298…`
  (Aho–Sloane orbit constant; closed form unlikely).
- *Sandwich* (the provable two-sided bound): for n ≥ 3,
  `configCountD 2 (n−2) < T(n) < configCountD 2 (n−1)` — strict both
  sides; **the base is 2 = NT, not d = 5** (the resemblance to
  `d^(d^n)` is shape-only).
- *Modular*: mod 5 purely periodic, period 3, cycle (2,3,0) — an
  instance of the **generic self-restart** of towers
  `f(x) = 2 + q(x)`, `q(0)=0`, mod their own depth-2 value (every
  clause-variant does the same: B mod 17 (2,5,0), C mod 38 (2,6,0),
  D mod 14 (2,4,0)); not a 213-specific resonance.  Variant-specific
  and real: mod 7 fixed at 5 from n ≥ 2 (parabolic; mod 7^k period
  7^(k−1)); 5-adic attracting 3-cycle with
  `v₅(T(n+3) − T(n)) = ⌊(n+1)/3⌋ + 1`; mod 2 non-periodic (expanding
  2-adic map; window evidence to n = 4000).
- *Clause fingerprint*: from seed 2, the four pairing variants reach
  depth-2 values A(Raw) **5** / B(self allowed) 17 / C(ordered+self)
  38 / D(ordered) 14, with pairwise distinct growth constants —
  the clause set is recoverable from the count sequence
  (discrimination, not a physics falsifier).  Shift identity:
  `T(n) − 1` satisfies the 1-atom self-pair-allowed tower's
  recurrence (A006894 shape) — the clause *pair* (no-self, two
  atoms) trades off against (self, one atom) at exactly +1.
- *New-at-depth*: `newAt(n+1) = newAt(n)·T(n−1) + C(newAt(n),2)`.

**(c) Global stratum: the ancestor order, read two ways.**  The
interleaving-invariant content is carried by the ancestor order;
order and grading are both Lens readings of the same terms, the
order finer.  Numeric staging *as simultaneity* = a foliation Lens
(`seed/AXIOM/05_no_exterior.md` §5.7).  Order statistics at D₂:
(related, incomparable) = (8, 2), the two incomparable pairs being
exactly the swap-orbits; the Myrheim–Meyer-type ordering fraction of
bare Raw **diverges** (relatedPairs ≤ T(n)·2^(n+1) vs ~T(n)²/2
total), so no finite dimension readout lives on a depth scale — if
d = 4/5 is a counting theorem anywhere, it is at the
past-completeness boundary or inside the (NS,NT,c) deployment Lens.
This *constrains* G121 knot M2 rather than confirming it.

## 4. The two 5s (former O4) — mediated, not identical

Atomicity's 5 is a Diophantine uniqueness of **sizes**
(`Theory/Atomicity/Five.lean:21,81,134`: `5 = 2·1 + 3·1` =
pairSize + closureSize, unique alive decomposition); T(2) = 5 is a
**term count** (2 atoms + C(3,2) composites).  The agreement factors
through one fixed point: `choose2 n = n ⟺ n ∈ {0, 3}` — and 3 is
simultaneously `closureSize` ("the pair plus their relation" —
literally `Raw.level1_set = [a, b, a/b]`) and the level-≤1
population.  `level2_new` is a swap-orbit pair ↔ pairSize 2.  So:
not a one-line identity, not numerology — a short mediated theorem
(`two_fives`, agenda #3).  The earlier "the atomicity split
(NS,NT) = (3,2)" phrasing equivocated size with cardinality; the
split match itself is already PURE at `RawBipartition.lean:46` and
stays a cardinality statement.

## 5. Theorem agenda (marathon order; referee-ranked)

Items 1–8 **CLOSED** ∅-axiom (74 PURE total, 2026-06-10 marathon);
Lean anchors below.  The arc is promotion-eligible
(`theory/PROMOTION_CRITERIA.md`) — remaining seams are listed under
each item and in §6.

1. ✓ **O2-fused ladder** — `Theory/Raw/Async.lean` (14 PURE):
   `step1_forced`, `level2_canonical` (exact swap-conjugate list
   disjunction — stronger than MemEq-up-to-swap), `level3_diverges`
   (depth-2 completion vs depth-3 fork, beyond global swap),
   `level2_swap_partner`.  *Still open from this item*: the fused
   step-3 swap-class census (= 4) needs a state-enumeration
   function, deferred to item 7's machinery.
2. ✓ **D₂ past-completeness boundary** —
   `UniverseChain/RawPastCompleteness.lean` (6 PURE):
   `depthLe2_past_complete`, `depth3_boundary` (filter keeps exactly
   the full join `t1`), `past_complete_boundary_population`.
3. ✓ **two_fives mediated** —
   `UniverseChain/AtomicityCensusBridge.lean` (8 PURE):
   `choose2_fixed`, `two_fives`, `mediating_fixed_point_unique`,
   swap-orbit lemmas.
4. ✓ **Base-2 sandwich** — `UniverseChain/RawCountBounds.lean`
   (6 PURE): `rawCount_sandwich` (strict both sides),
   `rawCount_lower` (sharp at base: both sides 5),
   `census_step_lower/upper` (parametric squeeze).
5. ✓ **mod-5 period 3** — `UniverseChain/RawCountQuadratic.lean`
   (9 PURE): `rawCount_mod5_cycle` + `_table`, plus the quadratic
   normal form `rawCount_normal_form` and `choose2_add`/
   `choose2_double`.  B/C/D discrimination values via `rawCountG`
   not yet instantiated (optional).
6. ✓ **dagSize fold** — `UniverseChain/RawDagSize.lean` (8 PURE):
   `dag_census`, `dag_sandwich_le3`, `sharing_starts_at_depth3`
   (exactly `[t1, t4, t7]`).  *Still open from this item*: the
   uniform ∀-bounds `depth ≤ dagSize ≤ leaves − 1` by `Raw.rec`
   induction (census closes them for depth ≤ 3 only), and the
   min-run-length theorem (run length = dagSize, fused).
7. ✓ **O1 reachability** — `Theory/Raw/AsyncReach.lean` (12 PURE)
   + `Slash.lean` gains `slash_val_lt/gt`, `slash_inj` (pair
   injectivity — needed for the closure invariant):
   `reach_closed` (reachable ⟹ subterm-closed),
   `reach_extend`/`reach_joinable` (conflict-freeness, finite, no
   fairness), `every_raw_reached` (totality by `Raw.rec` +
   joinability), `list_reached` (finite joint reachability).
   `memDec` hand-rolled (core `∈`-instance propext landmine).
   *Still open from this item*: the exact-membership converse
   (`Closed P ∧ Nodup P ⟹ ∃ reachable s, MemEq s P` — needs the
   argmin-by-depth fill construction + `List213.
   length_filter_lt_of_mem` measure), and the fused step-3
   swap-class census (= 4) via state enumeration.
8. ✓ **Honest counting theorem** —
   `UniverseChain/RawEnumeration.lean` (+8 PURE): `honest_count` —
   `enumTreeDepth n` lists exactly the canonical Trees of depth ≤ n
   (`enum_members` + `enum_complete`), Nodup, length `rawCount n`.
   **The `Tree.cmp`-transitivity gate dissolved**: the strict
   `Pairwise (cmp · · = .lt)` invariant propagates through
   `newSlashes` using only the lex head structure
   (`cmp_slash_same`, `cmp_slash_lt_head`), `cmp_self_eq`, and the
   swap conversions — no transitivity, no sorted-insertion
   machinery.  So `rawCount = 2, 3, 5, 12, 68, …` genuinely counts
   the canonical Raw population per depth, and every count theorem
   in §3(b) (normal form, mod-5 cycle, base-2 sandwich) is now
   about the *actual* census, not just the recurrence.

## 6. Deferred (conjectures / notes only)

Order dimension of the event poset Θ(level) (incidence-poset lower
bound; upper open); general MM-dimension readouts; the Birkhoff
distributive-lattice structure (joinability suffices for the
agenda); `axisCount = |S| − 1` as a one-line corollary once O1's
connectivity lands; mod-2 aperiodicity (2-adic expanding-map
argument; window evidence only, not a Lean priority); normal-form
constant `K` closed form (unlikely; don't chase).

## Cross-references

`seed/ORIGIN_RAW.md` (origin dialogue);
`lean/E213/Theory/Raw/{Core,Levels,StateMachine}.lean`;
`lean/E213/Lib/Math/Foundations/UniverseChain/{RawRecurrence,
RawEnumeration,RawCountGeneric,RawDepthCount,RawBipartition}.lean`;
`lean/E213/Theory/Atomicity/{Five,PairForcing,PrimitiveSizes}.lean`;
`Lib/Math/Cohomology/Fractal/ConfigCount.lean`;
`seed/AXIOM/05_no_exterior.md` §5.7;
`G121_dim4_self_pointing_axis.md` (knot M2 — constrained by §3(c)).
