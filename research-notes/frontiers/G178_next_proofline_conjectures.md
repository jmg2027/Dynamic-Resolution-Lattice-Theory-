# G178 — next proof-line conjectures: populating νF (post-FSM arc)

**Date**: 2026-06-02.  **Status**: conjecture seed (tier-1 scratchpad).  **Method**: three
parallel agents (frontier survey + µF/νF extension + physics-bridge), synthesized + ranked.
**Context**: the self-pointing functor `F X = {a}⊎{b}⊎{x/y : x≠y}` arc is closed on both faces
(µF = `Raw`, νF = `CoResidue.SlashNu`) and the FSM Lens (`Theory/Raw/StateMachine`, 20 PURE,
§1–§9, merged to `main`).  This note seeds what to prove next.

## The headline finding

The genuinely new proof-line is **populating νF** — turning the lone escaping inhabitant
`spineL` into a richly-populated final coalgebra.  The physics-bridge directions are almost all
*consolidation* of integers the DRLT side already deploys `(NS,NT,d)=(3,2,5)`, not new results;
two are category errors to record-and-stop (below).  Recommended order: **C1 → C4 → C2**.

**STATUS 2026-06-02 — FULL TIER CLOSED** ∅-axiom (CoResidue 64→94 PURE, StateMachine +1):
  - P1 `spine_family_populates_nu` (CoResidue §13) — `spineOf` family, one escape per Raw.
  - P2 `coSwap_nu_endomorphism` (CoResidue §14) — `swap` acts on νF (leaf-relabel involution).
  - P3 `boolSpine_injects_bitstreams` (CoResidue §15) — `(Nat→Bool) ↪ SlashNu`, Distinct-preserving.
  - P4 `exact_descent` (StateMachine §5) — exact deep-spine descent length = `depth`.
  - P5 `spineL_unique` (CoResidue §16) — `spineL` the unique left-spine fixpoint (path induction).
  - P6 `nu_population_capstone` (CoResidue §17) — νF a `Distinct`-rich populated carrier.
  Adversarial-reviewed; essays `the_residue_as_{primitive,state_machine}.md` updated.

**STATUS 2026-06-04 — §18 cross-arc closed** ∅-axiom (CoResidue 94→99 PURE).  The §14 ⊗ §15
graft (`coSwap` ⊗ `boolSpine`): the lone Raw automorphism acts *freely* on the bit-stream
escapes —
  - `spineL_eq_boolSpine_true` — `spineL` is the `f ≡ true` member of the §15 injection.
  - `coSwap_boolSpine` — exact intertwining `coSwap ∘ boolSpine = boolSpine ∘ (Bool.not ∘ ·)`,
    clean precisely where §14's tree-seed intertwining fails (a leaf has no children to reorder).
  - `coSwap_boolSpine_distinct` — `coSwap` fixes *no* bit-stream escape (free action of the
    order-2 swap group on the `(Nat→Bool)`-many escapes).
  - `boolSpine_swap_orbit`, `coSwap_boolSpine_free_action` — the 2-element orbit + capstone.
  Fed the promoted essay `theory/essays/foundations/the_frontier_has_a_form.md` (the populated +
  *symmetric* frontier).

**STATUS 2026-06-04 — §19 shift dynamics closed** ∅-axiom (CoResidue 99→107 PURE).  The
bit-stream escapes carry the **shift dynamical system** (cross-arc §12 ⊗ §15 ⊗ §18 ⊗ the
non-holonomicity arc):
  - `boolSpine_congr` — pointwise stream-eq → pointwise spine-eq (funext-free, reads periodicity).
  - `boolSpine_coLeft` / `boolSpine_coRight` — left descent = head bit, right descent = the shift.
  - `boolSpine_shift_coalgebra` — `boolSpine` is the shift→νF coalgebra hom.
  - `boolSpine_periodic_selfsimilar` — self-similarity = shift-periodicity.
  - `spineL_shift_fixed` — `spineL` the period-1 (shift-fixed) escape (= `spineL_unique`'s p=1).
  - `boolSpine_swap_shift_commute` — the lone symmetry commutes with the shift.
  - `boolSpine_shift_dynamics` — capstone: νF carries the full shift as a faithful sub-coalgebra.
  Fed the essay's "the frontier carries dynamics" layer.  Remaining open: the consolidation
  bridges (C-phys) below + adjacent (native ε₀ diagonal G173, frozen=dynamic φ identity).

## Recommended next proof-line (νF population — all ∅-axiom-feasible)

### P1 (≙ agent-C1) — a spine *family*: one escaping behaviour per finite Raw ★ top pick
`spineOf (t : Tree) : LCoShape` = the left-spine whose left child is the finite tree `t`
(so `spineL = spineOf a`).  Targets:
```
spineOf_antiRefl   (t) (canonical) : AntiRefl (spineOf t)
spineOf_consistent (t)             : Consistent (spineOf t)
spineOf_escapes    (t s)           : spineOf t ≠ lToShape s
spineOf_distinct   {t t'} (t≠t')   : Distinct (spineOf t) (spineOf t')
```
Result: `SlashNu` contains a **Tree-indexed family** of distinct infinite inhabitants — the
whole finite µF injects into the escaping νF behaviours ("a rate per seed").
Leans on: `spineL_{antiRefl,consistent,escapes}` (same proof shape, leaf `some true` →
`lToShape t`), `treeDiffPath`/`lToShape_faithful`, `lToShape_rightspine_leaf`.
Tractability: easy–med, low risk.  Only subtlety: root anti-reflexivity when `t` is a leaf vs a
slash (both covered by existing lemmas).

### P2 (≙ agent-C4) — `swap` as a νF endomorphism that intertwines the embedding ★
`coSwap (s) := fun q => (s q).map Bool.not` (flip leaf labels, keep branch structure).
```
coSwap_involutive   (s) (q) : coSwap (coSwap s) q = s q
coSwap_lToShape     (t) (q) : coSwap (lToShape t) q = lToShape (Tree.swap t) q   -- intertwine
coSwap_antiRefl     {s} (AntiRefl s)   : AntiRefl (coSwap s)
coSwap_consistent   {s} (Consistent s) : Consistent (coSwap s)
coSwap_spineL_distinct : Distinct spineL (coSwap spineL)    -- swap moves the canonical escape
```
Connects the dormant `Theory/Raw/Swap` automorphism to the freshly-closed νF arc.
Leans on: `Raw.swap_swap`/injectivity pattern, `Bool.not_not` pointwise, `treeDiffPath`.
Tractability: easy–med; `Option.map Bool.not` is computational, no propext.  `Distinct`
preserved because `Bool.not` is injective (constructively).

### P3 (≙ agent-C2) — injection `(Nat → Bool) ↪ SlashNu` preserving `Distinct` ★ sharpest
`boolSpine (f : Nat → Bool)` places leaf `some (f k)` down the `true` branch at all-false
depth `k`.
```
boolSpine_mem (f)         : Consistent (boolSpine f) ∧ AntiRefl (boolSpine f)
boolSpine_inj {f g} (f≠g) : Distinct (boolSpine f) (boolSpine g)
```
This is the **∅-axiom-honest form of "uncountably many escapes"**: a pointwise injection of
`Nat → Bool` into `SlashNu` preserving `Distinct` — NOT a cardinality theorem.
`f ≠ g` reads as `∃ k, f k ≠ g k`, giving the witness path `replicate k false ++ [true]`
directly (positive `Distinct`, no choice).
Tractability: med.  Do P1/P2 first; the branch-distinctness bookkeeping mirrors
`spineL_diff_step`.

## Second tier (do after P1–P3)

- **P4 (agent-C7, exact descent length)** — strengthen `descent_chain_drops` (≥ bound) to an
  *exact realiser*: every `Raw` has an `IsPart`-chain dropping depth by *exactly* 1 per step,
  reaching an atom in exactly `r.depth` steps (deeper-child selector via `Nat.decLe`, no
  propext).  Tight converse to `every_state_reachable`'s `k ≤ depth`.
- **P5 (agent-C6, spineL uniqueness)** — characterise `spineL` among `SlashNu` by a local
  fixpoint property ("left child = leaf-`a`, right child = branch"), proved by **path
  induction** (the `lAna_unique` trick), bisimulation-free.  Gives `spineL` a uniqueness
  theorem (currently only existence + escape).
- **P6 (agent-C3, νF capstone — POINTWISE ONLY)** — bundle the νF-side mirror of §8: coalgebra
  decomposition + finality + the finite-embedding + escape.  ⚠ the "reduced on the whole
  carrier" conjunct **must stay pointwise** (`TraceEq s.val t.val`); the `s = t` form needs
  `funext` and is **forbidden**.  Largely re-bundling; modest new content.

## Consolidation bridges (safe but internal — low novelty)

- **C3-phys (det-`1` = ascent-`1` = glue-`1`)** — one ∅-axiom theorem identifying the Möbius
  `det P = NS−NT = 1`, the ascent unit (`ascent_adds_unit`), and the descent unit
  (`part_depth_succ_le`) as the *same* `1`.  Safest, fully internal; the `ResidueForm`
  docstring already asserts this unity narratively — this demands the Lean witness.
- **C1-phys (`N_gen` via the atom's own solver)** — link `C(NS,NT)=3` to the
  `solve_2a_3b_eq_5` machinery of `atomic_iff_five`, not a parallel `binom` fact.  ⚠ risk:
  `C(3,2)=3=NS` may be a small-number coincidence — must carry structure, not just numerics.
- **C7-phys (Koide `2/3 = NT/NS`)** — connect `koide_falsifier` (F21) to `Mobius213OneAsGlue`
  so Koide's `2/3` and the det atoms are the *same two atoms*.  Clean internal link; honest
  only as a *forced reading*, which F21 already frames correctly.
- **C6-phys (falsifier-roster uniqueness super-theorem)** — every falsifier integer (F1 `5`,
  F2 `3`, F8 `22`, F22 `6`, F26 `10`, F24 `192`) is a polynomial in `(NS,NT,d)`, the unique
  triple forced by `atomic_iff_five`+`pair_iff_two`.  High Validation-Standard value (one
  ∅-axiom theorem covering the surface) but capstone-inflation labor.

## Non-bridges — record and STOP re-fighting (per the failure-mode discipline)

These are seductive but are *forcible-map / stereotype-matching* errors the repo's own files
preemptively warn against (mirrors the `5²⁵ = N_U` deletion):

- **"three" → `N_gen = 3`** — the three self-reference outcomes (oscillate/converge/escape) live
  on *three different types* with no unifying operator (`SelfReferenceThreeOutcomes` says so
  itself); the three Raw constructors include `slash` (a binary former, not a peer of `a,b`).
  `N_gen = C(NS,NT)` is a combinatorial-selection `3`, a *different* `3`.  **Not a bridge.**
- **`det = NS−NT` → baryon asymmetry `η_B`** — `det=1` and `η_B`'s leading `6=NS·NT` both
  contain small `(NS,NT)` integers because the physics side is *already saturated* with
  `(3,2)`; "det = matter asymmetry" is a leap, not a cancellation count.  **Premature; do not
  pursue** absent a real mechanism.

## ∅-axiom traps (apply to every P-item)

| Trap | Triggers | Avoidance |
|---|---|---|
| Cardinality (`Cardinal`, `¬Countable`) | choice / propext | state P3 as an *injection preserving `Distinct`*, never a count |
| `funext` (pointwise → function eq) | the `s = t` form of any trace-eq | keep finality/reducedness **pointwise** (`∀ q`) — P6 caveat |
| `DecidableEq Raw` / decidable depth-filter | propext via Subtype | bounded `decide`-witnessed forms only (cf. agent-C5 per-depth count) |
| `simp only` / `rw` on `↔` | propext | explicit `rw`/`show`/`rfl` + `constructor`/`subst` (cf. `raw_traceEq_iff_eq` fix) |

## Provenance

Three agents (frontier survey, µF/νF extension, physics bridge), 2026-06-02.  Anchors:
`Theory/Raw/{CoResidue,MuNuMirror,Lambek,PrimitiveTower,StateMachine,Swap}`,
`Lib/Math/Foundations/ResidueForm`, `Theory/Atomicity/Five`, essays `the_residue_as_{primitive,state_machine}`.
Adjacent still-open (survey): native ε₀ diagonal (G173, hard), frozen=dynamic φ identity (med).
