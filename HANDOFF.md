# Session Handoff — 2026-06-24 (grounded-FTA + Leg-1 + Leg-3 marathon)

## Branch
`claude/fta-multiplicative-descent-frontier-5pun05` — pushed, ~73 commits ahead
of `origin/main`. Working tree clean. **Full `lake build E213` passes clean
(459/459)**; all new modules scanned `0 dirty`; certified this session.

## What Was Done This Session

One long arc on the **descent-leg frontier** (`research-notes/frontiers/the_descent_leg.md`):
ground the multiplicative discipline (FTA) on `Raw`'s own descent, then attack
Legs 1 and 3 directly. Every theorem below is **∅-axiom** (`#print axioms` empty)
and, where claimed "grounded", **closure-walked** free of
`Nat.div`/`Nat.mod`/`Nat.lt_wfRel`/`Nat.strongRecOn`.

### 1. The Fundamental Theorem of Arithmetic, fully grounded (PURE ✓) — PROMOTED
Both halves reconstructed with **no theorem in the chain depending on `Nat.div`,
`Nat.mod`, `Nat.strongRecOn`, or `Nat.lt_wfRel`** — the kernel's non-structural
well-founded division is entirely absent. `factorization_unique`: 485-constant
closure, zero forbidden hits.
- `Meta/Nat/SubMod213` — structural remainder/quotient `subMod`/`subDiv` (repeated
  subtraction over fuel); `subMod_zero_iff_dvd` = the `Nat.mod`-free divisibility test.
- `Meta/Nat/SubGcd213` — Euclidean `gcdSub` + `gcd_eq_one_of_prime_not_dvd` (the
  half of Euclid's lemma needing no Bézout).
- `Meta/Nat/SubBezout213` — **structural Bézout** `egcd`: coefficient quadruple
  `(g,x,y,s)` with `s:Bool` a sign flag, so Bézout stays in `Nat` (**no `Int`**).
  `egcd_bezout`, `bezout_one_of_coprime`.
- `Lib/.../EuclidLemmaGrounded` — `prime_dvd_mul` (Euclid's lemma). Purity craft:
  case on `gcd(p,a)∈{1,p}`, **not** `by_cases p∣a` (whose `Decidable` instance pulls `Nat.mod`).
- `Meta/Nat/VpSub213` — `vpSub`, the `p`-adic valuation on `subMod` (mirrors
  `Valuation.vp`, which is `Nat.mod`-dirty). Four laws clean.
- `Lib/.../VpMulGrounded` — `vpSub_mul` (`vₚ(a·b)=vₚa+vₚb` at a prime).
- `Lib/.../FTAUniquenessGrounded` — `factorization_unique` (valuation-count invariance).
- **Promotion**: `theory/math/numbertheory/grounded_fundamental_theorem.md` written
  (H1–H4 gates met); the closed engineering in the frontier note collapsed to a pointer.

### 2. Leg 1 — ℕ generated from `Raw`, essentially closed (PURE ✓)
`Theory/Raw/RawNat.lean` (in `Theory.Raw.API` umbrella): the naturals as a reading
of `Raw`'s `slash`-successor spine, not borrowed from Lean's `Nat`.
- carrier `RawNat = {r // ∃ n, rawTower n = r}`; `succ = slashOrSelf Raw.a`
  (point once more with `a`); `depth` Lens = `toNat` iso to ℕ.
- **Peano**: `succ_inj`, `succ_ne_zero`, `rec` (via `Nat.succ.inj`/`Nat.noConfusion`,
  not the propext-leaking `Nat.add_right_cancel`/`succ_ne_zero`).
- **Commutative semiring** (§3): `add`/`mul` iterate `succ`/`add`; `depth` is a
  semiring homomorphism (`toNat_add`, `toNat_mul`); all laws (`add_comm`..`right_distrib`)
  transport through `toNat_inj`. `mul_assoc`/`right_distrib` via `NatHelper.mul_assoc`/`add_mul`.
- **Recursion grounded in `isPart_wf`** (§4): `strongRec_isPart` + `rec_grounded` —
  descent on `Raw`'s `slash`-peel (`tower_ascent_isPart`), NOT `Nat.lt`. Closure
  probe: `isPart_wf` present, `Nat.lt_wfRel`/`Nat.strongRecOn` **absent**.
- **Carrier without `Nat`** (§5): `inductive IsRawNat` (closure of `b` under `rawSucc`);
  `rawNat_induction` has a 125-const closure containing **only `IsRawNat`/`IsRawNat.rec`**
  — zero `Nat`. `isRawNat_iff`: coincides with the tower carrier.
- **Count-spine tied in**: `Lib/.../UniverseChain/RawNatCensus` — `census x = rawCount(toNat x)`
  reads the same spine as the population `2,3,5,12,68` (`census_succ`, `two_readings`).

### 3. Leg 3 — forcing vs rival primitives, four corners excluded (PURE ✓)
`Lib/.../UniverseChain/RivalArity.lean` extended (§3–§5):
- **unary** (negation-first): linear `unaryCount` < super-linear `rawCount` (pre-existing).
- **ternary-distinct**: `ternCount_sterile` — sterile on the 2-atom seed (`choose3 2 = 0`),
  stuck at 2. Arity > 2 too much for the seed one distinguishing yields.
- **non-distinct binary**: `nondistinct_rival_exceeds` — over-generates (pre-existing).
- **relation-first**: `relation_outputs_le_two` — a `Bool`-codomain relation takes ≤ 2
  values (Bool pigeonhole), produces no carrier element; collapses to operation-first
  when functionalised.
- **capstone** `arity_distinctness_forcing`: the (arity, distinctness) design space is
  squeezed from both sides onto binary-distinct = 213.
- **relation-first** (added after first handoff): `relation_outputs_le_two` — a `Bool`-codomain
  relation takes ≤ 2 values, produces no carrier element; collapses to operation-first.

### 4. Post-handoff: `RawNat` carrier flipped + order + promotion (PURE ✓)
- **Carrier flip** (Open Problem 2 closed): `RawNat = { r // IsRawNat r }` — a `Nat`-free type;
  `toNat_succ` made `Nat`-free via `rawSucc_depth`; `∃ n` survives only as a derived reading.
- **Order** (§6): `le x y := ∃ z, add x z = y` (additive reachability) `↔ toNat x ≤ toNat y`
  (`le_iff_toNat`); `le_refl/trans/antisymm/total`, `add_le_add_left` — `RawNat` is now an
  **ordered commutative semiring**.
- **Promotion**: `theory/math/numbersystems/naturals_from_the_spine.md` (Leg-1 + count-spine +
  rival forcing), cross-linked with `arithmetic_generation.md` + `grounded_fundamental_theorem.md`.
- **Certification**: full `lake build E213` clean (459/459); all new modules `0 dirty`.

## Current Precision Results (0 free parameters)
**No physics touched this session** (pure math/foundations work). The DRLT
precision table is unchanged — see `catalogs/physics-constants.md` (canonical).
No new entries to `STRICT_ZERO_AXIOM.md`'s physics catalog; all new theorems are
math-tier and verified `#print axioms`-empty individually.

## Open Problems (Priority Order)

### 1. Leg 3 residue — "suffices by breadth, not proven unique"
Four rival classes (unary, ternary, non-distinct binary, relation-first) are now
formally excluded, but this is NOT a proof that *no* conceivable primitive
(differently-seeded, genuinely exotic) generates equal richness. This is the
deepest open item and likely not fully closable.
Frontier note: `research-notes/frontiers/the_descent_leg.md` (Leg-3 section) +
`research-notes/frontiers/the_one_act.md` (the open middle; failure-mode row
"Sufficiency read as uniqueness").

### 2. Leg 1 final residue — the kernel `inductive` itself
`RawNat`/`IsRawNat` still borrow the kernel's `inductive` mechanism to *have*
`Raw` (conceded in Attack 1 — the distinguishing IS an inductive act), and `Nat`
as the `depth` **readout** (a Lens reading *out*, the legitimate direction). The
live `RawNat` carrier still uses `∃ n` for continuity though §5 shows it is
`Nat`-free *in principle*. Optional tidy: refactor `RawNat` to carry `IsRawNat`
directly (moderate; would drop `Nat.rec` from `zero_or_succ`).
Frontier note: `research-notes/frontiers/the_descent_leg.md` (§5 / honest-scope).

### 3. FTA uniqueness via permutation (alternative form)
`factorization_unique` is stated as per-prime count invariance (valuation form).
A multiset/permutation form (`l1 ~ l2`) on the grounded `prime_dvd_mul` is a
possible companion but not required. Low priority — no frontier note.

## Unresolved from This Session
- ~~Full `lake build` not re-run~~ — **DONE**: `lake build E213` passes clean
  (459/459) and all new modules scan `0 dirty`. Branch is build-certified.
- `relation_outputs_le_two` is the honest *partial* relation-first exclusion (output
  bound), not a from-scratch "relations generate nothing" closure model — by design,
  to avoid a strawman. Documented as such in its docstring.
- `tools/scan_axioms.py` cannot probe the nested `RawNat.RawNat.*` namespace decls
  (double-`RawNat` from the file namespace + inner `namespace RawNat`); those were
  `#print axioms`-verified individually instead. Cosmetic tool limitation, not a purity gap.

## Next
Recommended: either (a) run the full `lake build` + `tools/scan_all_axioms.py` to
certify the whole branch before any merge consideration, or (b) refactor `RawNat`
to carry `IsRawNat` (Open Problem 2) to fully retire the carrier-`Nat`. Leg-3
residue (Open Problem 1) is research-grade and open-ended — approach only with a
specific new rival model in hand.

## Three-tier state (per `CLAUDE.md` "Three-tier discipline")
- **Promotions this session**: (1) `theory/math/numbertheory/grounded_fundamental_theorem.md`
  ← the FTA-grounding engineering (cont.1–11); (2)
  `theory/math/numbersystems/naturals_from_the_spine.md` ← Leg-1 (ℕ from the spine) +
  count-spine + rival forcing. Both ← `research-notes/frontiers/the_descent_leg.md`
  (closed engineering collapsed to pointers; conceptual residue stays open).
- **Promotion candidates**: `Theory/Raw/RawNat` (Leg-1) is PURE and coherent — a
  `theory/math/foundations/` chapter on "ℕ as a reading of the Raw spine" is a
  candidate once Open Problem 2 settles the carrier. `RivalArity` (Leg-3) could
  anchor a `theory/` forcing chapter.
- **Active scratchpad**: `research-notes/frontiers/the_descent_leg.md` remains the
  open-frontier record (Leg-1 residue, Leg-3 residue).

## File Map
```
lean/E213/Meta/Nat/SubMod213.lean              ← structural division (subMod/subDiv)
lean/E213/Meta/Nat/SubGcd213.lean              ← grounded gcd + prime coprimality
lean/E213/Meta/Nat/SubBezout213.lean           ← structural Bézout (egcd, Bool sign, no Int)
lean/E213/Meta/Nat/VpSub213.lean               ← grounded p-adic valuation vpSub
lean/E213/Lib/Math/NumberTheory/EuclidLemmaGrounded.lean   ← prime_dvd_mul grounded
lean/E213/Lib/Math/NumberTheory/VpMulGrounded.lean         ← vpSub_mul
lean/E213/Lib/Math/NumberTheory/FTAUniquenessGrounded.lean ← factorization_unique
lean/E213/Theory/Raw/RawNat.lean               ← Leg-1: ℕ on the Raw slash-spine (§1–§5)
lean/E213/Lib/Math/Foundations/UniverseChain/RawNatCensus.lean ← count-spine reading
lean/E213/Lib/Math/Foundations/UniverseChain/RivalArity.lean   ← Leg-3 §3–§5 (modified)
lean/E213/Meta/Nat.lean                        ← aggregator (+SubMod213/SubGcd213/SubBezout213/VpSub213)
lean/E213/Lib/Math.lean                        ← aggregator (+EuclidLemma/VpMul/FTAUniqueness Grounded)
lean/E213/Theory/Raw/API.lean                  ← umbrella (+RawNat)
lean/E213/Lib/Math/Foundations/UniverseChain.lean ← umbrella (+RawNatCensus)
theory/math/numbertheory/grounded_fundamental_theorem.md ← NEW chapter (promotion)
research-notes/frontiers/the_descent_leg.md    ← updated (cont.1–11 → pointer; Leg1 §1–5; Leg3 bracket)
```
