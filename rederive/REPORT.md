# REPORT — independent rederivation, session 1

**Scope.** Executes `research-notes/drafts/independent_rederivation_program.md`
from the raw utterances alone (`seed/ORIGIN.md`, `seed/ORIGIN_RAW.md`),
under `rederive/SPEC.md`. No other repository content was read by any
worker. Produced by a multi-agent team (builders + adversarial refuters +
synthesis); this file records what survived verification and, explicitly,
what has **not** yet been adversarially checked.

## Executive summary

The originator's raw utterances contained three unproved observations
about the asynchronous distinction system of ORIGIN_RAW §5–§10:

1. growth has "a tension" — the lockstep foliation is suspect (§6);
2. natural-number strata "work up to level 2 but not beyond" (§9);
3. an open question: which number scale grades the layers above (§10).

This session turned all three into theorems (prose, most core-formalized
in Lean, ∅-axiom), and answered §10 by computation rather than by
choosing a scale:

- **§6 becomes Q1 (order-invariance):** the system is confluent. The
  state after a finite run depends only on the *set* of events executed;
  the executed sets are exactly the finite downsets of one explicitly
  presented causal partial order **D**; runs are its linear extensions;
  every weakly-fair maximal run produces every tree and converges to the
  same limit. Staging is a choice of linear extension; only **D** is
  invariant. — *Fully proved in prose (`theory/order_invariance.md`);
  the F-obj carrier facts it rests on are ∅-axiom Lean.*
- **§9 becomes Q2 (level-2 obstruction):** in three precise senses **D**
  carries a height but no ℕ-stratification past the level-2 zone, each
  with an explicit minimal witness at the **same first tree**
  `((ab)(a(ab)))` — the first contrast *between* two reified differences.
  The positive half (the five level-≤2 objects **are** graded) is also a
  theorem. — *Proved in prose (`theory/grading_obstruction.md`) and the
  core formalized in Lean (`Rederive/Grading.lean`): the no-rank theorem
  is universally quantified over all candidate rank functions; verified
  ∅-axiom.*
- **§10 becomes Q3 (universal grading):** the answer is "**no scale; the
  order itself**", made non-tautological by the Q2 impossibility results
  plus a theorem that the chain-valued gradings have no universal object
  in either direction. — *Proved in prose; rests on the Lean-backed Q2.*
- **Q4 (duality), from §2's "a, b are not objects":** a second,
  event-primary formalization (F-ev) was designed, with term/state
  translations to F-obj and a precise equivalence conjecture — plus an
  **asymmetry catalog** (structural properties one side has and the other
  lacks). — *Design only (`theory/event_primary_design.md`); the Lean
  implementation and the equivalence proof were NOT completed this
  session.*

## Per-question status

| Q | Claim | Status | Evidence | Adversarially checked? |
|---|---|---|---|---|
| Q1 | Confluence; runs = linear extensions of **D**; common limit under weak fairness | **Proved (prose)**; carrier facts ∅-axiom Lean | `theory/order_invariance.md` Thm 5.3, 5.7, 6.5, 6.7, 7.1–7.3; `Rederive/Tree.lean` | **No** — refuter R2 did not run (credits) |
| Q2 | No ℕ-stratification past level 2; height not a rank; folds diverge; positive half graded | **Proved (prose) + core ∅-axiom Lean** | `theory/grading_obstruction.md` §3–§5; `Rederive/Grading.lean` `no_rank`, `witness_diverges`, `height_is_rank_on_Z`, `rank_on_Z_unique` | **Partial** — Lean statement-matching audited by the session driver (passed); independent refuter R3 did not run |
| Q3 | "No scale; the order itself", non-tautologically | **Proved (prose)** | `theory/grading_obstruction.md` §6 (Thm 6.2 flagged deflationary; content = Thm 6.3–6.7) | **No** — refuter R3 did not run |
| Q4 | F-obj ≅ F-ev, or a concrete asymmetry | **Designed only** — conjecture + asymmetry catalog; not proved, not in Lean | `theory/event_primary_design.md` §8–§9 | **No** — L2 Lean and refuter R5 did not run |

## Quantitative findings (enumerator, all re-derived by hand in the prose)

- Reachable states after `k` events (k=0..14):
  `1,1,1,2,3,8,19,57,186,652,2548,10540,46915,222093,1110042`. **No OEIS
  match** (candidate new sequence).
- Trees by leaf-count: `2,1,2,4,10,25,68,187` = **OEIS A063894** (unordered
  binary trees over two atoms, distinct children) — exact, unique match.
- Lockstep layer widths `|G_k|`: `2,3,5,12,68,2280`, recurrence
  `|G_{k+1}| = C(|G_k|,2)+2` (doubly exponential) = **A108225** shifted.
- First fold divergence and first stratification failure: both at
  `((ab)(a(ab)))` (λ=5, δ=3). First **rank-function** failure (covers
  only, chord excluded): `((a(ab))(a(b(ab))))` (λ=7), two saturated
  bottom-chains of lengths 4 and 6; defect unbounded (Prop 4.3).

## What the process caught (self-refutation that did survive)

- **The chord caveat.** The naive "cover" relation `resolve p ≺ link q`
  is a *chord*, not a cover, whenever one endpoint is buried in the other
  (Lemma 2.1 + 2.4(iii)). The enumerator flagged it; the prose confirmed
  it by hand and split Q2 into two theorems with two different first
  witnesses (stratification λ=5 vs rank-function λ=7), rather than
  conflating them. The Lean `no_rank` `coverList` contains only genuine
  covers — audited.
- **The Q3 tautology risk.** "The universal grading is **D** itself" is
  deflationary in isolation (identity is initial in any coslice). This is
  stated as such (Thm 6.2) and given content only by the impossibility
  theorems — the honest form of the §10 answer.

## Verification performed by the session driver (Opus)

- `lake build` from a clean state: **succeeds**, zero `sorry`.
- Cheat scan (`native_decide`, `Classical`, `Quot.sound`, `propext`,
  `partial`, `unsafe`, `admit`): **none** in proof terms (only in
  comments documenting their avoidance).
- `#print axioms` on **58** theorems: every one "does not depend on any
  axioms".
- Statement-matching audit of `no_rank`: the 9 `coverList` pairs are all
  genuine **D**-covers (Lemma 2.4), the excluded chord is correctly
  absent, the theorem quantifies over all `rank : Elem → Nat`. **Passed.**

## Honest limitations of this session

1. **The refutation track did not run** (4 of 5 refuters + independent
   re-synthesis lost to a credit exhaustion mid-workflow). The driver
   performed only the Lean statement-matching audit. Q1, Q3, the SPEC
   choice points, and the Q4 duality have **not** had an independent
   adversarial pass. This is the top item in `PROGRAM.md`.
2. **Q4 is design-stage.** No Lean, no proof; the asymmetry catalog is
   conjectural.
3. **Physics (Program B) not started.** By design — the bridge is gated
   on Q1–Q3 and quarantined; see `PROGRAM.md` milestone B1.
4. Nothing here has been checked against the pre-existing corpus (by the
   independence rule); convergences or conflicts with it are unexamined
   and out of scope for the rederivation.
