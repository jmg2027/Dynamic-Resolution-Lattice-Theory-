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
  lacks). — *Carrier bijection `Operand ≅ Tree` proved in Lean, ∅-axiom
  (`Rederive/EventPrimary.lean`); the causal-order equivalence remains a
  conjecture and the refuter (R5) downgraded several supporting claims —
  see the status table.*

## Per-question status

| Q | Claim | Status | Evidence | Adversarial verdict |
|---|---|---|---|---|
| Q1 | Confluence; runs = linear extensions of **D**; common limit under weak fairness | **Proved (prose)**; carrier facts ∅-axiom Lean | `theory/order_invariance.md` Thm 5.3, 5.7, 6.5, 6.7, 7.1–7.3; `Rederive/Tree.lean` | **CONFIRMED** (R2): all four attack vectors failed; independent re-implementation matched. Three overstatements to tighten (below), no theorem defect |
| Q2 | No ℕ-stratification past level 2; height not a rank; folds diverge; positive half graded | **Proved (prose) + core ∅-axiom Lean** | `theory/grading_obstruction.md` §3–§5; `Rederive/Grading.lean` `no_rank`, `witness_diverges`, `height_is_rank_on_Z`, `rank_on_Z_unique` | **CONFIRMED** (driver + R3): `no_rank` statement-matching passed; witnesses re-derived by hand |
| Q3 | "No scale; the order itself", non-tautologically | **Proved (prose)** | `theory/grading_obstruction.md` §6 (Thm 6.2 flagged deflationary; content = Thm 6.3–6.7) | **CONFIRMED** (R3): three rigging vectors checked, all fail to manufacture **D**; Thm 6.3–6.7 survive a non-rigged definition. One internal-contradiction fix in Remark 3.6 (below) |
| Q4 | F-obj ≅ F-ev, or a concrete asymmetry | **Proved (Lean) at the carrier level** — `Operand ≅ Tree` bijection (retraction both ways, ∅-axiom); causal-order equivalence still conjecture; asymmetry catalog | `theory/event_primary_design.md` §8–§9; `Rederive/EventPrimary.lean` (24 theorems, ∅-axiom) | **WEAKENED** (R5): genuine dual, not a relabeling — but the Q4 equivalence is unproven and is to a *reachable-only restriction* of F-obj; the carrier-bijection ("A1") was oversold; event-primacy over §2 is circumvented (poles are constructionally prior to the difference), not honored |

### Refutation punch-list (non-fatal fixes the confirmed verdicts require)

- **R1 (SPEC C1).** The C1-pinned rationale leans partly on §5's "not
  *currently* joined" phrasing, which actually reads toward the C1-*alt*;
  re-ground C1 solely on §3 (uniqueness of the difference-object). Note
  that point=tree is *entailed* by C1-pinned + §8 (one point per line),
  not a free choice. No proof changes.
- **R2 (Q1).** (i) `order_invariance.md` §1.1 says "T1–T4 machine-checked"
  but only T1, T2 are Lean; T3/T4 are prose — relabel. (ii) Prop 6.8(⊇)
  constructivity claim fails for arbitrary infinite downsets (needs
  choice) — restrict to `E_all` / decidable downsets or mark classical.
  (iii) the adjacent-transposition parenthetical should cite the
  co-enabledness precondition or be cut (the state formula, not it, is
  load-bearing).
- **R3 (Q2/Q3).** Remark 3.6 justifies "just past level 2" by λ-order,
  which contradicts its neighbour Thm 3.5(i) ("`D_4 ⊋ Z`; stratification
  survives the depth-3 λ=4 combs"). Re-ground it in the depth-downset
  framing: the maximal depth-complete downset admitting a stratification
  is exactly `{δ≤2} = Z`; the first skew link `ℓ*` (first level-3 object)
  breaks it. §6.2 should explicitly cash out the Thm 6.2 concession.

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

1. **The refutation track ran in a second workflow and Q1–Q3 survived.**
   R1 (SPEC), R2 (Q1), R3 (Q2/Q3) returned **confirmed**; R5 (Q4) returned
   **weakened**. Verdicts and required fixes are in the status table and
   punch-list above; full analyses in `theory/refutations/R{1,2,3,5}.md`.
   The confirmed verdicts carry non-fatal framing/honesty fixes (not yet
   applied to the underlying docs — tracked as `PROGRAM.md` M-F).
2. **Q4 equivalence is still a conjecture.** The carrier bijection
   `Operand ≅ Tree` is proved in Lean (∅-axiom); the causal-order
   equivalence is not, and R5 showed the honest target is a *reachable-only
   restriction* of F-obj. Three overclaims in `event_primary_design.md`
   (A1 oversold; §2 event-primacy circumvented; Design-S argument a
   non-sequitur) must be corrected — `PROGRAM.md` M-C.
3. **Physics (Program B) not started.** By design — the bridge is gated
   on Q1–Q3 (now cleared) and quarantined; see `PROGRAM.md` milestone B1.
4. Nothing here has been checked against the pre-existing corpus (by the
   independence rule); convergences or conflicts with it are unexamined
   and out of scope for the rederivation.
