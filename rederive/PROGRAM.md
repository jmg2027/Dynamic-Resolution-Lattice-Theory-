# PROGRAM — multi-session state for the independent rederivation

**How to use this file.** Each session: read `rederive/SPEC.md`, this
file, then the referenced deliverables. Pick the highest-priority NEXT
milestone, execute it to its stated verification bar, update DONE /
IN-FLIGHT here, commit. The independence rule (SPEC top) is absolute:
work from `seed/ORIGIN.md`, `seed/ORIGIN_RAW.md`, the program memo, and
`rederive/` only — never the rest of the corpus.

Verification bar for any Lean: `cd rederive/lean && lake build` clean,
zero `sorry`, and `#print axioms` empty for every new theorem (extend
`Rederive/AxiomCheck.lean`). No `Classical`, `native_decide`,
`Quot.sound`, `propext`, Mathlib.

---

## DONE (session 1)

- **SPEC** pinned: `rederive/SPEC.md` (event system, choice points
  C1–C5, questions Q1–Q4).
- **Q1 order-invariance** — proved (prose): `theory/order_invariance.md`.
  Confluence, causal poset **D**, runs = linear extensions, common limit
  under weak fairness.
- **Q2 obstruction** — proved (prose) + core ∅-axiom Lean:
  `theory/grading_obstruction.md` §3–§5, `Rederive/Grading.lean`.
  `no_rank` (∀ rank functions), `witness_diverges`, `height_is_rank_on_Z`,
  `rank_on_Z_unique`. Statement-matching audited (driver): passed.
- **Q3 universal grading** — proved (prose): `grading_obstruction.md` §6.
  "No scale; the order itself", non-tautological via Thm 6.3–6.7.
- **Q4 duality** — DESIGN ONLY: `theory/event_primary_design.md`
  (design P chosen, translations, equivalence conjecture, asymmetry
  catalog). No Lean, no proof.
- **Enumerator**: `enumerator/enumerate.py`, `RESULTS.md` (states/runs to
  k=14; OEIS A063894/A108225/A103410; witnesses).
- **Lean package** `rederive/lean/`: `Tree.lean`, `Object1.lean`,
  `Grading.lean`, `AxiomCheck.lean` — builds, 58 theorems ∅-axiom.

---

## IN-FLIGHT / WEAKENED (must be resolved before any result is final)

**W1 — the refutation track never ran (TOP PRIORITY).** Session 1 lost 4
of 5 refuters + re-synthesis to credit exhaustion. Only the Lean
statement-matching audit was done (by the driver). The following claims
have had **no independent adversarial pass** and must not be treated as
settled until they do:
- Q1 (`order_invariance.md`): audit the persistence case analysis; the
  "state = function of event set" step (adjacent-transposition vs
  arbitrary permutation trap); the ω-fairness/limit argument; whether
  **D** is well-defined independently of the invariance proof
  (circularity check).
- Q3 (`grading_obstruction.md` §6): independent tautology audit — is
  `Grad(D)`'s morphism class rigged so **D** trivially wins? Re-derive
  the §9-boundary "level 2" identification and check it is not chosen
  after the fact (retrofit audit).
- SPEC choice points C1–C5: is each pinned choice forced by the raw
  text, or smuggled? Recompute Q1/Q2 under the strongest variant reading
  (esp. C1 line-persistence: if lines vanish on resolve and re-linking is
  allowed, do persistence/commutation survive?).
- Q4: triviality attack — is F-ev a genuine dual or F-obj relabeled?

**W2 — Q4 is design-stage.** The equivalence conjecture and asymmetry
catalog are unproved and un-mechanized.

---

## NEXT MILESTONES (self-contained task specs)

### M-A (do first) — run the refutation track W1
- **Goal.** An independent adversarial pass on Q1, Q3, SPEC C1–C5, Q4.
- **Method.** One skeptic per target, prompted to *break*, not review;
  default to skepticism; a claim is "confirmed" only after surviving.
  Each recomputes at least one nontrivial case by hand. Deliverables:
  `theory/refutations/R{1..5}.md` with an explicit verdict
  (confirmed / weakened / refuted) and required fixes.
- **Verification bar.** Every central theorem either survives or is
  degraded in `REPORT.md` (which must mirror the verdicts). Fold findings
  into `PROGRAM.md`.
- **Expected size.** 5 focused analyses; some may demand prose fixes.

### M-B — mechanize the Q2 order-theory in Lean (currently only the finite fragment is formal)
- **Goal.** Lift `Grading.lean` from the hand-picked 9-element fragment to
  the general statements: Lemma 2.4 (cover classification), Lemma 2.5
  (height formula `h(link c t)=2δ−2`, `h(resolve c t)=2δ−1`), Theorem 3.3
  (stratification ⇔ no skew link), Theorem 4.2 (D_n graded ⇔ n≤6).
- **Method.** Formalize `Tree` subterm order and the event type over
  `Tree`; define **D** by the two generator rules; prove the height
  formula by structural recursion. This needs the `order_invariance.md`
  infrastructure (**D** well-defined) — coordinate with M-D.
- **Verification bar.** ∅-axiom; the general `no_rank` (over **D**, not a
  fragment) as a corollary of Theorem 4.1 with `E*` reconstructed.
- **Expected size.** Substantial — a new `Rederive/CausalOrder.lean`.

### M-C — Q4: implement F-ev in Lean and settle the duality
- **Goal.** `Rederive/EventPrimary.lean`: the design-P carrier, the
  `opToTree`/`treeToOp` translations, mutual-inverse on the intended
  fragments, and structure preservation. Then either prove the
  equivalence at the causal-order level (SPEC Q4) or **prove an
  asymmetry** from the catalog (a structural property one side has and
  the other provably lacks) — an asymmetry is a first-class result.
- **Verification bar.** ∅-axiom, no quotients; build stays clean.
- **Expected size.** Medium; the design doc gives intended signatures
  (§10).

### M-D — residue-shape classification (memo A2 hard half, continued)
- **Goal.** Extend `Object1.lean`'s residue-shape theorem past step 1.
  Proved so far: image = single-point indicators; residue includes
  const-false, const-true, every 2-point indicator. Open: the uniform
  finite-support characterization (k≥2), and a descriptive-complexity
  grading of the non-finite-support residue.
- **Method.** Stay intensional where possible (the extensional converse
  is `funext` = `Quot.sound`, forbidden); classify by support size.
- **Verification bar.** ∅-axiom.
- **Expected size.** Small–medium; genuinely open at the tail.

### M-E — the state/downset lattice (new sequence)
- **Goal.** The states-per-k sequence
  `1,1,1,2,3,8,19,57,186,652,…` had **no OEIS match**. It counts the
  finite downsets of **D** graded by size (the distributive lattice of
  Cor 5.8). Characterize it; submit to OEIS if genuinely new.
- **Method.** Count antichains/downsets of the presented **D** by rank;
  compare against the Birkhoff dual.
- **Verification bar.** Recurrence proved, not just enumerated.
- **Expected size.** Medium; a possible genuinely-new combinatorial
  result.

### B1 (gated on Q1–Q3 surviving M-A) — the single physics bridge
- **Goal.** Test, don't assume, the one bridge the raw text licenses
  (`ORIGIN` §6–§7): spacetime = one run of the event system; one event =
  one distinction (1 bit); information invariance = one distinction per
  event; resolution covariance = linearization-dependence of event order.
- **Method.** Map **D** onto causal sets. Compute what the two event
  kinds + the internal tree structure (A1) add over bare Rideout–Sorkin
  classical sequential growth. **Kill-tests FIRST**: Lorentz-violation
  bounds (GRB time-of-flight) are where resolution-covariance proposals
  die — B1 must pass before any prediction. Compare adversarially with
  't Hooft cellular-automaton QM.
- **Verification bar (numeric quarantine).** No physical constant may be
  stated as a result without a *pre-registered* forcing derivation
  (write the forced value before computing) that is machine-checked. The
  raw utterances contain no numbers; keep it that way as long as
  possible.
- **Expected size.** Large; a multi-session arc of its own. Do NOT start
  before M-A clears Q1–Q3.

---

## Standing rules (do not drop)

1. **Independence.** Only `seed/ORIGIN*.md`, the program memo, and
   `rederive/`. Never cite `lean/E213/`, `theory/`, `seed/AXIOM/`.
2. **∅-axiom or it doesn't count.** Every Lean theorem `#print axioms`
   empty.
3. **Bilingual ledger.** Every classical concept used → `LEDGER.md`.
4. **No numerology.** No constant as a result without pre-registered,
   machine-checked forcing.
5. **Builders don't commit; the driver commits** after verifying the
   build and axiom-cleanliness independently.
6. **Refute before believing.** Builders : breakers ≈ 2 : 1; nothing a
   refuter refuted may appear as a result in `REPORT.md`.
