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
- **Q4 duality** — CARRIER BIJECTION PROVED, equivalence still open:
  `theory/event_primary_design.md` (design P, translations, conjecture,
  asymmetry catalog) + `Rederive/EventPrimary.lean` (`Operand ≅ Tree`
  retraction both ways, 24 theorems ∅-axiom). Causal-order equivalence
  unproved.
- **Refutation track (session 2)** — RAN: R1 (SPEC), R2 (Q1), R3 (Q2/Q3)
  = **confirmed**; R5 (Q4) = **weakened**. Files
  `theory/refutations/R{1,2,3,5}.md`. Verdicts mirrored in `REPORT.md`.
- **Enumerator**: `enumerator/enumerate.py`, `RESULTS.md` (states/runs to
  k=14; OEIS A063894/A108225/A103410; witnesses).
- **Lean package** `rederive/lean/`: `Tree.lean`, `Object1.lean`,
  `Grading.lean`, `EventPrimary.lean`, `AxiomCheck.lean` — builds, **82
  theorems ∅-axiom**.

---

## IN-FLIGHT / WEAKENED (must be resolved before any result is final)

**W1 — RESOLVED.** The refutation track ran (session 2). Q1, Q2, Q3
survived independent adversarial attack (R1/R2/R3 confirmed, with
recomputation and, for Q1, an independent re-implementation). The
non-fatal fixes those verdicts demand are collected as milestone **M-F**
below and are **not yet applied** to the underlying documents.

**W2 — Q4 weakened (R5).** The duality is a genuine dual (one natural
F-ev question, a real guard-fusion), not a relabeling — but: the Q4
equivalence is unproved and, as stated, is equivalence to a *reachable-only
restriction* of F-obj, not F-obj; the "A1 carrier off-by-two" is a trivial
`Operand ≅ Tree` repackaging that was oversold; and event-primacy over
ORIGIN_RAW §2 is *circumvented* (poles are constructionally prior to the
difference), not honored. Corrections tracked in M-C.

---

## NEXT MILESTONES (self-contained task specs)

### M-F (do first — cheap, closes session 2's open loop) — apply the confirmed-verdict fixes
- **Goal.** Apply the non-fatal corrections the refuters demanded to the
  underlying docs (they are honesty/framing fixes; the theorems stand).
- **Punch-list.**
  - `SPEC.md` C1: re-ground the rationale on §3 (difference-object
    uniqueness), drop the §5 "not currently joined" clause (it reads
    toward the C1-alt); note point=tree is entailed by C1+§8 (R1).
  - `order_invariance.md`: §1.1 relabel "T1–T4 machine-checked" → "T1,T2
    only; T3,T4 prose"; restrict Prop 6.8(⊇) constructivity to
    `E_all`/decidable downsets (or mark classical); fix the
    adjacent-transposition parenthetical to cite co-enabledness (R2).
  - `grading_obstruction.md`: rewrite Remark 3.6 in the depth-downset
    framing (max depth-complete stratifiable downset is `{δ≤2}=Z`; `ℓ*`
    the first level-3 object breaks it) — the current λ-order wording
    contradicts Thm 3.5(i); cash out the Thm 6.2 concession in §6.2 (R3).
- **Verification bar.** Docs self-consistent; no theorem statement
  changes; `REPORT.md` punch-list cleared.
- **Expected size.** Small — prose edits only.

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

### M-C — Q4: settle the duality (carrier done; causal-order open) + fix R5 overclaims
- **Done.** `Rederive/EventPrimary.lean` proves the carrier bijection
  `Operand ≅ Tree` (retraction both ways), faithfulness, image
  characterization — ∅-axiom, no quotients.
- **Goal.** (1) Lift to the **causal-order** equivalence (SPEC Q4): build
  the F-ev event system and prove its causal poset ≅ **D**, OR prove an
  asymmetry from the catalog (first-class). (2) Apply R5's corrections to
  `event_primary_design.md`: state the equivalence honestly as being to a
  *reachable-only restriction* of F-obj (not F-obj); tone down the A1
  carrier claim (it is `Operand ≅ Tree` on the nose, not a first-class
  result); either honor ORIGIN_RAW §2 (poles must not be constructionally
  prior to the difference) or concede that F-ev, like F-obj, needs two
  primitive poles and drop the "atoms are not elements" boast; drop the
  Design-S "dies without quotients" non-sequitur.
- **Verification bar.** ∅-axiom, no quotients; build stays clean; the
  design doc's claims match what is proved.
- **Expected size.** Medium (causal-order half) + small (doc fixes).

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

### B1 (gated on Q1–Q3, now cleared by session 2) — the single physics bridge
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
  before Q1–Q3 are secured (done: R1/R2/R3 confirmed).

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
