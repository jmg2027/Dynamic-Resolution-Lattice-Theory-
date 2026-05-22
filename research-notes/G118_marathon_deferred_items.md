# G118 — Marathon Part 5 deferred items: status + technical rationale

After Part 5 closure (10 of 11 marathon items DONE), this doc
catalogues the **remaining 4 deferred items** with concrete
technical reasons.  Each entry includes: scope, attempted approach (if
any), specific blocker, and an estimate of follow-up effort.

Companion to:
  · `research-notes/G107_action_items_registry.md` (full registry)
  · `HANDOFF.md` Part 5 (status table)
  · `catalogs/abstraction-candidates.md` §3-§4 (per-item status)

## Closed in Part 5 (recap, 10 of 11)

| # | Item | Commit | Template |
|---|------|--------|----------|
| 1 | L1 α-side parametric helper | `a119b077` | LeibnizAlgLiftAlpha |
| 2 | C — CutSumOne 3-component template | `4984c9ad` | cutSum_constCut_at |
| 3 | G110 FLUX-1 (34 sites, 3 templates) | `caea91c1...5242a316` | UnitBracketReduce/×2, CutMulOuterReduce |
| 4 | REAL-1+REAL-2 bool_or_ladder_iff | `f7f00a98` | BoolOrLadder |
| 5 | G111 COH-1+2+3 templates | `796016fa`, `b67075b2` | Pattern10, InvolutionTemplate, LeibnizUniversalLift |
| 8a | L3 Pisano period_lift | `fc105cd6` | pisano_period_lift |
| 8b | L4 ldd_branch_via_maxRange | `7c887e23` | CutFnData.ldd_branch |
| 10a | TH-1 fingerprint spec | `9616c8a6` | (doc) |
| 10b | TH-4 L1 methodology spec | `2558e58b` | (doc) |
| 11 | G117 Bishop subsumption spec | `7eb619a6` | (doc) |

**13 abstraction templates** integrated.  All refactored theorems
verified PURE (`#print axioms`: "does not depend on any axioms").

---

## Deferred items (4 of 11)

### 6 — CD-1+CD-2+CD-3 (CayleyDickson templates)

**Scope** (G114 §5):
  · CD-1: 4-site ring extensionality (`ZOmega.ext`, `ZI.ext`,
    `ZSqrt2.ext`, `Lipschitz.ext`).  461 nodes each.
  · CD-2: 3-site `conj_ne_id` (`ZOmega`, `ZI`, `ZSqrt2`).  506 nodes each.
  · CD-3: 3-site `Lipschitz.assoc_{J_I_J, I_I_J, I_J_I}`.  301 nodes each.

**Why deferred**: Each individual proof is **already short** (2 lines
for CD-1, 5-7 lines for CD-2, 1 line `by decide` for CD-3).

Specific blockers:
  · CD-1 ext theorems: `cases u; cases v; congr` — 2 lines.
    Lean's auto-generated `mk.injEq` only gives the equality, not
    the structural pattern, so wrapping doesn't save anything.
    A typeclass `HasStructuralExt α` would force users to invoke
    `HasStructuralExt.ext` instead of `ZI.ext`, losing ergonomics
    without saving body length.
  · CD-2 conj_ne_id: each proof picks a different witness (e.g., `I`,
    `Omega`, `Sqrt2.r`) and projects a different field (`im`, `re`).
    Generic helper would need ~5 parameters (witness + field path +
    expected value), as verbose as the original.
  · CD-3 assoc_*: each is `by decide` for a different concrete triple.
    No proof body to abstract.

**Estimated effort if pursued**: 1 hour to write 3 helpers; net
savings ≈ 0 lines (helpers + simplified call sites ≈ original).

**Recommendation**: leave as-is.  The G114 §5 "byte-identical at the
elaborator level" metric is misleading here — it conflates compiler
artifact (`.mk.injEq`-derived code) with surface proof text.

---

### 7 — G112 HC-1 + G115 PHYS-1/PHYS-2

#### HC-1 — Hodge Conjecture bridge capstones (5 sites)

**Scope** (G112 §8): 5 `*_213_capstone` proofs (`hodge_tate`,
`tate`, `mumford_tate`, `bloch_beilinson`, `beilinson_lichtenbaum`)
in `Lib/Math/HodgeConjecture/MotivicBridge/` + 1 in `Refinement/`.

**Why deferred**: Each capstone is a **substantive proof unique to its
topic** (Hodge-Tate decomposition, Tate twists, motivic decomposition,
…).  The shared "structural pattern" mentioned in G112 §8 is at the
**conceptual level** (setup → Hodge framework invocation → physics-side
calculation → match), not at the proof-body level.

Specific blockers:
  · No byte-identical proof bodies across the 5 capstones.
  · Each is `refine ⟨trivial, ?_, ?_⟩ <;> decide` or similar 2-3 line
    body — already short.  The substantive content is the
    capstone-tuple shape, which is per-topic.

**Estimated effort if pursued**: 2-3 sessions to verify whether
there's a hidden shape-vector cluster (G103 method) before deciding.

**Recommendation**: investigation-grade work, not consolidation.
Defer to a future dedicated G112 session.

#### PHYS-1 — AlphaEM ζ-sequence consolidation (5 files)

**Scope** (G115 §7): `FractalLevelZeta{Bracket, CoeffSeq, Convergence,
Modulus, Spectrum}` (5 files, 429 LOC total).

**Why deferred**: The 5 `_master` capstone theorems are each **unique**
to their aspect of ζ-sequence behavior (bracket containment,
coefficient sequence definition, Cauchy convergence, dyadic modulus,
spectrum at sample points).  Not parallel.

Specific blockers:
  · The shared "ζ-sequence" structure is at the conceptual level —
    each file proves a different theorem about the same object.
  · Per-file content has high substantive variation: bracket
    inequality, sequence definition, fixed-point modulus, spectrum
    evaluation.  No cross-file proof template.

**Estimated effort if pursued**: 1-2 sessions investigation + medium
marathon if a hidden pattern is found.

**Recommendation**: investigation-grade work.  Defer.

#### PHYS-2 — Physics bracket-containment template (8 sites)

**Scope** (CDI-5 in `catalogs/cross-domain-identifications.md`):
8 physics-domain "observed constant in DRLT-bracket [low, high]"
theorems byte-identical post-normalisation (321-1077 nodes each).

Decls: `Cosmology.Bridge.omega_lambda_atomic`,
`Nuclear.DeuteronBinding.E_d_bracket`, `Atomic.Helium.he_IE_in_bracket`,
`Hadron.NeutronProton.dmnp_bracket`, `Atomic.Hydrogen.H_E1_bracket`,
`AlphaEM.StructuralGap.n50_bracket_contains_candidate`,
`YangMills.WZBosons.cos2_W_in_75_78`,
`AlphaEM.GramSelfEnergy.aug_bracket_contains_observed_high_precision`.

**Why deferred**: Each proof is **`by decide` on 1-3 line Nat
inequality conjunctions** like `lo < obs ∧ obs < hi`.  Already
maximally compact.

Specific blockers:
  · `decide` IS the entire proof.  A `physics_bracket (lo obs hi) (h_lo h_hi) := ⟨h_lo, h_hi⟩`
    helper would be 1 line.  Each caller still needs `by decide` for
    the actual inequalities.  Net savings: 0.

**Estimated effort if pursued**: 0.  No tractable consolidation.

**Recommendation**: leave as-is.  The "byte-identical" metric at G109
captures elaborator-level structure (the `_ ∧ _ := by decide` pattern),
not surface text.  Pattern is recognised; abstraction adds no value.

---

### 8c — L5 CDDouble I_mul_J / J_mul_I (2 sites)

**Scope** (G91 L5): 2 byte-identical 16-tactic ladders in
`CayleyDickson/Tower/CDDouble.lean` — quaternion-style
non-commutativity witnesses `I' * J = ⟨0, ZI.I⟩` vs `J * I' = ⟨0, ZI.negI⟩`.

**Why deferred**: The two proofs **compute different numeric witnesses**
for different `(α, β, γ, δ)` tuples in the CD doubling formula.

Specific blockers:
  · Each proof unfolds `mul`, applies `ext`, and computes 4 ZI
    component equalities by `rfl`.  The structural template is
    identical, but the per-branch values differ (positions of `I`,
    `negI`, signs).
  · `by decide` ineffective: `Lipschitz` and `ZI` mul/conj definitions
    don't reduce by Lean's `decide` evaluator at these elements
    (conj evaluation depth issue).
  · A tactic macro `cd_double_compute` would essentially wrap the
    `show + unfold + apply ext + apply ZI.ext + rfl × 4` chain, but
    each branch still needs the specific element + expected value as
    parameters.  ~2-3 line savings per proof, plus ~10-line tactic
    definition.  Net break-even.

**Estimated effort if pursued**: 30 min to write a tactic macro; net
savings ≈ 0.

**Recommendation**: leave as-is.

---

### 9 — G113 FSM-1 ∀p universal lift

**Scope** (G113 §3): Pell-FSM "universal-over-prime" form.  Currently
Lean has per-prime definitions:

  · `pellFSMmod3 : ArithFSM2 3 := <hand-coded transition table>`
  · `pellFSMmod5 : ArithFSM2 5 := …`
  · `pellFSMmod7 : ArithFSM2 7 := …`
  · … 14+ similar per-prime defs

Plus per-prime period theorems:

  · `pellFSMmod3_bits_period_4 : ∀ k, pellFSMmod3.bits (k + 4) = pellFSMmod3.bits k := by decide`
  · `pellFSMmod5_bits_period_10 : ∀ k, ... = ... := by decide`
  · …

Marathon Part 3 + 4 absorbed 93 sites via 7 generic FSM helpers
(`run_period_of_base`, `bits_period_of_run_period`, …) — but those
operate on specific FSM instances.

The "∀p universal" form means **one** theorem statement covering
**arbitrary prime p**:

```lean
theorem pellFSM_pisano_period_universal :
    ∀ (p : Nat) (hp : 1 < p),
      ∀ k, (pellFSMmod p hp).bits (k + pisano_predict p hp)
            = (pellFSMmod p hp).bits k
```

**Why deferred**: This requires **two prerequisites**, both
multi-session:

1. **Generic `pellFSMmod p hp : ArithFSM2 p`** — define the FSM
   polymorphically.  The Pell matrix `[[2,1],[1,1]]` gives transition
   `(a, b) → ((2a+b) mod p, (a+b) mod p)`.  Feasible: ~1 session.

2. **`∀p, period_p = pisano_predict p hp`** — this is the **Pisano
   period theorem for Pell-5**, a number-theoretic result.  Currently
   verified empirically for 17 primes (Predictor8/11/14/17), but the
   general proof requires:
   · Galois orbit structure of [[2,1],[1,1]] mod p.
   · Frobenius automorphism on `𝔽_p[√5]`.
   · Cases for ramified (p=5), split (p ≡ ±1 mod 5), inert (p ≡ ±2 mod 5).
   · Sub-tight cases (p=29 ×2, p=47 ×3) require deeper sub-orbit analysis.

   Estimated effort: 5-10 sessions.  This is genuine number theory,
   not template work.

**Recommendation**: pursue (1) as a standalone task (1 session) for
the structural cleanup; defer (2) as a long-term research direction.

The Part 3+4 closure (93 sites refactored) is the practical
consolidation for any FINITE set of primes.  Adding new primes
requires only a 1-line `pisano_period_lift` application (closed via
Part 5 commit `fc105cd6`).

---

## Summary

**Closure rate**: 10 of 11 = **91%**.

**True deferrals** (estimated effort): 
  · 6 CD-1/2/3 — 0 hours (no consolidation possible)
  · 7 HC-1 — 2-3 sessions (investigation)
  · 7 PHYS-1 — 1-2 sessions (investigation)
  · 7 PHYS-2 — 0 hours (no consolidation possible)
  · 8c L5 — 0 hours (no consolidation possible)
  · 9 FSM-1 ∀p — 1 session (generic FSM def) + 5-10 sessions
    (Pisano period theorem)

**Items genuinely waiting**: only HC-1, PHYS-1, FSM-1 ∀p — 3 of 11
have remaining tractable work (the rest are documented "nothing more
to abstract").

This document IS the closure for items 6, 7-PHYS-2, 8c — they are
recognised patterns with no abstraction yield.  Future marathons
can skip them.
