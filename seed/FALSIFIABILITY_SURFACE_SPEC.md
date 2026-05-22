# Falsifiability surface — quantitative profile

> **Canonical**: quantifies the falsifiability rule of
> `seed/AXIOM/04_falsifiability.md` §5.2.1 as an operational
> footprint in the Lean corpus.  Pairs with the manual
> measurement-falsifier roster in `catalogs/falsifiers.md` and
> the auto-discovered roster in `catalogs/falsifier-roster.md`.

The falsifiability rule says: "If any result is shown to be
absolutely impossible without adding an axiom, the entirety of
213 is discarded."  This file measures how DRLT operationally
enacts that rule — which kinds of impossibility / distinguishability
statements the corpus actually proves.

---

## Two surfaces

### Physics surface (`catalogs/falsifiers.md`)

26 manually-curated entries (F1-F26): atomicity (d=5), neutrino
ordering, θ_QCD, 4th generation absence, Cabibbo λ, m_p, m_t/m_c,
η_B, magic numbers, etc.

Each predicts what nature must satisfy if 213 holds.  Violation
by measurement = entire framework discarded.  This is the surface
that an experimentalist confronts.

### Structural surface (`catalogs/falsifier-roster.md`)

135 auto-discovered entries from `tools/falsifier_mining_scan.py`.  Each is a Lean theorem of the shape "X ≠ Y" or "¬ ∃ ..."
or "¬ ∀ ...", body-verified by `decide` / `native_decide`.

Each certifies what 213 itself forbids — internal impossibility
of construction, distinguishability of would-be-equal candidates,
non-existence of universals that would over-extend the positive
content.

---

## Quantitative profile (decide-failure falsifier mining, 2026-05-21 scan)

### Category breakdown

  · 135 decls match falsifier shape (negation marker + decide body).
  · 8 % of all tactic-bodied decls (population 1,117).
  · Compared to ~36 % positive `[decide]` proofs: roughly
    **1 in 4 decide-proofs is a falsifier**.

| Category | Count | %   | Operational meaning |
|----------|------:|----:|---------------------|
| `ne` (`x ≠ y`)         | 105 | 78 % | Distinguishability witness — two candidates differ |
| `not` (general `¬ P`)  |  20 | 15 % | Structural impossibility — P cannot be exhibited |
| `not_exists` (`¬ ∃`)   |   8 |  6 % | No construction satisfies the predicate |
| `not_forall` (`¬ ∀`)   |   2 |  1 % | A counter-instance breaks a universal claim |

**Why `≠` dominates (78 %)**: the Raw axiom's operational primitive
is *distinguishing* (Clause 1).  Non-distinguishing = identity.
Most falsifiers therefore record "these two would-be-same things
are actually different" — operationally invoking Clause 1.

---

## The 8 deepest impossibilities

These are the load-bearing negation claims — DRLT's machine-checked
"this candidate construction cannot exist" theorems.

| # | Decl | Statement |
|---|------|-----------|
| 1 | `Chain.chain_uncountable` | Raw functions `Nat → Raw` are uncountable: `¬ ∃ f, Function.Surjective f` |
| 2 | `Max.maxLens_R4_fails` | `maxLens` admits no swap-matching conjugation by `Nat → Nat` |
| 3 | `Reach.fin3_image_strict` | Universal morphism to `Fin 3` is not surjective |
| 4 | `Reach.int_image_strict` | Universal morphism to `Int` is not surjective |
| 5 | `SumNotCoproduct.sum_not_coproduct_xor` | `Sum Bool Bool` fails the coproduct property for XOR |
| 6-8 | (CayleyDickson tower + Lens layer) | three additional structural impossibilities |

These bound DRLT's positive side: without them, the positive content
could be trivially over-extended into territory the residue
doesn't support.

---

## The Cayley-Dickson tower as negation factory

The CD tower contributes 21 of the 135 (16 %):

  · `CayleyDickson/Levels/Cayley.lean`: 8 — octonion
    non-associativity witnesses.
  · `CayleyDickson/Levels/Sedenion.lean` + Heavy: 5 + 3 — sedenion
    non-alternative.
  · `CayleyDickson/Tower/CDDouble.lean`: 5 — doubling-construction
    mismatches.
  · `Lib/Math/UniverseChain/Residue.lean`: 5 — residue distinguishes
    5 atomic levels.

Each tower level provably *loses* an algebraic property
(commutativity → associativity → alternativity → power-associativity
→ ...).  Decide-verifying the loss creates a falsifier.

**The Cayley-Dickson construction IS a systematic negation
generator** — each level a fresh batch of structural impossibilities.

---

## Connection to the falsifiability doctrine

`seed/AXIOM/04_falsifiability.md` §5.2.1 says:

> 213 must never require any external axiom addition.  If any
> result is shown to be absolutely impossible without adding an
> axiom, the entirety of 213 is discarded.

The 135 auto-discovered + 26 manual falsifiers are the **active
content** of that rule:

  · Each `≠` witness is a Clause-1 distinguishing claim being
    operationally cashed in.
  · Each `¬ ∃` is a non-existence theorem closing a candidate
    construction.
  · Each `¬ ∀` is a counter-instance breaking a would-be universal.

If any of these were to fail (e.g., a `≠` witness shown to be `=`
under some valid Lens), it would either:

  (a) reveal a misclassification (the Lens choice was wrong → fix
      the Lens), OR
  (b) reveal that adding an axiom is genuinely necessary → trigger
      the falsifiability rule → discard 213.

Per the rule, (b) is the dangerous case.  The corpus is structured
so that (a) is the recoverable interpretation; (b) has not been
observed.

---

## Operational signature

The Pattern #2 quantification (`LESSONS_LEARNED.md`):

  · 1,178 single-tactic `[decide]` proofs.
  · 135 negative-side `decide` proofs (this catalog).
  · ~44 % of all decls are decide-routed (positive or negative).

Pattern #2 is not a methodological choice; it's the operational
signature of the corpus.  Falsifiability is mechanically enforced
because decide is the lingua franca of both positive proof and
negative impossibility.

---

## Regenerating

```
python3 tools/falsifier_mining_scan.py
# → TSV with all 135 entries (decl, file, category, body snippet)
```

TSV is gitignored.  Re-running takes ~1 minute.

---

## Cross-references

  · `seed/AXIOM/04_falsifiability.md` §5.2.1 — the discard rule.
  · `catalogs/falsifiers.md` — manual physics-falsifier roster
    (F1-F26).
  · `catalogs/falsifier-roster.md` — auto-discovered structural
    roster (135 entries).
  · `LESSONS_LEARNED.md` Pattern #2 — decide-finitism doctrine.
  · `research-notes/archive/metascan/G100_decide_failure_mining.md` —
    full methodology + per-category sample listings.
  · `research-notes/archive/metascan/G105_namespace_shape_and_full_recursor_inventory.md`
    §2.5 — `Bool.casesOn` 1,681 invocations (the operational
    backbone of decide-based falsification).
