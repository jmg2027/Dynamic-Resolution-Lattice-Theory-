# Falsifier Roster — auto-discovered + manual

CAT-1 per `research-notes/G107_action_items_registry.md` §10.2.

Two complementary surfaces of DRLT's falsifiability footprint:

  · **Manual headline set** — `catalogs/falsifiers.md` (F1-F26):
    physical-measurement falsifiers curated by physics relevance.
    What an experimentalist would compare against.
  · **Auto-discovered roster** — this file: every machine-verified
    impossibility / distinguishability theorem in the Lean corpus,
    mined by `tools/falsifier_mining_scan.py` (G100).
    What the Lean kernel certifies as 213-internal "what cannot be".

Together they cover both the **physics surface** (will be falsified
by external measurement) and the **structural surface** (already
falsified by 213-internal decide).

---

## Tally (G100 §Results, 2026-05-21)

  · **135 decls** match the falsifier shape (negation marker +
    `decide`/`native_decide` body).
  · **8 % of all tactic-bodied decls** (population 1,117) are
    machine-verified impossibilities / distinguishabilities.
  · For comparison: ~36 % of decls are positive `[decide]` proofs
    (G91).  Roughly 1 in 4 decide-proofs is a falsifier.

### Category breakdown

| Category | Count | %  | Operational meaning |
|----------|------:|---:|---------------------|
| `ne` (`x ≠ y`)         | 105 | 78 % | Distinguishability witness — two candidates differ |
| `not` (general `¬ P`)  |  20 | 15 % | Structural impossibility — P cannot be exhibited |
| `not_exists` (`¬ ∃`)   |   8 |  6 % | No construction satisfies the predicate |
| `not_forall` (`¬ ∀`)   |   2 |  1 % | A counter-instance breaks a universal claim |

**Why `≠` dominates (78 %)**: the Raw axiom's operational
primitive is *distinguishing*; non-distinguishing = identity.
Most falsifiers therefore record "these two would-be-same things
are actually different".

---

## Top falsifier-producing files (G100 §Top files)

| count | file | what it certifies |
|------:|------|-------------------|
| 8 | `Lib/Math/CayleyDickson/Levels/Cayley.lean` | octonion non-associativity |
| 6 | `Theory/Raw/ParenthesizationDistinct.lean` | `((a/b)/c) ≠ (a/(b/c))` over 6 trees |
| 5 | `Lib/Math/CayleyDickson/Levels/Sedenion.lean` | sedenion non-alternative |
| 5 | `Lib/Math/CayleyDickson/Tower/CDDouble.lean` | doubling-construction mismatches |
| 5 | `Lib/Math/UniverseChain/Residue.lean` | residue distinguishes 5 atomic levels |
| 4 | `Lens/Instances/F9.lean` | finite-field 9-element non-trivialities |
| 3 each | `Lens/Instances/{Reach,Diagonal}.lean`, ... | Lens-layer distinguishabilities |

**Methodological observation**: the Cayley-Dickson tower
contributes 21 of 135 (16 %).  Each level provably *loses* an
algebraic property (commutativity → associativity → alternativity
→ power-associativity → ...).  Decide-verifying each loss yields
a falsifier.  **The Cayley-Dickson construction IS a systematic
negation generator.**

---

## The 8 `not_exists` deep impossibilities (G100 §2)

These are the load-bearing negation claims — DRLT's machine-
checked impossibility-of-construction theorems.

| # | Decl | Statement |
|---|------|-----------|
| 1 | `Chain.chain_uncountable` | Raw functions `Nat → Raw` are uncountable: `¬ ∃ f : Nat → (Nat → Raw), Function.Surjective f` |
| 2 | `Max.maxLens_R4_fails` | `maxLens` has no swap-matching conjugation by `Nat → Nat` |
| 3 | `Reach.fin3_image_strict` | Universal morphism to `Fin 3` is not surjective |
| 4 | `Reach.int_image_strict` | Universal morphism to `Int` is not surjective |
| 5 | `SumNotCoproduct.sum_not_coproduct_xor` | `Sum Bool Bool` fails the coproduct property for XOR |
| 6-8 | CayleyDickson tower + Lens layer | three additional structural impossibilities |

**Interpretation**: these formally close candidate constructions
that "look like they should work" but don't.  They bound DRLT's
positive side — without them, the positive theory could be
trivially over-extended.

---

## Cross-link to manual catalog

The 26 manual entries in `catalogs/falsifiers.md` are **physics**
falsifiers (atomicity, neutrino ordering, θ_QCD, Cabibbo λ,
m_t/m_c, η_B, etc.).  They predict what nature must satisfy if
213 holds.

The 135 here are **structural** falsifiers (Raw-tree
distinguishabilities, Cayley-Dickson tower losses, Lens-layer
non-conjugacies).  They certify what 213 itself forbids.

Overlap is small (~5 entries in both lists): the manual catalog
tracks *measurement* falsifiers, this catalog tracks *kernel-checked
impossibility* theorems.  The two together form the falsifiability
surface DRLT exposes.

---

## Regenerating the full roster

```
python3 tools/falsifier_mining_scan.py
```

Produces TSV with each of the 135 entries (decl, file, category,
body snippet).  TSV is gitignored — rerun anytime.

See G100 for the full methodology and per-category sample listings.
