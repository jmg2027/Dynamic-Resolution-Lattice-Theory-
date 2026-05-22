# DRLT Falsifier Roster (G100 + parallel G87 manual catalog)

Complete catalog of DRLT's machine-verified impossibility +
distinguishability theorems.  Each entry is a `decide`-proven
negative claim (¬ P, x ≠ y, ¬ ∃, ¬ ∀).  These are the
**falsifiability bite-points** — what DRLT formally claims
CANNOT happen.

Source:
  · `research-notes/G100_decide_failure_mining.md` —
    automated catalog (135 entries)
  · `research-notes/G87_raw_native_emergence_audit.md`
    (parallel branch) — manual headline catalog (~10 entries)

The G100 automated catalog is the complete machine-verified
surface; G87 highlights the conceptually-load-bearing subset.

---

## Headline structural-impossibility theorems (G100 §3 not_exists, 8 entries)

The deepest finds — automatically discovered "no construction
exists" claims:

| # | Theorem | Significance |
|---|---------|--------------|
| 1 | `Chain/chain_uncountable` : ¬ ∃ f : Nat → (Nat → Raw), Function.Surjective f | Raw functions Nat → Raw are uncountable |
| 2 | `Max/maxLens_R4_fails` : ¬ ∃ conj : Nat → Nat, SwapMatching maxLens conj | maxLens has no swap-matching conjugation |
| 3 | `Reach/fin3_image_strict` : ∃ x : Fin 3, ¬ ∃ r : Raw, universalMorphism (Fin 3) r = x | Universal morphism into Fin 3 not surjective |
| 4 | `Reach/int_image_strict` : ∃ x : Int, ¬ ∃ r : Raw, universalMorphism Int r = x | Same for Int |
| 5 | `SumNotCoproduct/sum_not_coproduct_xor` : ¬ ∃ h : Sum Bool Bool → Bool, ... | Sum Bool Bool fails coproduct UP for XOR |
| 6-8 | 3 more (Cayley-Dickson tower + Lens layer) | |

These 8 are DRLT's **most-load-bearing negation claims**.  Each
formally closes a major candidate construction that would
otherwise be plausible.

---

## Category distribution (G100 §"Category breakdown")

| Category | Count | % | Significance |
|----------|------:|--:|--------------|
| `ne` (`x ≠ y`)              | 105 | 78 | distinguishability witnesses |
| `not` (general `¬ P`)       |  20 | 15 | Lens/property failures |
| `not_exists` (`¬ ∃ ...`)    |   8 |  6 | structural impossibility |
| `not_forall` (`¬ ∀ ...`)    |   2 |  1 | universality failures |

**Distinguishability dominates** (78 %) — consistent with
Raw's distinguishability primitive being the operational
essence of the 4 clauses.

---

## File concentration (G100 §"Top files")

| Count | File | Notes |
|------:|------|-------|
| 8 | `Lib/Math/CayleyDickson/Levels/Cayley.lean` | Octonion R3 (associativity) drops |
| 6 | `Theory/Raw/ParenthesizationDistinct.lean` | Parenthesisations distinct (a|b|slash) |
| 5 | `Lib/Math/CayleyDickson/Levels/Sedenion.lean` | Sedenion R4 (alternative) drops |
| 5 | `Lib/Math/CayleyDickson/Tower/CDDouble.lean` | CD doubling property drops |
| 5 | `Lib/Math/UniverseChain/Residue.lean` | Residue distinguishability (5 atomic levels) |
| 4 | `Lens/Instances/F9.lean` | Finite-field arithmetic |
| 3 | `Lens/Instances/Reach.lean` | Reach map failures |
| 3 | `Lens/Properties/Diagonal.lean` | Diagonal Lens properties |
| 3 | `Lens/Universal/Witnesses/Nat2.lean` | Nat-2 universal witnesses |
| 3 | `Lib/Math/CayleyDickson/Levels/SedenionHeavy.lean` | Heavy Sedenion |
| 3 | `Lib/Math/CayleyDickson/Tower/TowerFixedPoint.lean` | Tower fixed-point structure |
| 3 | `Lib/Math/Choice/CanonicalTruthChar.lean` | Canonical truth characterisation |
| 3 | `Lib/Math/DyadicFSM/Signature/SignatureBipartite.lean` | Bipartite signature |

### Cayley-Dickson tower as systematic negation factory

**4 CD files contribute 21 of 135 falsifiers (16 %)**:
  · Cayley.lean (8) — octonion structural drops
  · Sedenion.lean (5) — sedenion structural drops
  · CDDouble.lean (5) — doubling property drops
  · SedenionHeavy.lean (3)

Plus `TowerFixedPoint.lean` (3) and `Levels/CayleyOrder4Monopoly`
+ `SedenionOrder4Monopoly` falsifiers.

The CD construction **provably loses a property at each
level** → each loss is a decide-witnessed falsifier.  Strongly
methodological: the **CD tower IS a negation generator**, not
an incidental source of falsifiers.

---

## Sample `ne` (distinguishability) falsifiers

| File | Decl | Statement |
|------|------|-----------|
| `Theory/Raw.lean` | `T_ne_F` | `T ≠ F` |
| `Lens/Instances/AB/abLens` | `abLens_distinguishes` | `abLens.view rAAB ≠ abLens.view rABB` |
| `Lens/Instances/Bool` | `bool_not_ne_id` | `(!·) ≠ (id : Bool → Bool)` |
| `Lens/Instances/F9` | `F9.one_ne_i` | `F9.one ≠ F9.i` |
| `Lens/Instances/F9` | `F9.i_mul_i_nonzero` | `F9.mul F9.i F9.i ≠ F9.zero` |
| `DepthIncomparable` | `depth_distinguishes` | `Lens.depth.view rDeep ≠ Lens.depth.view rBalanced` |
| `Theory/Raw/ParenthesizationDistinct` | `((a/b)/c) ≠ (a/(b/c))` | × 6 distinct trees |
| `UniverseChain/Residue` | `residue_*_ne_*` | residue distinguishes 5 atomic levels |

**Naming conventions**:
  · `*_distinguishes` (~10 % of `ne` decls)
  · `*_ne_*` (~30 %)
  · `*_not_*` (in `not` category, ~50 %)

---

## Sample `not` (Lens-property failure) falsifiers (20 entries)

| File | Decl | Statement |
|------|------|-----------|
| `Lens/Instances/Bool` | `boolXorLens_not_homomorphism` | `¬ (∀ u v : Bool, !(xor u v) = xor (!u) (!v))` |
| `DepthJoin` | `three_classes_distinct` | three JoinEquiv classes mutually non-equivalent |
| `RefinesParity` | `parity_not_refines_leaves` | `¬ parityLens.refines Lens.leaves` |
| `Max` | `maxLens_not_injective` | `¬ Function.Injective maxLens.view` |
| `Parity` | `parityLens_not_injective` | `¬ Function.Injective parityLens.view` |

The `_not_homomorphism` / `_not_refines` / `_not_injective`
naming family maps out the **Lens incomparability lattice** —
which Lens-property combinations fail.

---

## Sample `not_forall` (universality failures, 2 entries)

| File | Decl |
|------|------|
| Various | `¬ ∀ ...` form (small category) |

Most universality failures are recast as `not_exists` (¬∃
witness of the universal claim), shifting to that category.

---

## G100 vs G87 manual roster

| | G87 (parallel branch, manual) | G100 (meta branch, automated) |
|---|------------------------------|------------------------------|
| Method | curated headline | shape-pattern matching |
| Coverage | ~5-10 entries | 135 entries |
| Focus | conceptually load-bearing | complete machine-verified surface |
| Cross-reference | each headline cited from research-notes | per-decl TSV |
| Strength | narrative coherence | comprehensiveness |

The two are **complementary**: G87 explains WHY specific
falsifiers matter; G100 confirms they exist + identifies the
full surface.

---

## How DRLT achieves the falsifiability surface

DRLT's `decide`-finitism (Pattern #2 + LESSONS_LEARNED Pattern #13)
operationalises falsifiability:

  · Every theorem in the 0-axiom standard is either decidable
    or rigorously proven.
  · 8 % of decls are decide-verified negative claims (G100).
  · 78 % of negation is distinguishability (`≠`) — directly
    using Raw's distinguishability primitive.

This makes DRLT's "falsifiability contract"
(`seed/AXIOM/04_falsifiability.md`) **measurable**: 135
decide-verified impossibilities provide the empirical basis.

---

## How to refresh this catalog

```
python3 tools/falsifier_mining_scan.py
# Regenerates _falsifier_rows.tsv with all 135 entries
# (or current count if new content added)
```

---

## Cross-references

  · `research-notes/G100_decide_failure_mining.md` — full
    automated catalog with categories + samples.
  · `research-notes/G87_raw_native_emergence_audit.md`
    (parallel branch) — manual headline catalog.
  · `seed/AXIOM/04_falsifiability.md` — falsifiability
    doctrine.
  · `LESSONS_LEARNED.md` Pattern #2 (decide-finitism) +
    Pattern #13 (quantitative profile).
  · `STRICT_ZERO_AXIOM.md` — 0-axiom standard.
