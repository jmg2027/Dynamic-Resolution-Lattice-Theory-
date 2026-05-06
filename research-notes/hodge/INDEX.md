# research-notes/hodge/ — Hodge program closure (six notes)

The Hodge-conjecture-translation arc, formalised in
`lean/E213/Lib/Math/Cohomology/HodgeConjecture/`.  Six exploratory
notes that fed into the closed Lean program (138+ strict ∅-axiom
theorems, per G10).

## Reading order

| # | File | Theme | Lean closure |
|---|---|---|---|
| 1 | `G6_hodge_213_translation.md` | Standard Hodge ↔ 213 dictionary; redundant completed-infinity packaging stripped (canonical reading: §0 corrected position) | `Foundation/Conjecture.lean`, `Foundation/Canonical.lean`, `Foundation/Filled.lean` |
| 2 | `G7_lens_initiality_cup_blueprint.md` | Lens initiality + cup-subring blueprint (uniform-proof scheme) | `Foundation/LensCata.lean` |
| 3 | `G8_hodge_213_bridge_to_standard_math.md` | HC²¹³ ↔ standard HC bridge | `Bridge/` cluster |
| 4 | `G9_hodge_conjecture_complete.md` | HC²¹³ closure narrative | `Foundation/Complete.lean` |
| 5 | `G10_post_hodge_program.md` | 17 post-HC classical theorems programme | `Refinement/`, `Toolkit/`, `Pairing/`, `Structure/` |
| 6 | `G11_galois_at_eighty.md` | Historical-philosophical: Galois at eighty | (no Lean — narrative) |

## Status

All six notes correspond to closed Lean work.  The `Bridge/` cluster
in HodgeConjecture/ contains the explicit Lean ↔ standard HC
correspondence; `Refinement/` adds the 17 Hodge-adjacent classical
theorems summarised in G10.

## Cross-references

  - `lean/E213/Lib/Math/Cohomology/HodgeConjecture/INDEX.md` — formal
    side navigation.
  - `lean/E213/Lib/Math/Cohomology/HodgeConjecture/Foundation/` — Lens
    initiality + cup-chain core.
  - `research-notes/INDEX.md` — top-level note registry.

## Note on framing (2026-05-05 audit)

G6 §1–§7 was originally drafted under the deprecated "Finitism is
Forced" header.  G6 §0 (corrected position) is now canonical and
should be read first; §1–§7 retain the math content but the
framing language is corrected per
`seed/RESOLUTION_LIMIT_SPEC.md` §3.  G10 echoes the corrected
position implicitly throughout.
