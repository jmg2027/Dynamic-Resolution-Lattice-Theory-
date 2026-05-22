# research-notes/archive/hodge/ — Hodge program closure (archived)

The Hodge-conjecture-translation arc, formalised in
`lean/E213/Lib/Math/HodgeConjecture/`.  Six (now seven, incl. G12)
exploratory notes that fed into the closed Lean program (31 master
capstones, per G10).

**Archived 2026-05-21**: this cluster has been promoted to a
`theory/` chapter at `theory/math/cohomology/hodge_conjecture.md`.
The notes here are kept as **record of the path** — read the
theory chapter for current narrative.

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

  - **`theory/math/cohomology/hodge_conjecture.md`** — promoted
    narrative (read this for current state).
  - `lean/E213/Lib/Math/HodgeConjecture/INDEX.md` — formal-side
    navigation (67 .lean files, 31 master capstones).
  - `lean/E213/Lib/Math/HodgeConjecture/Foundation/Complete.lean` —
    master theorem `hodge_conjecture_213_complete`.
  - `research-notes/INDEX.md` — top-level note registry.

## Note on framing (2026-05-05 audit)

G6 §1–§7 was originally drafted under the deprecated "Finitism is
Forced" header.  G6 §0 (corrected position) is now canonical and
should be read first; §1–§7 retain the math content but the
framing language is corrected per
`seed/RESOLUTION_LIMIT_SPEC.md` §3.  G10 echoes the corrected
position implicitly throughout.
