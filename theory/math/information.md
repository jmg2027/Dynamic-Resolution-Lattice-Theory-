# Information 213

**Status**: Closed (8 files; marathon-completed).

## Overview

213-native information theory: **`Information.Bit`** as the atomic
distinguishing unit, `bitsAfterBisections`, depth-modulus bridges.
Replaces continuous Shannon entropy with **discrete bit-counting**.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Information/` (8 files)
- **Umbrella**: `Information.lean`
- **Blueprint**: `blueprints/math/12_information_213.md`
- **∅-axiom status**: PURE

## Narrative

Per Mingu's framing: distinguishing IS the primitive (per
`seed/AXIOM/01_residue.md` "Linguistic inevitability").  Information
in 213 is what survives this primitive:

- 1 distinguishing = 1 bit
- N distinguishings = N bits (independent) or `log_2(k)` bits
  (k mutually exclusive)
- `bitsAfterBisections n` = bits available after n binary cuts
  = `n` exactly

The 213-native rate (1 bit per distinguishing) replaces the
continuous Shannon `−Σ p log p` with the discrete count.  At the
DRLT physics level, Holevo's bound becomes "1 hinge = 1 bit"
structurally.

## Connection

- `theory/math/cross_domain_unification.md` (C6) — Information as
  paradigm instance
- `theory/physics/alpha_em/precision_derivation.md` C5 Step 5 —
  H¹(K) rank 8 = 2³ = 3 bits = 1 octal digit
