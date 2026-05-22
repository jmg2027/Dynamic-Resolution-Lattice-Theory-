# Cosmology

**Status**: Closed (8 files; F26 η_B falsifier).
**Promoted from research-notes**: 2026-05-22.

Pattern 2.

## Overview

Cosmological observables: **Hubble constant**, N_eff (effective
neutrino species), dark energy, gravity shadow, horizon information.
Includes **F26 falsifier**: `η_B · 10¹⁰ ∈ [5, 7]` (baryon-to-photon ratio).

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/Cosmology/` (8 files)
- **Umbrella**: `Cosmology.lean`
- **∅-axiom status**: PURE

## Narrative

Cosmological observables in DRLT derive from the universe-chain
closure (per `theory/math/universe_chain.md`) — the same atomic
substrate that produces the gluon octet at the gauge level
produces large-scale observables at the cosmological level via
the resolution-limit `N_U = 5²⁵` count.

**F26 falsifier (`EtaBFalsifier.lean`)**: η_B (baryon-to-photon
ratio) × 10¹⁰ brackets to [5, 7].  Measured ~6.1 sits in bracket.
Measured value outside [5, 7] · 10⁻¹⁰ would falsify.

Hubble constant, N_eff, dark energy density similarly bracketed.

## Connection

- `theory/math/universe_chain.md` — atomicity → cosmological scale via N_U
- `catalogs/falsifiers.md` — F26 entry
