# Analysis — FluxMVT

**Status**: Closed (22 files in `Analysis/FluxMVT/` + ~30 in
adjacent sub-clusters; 182+ decls).  Largest single sub-cluster in
Analysis.
**Promoted from research-notes**: 2026-05-22.

Pattern 2 (narrative-from-scratch).

## Overview

**Flux-form Mean Value Theorem** in 213: chain of MVT instances
on **FluxCut** structures + dyadic-bracket modulus tracking.  No
classical ε-δ; flux-bracket arithmetic with explicit moduli per G40.

FluxMVT is the operational MVT used downstream by `Lib/Physics/Couplings/`
running-coupling derivations and `Lib/Physics/AlphaEM/` precision
work (Gram-self-energy term).

Per G110 (Tier-2 deep dive, 2026-05-22): **0 direct Raw atom
touches** in the 182-decl FluxMVT inventory — operates entirely on
the FluxCut + DyadicBracket carrier types.  Per the (α/β/γ)
Raw-derivation taxonomy (`theory/meta/raw_derivation_levels.md`),
FluxMVT lives at the **(β) structural-content** level: derived
mathematics built on generic Lean carriers without direct Raw-shape
references.

## Lean source

- **Sub-cluster**: `lean/E213/Lib/Math/Analysis/FluxMVT/` (22 files)
- **Adjacent**: FluxMVTHigh, FluxMVTClosure, FluxMVTApplications, FluxMVTGeneric
- **∅-axiom status**: PURE on production critical path

### File inventory (selected)

| Group | Files | Role |
|---|---|---|
| Core flux | `FluxCut`, `FluxDivergence`, `FluxCochain`, `FluxSeries` | Flux-form carrier + divergence + cochain + series |
| MVT | `FluxMVT`, `FluxMVTPolynomial`, `FluxMVTPassthrough`, `FluxMVTWitness`, `FluxMVTWitnessCombinators` | MVT statements + polynomial / passthrough variants + explicit witnesses |
| FTC | `FluxFTCPolynomial` | Fundamental Theorem of Calculus in polynomial setting |
| Pass-through | `FluxPassthroughClass`, `FluxPassthroughCatalog` | Class machinery for MVT-pass-through |
| Equivalences | `FluxEquiv` | Equivalence of flux statements |
| Propagation | `FluxMVTPropagate`, `MVTWitnessChain` | Chain of MVT instances propagating across coupling levels |
| **Unit bracket** | `UnitBracketReduce`, `UnitBracketReduceSum` (new 2026-05-22) | Unit-bracket reduction lemma (G117 TH-1 / REAL-1+REAL-2 template) |

The `UnitBracketReduce*` files (2026-05-22 marathon, REAL-1+REAL-2
closure) provide the *generic template* for collapsing flux
expressions with unit brackets — replaces 12 ad-hoc instances per
HANDOFF Part 5.

## The narrative

### FluxCut as the carrier

`FluxCut` is a Real213-cut-based structure carrying flux quantity
+ explicit modulus.  All FluxMVT operations preserve modulus
(per G40 discipline).  Mean value statements have form:

> ∀ FluxCut input, ∃ explicit witness w such that the flux
> output equals the MVT identity at w, with bracket-precision N.

The witness is *part of the data*, not Skolemized — same pattern as
G31 trajectory-as-witness + G40 modulus.

### Telescoping = conservation

Per Gemini Pro's observation (round-2 multi-agent debate in
`claude/research-notes-organization-Gr3Tp`): FluxMVT's **dyadic
telescoping** (each bracket cancels the next at the boundary) is
the 213-native identity of:
- Gauss divergence theorem (∮ F · dA = ∭ div F dV)
- Conservation laws (∂_μ J^μ = 0 → integrated flux invariant)

The cancellation IS the conservation; no separate "conservation
law" axiom needed.  This identification needs an explicit chapter
or theorem citation to fully land — currently in chapter as
observation, not yet capstoned in Lean.

### Connection to physics-side

- `Lib/Physics/Couplings/RunningGap.lean` uses MVTWitnessChain to
  propagate α_em IR/UV gap across coupling levels
- `Lib/Physics/AlphaEM/GramSelfConsistency.lean` uses the
  Flux passthrough class for α²/d² self-energy

## Connection

- `theory/math/analysis/minimal_root.md` (G31 DyadicSearch sibling) — trajectory-as-witness shares the modulus discipline
- `theory/math/modulus.md` (G40) — explicit moduli
- `theory/math/real213.md` — Real213 carrier underlies FluxCut
- `theory/physics/couplings.md` — primary downstream consumer
- `research-notes/G110_fluxmvt_deep_dive.md` — 22-file Tier-2 deep dive (2026-05-22)
- `research-notes/archive/G118_marathon_deferred_items.md` — REAL-1+REAL-2 closure registered

## Open frontier

- **Telescoping ↔ Gauss / conservation identification**: still
  observation-level, not yet a citable theorem in Lean.  Worth
  formalizing as `FluxMVT/Telescoping_Conservation.lean`.
- **MVT chain at higher depth**: current chains close at 3-4
  bracket levels; deeper chains (d-depth-5 per resolution limit)
  pending.
- Per G118 REAL-RES4 follow-ups in deeper FluxMVT analysis.
