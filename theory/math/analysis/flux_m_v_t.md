# Analysis — FluxMVT

**Status**: Closed (22 files in `Analysis/FluxMVT/` + ~30 in
adjacent sub-clusters; 182+ decls).  Largest single sub-cluster in
Analysis.

## Overview

**Flux-form Mean Value Theorem** in 213: chain of MVT instances
on **FluxCut** structures + dyadic-bracket modulus tracking.  No
classical ε-δ; flux-bracket arithmetic with explicit moduli per ε-δ modulus.

FluxMVT is the operational MVT used downstream by `Lib/Physics/Couplings/`
running-coupling derivations and `Lib/Physics/AlphaEM/` precision
work (Gram-self-energy term).

Per the FluxMVT Tier-2 deep dive: **0 direct Raw atom
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
| **Unit bracket** | `UnitBracketReduce`, `UnitBracketReduceSum` | Unit-bracket reduction lemma (Bishop comparison TH-1 / REAL-1+REAL-2 template) |

The `UnitBracketReduce*` files provide the *generic template* for
collapsing flux expressions with unit brackets — one identity
replaces ad-hoc instances at each use site.

## The narrative

### FluxCut as the carrier

`FluxCut` is a Real213-cut-based structure carrying flux quantity
+ explicit modulus.  All FluxMVT operations preserve modulus
(per ε-δ modulus discipline).  Mean value statements have form:

> ∀ FluxCut input, ∃ explicit witness w such that the flux
> output equals the MVT identity at w, with bracket-precision N.

The witness is *part of the data*, not Skolemized — same pattern as
trajectory-as-witness + ε-δ modulus.

### Telescoping = conservation

FluxMVT's **dyadic telescoping** (each bracket cancels the next at
the boundary) is the 213-native identity of:
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

- `theory/math/analysis/minimal_root.md` (DyadicSearch sibling) — trajectory-as-witness shares the modulus discipline
- `theory/math/analysis/modulus.md` — explicit moduli
- `theory/math/numbersystems/real213.md` — Real213 carrier underlies FluxCut
- `theory/physics/couplings.md` — primary downstream consumer

## Telescoping ↔ Gauss / Conservation — closed (TelescopingConservation.lean)

`FluxMVT/TelescopingConservation.lean` (6 PURE + 2 structures)
makes the multi-agent observation a citable Lean theorem:

  · `Adjacent db₀ db₁` — same exponent + `db₀.numB = db₁.numA`
    (i.e., the shared wall cut matches).
  · `adjacent_walls_match` — adjacency ⇒ `db₀.rightCut = db₁.leftCut`.
  · ★ `flux_edge_match` — local edge-matching identity:
    `(fluxAlong f db₀).forward = (fluxAlong f db₁).backward`.
  · `flux_triple_telescope` (n=3 chain) and `flux_quad_telescope`
    (n=4 chain) — both interior walls cancel by the same pattern.
  · ★★★★ `gauss_conservation_telescope` — capstone:
      (a) interior walls cancel pairwise,
      (b) only the outer boundary cuts (`db₀.leftCut`,
          `db_{N-1}.rightCut`) survive.

213-native reading: the classical Gauss divergence theorem
`∫_Ω (∇·F) dV = ∮_∂Ω F · dA` and conservation `∂_μ J^μ = 0
⇒ flux invariant` are both realised as cohomological
wall-cancellation in the FluxCochain.  No integral or measure
machinery needed; the cancellation IS the conservation.

## d-depth-5 quintuple chain — closed (QuintupleTelescope.lean, 3 PURE)

`Lib/Math/Analysis/FluxMVT/QuintupleTelescope.lean` extends
`TelescopingConservation` (triple + quadruple chains) to the
**d-depth-5 chain**: a 5-bracket telescoping at the atomic
resolution dimension `d = 5`.

  · `QuintupleChain` predicate (4 adjacencies covering all
    interior walls).
  · `flux_quintuple_telescope` — all 4 interior walls cancel
    pairwise.
  · `flux_quintuple_boundary` — outer cuts `(db₀.leftCut,
    db₄.rightCut)` survive.
  · ★★★★★ `d_depth_5_capstone` packages both — the
    Gauss/conservation telescoping at d=5.

## Open frontier

- ~~Telescoping ↔ Gauss / conservation identification~~ — CLOSED
  via `TelescopingConservation.lean` (6 PURE) above.
- ~~MVT chain at higher depth (d-depth-5)~~ — CLOSED via
  `QuintupleTelescope.lean` (3 PURE) above.
- Deferred REAL-RES4 follow-ups in deeper FluxMVT analysis.
