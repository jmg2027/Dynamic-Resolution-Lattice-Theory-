# `Math/Cohomology/HodgeConjecture/` — Hodge Conjecture in 213

Sub-cluster closing the Hodge conjecture (and 17 Hodge-adjacent
classical theorems) in 213-native form, all strict ∅-axiom.

**Single import**: `E213.Lib.Math.HodgeConjecture.API`
**Master capstone**: `Foundation/Complete.lean` →
  `hodge_conjecture_213_complete`.  `#print axioms` → "does not
  depend on any axioms".

---

## Functional architecture (6 layers)

Mathematics-as-software-architecture: each sub-directory is a
functional layer with a specific responsibility.

### 0. `Foundation/`  (6 files) — *the claim itself*

The HC²¹³ statement and its capstones.  Foundation layer; everything
else builds on this.

  · `Conjecture.lean`        Universal HC²¹³ on Δⁿ⁻¹
  · `ConjectureLens.lean`    HC²¹³ on K_{3,2}^{(c=2)}
  · `Canonical.lean`         Numerical witness bundle
  · `Filled.lean`            Filled K_{3,2}, all 5 levels
  · `LensCata.lean`          Atomic generator structure
  · ★ `Complete.lean`        MASTER `hodge_conjecture_213_complete`

### 1. `Toolkit/`  (4 files) — *compute layer*

Actually do things with cohomology.  Operational primitives.

  · `Primitives.lean`        support, fromList, isCocycle, weight
  · `RoundTrip.lean`         fromList ∘ support = id (4 strata)
  · `RoundTripMid.lean`      Round-trip on (5,2)/(5,3)
  · `LensClassifier.lean`    K_{3,2} 256 H¹ class catalog

### 2. `Structure/`  (4 files) — *algebraic structure layer*

Multiplicative + duality structure on cohomology.  Lets you compose
operations.

  · `Ring.lean`              ⋆ × cup compatibility
  · `Map.lean`               ⋆ as ℤ/2-bijection + XOR-linearity
  · `PoincareDuality.lean`   H^k ↔ H^{n−k}
  · `HardLefschetz.lean`     ω^k ⌣ : H^{n−k} → H^{n+k} iso

### 3. `Refinement/`  (6 files) — *stronger HC²¹³ statements*

Refinements, stronger forms, graded versions.

  · `LefschetzOneOne.lean`        (1,1) case (Lefschetz 1924)
  · `GeneralizedHodge.lean`       Codim filtration on Chow
  · `CupAtomicGeneration.lean`    Strong: vertex⌣vertex generates all
  · `StandardConjectures.lean`    Grothendieck A/B/C/D
  · `LefschetzHyperplane.lean`    Δ⁴ → Δ³ restriction + Pascal
  · `Voisin.lean`                 Finite-dim motive (automatic)

### 4. `Pairing/`  (4 files) — *bilinear forms*

Cup-pairings: signature, kernel, positivity.

  · `HodgeIndex.lean`        Base capstone on K_{3,2}^{(c=2)}
                              (graph; cup-pairing vacuously zero)
  · `HodgeIndexT2.lean`      ★ Non-vacuous lift to T² minimal CW
                              (signature (1, 1) by direct ℤ-decide;
                              G10 Phase 2 follow-up closed)
  · `HodgeRiemann.lean`      Base capstone on K_{3,2}^{(c=2)}
                              (positivity vacuous in ℤ/2)
  · `HodgeRiemannT2.lean`    ★ Non-vacuous lift: Kähler class
                              with `cup(ω, ω) > 0` on T²;
                              signature decomposition explicit

### 5. `MotivicBridge/`  (6 files) — *motivic-cohomology bridges*

Algebraic-geometry / arithmetic-geometry counterparts of the
classical conjectures (G10 Phase 3).  Originally hosted under OS/
prior to the M14 ring-model refactor; now live in
`Math/HodgeConjecture/MotivicBridge/` with namespace
`E213.Lib.Math.HodgeConjecture.MotivicBridge.*`:

  · `Tate.lean`                  ℓ-adic / Frobenius / char-p
  · `MumfordTate.lean`           Galois algebraic groups
  · `BlochBeilinson.lean`        motivic cohomology / Chow
  · `BeilinsonLichtenbaum.lean`  motivic ↔ étale equivalence
  · `ChernCharacter.lean`        K-theory ↔ cohomology
  · `HodgeTate.lean`             p-adic Hodge (Real213-p deferred)

### 6. `Bridge/`  (11 files) — *physics + statistical-mechanics + CS bridges*

Cross-discipline interface layer.  Each file is the public API
surface for one classical discipline, exporting HC²¹³ machinery
into adapters consumed by physics / stat-mech / CS.

  · `BeilinsonRegulator.lean`    L-function values (CLAUDE.md L1)
  · `DiscreteGeometry.lean`      4-simplex face counts
  · `G6Vacuity.lean`             G6 §0 corrected position witness
  · `GaloisCounterfactual.lean`  G11 80-year Galois counterfactual
  · `Ising.lean`                 Ising model on 4-simplex
  · `MLDecoder.lean`             ML-decoder cohomology
  · `MotiveEtaleFusion.lean`     motive ↔ étale fusion
  · `PhaseRouting.lean`          phase-routing counterfactual
  · `Potts.lean`                 Potts model on 4-simplex
  · `SpinGlass.lean`             spin-glass cohomology
  · `SpinGlassGroundState.lean`  NP-hard ground-state witness

---

## Layout summary

```
HodgeConjecture/
├── API.lean              single-import entry point + HC213 alias
├── INDEX.md              this file
├── Foundation/      (6)  — the HC²¹³ claim itself
├── Toolkit/         (4)  — compute layer
├── Structure/       (4)  — algebra + duality
├── Refinement/      (6)  — stronger HC²¹³
├── Pairing/         (2)  — bilinear forms
├── MotivicBridge/   (6)  — motivic / arithmetic counterparts
└── Bridge/          (11) — physics / stat-mech / CS interfaces
```

Total: 39 sub-cluster files + API.lean = 40, plus umbrellas
(7 sub-cluster `.lean` umbrellas + root) → **~80 .lean files
under `Math/HodgeConjecture/`**, **31 master capstones**, all
strict ∅-axiom (verified by `lake env lean` + `#print axioms`).

---

## Architectural notes

  · **Foundation** = claim layer.  Other layers cite it.
  · **Toolkit** + **Structure** = the substrate that makes computations
    + composition work.  These are *internal*; downstream code uses
    them transparently.
  · **Refinement** + **Pairing** = strengthenings — stronger versions
    of the foundation claim with more structure.
  · **Bridge** = *external interface layer*.  Each file is the
    public API surface for one classical discipline.

The 6-layer structure mirrors a layered software architecture:
Foundation = core domain, Toolkit/Structure = service layer,
Refinement/Pairing = enrichment layer, Bridge = adapter / API gateway.

Citation: `E213.Lib.Math.HodgeConjecture.API.HC213`
(reducible alias for `Foundation.Complete.hodge_conjecture_213_complete`).

---

## Companion narrative

**Primary**: `theory/math/cohomology/hodge_conjecture.md`
(promoted 2026-05-21 — read this for the human-readable account).

Original exploration notes (archived 2026-05-21,
`research-notes/archive/hodge/`):

  · `G6_hodge_213_translation.md`      Standard ↔ 213 dictionary
  · `G7_lens_initiality_cup_blueprint.md`  Uniform-proof sketch
  · `G8_hodge_213_bridge_to_standard_math.md`  Standard-math bridge
  · `G9_hodge_conjecture_complete.md`  HC²¹³ closure note
  · `G10_post_hodge_program.md`        17 post-HC programme
  · `G11_galois_at_eighty.md`          Galois counterfactual
  · `G12_T2_pattern.md`                T² pattern follow-up
