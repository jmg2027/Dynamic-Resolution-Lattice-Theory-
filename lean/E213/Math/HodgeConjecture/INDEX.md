# `Math/Cohomology/HodgeConjecture/` — Hodge Conjecture in 213

Sub-cluster closing the Hodge conjecture (and 17 Hodge-adjacent
classical theorems) in 213-native form, all strict ∅-axiom.

**Single import**: `E213.Math.HodgeConjecture.API`
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

### 4. `Pairing/`  (2 files) — *bilinear forms*

Cup-pairings: signature, kernel, positivity.

  · `HodgeIndex.lean`        Cup-pairing signature on H¹
  · `HodgeRiemann.lean`      Bilinear positivity (ℚ²¹³ pending)

### 5. ~~`Bridge/`~~ → **MOVED to `lean/E213/OS/HodgeConjecture/Bridges/`**

The 7 cross-discipline interface files have been migrated to the
new OS layer per G12 §5 Option γ.  They now live at namespace
`E213.OS.HodgeConjecture.Bridges.*`:

  · `Tate.lean`                  → ℓ-adic / Frobenius / char-p
  · `MumfordTate.lean`           → Galois algebraic groups
  · `BlochBeilinson.lean`        → motivic cohomology / Chow
  · `BeilinsonRegulator.lean`    → L-function values (CLAUDE.md L1)
  · `BeilinsonLichtenbaum.lean`  → motivic ↔ étale equivalence
  · `ChernCharacter.lean`        → K-theory ↔ cohomology
  · `HodgeTate.lean`             → p-adic Hodge (Real213-p deferred)

Rationale: Bridges are *orchestration* of the HC²¹³ subsystem
into adapters consumed by other classical disciplines — that is
exactly the OS layer's role (per ARCHITECTURE.md §1.4.5 and G12
§5).  Foundation/Toolkit/Structure/Refinement/Pairing remain in
Math/ as they are *definitional* content (Hypervisor-flavored).

---

## Layout summary

```
HodgeConjecture/
├── API.lean         single-import entry point + HC213 alias
├── INDEX.md         this file
├── Foundation/  (6) — the HC²¹³ claim itself
├── Toolkit/     (4) — compute layer
├── Structure/   (4) — algebra + duality
├── Refinement/  (6) — stronger HC²¹³
└── Pairing/     (2) — bilinear forms
   (Bridge/* MOVED to lean/E213/OS/HodgeConjecture/Bridges/)
```

Total: 29 .lean files, ~140 strict ∅-axiom theorems.

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

Citation: `E213.Math.HodgeConjecture.API.HC213`
(reducible alias for `Foundation.Complete.hodge_conjecture_213_complete`).

---

## Companion research notes

  · `G6_hodge_213_translation.md`      Standard ↔ 213 dictionary
  · `G7_lens_initiality_cup_blueprint.md`  Uniform-proof sketch
  · `G8_hodge_213_bridge_to_standard_math.md`  Standard-math bridge
  · `G9_hodge_conjecture_complete.md`  HC²¹³ closure note
  · `G10_post_hodge_program.md`        17 post-HC programme
  · `G11_galois_at_eighty.md`          Galois counterfactual
