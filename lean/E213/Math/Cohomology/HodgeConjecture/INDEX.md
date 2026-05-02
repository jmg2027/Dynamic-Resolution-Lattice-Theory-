# `Math/Cohomology/HodgeConjecture/` — Hodge Conjecture in 213

Sub-cluster closing the Hodge conjecture (and 17 Hodge-adjacent
classical theorems) in 213-native form, all strict ∅-axiom.

**Single import**: `E213.Math.Cohomology.HodgeConjecture.API` —
re-exports all 29 sub-modules.

**Master capstone**: `hodge_conjecture_213_complete` in
`Core/Complete.lean`.  `#print axioms` → "does not depend on any
axioms".

---

## Layout

```
HodgeConjecture/
├── API.lean             (single-import entry point)
├── INDEX.md             (this file)
│
├── Core/                (6 files — statement + capstones)
│   ├── Conjecture.lean        Universal HC²¹³ on Δⁿ⁻¹
│   ├── ConjectureLens.lean    HC²¹³ on K_{3,2}^{(c=2)}
│   ├── Canonical.lean         Canonical bundle (Δ⁴ + K_{3,2})
│   ├── Filled.lean            Filled K_{3,2}, all 5 levels
│   ├── LensCata.lean          Atomic generation (Lens-cata)
│   └── Complete.lean          ★ MASTER: HC²¹³ COMPLETE
│
├── Toolkit/             (6 files — operational primitives)
│   ├── Primitives.lean        support, fromList, isCocycle
│   ├── RoundTrip.lean         fromList ∘ support = id
│   ├── RoundTripMid.lean      Round-trip on (5,2)/(5,3)
│   ├── LensClassifier.lean    K_{3,2} 256 H¹ classes
│   ├── Ring.lean              ⋆ × cup compatibility
│   └── Map.lean               ⋆ as ℤ/2-bijection
│
└── PostHC/              (17 files — Hodge-adjacent theorems)
    ├── LefschetzOneOne.lean
    ├── PoincareDuality.lean
    ├── GeneralizedHodge.lean
    ├── StandardConjectures.lean
    ├── HardLefschetz.lean
    ├── Tate.lean
    ├── HodgeIndex.lean
    ├── HodgeRiemann.lean
    ├── CupAtomicGeneration.lean
    ├── LefschetzHyperplane.lean
    ├── MumfordTate.lean
    ├── BlochBeilinson.lean
    ├── BeilinsonRegulator.lean
    ├── Voisin.lean
    ├── ChernCharacter.lean
    ├── HodgeTate.lean
    └── BeilinsonLichtenbaum.lean
```

---

## Theorem inventory

**Total**: 29 Lean files + 1 API + 1 INDEX, ~140 strict ∅-axiom
theorems / definitions.

  · Core (6 files): HC²¹³ statement, K_{3,2} variant, canonical
    + filled + lens-cata witnesses, master capstone
  · Toolkit (6 files): support/fromList/isCocycle primitives,
    round-trip on all 5 strata, K_{3,2} 256 H¹ class catalog,
    ⋆ × cup compat, ⋆ as ℤ/2-bijection
  · PostHC (17 files): Hodge-adjacent classical theorems

Most-cited theorem:
  `E213.Math.Cohomology.HodgeConjecture.Core.Complete.hodge_conjecture_213_complete`
short alias: `E213.Math.Cohomology.HodgeConjecture.API.HC213`.

---

## Companion research notes

  · `G6_hodge_213_translation.md`   — Standard ↔ 213 dictionary
  · `G7_lens_initiality_cup_blueprint.md` — Uniform proof sketch
  · `G8_hodge_213_bridge_to_standard_math.md` — Standard-math bridge
  · `G9_hodge_conjecture_complete.md` — HC²¹³ closure note
  · `G10_post_hodge_program.md` — 17 post-HC programme
  · `G11_galois_at_eighty.md` — Galois counterfactual

---

## Phase summary

  · **HC²¹³ COMPLETE** — Core + Toolkit (12 files)
  · **Phase 1** — Lefschetz(1,1), Poincaré, GHC, Standard Conjectures
  · **Phase 2** — Hard Lefschetz, Tate, Hodge Index, Hodge-Riemann
  · **Phase 3** — Cup atomic gen, Lefschetz hyperplane, Mumford-Tate,
    Bloch-Beilinson, Beilinson regulator, Voisin, Chern character,
    Hodge-Tate, Beilinson-Lichtenbaum

All three phases closed strict ∅-axiom.
