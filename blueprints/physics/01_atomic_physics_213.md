# Atomic Physics 213 — Blueprint

**Priority**: ★★★ Top priority (Phase 4 IE library already in place)

## 1. Why This Field

Standard atomic physics:
- Schrödinger equation + many-body quantum mechanics (NP-hard)
- Slater rules (~5-10% precision, ad hoc)
- Hartree-Fock + correlation energy (variational/perturbative)

Natural emergence in 213:
- Phase 4 HydrogenIE: **4.3 ppb formal Lean** verification
- Phase 4 Library: 28 sub-libraries, IE/atomic chain
- Period closures *all* atomic (Phase 4 PeriodClosures)
- Hund's rule = α_3 atomic penalty (Phase 4 HundPenalty)
- Closed propagator P(x) atomic correction universal

## 2. 213-native Emergence

### 2.1 Periodic table atomic
113 + 5 super-heavy elements all represented atomically (Phase 4
CompletePeriodicTable).  Z=168 = HO magic 7 prediction.

### 2.2 σ_atomic catalog
- σ_1s_to_outer = 7/8
- σ_2s_to_2s = NS/d
- σ_2s_to_2p = 17/(4d)
- σ_2p_to_2p = (NS²+NT)/(d·NS)

Each σ is a ratio of atomic primitives.

### 2.3 P(x/k) family
All corrections = closed propagator P(x/k_Z) atomic.

## 3. Already-Laid Building Blocks

- HydrogenIEPPM.lean (4.3 ppb)
- HeliumIEPPM, LithiumIE, BerylliumIE, BoronIE
- CNOFNeIE, Period3IE, Period4-7IE
- HundPenalty, PropagatorFamily
- IECapstone, CompletePeriodicTable

## 4. Phase Progression Plan

### Phase EA — IE ppm refinement (Z=2-10)
He, Li, Be, B: σ atomic additional terms → ppm.

### Phase EB — Hund generalization (s/p/d all)
ε_pair atomic = R · NS/(NS²-1) d-shell extension.

### Phase EC — Lanthanide/Actinide
Z=57-71, 90-103 atomic chain.

### Phase ED — Atomic spectroscopy
Rydberg series, fine structure, hyperfine splitting.

### Phase EE — Molecular
H₂, O₂, N₂ binding energy + bond length atomic.

## 5. Connections to Other Tracks

- Nuclear track: nuclear binding ~ 1/α_3 = 8 MeV
- Cosmology: stellar nucleosynthesis atomic
- Math track: Phase 4 Library = catalog module

## 6. Open Problems

- σ_atomic for Lanthanide 4f shell
- Spin-orbit coupling atomic derivation
- QED Lamb shift atomic chain
