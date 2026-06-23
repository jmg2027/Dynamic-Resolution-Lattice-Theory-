# C3 Chain — Gauge Emergence from K_{3,2}^{(c=2)}

**Status**: Closed in `lean/E213/Lib/Physics/Symmetry/`
(13 .lean files, all strict ∅-axiom).

## Overview

The QCD colour octet emerges **structurally** as the rank-8 𝔽₂
module sourced from `NS² − 1 = adj SU(3)`, decomposed under the
Sym(3) ⊂ SU(3) Weyl group:

```
colour octet := Octet := Fin 8 → Bool       (rank-8 𝔽₂-module)
             rank = NS² − 1 = 3² − 1 = 8     (SU(3) adjoint, from NS = 3)
             ↓ Sym(3) = 2 · trivial ⊕ 3 · standard  (over 𝔽₂)
```

No SU(3) is *postulated*.  The 8 octet DOF are the dimension of the
SU(3) adjoint, `NS² − 1 = 8`, taken directly from `NS = 3`
(`SpectrumComplete.alpha_3_channel`); the carrier is the abstract
module `OctetModule.Octet := Fin 8 → Bool`, **not** a graph cycle
space.  The χ(K) = 1 − 8 = −7 / b₁(K) = 8 reading of the
K_{3,2}^{(c=2)} bipartite multigraph is a coincident count, not the
definition.  The Sym(3) ⊂ SU(3) Weyl-group restriction acts on the
8 DOF via two involution generators `M_S01`, `M_S12` satisfying the
Coxeter presentation `s² = t² = (st)³ = e`.

The single citable Lean theorem is `c3_chain_master` ∈
`Symmetry.C3ChainCapstone`, a PURE bundle.
`#print axioms` reports **"does not depend on any axioms"**.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/Symmetry/`
- **Master theorem**: `C3ChainCapstone.c3_chain_master`
- **File count**: 13 .lean files (all strict ∅-axiom)
- **∅-axiom status**: all module results + master PURE

### Module architecture (13 files)

| Module | What it gives |
|---|---|
| `OctetModule` | rank-8 𝔽₂-module `Octet := Fin 8 → Bool`, `rank = NS² − 1 = 8`; Sym(3) generators `M_S01`, `M_S12`; `s² = t² = (st)³ = e`; fixed subspace `fixedSize = 4`; explicit standard 2-rep pairs; block structure `2·trivial ⊕ 3·standard` |
| `Sym3Group` | Sym(3) as a proper Group on `Fin 6` (Cayley table, non-abelian) |
| `AutKGroup` | `Aut(K) = Sym3 × Sym2 × C2_6` Group, card `768 = 6·2·64` |
| `AutKType` | `Aut_K` as a Type with cardinality 768 |
| `AutKSemidirect` / `AutKSemidirectFull` | semidirect twist sample; full semidirect Group axioms PROVEN |
| `AutKChiral` | chiral auto-action on K |
| `AutKType` / `AutAction` | automorphism action on Raw / lattice |
| `AutEdgeAction` + `AutEdgeActionGenerators` | edge action + generators |
| `AutEdgeOrbits` | edge orbit classification |
| `GluonChannelInterpretation` | physical reading: 8 DOF = 8 gluon channels |
| ★ `C3ChainCapstone` | `c3_chain_master` master bundle |

The `H¹(Δ⁴) = 0` contractibility witness (`kerSizeDelta 5 2 = 16`)
used by the capstone lives in
`lean/E213/Lib/Math/Cohomology/Examples/BettiKernel.lean`.

## The narrative

### 1. The substrate

K_{3,2}^{(c=2)} is the bipartite multigraph with NS = 3 spatial
vertices, NT = 2 temporal vertices, and c = 2 edges between every
(spatial, temporal) pair — total 3 × 2 × 2 = 12 edges.  In 213,
this is the canonical Lattice substrate for physics (per
`seed/AXIOM/` and the 213-Algebra catalog chiral cup ring catalog).

Its automorphism group `Aut(K)` factors as:

```
Aut(K) = Sym(NS) × Sym(NT) × C_2^c·NS·NT
       = Sym(3) × Sym(2) × C_2^6
```

with cardinality `6 · 2 · 64 = 768`.  The Sym(NS) × Sym(NT) part is
the *external* symmetry (vertex relabeling); C_2^6 is the *internal*
symmetry (per-edge-pair multiplicity swap).

The group structure is established in Lean by:
- `AutKType`: Aut_K as a Type with cardinality 768
- `AutKGroup`: Group axioms via direct product
- `AutKSemidirect`: non-trivial semidirect twist sample
- `AutKSemidirectFull`: full semidirect Group axioms

### 2. The octet module and the Sym(3) action

The colour octet carrier is the rank-8 𝔽₂-module
`Octet := Fin 8 → Bool` (`OctetModule`).  Equivalently,
|Octet| = 2⁸ = 256.

The rank equals `NS² − 1 = 9 − 1 = 8`, the adjoint representation
dimension of SU(NS) = SU(3), taken directly from `NS = 3`
(`OctetModule.rank_eq_alpha_3_channel`,
`OctetModule.rank_eq_NSsq_minus_1`).  The χ(K) = 1 − 8 = −7 /
b₁(K) = 8 reading of the K_{3,2}^{(c=2)} graph is a coincident
count, not the source of the rank.

The Sym(3) ⊂ SU(3) Weyl group acts on `Octet` via two involution
generators `M_S01`, `M_S12` (`OctetModule`), each represented as an
8×8 𝔽₂-matrix (`M : Fin 8 → Octet`).  They satisfy the Coxeter
presentation `⟨s, t | s² = t² = (st)³ = e⟩`:
- `M_S01_squared`, `M_S12_squared`: each generator is an involution.
- `M_ρ_cubed`: the braid relation `(st)³ = e`.

### 3. Contractibility witness H¹(Δ⁴) = 0

The capstone also bundles the contractibility witness
`kerSizeDelta 5 2 = 16` (`BettiKernel`, in
`Lib/Math/Cohomology/Examples/`): `|ker δ¹| = 16 = 2⁴ = |im δ⁰|`,
closed by `decide` on the 1024 = 2¹⁰ edge cochains of Δ⁴
(`maxRecDepth 2048`).  The 4-simplex is contractible, so its first
cohomology vanishes.

### 4. Irrep decomposition (the master result)

`OctetModule` closes the Weyl-restriction decomposition:

```
Octet ↓ Sym(3) = 2 · trivial ⊕ 3 · standard  (over 𝔽₂)
```

The decomposition is verified by:
- `fixedSize_eq_4`: the Sym(3)-fixed subspace has 4 elements
  (= 2² = |trivial^{⊕2}|, decided on all 256 vectors).
- Cardinality bridge: 4 = 2², matching the multiplicity-2 trivial.
- Remaining 8 − 2 = 6 dimensions form 3 copies of the 2-dim standard.
- `std1_S01_v1`: an explicit standard 2-rep vector fixed under `s`.

`Sym3Group` closes Sym(3) as a proper Lean Group on Fin 6
via explicit Cayley table — non-abelian (`Sym3.non_abelian`).

### 5. The automorphism group

`Aut(K) = Sym(3) × Sym(2) × C_2^6` is realised as a Lean Group with
cardinality `768 = 6 · 2 · 64` (`AutKGroup`, `AutKType`).  The
semidirect structure is established in `AutKSemidirect` /
`AutKSemidirectFull`.

### 6. The master theorem

`C3ChainCapstone.c3_chain_master` bundles its conjuncts:

| (a) | Aut(K) cardinality | 6 · 2 · 64 = 768 |
| (b) | Aut(K) Group identity | one · g = g |
| (c) | Sym(3) non-abelian | a · b ≠ b · a |
| (d) | octet module rank | 8 = NS² − 1 |
| (e) | M_S01 involution | s² = e (M_S01 · M_S01 = Id) |
| (f) | braid relation | (ts)³ = e (M_ρ³ = Id) |
| (g) | H¹(Δ⁴) = 0 | kerSizeDelta 5 2 = 16 |
| (h) | M_S12 involution | t² = e (M_S12 · M_S12 = Id) |
| (i) | Sym(3)-fixed subspace dim | 4 (= 2² for 2·trivial) |
| (j) | Decomposition arithmetic | 2 + 2·3 = 8 |
| (k) | Standard 2-rep verification | std1_v1 is M_S01-fixed |
| (l) | Cardinality | 2⁸ = 256 |

`#print axioms c3_chain_master` reports **"does not depend on any axioms"**.

## Key results (single-line summary)

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `c3_chain_master` | `C3ChainCapstone` | full gauge-emergence bundle |
| `rank_eq_NSsq_minus_1` | `OctetModule` | octet rank = NS² − 1 = 8 |
| `kerSize_delta_5_2 = 16` | `C3ChainCapstone` / `BettiKernel` | H¹(Δ⁴) = 0 via 1024-decide |
| `M_S01_squared`, `M_S12_squared` | `OctetModule` | s², t² involutions |
| `M_ρ_cubed` | `OctetModule` | braid relation (st)³ = e |
| `Sym3.non_abelian` | `Sym3Group` | Sym(3) Group is non-abelian |
| `fixedSize_eq_4` | `OctetModule` | 2·trivial fixed subspace |
| `std1_S01_v1` | `OctetModule` | Explicit standard 2-rep |
| `AutKSemidirectFull` capstone | `AutKSemidirectFull` | Full semidirect Group |

## Connection to physics

The chain delivers the **structural** half of the gluon-octet picture:

- **Counting**: 8 = NS² − 1 = adj SU(3).  No SU(3) postulated;
  sourced directly from `NS = 3` (`OctetModule`,
  `SpectrumComplete.alpha_3_channel`).  The b₁(K) = 8 / χ(K) = −7
  graph reading is a coincident count, not the source.
- **Symmetry**: Sym(3) ⊂ SU(3) Weyl-group restriction acts on the
  8 DOF.  Sym(3) action determined directly by edge-permutation.
- **Representation**: F_2-irrep decomposition is explicit
  (2·trivial ⊕ 3·standard).

What this **does not** give (open frontier, §below):
- The coupling constant α_3 from the explicit Sym(3) rep
- Full SU(3) (not just the Weyl group Sym(3))
- Continuous gauge transformations

## Open frontier

The C3 chain closes the **structural** picture.  Open extensions:

1. **C3 ↔ α_3** — connect the explicit Sym(3) rep to the strong
   coupling `α_3 = NS² − 1 = 8` in
   `Lib/Physics/Couplings/SpectrumComplete.lean`, deriving it from
   the gauge group structure.

2. **Full SU(3) lift** — Sym(3) is the Weyl group of SU(3);
   extending to the full continuous group requires the 213-native
   continuous-group machinery (currently scattered across
   `Math/Trajectory/` and `Math/Analysis213/`).

3. **Inverse-pullback / hom-direction documentation** —
   `AutKSemidirectFull` uses `bit_act_of` with inverse-pullback to
   recover the true group hom direction (pullback gives anti-hom,
   push-forward gives hom); the convention deserves a short note.

## How to verify

```bash
cd lean
lake build E213.Lib.Physics.Symmetry            # build clean
python3 tools/scan_axioms.py Lib/Physics/Symmetry  # PURE/DIRTY tally
```

Expected: build succeeds, every module capstone + master reports
"does not depend on any axioms", scan reports 0 DIRTY in Symmetry/.

The single citable theorem from elsewhere:

```lean
import E213.Lib.Physics.Symmetry.C3ChainCapstone
open E213.Lib.Physics.Symmetry.C3ChainCapstone
#check @c3_chain_master    -- gauge-emergence bundle
#print axioms c3_chain_master
-- => "does not depend on any axioms"
```

## Citation guidance

When citing the C3 chain from Lean docstrings, prefer the master
theorem + this chapter:

```
-- ✅ preferred
`theory/physics/symmetry/c3_chain.md` (narrative)
`Lib/Physics/Symmetry/C3ChainCapstone.c3_chain_master` (theorem)
```

For deep dives, cite the individual module file + this chapter.
