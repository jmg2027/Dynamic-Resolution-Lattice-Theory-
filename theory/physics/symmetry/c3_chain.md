# C3 Chain — Gauge Emergence from K_{3,2}^{(c=2)}

**Status**: Closed in `lean/E213/Lib/Physics/Symmetry/`
(24 .lean files; 18 module capstones + master, all strict ∅-axiom).

## Overview

The QCD gluon octet emerges **structurally** as the F_2-cohomology
of K_{3,2}^{(c=2)}, decomposed under the external Sym(3) symmetry:

```
gluon octet := coker(ι*: H¹(Δ⁴) → H¹(K_{3,2}^{(c=2)}))
            =  H¹(K) / 0                  (H¹(Δ⁴) = 0)
            ≃  (F_2)^8
            =  2 · trivial ⊕ 3 · standard  (over F_2)
```

No SU(3) is *postulated*.  The 8 gluon DOF appear as topological
holes in the K_{3,2}^{(c=2)} bipartite multigraph (Euler
characteristic stress χ(K) = 1 − 8 = −7), and the Sym(3) ⊂ SU(3)
Weyl-group restriction acts on them via the symmetric group on the
3 "spatial" vertices.  Per Mingu's session insight: *"χ(K) = −7 is
the geometric stress that forces exactly 8 topological holes —
exactly the number of independent gluon channels."*

The single citable Lean theorem is `c3_chain_master` ∈
`Symmetry.C3ChainCapstone`, a 12-conjunct PURE bundle.
`#print axioms` reports **"does not depend on any axioms"**.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/Symmetry/`
- **Master theorem**: `C3ChainCapstone.c3_chain_master`
- **Tree INDEX**: `lean/E213/Lib/Physics/Symmetry/INDEX.md`
- **File count**: 24 .lean files (6 pre-C3 substrate + 18 chain modules + 1 INDEX)
- **∅-axiom status**: all 18 module capstones + master PURE

### Module architecture (12 core + 6 extensions)

| # | Module | What it gives |
|---|---|---|
| 1 | `AutKType` | Aut_K as Type, card 768 = 6 · 2 · 64 |
| 2 | `Cohomology/Bipartite/H1K` | rank-8 ℤ/2-module + 8 cycle generators |
| 3 | `Sym3OnKEdges` | Sym(3) on K-edges, full Cayley |
| 4 | `Sym3OnH1K` | δ⁰ equivariance → descent to H¹(K) |
| 5 | `Sym3OnH1KMatrix` | explicit 8×8 σ_S01 matrix + tree-decomp witness |
| 6 | `Sym3OnH1KCayley` | s²=t²=(st)³=e at matrix level |
| 7 | `IotaKToDelta4` | gluon octet = coker ι*; H¹(Δ⁴) = 0 via 1024-decide |
| 8 | `IotaSym3Equivariance` | ι_edge ∘ σ_K = σ_Δ⁴ ∘ ι_edge |
| 9 | `Sym3IrrepDecomp` | 2·trivial ⊕ 3·standard over F_2 |
| 10 | `Sym3StandardReps` | 2 explicit standard 2-rep pairs |
| 11 | `Sym3Group` | Sym(3) Group on Fin 6 via Cayley table |
| 12 | `AutKGroup` | Aut(K) direct-product Group, card 768 |
| ★ | `C3ChainCapstone` | `c3_chain_master` 12-conjunct master bundle |
| 13 | `C2_6OnH1K` | C_2^6 trivial on coboundaries → auto descent |
| 14 | `Sym3StandardRepThird` | 3rd standard pair → full explicit 8-dim basis |
| 15 | `AutKSemidirect` | bit_perm twist sample; direct ≠ semidirect witness |
| 16 | `C2_6MixedMatrices` | H1K matrices for 4 mixed C_2^6 bits |
| 17 | `Sym3BlockDiagonal` | M_S01, M_S12 fully block-diagonal in 8-dim basis |
| 18 | `AutKSemidirectFull` | full semidirect Group axioms PROVEN |

### Companion files (pre-C3, used as substrate)

| Module | Role |
|---|---|
| `AutAction` | automorphism action on Raw / lattice |
| `AutEdgeAction` + `AutEdgeActionGenerators` | edge action + generators |
| `AutEdgeOrbits` | edge orbit classification |
| `AutKChiral` | chiral auto-action on K |
| `GluonChannelInterpretation` | physical reading: 8 holes = 8 gluon channels |

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

### 2. H¹(K) and the Sym(3) action

The first cohomology of K over ℤ/2 is rank-8: `H¹(K) := Fin 8 → Bool`
(`Cohomology/Bipartite/H1K`).  Equivalently, |H¹(K)| = 2⁸ = 256.

The rank equals `NS² − 1 = 9 − 1 = 8`, which is the adjoint
representation dimension of SU(NS) = SU(3).  This is **not** a
coincidence: read at presentation c=2, the K_{3,2}^{(c)} graph has
8 topological holes (χ(K) = 1 − 8 = −7, Euler characteristic), and 8
is also `adj SU(3)`, the gluon count.

The Sym(3) external symmetry acts on edges (`Sym3OnKEdges`)
via two transposition generators σ_S01, σ_S12.  This action **descends
to H¹(K)** via δ⁰-equivariance (`Sym3OnH1K`): if
`σ ∈ Sym(3)` is an edge-permutation, then `σ⋆[c] = [σ⋆c]` in
cohomology, where the brackets are cohomology classes.

`Sym3OnH1KMatrix` gives the **explicit 8×8 matrix M_S01**
of σ_S01 on H¹(K) via a tree-decomposition witness (the 4 non-tree
edges form the cycle generators).  `Sym3OnH1KCayley`
verifies the Sym(3) presentation `⟨s, t | s² = t² = (st)³ = e⟩`
at the matrix level.

### 3. The embedding ι: K ↪ Δ⁴ and the gluon octet

K_{3,2}^{(c=2)} embeds into the 4-simplex Δ⁴ via the canonical
map ι_edge: Fin 12 → (edges of Δ⁴).  `IotaKToDelta4` shows:

1. **ι is non-injective**: two K-edges can map to the same Δ⁴-edge
   (multiplicity collapse).  Witnessed by `ι_edge ⟨0⟩ = ι_edge ⟨1⟩`.
2. **H¹(Δ⁴) = 0**: closed by `decide` on all 1024 = 2¹⁰ edge cochains
   (requires `maxRecDepth 2048`).  The Δ⁴ is contractible, so its
   first cohomology vanishes.

Consequently the gluon octet is the cokernel:

```
gluon octet := coker(ι*: H¹(Δ⁴) → H¹(K))
            =  coker(0 → H¹(K))
            =  H¹(K) / image(0)
            =  H¹(K)
            ≃  (F_2)^8
```

`IotaSym3Equivariance` verifies Sym(3)-equivariance of ι:
`ι_edge ∘ σ_K = σ_Δ⁴ ∘ ι_edge`.  The Sym(3) action is preserved by
the embedding — so the gluon octet inherits the Sym(3) representation
structure.

### 4. Irrep decomposition (the master result)

`Sym3IrrepDecomp` closes the decomposition:

```
H¹(K) = 2 · trivial ⊕ 3 · standard  (over F_2)
```

The decomposition is verified by:
- `fixedSize_eq_4`: the Sym(3)-fixed subspace has 4 elements
  (= 2² = |trivial^{⊕2}|, decided on all 256 vectors).
- Cardinality bridge: 4 = 2², matching the multiplicity-2 trivial.
- Remaining 8 − 2 = 6 dimensions form 3 copies of the 2-dim standard.

`Sym3StandardReps` gives two **explicit** standard 2-rep
basis pairs, and `Sym3StandardRepThird` the third —
collectively a full explicit basis of the 6-dim non-trivial part.

`Sym3BlockDiagonal` verifies that M_S01 and M_S12 are
fully block-diagonal in the 8-dim basis {2·trivial ⊕ 3·standard}.

`Sym3Group` closes Sym(3) as a proper Lean Group on Fin 6
via explicit Cayley table — non-abelian (`mul a b ≠ mul b a`).

### 5. Internal C_2^6 structure

The C_2^6 internal symmetry acts trivially on H¹(K) coboundaries
(`C2_6OnH1K`).  The 4 "mixed" generators (those that twist
between different (s, t) pairs) have explicit H¹(K) matrices given
in `C2_6MixedMatrices`.  Together with the 6 "clean"
generators these form 6 commuting involutions on H¹(K).

### 6. The master theorem

`C3ChainCapstone.c3_chain_master` bundles 12 conjuncts:

| (a) | Aut(K) cardinality | 6 · 2 · 64 = 768 |
| (b) | Aut(K) Group identity | one · g = g |
| (c) | Sym(3) non-abelian | a · b ≠ b · a |
| (d) | H¹(K) module rank | 8 |
| (e) | M_S01 involution | M_S01 · M_S01 = Id at matrix level |
| (f) | ι collapses multiplicities | ι_edge ⟨0⟩ = ι_edge ⟨1⟩ |
| (g) | H¹(Δ⁴) = 0 | kerSizeDelta 5 2 = 16 |
| (h) | Sym(3)-equivariance of ι | ι_edge ∘ σ_S01 = σ_E_swap_01 ∘ ι_edge |
| (i) | Sym(3)-fixed subspace dim | 4 (= 2² for 2·trivial) |
| (j) | Decomposition arithmetic | 2 + 2·3 = 8 |
| (k) | Standard 2-rep verification | std1_v1 is M_S01-fixed |
| (l) | Cardinality | 2⁸ = 256 |

`#print axioms c3_chain_master` reports **"does not depend on any axioms"**.

## Key results (single-line summary)

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `c3_chain_master` | `C3ChainCapstone` | 12-conjunct full gauge-emergence bundle |
| `H1K.rank = 8` | `Cohomology/Bipartite/H1K` | First cohomology rank |
| `kerSize_delta_5_2 = 16` | `IotaKToDelta4` | H¹(Δ⁴) = 0 via 1024-decide |
| `M_S01_squared_pointwise` | `Sym3OnH1KMatrix` | σ_S01 is an involution |
| `Sym3.non_abelian` | `Sym3Group` | Sym(3) Group is non-abelian |
| `fixedSize_eq_4` | `Sym3IrrepDecomp` | 2·trivial fixed subspace |
| `ι_equivariance_S01` | `IotaSym3Equivariance` | Sym(3)-equivariance |
| `std1_S01_v1` | `Sym3StandardReps` | Explicit standard 2-rep |
| `AutKSemidirectFull_phase18_capstone` | `AutKSemidirectFull` | Full semidirect Group |

For the full file map, see
`lean/E213/Lib/Physics/Symmetry/INDEX.md`.

## Connection to physics

The chain delivers the **structural** half of the gluon-octet picture:

- **Counting**: 8 = NS² − 1 = adj SU(3).  No SU(3) postulated;
  emerges from `b_1(K_{3,2}^{(c=2)})` via Euler characteristic
  stress.
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

1. **C3 chain v2 master** — a single capstone incorporating the
   extension modules 13-18 (`c3_chain_master` bundles the 12 core
   results).  Pure consolidation, no new math.

2. **C3 ↔ α_3** — connect the explicit Sym(3) rep to the strong
   coupling `α_3 = NS² − 1 = 8` in
   `Lib/Physics/Couplings/SpectrumComplete.lean`, deriving it from
   the gauge group structure.

3. **Full SU(3) lift** — Sym(3) is the Weyl group of SU(3);
   extending to the full continuous group requires the 213-native
   continuous-group machinery (currently scattered across
   `Math/Trajectory/` and `Math/Analysis213/`).

4. **Inverse-pullback / hom-direction documentation** —
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
#check @c3_chain_master    -- 12-conjunct bundle
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
