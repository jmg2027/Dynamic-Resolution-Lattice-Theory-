# 4-manifolds geometrization in 213: cork-twist + JSJ + Heegaard joint reading

The K_{3,2}^{(c=2)} bipartite graph at chartBase 5 carries three
simultaneous structural readings — cork-twist Z/2 grading for 4-mfd
exotica, bipartite S/T cut + cell-complex (k, j) attaching for 3-mfd
decomposition, and decidable Heegaard genus invariant.

## 213-native answer

A 213-native closed orientable 3-mfd realisation is a
`CellComplexK32Attaching` — `cells2 : List (List Nat)` (2-cell
attaching cycles as edge-index lists) + `cells3 : List (List Nat)`
(3-cell attaching boundaries as 2-cell-index lists) — satisfying
`attachingChi = 0`, i.e., `k − j = 7`
(`lean/E213/Lib/Math/Geometry/GeometrizationConjecture/JsjDeep.lean`
§FW-2.I).  The K_{3,2}^{(c=2)} substrate has V = 5, E = 12, so
χ = V − E + k − j = k − j − 7.

A 213-native 4-mfd exotic invariant is `signedCorkTwistCount = +4`,
the Z/2-graded count of Sym(3)-orbits on H¹(K_{3,2}^{(c=2)}) under
the M_S01 transposition
(`lean/E213/Lib/Math/Geometry/AkbulutCork/SignedOrbits.lean`).

## Derivation

The substrate is the same.  K_{3,2}^{(c=2)} sits at chartBase
= NS + NT = 5, with NS = 3, NT = 2, c = 2 (Möbius P pentagonal
closure, `theory/math/cohomology/bipartite.md`).  At this single
graph:

- **Cork frame** (`theory/math/geometry/exotic_4mfd_cork.md`): the H¹
  Sym(3)-fixed subspace has cardinality 4
  (`Sym3IrrepDecomp.fixedSize = 4`); the cork-twist signed count
  via M_S01 Z/2 grading is `+4 = #twistEven − #twistOdd
  = 32 − 28`.  Supersedes FW-1 signed Donaldson construction
  internally.

- **JSJ frame** (`theory/math/geometry/geometrization_conjecture.md`,
  FW-2 deepening): bipartite S/T cut separates K_{3,2}^{(c=2)}
  into 3 + 2 = 5 isolated vertex-components with 12 crossing edges
  — JSJ-torus parallel one dimension lower (graph cohomology
  truncates at H¹).  The atomic cycle inventory (6 multi-edge
  2-cycles + 3 simple 4-cycles = 9 cycles, rank 8 cycle space)
  supplies the 2-cell attaching primitives.

- **Heegaard frame** (`JsjDeep.lean` §FW-2.CC, §FW-2.DD):
  `heegaardGenus .S3 = 0`, `heegaardGenus .T3 = 3`,
  `heegaardGenus .LpQ = 1`; the additivity
  `targetListGenus_eq_multi` (proved PURE by list induction) makes
  connected sum genus combinatorial.  L(p, q) parameter family
  carries `lensTorsionOrder = p`, `lensLinkingNumber = q`.

The joint reading is anchored at the 5-way Sym(3) cross-frame
capstone (`lean/E213/Lib/Math/Geometry/AkbulutCork/CrossFrame.lean`):
cork-signed-count +4 = `Sym3IrrepDecomp.fixedSize` = 4
trivial-irrep cochains = isotropic-geometry count + 1.  The
composite H¹+H² cork count `+6` = anisotropic-geometry count + 1
(`cork_isotropic_plus_one`, `cork_H1H2_anisotropic_plus_one`).

## Dual function

The cork +4 invariant is 4-mfd exotic enumeration with the
standard-math `smooth structure equivalence` predicate stripped —
no external category of smooth 4-mfds, just the K_{3,2}^{(c=2)}
substrate and its Sym(3)-orbit decomposition.  The (k, j) = 7
constraint is the JSJ Euler-target for closed orientable 3-mfds
with the χ(M) = 0 universal property absorbed into the
cell-complex level.  The Heegaard genus is the standard-math
invariant restored at the discrete combinatorial layer — 0/1/3
directly typed per target without continuous splitting-surface
formalism.

## Cross-frame connections

The d = 4 self-pointing axis (`Capstone.dim4_information_richness`)
makes the joint reading non-coincidence.  `d_M = d_213 − 1
= 5 − 1 = 4` forces K_{3,2}^{(c=2)} at chartBase = 5 to be the
unique dimension where both **tree branch** (K_{1,4}^{(c=1)}, cork
host, b_1 = 0) and **critical branch** (K_{3,2}^{(c=2)}, b_1 = 8)
coexist.  Cork-of-cork
(`lean/E213/Lib/Math/Geometry/AkbulutCork/MultiCork.lean`) lives on the
K_{1,4} ⊂ K_{3,2} embedding; JSJ S/T cut decomposes the K_{3,2}
side; Heegaard genus is invariant under the (k, j) →
connected-sum operation.

Same Sym(3) algebraic spine — five frames: Geometrization
8 = 3 + 5 isotropic / anisotropic; gluon octet H¹ rank 8 = 2·trivial
⊕ 3·standard; octet full cohomology |H¹| = 2⁸ = 256; Möbius P mod-5 pentagonal
closure; cork signed-count +4.  The
`five_way_sym3_cross_frame_capstone` records this convergence.

## Constructive accessibility

The matrix entries are pointable: `M_S01 : Fin 8 → Fin 8 → Bool`
defined cellwise
(`lean/E213/Lib/Physics/Symmetry/Sym3OnH1KMatrix.lean`);
`Lpq_attaching_pq 5 1` has cells3 with explicit modular-q indexing;
`heegaardGenus_Lpq_universal : ∀ p q, heegaardGenus_Lpq p q = 1`
returns `1` for any (p, q).  The cork twist + JSJ + Heegaard
joint reading is the structural correspondence among these three
concrete pointers on the K_{3,2}^{(c=2)} substrate at d = 4.
