# The "− 1" under three Lenses

`b₁ = NS² − 1 = 1/α₃ = 8` at `K_{3,2}^{(c=2)}` is not three coincident
numbers. The `−1` is a single residue self-pointing, counted once and
read out by the cohomology-Lens, the gauge-Lens, and the chart-Lens.

## 213-native answer

The first Betti number of the atomically-forced bipartite complex is the
count `b₁ = E − V + 1`, and the structural content sits in the `+1` /
`−1`: the lone constant that survives the kernel of the degree-0
coboundary. `isKer_iff_const` makes this exact — a 0-cochain is a cocycle
iff it is constant on each connected component
(`Cohomology/Bipartite/Parametric/Betti/KernelConstancyUniversal.lean`),
and `BoolEnum.bcount_const = 2` counts those constants as `2 = 2¹`
(`Lib/Math/Combinatorics/BoolEnum.lean`). The "minus one" is the single
constant mode subtracted off.

## Derivation

Read that same constant mode three ways.

**Cohomology-Lens.** `ker δ⁰` is the constants; `b₀ = 1` is the one
connected component; the `−1` in `b₁ = E − V + 1` is precisely that one
constant removed from the vertex count
(`theory/math/cohomology/bipartite.md`, b₀/b₁ sections). The rank–nullity
bookkeeping never needs a field: `im_count_inj_complement` realises
`|im δ⁰| = 2^(V−1)` as a `List.length` over a fixed-point-free involution
pairing the fibres (`Betti/PathCoboundary.lean`). The "dimension over
`𝔽₂`" was a count-Lens readout all along; built as an enumeration, the
field drops out.

**Gauge-Lens.** The same single mode is the trace removed from the `NS²`
matrix entries to form the `SU(NS)` adjoint: `NS² − 1 = 8` is the gluon
octet, `1/α₃` (`theory/physics/symmetry/c3_chain.md`). The constant
direction that the cohomology-Lens subtracts as `b₀` is the trace
direction the gauge-Lens subtracts as the `U(1)` center.

**Chart-Lens.** And it is the one self-pointing axis of the forced chart,
`d_M = d_213 − 1`: `forcedKChartLens` builds the chart in which exactly
one coordinate is the residue pointing at itself
(`Geometry/GeometrizationConjecture/KChartLensAbstract.lean`). The `−1`
is the self-axis quotiented out.

`ker δ⁰`'s lone constant, `SU(NS)`'s removed trace, and the chart's
self-pointing axis are not three facts about three objects — they are the
residue read three ways.

## Dual function

Classically these live in separate disciplines: algebraic topology's
Euler-characteristic correction, gauge theory's traceless-generator
count, and differential geometry's chart dimension. The shared `square
minus one` is the redundant packaging stripped — what survives is one
count of one residue. 213's reading is sharper than the analogy: the
involution count (`im_count_inj_complement`) shows the invariant is
field-free and division-free, so "subtract the trace / subtract `b₀` /
quotient the self-axis" are not analogous operations but a single
`bcount_const = 2` read under each domain's Lens.

## Cross-frame connections

The guard against over-reading is the *view-promoted-to-identity* failure
mode: none of cohomology-Lens, gauge-Lens, chart-Lens is what the `−1`
*is* — each is a readout, and the residue is outside every view's image
(`seed/AXIOM/05_no_exterior.md`; primacy as breadth,
`seed/AXIOM/07_primacy.md` §7.1). The convergence is licensed not by
resemblance but by the constants being one `BoolEnum` cardinality.

## Open frontier

Whether the `+1` / `−1` residual of the *other* forced constants
(`1/α_em`, `m_μ/m_e`, which route through the same atomic `(3,2,5)`) is
this same single count, readable the same division-free way, is open —
as is whether the `c`-multiplicity ever enters a higher `b_k` of the
filled complex (`Filled3Cell*`) through the same cardinality machinery.
