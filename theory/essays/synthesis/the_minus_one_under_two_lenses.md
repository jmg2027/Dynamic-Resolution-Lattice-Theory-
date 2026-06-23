# The "− 1" under two Lenses

`b₁ = NS² − 1 = 1/α₃ = 8` at `K_{3,2}^{(c=2)}` is not two coincident
numbers. The `−1` is a single residue self-pointing, counted once and
read out by the cohomology-Lens and the gauge-Lens.

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

Read that same constant mode two ways.

**Cohomology-Lens.** `ker δ⁰` is the constants; `b₀ = 1` is the one
connected component; the `−1` in `b₁ = E − V + 1` is precisely that one
constant removed from the vertex count
(`theory/math/cohomology/bipartite.md`, b₀/b₁ sections). The rank–nullity
bookkeeping never needs a field: the kernel is exactly the two constant
cochains for every connected deployment (`isKer_const_false_or_true`), so
the visible part has dimension `(NS + NT) − 1` (`visible_plus_one`,
`Betti/KernelConstancyUniversal.lean`) and `b₁ = E − V + 1`
(`EulerAndCapstone.b1Formula`). The "dimension over `𝔽₂`" was a count-Lens
readout all along; the `−1` is just the one removed constant.

**Gauge-Lens.** The same single mode is the trace removed from the `NS²`
matrix entries to form the `SU(NS)` adjoint: `NS² − 1 = 8` is the gluon
octet, `1/α₃` (`theory/physics/symmetry/c3_chain.md`). The constant
direction that the cohomology-Lens subtracts as `b₀` is the trace
direction the gauge-Lens subtracts as the `U(1)` center.

`ker δ⁰`'s lone constant and `SU(NS)`'s removed trace are not two facts
about two objects — they are the residue read two ways.

## Dual function

Classically these live in separate disciplines: algebraic topology's
Euler-characteristic correction and gauge theory's traceless-generator
count. The shared `square minus one` is the redundant packaging
stripped — what survives is one count of one residue. 213's reading is
sharper than the analogy: the kernel is exactly the two constant cochains
(`isKer_const_false_or_true`), field-free and division-free, so "subtract
the trace / subtract `b₀`" are not analogous operations but a single
`|ker δ⁰| = 2` count read under each domain's Lens.

## Cross-frame connections

The guard against over-reading is the *view-promoted-to-identity* failure
mode: neither cohomology-Lens nor gauge-Lens is what the `−1`
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
