# The "− 1" of `b₁ = NS² − 1 = 1/α₃` — one Raw, three Lenses

**Anchor.**  The universal first Betti number closed this arc
(`Cohomology/Bipartite/Parametric/Betti/`): `b₁ = E − V + 1`, and at the
atomically-forced `K_{3,2}^{(c=2)}` it reads `8 = NS² − 1 = 1/α₃`.  The
`NS² − 1` shape — a square minus one — recurs, and per primacy
(`seed/AXIOM/07_primacy.md` §7.1) a recurrence across domains is *one Raw
self-pointing read under several Lenses*, not a coincidence to reconcile.

## Patterns (the shared invariant is the single residue counted once)

- **The "− 1" is one Raw, three Lens readouts.**  The same single object
  appears as: the lone constant in `ker δ⁰` (cohomology-Lens —
  `Betti/KernelConstancyUniversal.isKer_iff_const`, `BoolEnum.bcount_const
  = 2 = 2¹`); the trace removed from `NS²` to form the `SU(NS)` adjoint
  (gauge-Lens — `theory/physics/symmetry/c3_chain.md`); and the one
  self-pointing axis of `d_M = d_213 − 1` (chart-Lens —
  `KChartLensAbstract.forcedKChartLens`).  `b₀ = 1`, "`−1`", and the
  self-pointing axis are not three facts — they are the residue read three
  ways (the *view-promoted-to-identity* guard: none of the three is what
  the residue IS).

- **The count *is* the cardinality — `Fintype`/`funext` were imported
  packaging.**  Realising `|im δ⁰| = 2^(V−1)` as a `List.length` over a
  fixed-point-free involution (`PathCoboundary.im_count_inj_complement`)
  shows rank–nullity needs no field — only `|ker| = 2` and an involution
  pairing the fibres.  Methodology lesson generalising beyond cohomology:
  a finite "dimension over `𝔽₂`" is a count-Lens readout; build it as an
  enumeration (`Combinatorics.BoolEnum`) and the field drops out.

## New questions (shape now clear)

- Does `NS² − 1` as "square-minus-the-self-pointing-one" appear in the
  other forced constants?  `1/α_em`, `m_μ/m_e` route through the same
  atomic `(3,2,5)` — is each "− 1" / "+ 1" residual the same single
  constant read under that domain's Lens, countable the same div-free way?

- The image count used the `c = 1` edge set (`|im|` is `c`-independent).
  Is there a count-Lens reading where the `c`-multiplicity *does* enter a
  Betti-like invariant — i.e. a higher `b_k` of the filled complex
  (`Filled3Cell*`) whose universal form needs the same `BoolEnum`
  cardinality machinery, now available?

## Cross-references

`theory/math/cohomology/bipartite.md` (b₀ / b₁ sections);
`theory/physics/symmetry/c3_chain.md` (1/α₃ octet);
`seed/AXIOM/07_primacy.md` §7.1 (domain = Lens readout of the residue).

## Cross-domain resonance (branch ↔ main, to test)

- **The betti `−1` (= `b₀`, the subtracted constant mode) ↔ the
  Δ-annihilated degree-0 floor of main's dimension calculus.**  In
  `b₁ = E − V + 1` the `−1`/`+1` is `b₀ = 1`, the lone constant mode of
  `ker δ⁰` (`bcount_const = 2 = 2¹`).  Main's merged Δ/Σ dimension calculus
  has `MultSystem.diffIter_dim_zero` — the forward difference annihilates
  exactly the degree-0 (constant) graded count — and `sumfIter_const_one`
  builds the ladder up from it (`Σ^k 1 = monoCount(k+1)`).  One Raw — the
  constant / degree-0 mode — read two ways: the cohomology-Lens subtracts it
  as `b₀` (the `−1` of `NS² − 1`), the difference-calculus Lens reads it as
  the bottom rung `Δ` floors to.  The `−1` and the dimension-0 floor are the
  same lone constant counted once.  *Test*: is `b₀` literally the `Δ`-floor
  (equivalently `Σ⁰ 1`) of the cohomology graded count — i.e. does
  `the_minus_one_under_three_lenses` add a fourth (difference-calculus) Lens
  to the same residue `dimension_is_a_computed_depth` reads?
