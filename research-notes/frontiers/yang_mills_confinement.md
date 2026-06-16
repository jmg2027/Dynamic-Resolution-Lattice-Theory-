# Yang–Mills confinement — Wilson-loop area law (frontier)

**Status (2026-06-16):** the **mass gap** half of the 213 Yang–Mills
conjecture is *closed* — `lean/E213/Lib/Physics/YangMills/Gap.lean`,
`mass_gap_master`: the gauge-lattice Hodge Laplacian `Δ₀` of
`K_{3,2}^{(c=2)}` has exact spectrum `{0,4,4,6,10}` (complete eigenbasis,
`det = −30 ≠ 0`), one-dimensional `0`-eigenspace (connected lattice = unique
vacuum), and a strictly positive gap `= c·min(NS,NT) = 4` (∅-axiom). This
note tracks the **companion open frontier: confinement.**

## The open problem

The 213 reading of confinement: only color-**singlet** combinations are free
asymptotic states; isolated color charge cannot propagate. Two angles, both
currently *readings* (not yet ∅-axiom theorems):

1. **Gap ⇒ confinement of colored modes.** Every non-vacuum (non-constant)
   configuration has Laplacian energy `≥ massGap = 4`, so colored
   (non-singlet) excitations are gapped — none is a massless free state. The
   verified eigenbasis gives this *on the eigenbasis*; the general statement
   ("every vector orthogonal to the constant has Rayleigh quotient `≥ 4`")
   is the Courant–Fischer min, which needs a ∅-axiom spectral/Rayleigh bound
   beyond the exhibited basis. **Open: the general Rayleigh lower bound.**

2. **Wilson-loop area law.** The gauge-invariant observable is a loop
   holonomy on `K_{NS,NT}^{(c)}`; confinement = area-law decay of its
   expectation. Needs a 213-native combinatorial Wilson-loop functional on
   the bipartite complex and a cohomological area/perimeter readout. **Open:
   the loop functional + area-law statement.** Connect to
   `theory/math/analysis/holonomy_of_the_lattice.md` (lattice holonomy) and
   the cup-ring / flux machinery (`Math/Cohomology/Cup/`).

## Next targets

- A ∅-axiom Rayleigh-quotient lower bound for `Δ₀` on the orthogonal
  complement of the constant mode (would upgrade angle 1 from "on the basis"
  to "all colored configs"), reusing the complete eigenbasis already proven.
- A `WilsonLoop` definition on `K_{3,2}^{(c=2)}` + area-law witness; this is
  the genuinely new construction (angle 2).
