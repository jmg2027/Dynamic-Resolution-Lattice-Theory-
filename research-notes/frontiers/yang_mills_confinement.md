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

1. **Gap ⇒ confinement of colored modes.** ✅ **CLOSED ∅-axiom (2026-06-16)** —
   `lean/E213/Lib/Physics/YangMills/ColoredGap.lean`. The Courant–Fischer/Rayleigh
   lower bound is now a theorem for *every* configuration, not only the exhibited
   basis. The mechanism is an explicit **sum-of-squares certificate** for the
   operator `Δ₀² − massGap·Δ₀`:

   > `⟨Δ₀f,Δ₀f⟩ − 4·⟨Δ₀f,f⟩ = 2·(2(f₀+f₁+f₂) − 3(f₃+f₄))² + 6·(f₃−f₄)²`
   > (`colored_form_identity`, PURE).

   The two squares are exactly the two **gapped** eigen-directions of the forced
   spectrum — `vTop` (cross mode, `λ=10 ⇒ λ²−4λ=60`) and `vTemp` (temporal
   difference, `λ=6 ⇒ 12`); the kernel `vVac` (`λ=0`) and the spatial-difference
   modes (`λ=4`) contribute nothing, since `λ²−4λ ≥ 0` for every `λ∈{0,4,6,10}`
   and the coefficients `2,6` are forced by completing the square. From it:
   - `colored_rayleigh_ge` — `⟨Δ₀f,Δ₀f⟩ ≥ massGap·⟨Δ₀f,f⟩` for **all** `f` (the
     operator inequality `Δ₀(Δ₀−massGap·I) ⪰ 0`, no mean-zero restriction);
   - `colored_gap` — feeding it through `DiscreteLichnerowicz.lichnerowicz_abstract`,
     **every** eigenfunction `Δ₀v=λv` with `λ>0`, `Σv²>0` has `λ ≥ massGap = 4`.

   This is the **spectral face of confinement**: colored modes are gapped, the
   singlet vacuum is the unique zero-energy state, proven for an arbitrary
   excitation. ∅-axiom (`#print axioms colored_confinement_master` → empty).
   Promotion candidate when angle 2 also closes.

2. **Wilson-loop area law.** The gauge-invariant observable is a loop
   holonomy on `K_{NS,NT}^{(c)}`; confinement = area-law decay of its
   expectation. Needs a 213-native combinatorial Wilson-loop functional on
   the bipartite complex and a cohomological area/perimeter readout. **Open:
   the loop functional + area-law statement.** Connect to
   `theory/math/analysis/holonomy_of_the_lattice.md` (lattice holonomy) and
   the cup-ring / flux machinery (`Math/Cohomology/Cup/`).

## Next targets

- ~~A ∅-axiom Rayleigh-quotient lower bound for `Δ₀`~~ — **done** (`ColoredGap.lean`).
- A `WilsonLoop` definition on `K_{3,2}^{(c=2)}` + area-law witness; this is
  the genuinely new construction (angle 2). **Honest wall (multi-agent panel,
  2026-06-16):** on the abstract bipartite complex `K_{3,2}` there is no embedding,
  hence no enclosed "area" and no absolute string tension to even *state* the
  continuum law `⟨W⟩ ∼ exp(−σ·Area)` (§5.1, no exterior). The existing holonomy
  machinery (`HolonomyLattice`) proves the ℕ⁺ sector is loop-free and the first
  loop is order-4 torsion — so an exponential-in-loop-size decay is not hiding
  there; forcing one would be a value-coincidence, not a structural identity.
  A genuinely 213-native combinatorial Wilson functional + perimeter/area
  cohomological readout would have to be *built*; no internal handle found yet.
