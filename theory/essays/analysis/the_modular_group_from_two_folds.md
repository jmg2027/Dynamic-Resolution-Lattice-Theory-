# The modular group from the two folds — one discriminant, one identity, the dial and its dynamics

`SL(2, ℤ)` is not imported. It is **what the two founding folds generate** — negation
(`ℤ = invert(+)`) and reciprocal (`ℚ = invert(×)`) are reflections, their products are the modular
generators, and a single identity (Cayley–Hamilton) with a single discriminant (`tr² − 4·det`)
governs both the static elliptic/parabolic/hyperbolic classification and the periodic/aperiodic
dynamics. The whole order-2 story is one fold-pair, read statically and then in motion.

## 213-native answer

### The two folds are reflections, and their product is the elliptic swap

The additive fold is the integer matrix `N = [[−1,0],[0,1]]` (negation `z ↦ −z`); the multiplicative
fold is `R = [[0,1],[1,0]]` (reciprocal `z ↦ 1/z`). Both are **involutive reflections** —
`N² = R² = I`, `det N = det R = −1` (`Real213/FoldReflections.{N_involutive, R_involutive, N_det,
R_det}`). On the four-point fixture `{∞, 0, +1, −1}` the additive fold **fixes** the `0`/`∞` pair and
**swaps** the units, the multiplicative fold the mirror (`FoldDuality.two_folds_dual_on_pairs`); each
ℤ/2 fixes the orbit the other swaps, and their composite is fixed-point-free — `{id, N, R, N·R}` is a
Klein four-group (`FoldKlein.klein_four_group`). The composite is the elliptic swap
`N · R = S = [[0,−1],[1,0]] = z ↦ −1/z` (`FoldReflections.negation_recip_eq_swap`): two reflections
in intersecting mirrors compose to a rotation.

### The generators are `PSL(2, ℤ) = ℤ₂ * ℤ₃`

`S` has projective order `2` (`S² = −I`); the second elliptic generator `U = [[0,−1],[1,1]]` has
projective order `3` (`U³ = −I`), its Möbius action the fixed-point-free 3-cycle `∞ ↦ 0 ↦ −1 ↦ ∞`
on the Eisenstein fixture (`EllipticCycleFixtures.elliptic_generators_are_two_and_three`). The free
factors `2, 3` are the modular group: the `ℤ₂` is the folds' product (the `0 = ∞` swap), the `ℤ₃` is
Eisenstein. The matrix orders `4, 6` halve/third to the projective orders `2, 3` through the central
`−I` (the Cassini sign), which acts trivially on the projective line.

### Cayley–Hamilton is the primitive; the discriminant is its own

Every `2×2` matrix satisfies its characteristic equation `M² = tr(M)·M − det(M)·I`
(`Mat2CayleyHamilton.cayley_hamilton`, proved generally by `ring_intZ`). Its scalar shadow
`λ² − tr·λ + det` has discriminant exactly `tr² − 4·det = disc` (`char_poly_discriminant`). So the
dial is not a separate gadget — it is the discriminant of the one identity, and each generator's
relation is the `(tr, det)` specialization: `S² = −I`, `U² = U − I`, `T² = 2T − I`, `G² = 3G − I`.

### The trichotomy: one frame, the disc sign selects the face

Every `SL(2, ℤ)` element is a product of two reflections, and `tr² − 4` selects which
(`ParabolicTranslation.sl2_trichotomy_as_two_reflections`):

  - **elliptic** `S = N · R` — `disc < 0`, intersecting mirrors → **rotation** (periodic);
  - **parabolic** `T = Aₚ · Bₚ` — `disc = 0`, parallel mirrors → **translation** (the difference-Lens
    depth-1 rung);
  - **hyperbolic** `G = A · B` — `disc > 0`, ultraparallel mirrors → **boost** (aperiodic).

The classical "two reflections compose to a rotation / translation / boost" is here read on the two
*founding folds*: additive ∘ multiplicative, classified by one number.

### The dynamics: Cayley–Hamilton iterated is the trace recurrence

With associativity (`Mat2Assoc.mul_assoc`), Cayley–Hamilton iterates to the **trace recurrence**
`tr(Mⁿ⁺²) = tr(M)·tr(Mⁿ⁺¹) − det(M)·tr(Mⁿ)` (`Mat2TraceRecurrence.trace_recurrence`). The powers'
traces are a constant-coefficient (`C`-finite) recurrence whose characteristic discriminant is the
dial. The static trichotomy becomes dynamic:

  - **elliptic — bounded, periodic.** `S`: `tr(Sⁿ⁺²) = −tr(Sⁿ)`, period 4, cycling `2, 0, −2, 0`
    (`EllipticTracePeriodic`). `U`: `tr(Uⁿ⁺³) = −tr(Uⁿ)`, period 6, cycling `2, 1, −1, −2, −1, 1`
    (`UTracePeriodic.elliptic_orders_four_and_six`). The `{4, 6}` are `|ℤ[i]^×|`, `|ℤ[ω]^×|` — the
    Gaussian/Eisenstein orders.
  - **hyperbolic — unbounded, aperiodic.** `G`: `tr(Gⁿ⁺²) = 3·tr(Gⁿ⁺¹) − tr(Gⁿ)`, the Lucas
    sequence `2, 3, 7, 18, 47, …` strictly increasing, so `Gⁿ⁺¹ ≠ I` for every `n`
    (`GoldenAperiodic.golden_aperiodic`).

This is **holonomicity at the matrix scale**: periodic = the holonomic floor; growing = the boost. The
sign of one discriminant is the dividing line.

### The finite-order spectrum is exactly `{1, 2, 3, 4, 6}` — uniform, two-sided

The trichotomy closes into a single structural theorem (`Real213/FiniteOrderSpectrum`, 29 PURE).
For **every** `M ∈ SL(2, ℤ)` and **every** exponent, `M^{n+1} = I` forces
`M = I ∨ M² = I ∨ M³ = I ∨ M⁴ = I ∨ M⁶ = I` (`finite_order_spectrum`), hence `M¹² = I`
(`finite_order_divides_twelve`) — every period of the integer modular family divides 12.  The
proof is the trace trichotomy run on the one engine:

  - `tr ≥ 3` — the trace strictly climbs from the floor 2 (`trace_mono_of_ge_three`, the
    `golden_trace_mono` argument freed from `t = 3`): no return;
  - `tr ≤ −3` — the square has `tr(M²) = tr² − 2 ≥ 7` and inherits the order: no return;
  - `tr = ±2` — **parabolic rigidity**: the closed form `Mᵏ = I + k·(M − I)` (`parabolic_pow`)
    returns only if it never left (`M = I`, resp. `M² = I`);
  - `tr ∈ {0, ±1}` — the elliptic orders fall out of Cayley–Hamilton unconditionally
    (`M² = −I`, `M³ = ∓I`).

And the spectrum is **two-sided**: orders 4 and 6 are realized *exactly* by `S` and `U`
(`exact_order_four`, `exact_order_six`), while ★ `no_order_five` — `M⁵ = I ⟹ M = I` — pins the
**first forbidden order**: a 2D integer lattice admits no five-fold symmetry (the pentagon /
quasicrystal axis, `PentagonGoldenTrace`'s golden trace `2cos(2π/5) = φ − 1` is irrational, and
here the matrix-level closure).  `no_order_seven` likewise; the only prime orders are `2, 3` —
the free factors of `PSL(2, ℤ) = ℤ₂ * ℤ₃` re-derived from the spectrum side.  Capstone:
`crystallographic_spectrum`.  Six is the **last finite period** of the modular family; the
hyperbolic `G` (`golden_aperiodic`) and the irrational-angle rotation (π's face, below) sit past
the wall in the two different directions — unbounded trace, and bounded trace with no return.

## Cross-frame

Classically: `SL(2, ℤ)` is generated by `S` and `T` (or `S` and `U`); `PSL(2, ℤ) = ℤ₂ * ℤ₃`; the
trace classifies isometries by `|tr|` against `2`; the trace of the powers obeys the Chebyshev/Lucas
recurrence; every isometry is a product of two reflections. Each classical statement is recovered —
but the modular group is read here as **the symmetry of the founding invert-moves**, not as a borrowed
object. And it meets the residue story (`seed/AXIOM/06_lens_readings.md` §6.9): the antipode `S =
z ↦ −1/z` swaps the residue pair `{0, ∞}` and the unit pair `{±1}` — the two ℤ/2-orbits the folds act
on, `0 = ∞` one pre-Lens residue, not a value.

## Constructive accessibility

Everything lands on syntactic objects: `N, R, S, U, T, G, A, B` are concrete `Mat2.mk` integer
literals; the classification is `Mat2.disc`; the dynamics is `pow` + `trace_recurrence`; the proofs
are `decide` (concrete) and `ring_intZ` / `Int213.Order` (general), all ∅-axiom (0 DIRTY). The modular
group is reached as a finite list of matrices and one general identity — no `Classical`, no completed
infinity.

## Self-check

  - *Is `SL(2, ℤ)` an exterior import?* No — it is generated by the two folds, which are
    residue-internal invert moves; the matrices are their readout.
  - *Is `0 = ∞` a dual pair smuggled as a value?* No (§6.9) — one pre-Lens residue, the swapped orbit
    of the antipode, never a stratum value.
  - *Is periodic-vs-aperiodic a dichotomy-import?* No — both are the single trace recurrence read at
    opposite signs of one discriminant; one mechanism, two faces.

## Open frontier

π is the **elliptic face at an irrational rotation angle**: `det = 1`, `disc < 0`, the trace bounded
in `[−2, 2]` like the elliptic generators — but with **no finite period**. The crystallographic
`{1, 2, 3, 4, 6}` are the only lattice periods — now the uniform theorem
(`FiniteOrderSpectrum.crystallographic_spectrum`), not a census; π's angle is irrational, so the
periodic floor fails and its continued fraction goes non-holonomic. The dial classifies the algebraic
faces exactly; the irrational pole is reached by no finite pointing — the standing boundary
(`theory/math/analysis/phi_pi_poles.md`). φ lives on the boost (proven aperiodic); π lives on the
rotation that never returns.

---

**Anchor chapters**: `theory/lens/zero_infinity_and_two_folds.md` +
`theory/math/analysis/phi_pi_poles.md` + `seed/AXIOM/06_lens_readings.md` §6.9.
**Lean**: `Real213/{FoldReflections, FoldDuality, FoldKlein, EllipticCycleFixtures,
ParabolicTranslation, Mat2CayleyHamilton, Mat2Assoc, Mat2TraceRecurrence, GoldenAperiodic,
EllipticTracePeriodic, UTracePeriodic, FiniteOrderSpectrum}` (all ∅-axiom).
