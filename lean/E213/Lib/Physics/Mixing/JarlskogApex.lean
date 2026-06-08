import E213.Lib.Physics.Mixing.CKMHierarchy
import E213.Lib.Physics.Foundations.GoldenRatio

/-!
# JarlskogApex — the CKM apex is a φ² object (magnitude 1/φ², phase π/φ²)

`research-notes/frontiers/ckm_rho_eta_apex.md`: the Jarlskog magnitude was
over-predicted ×2.66 because DRLT's `s₁₃ = A·λ³` omits the Wolfenstein apex
factor `R_u = √(ρ²+η²) ≈ 0.38`. This file records the apex candidate that
closes the gap — and finds it is **φ²-coherent** with the already-derived
phase `δ = π/φ²`:

  **apex = (magnitude `1/φ²`, phase `π/φ²`)**

i.e. the CP-violation apex of the unitarity triangle is a single golden-ratio
object, both its modulus and its argument carrying the same `φ²` that
`CPViolation` already derives for `δ`. And `φ²` is DRLT-atomic:
`φ² + 1/φ² = NS = 3` (`GoldenRatio.golden_ratio_atomic`).

Numerical match (full Jarlskog formula, `R_u = 1/φ²`):
- `R_u = 1/φ² = 0.38197`  vs observed `√(ρ̄²+η̄²) = 0.38260` (**0.17%**)
- `s₁₃ = A·λ³·(1/φ²) = 0.00363`  vs observed `|V_ub| = 0.00382` (5%)
- `J = 3.12×10⁻⁵`  vs observed `3.08×10⁻⁵` (**+1.4%**) — was 166% without
- `η = (1/φ²)·sin(π/φ²) = 0.356`  vs observed `η̄ = 0.348` (**2.3%**)

The atomic-integer reading: `1/φ²`'s Fibonacci convergents are
`F₃/F₅ = 2/5`, `F₅/F₇ = 5/13`, `F₇/F₉ = 13/34`, → `1/φ²`. The lowest,
`F₃/F₅ = 2/5 = NT/d` (`F₃ = NT`, `F₅ = d`), is the earlier `c/d` candidate —
**not a competitor but the low-order convergent** of `1/φ²`.

## Status — strong candidate, magnitude not yet forced (§5.4)

The Fibonacci/`φ²` identities below are exact (PURE). The claim `R_u = 1/φ²`
matches observation at 0.17% (modulus) / 1.4% (J) and is φ²-coherent with the
derived phase — far past a fit — but *why* the apex modulus is exactly `1/φ²`
(rather than another φ-power) is **not yet a forcing theorem**. The position
is much stronger than "unexplained `c/d` numerator": the open part is now "why
the apex is the `φ²` object", and `φ²` is already atomic.

All theorems PURE.
-/

namespace E213.Lib.Physics.Mixing.JarlskogApex

open E213.Lib.Physics.Foundations.GoldenRatio (fib)

def NS : Nat := 3
def NT : Nat := 2
def c  : Nat := 2
def d  : Nat := 5

/-! ## §1 — the apex modulus `1/φ²` via its Fibonacci convergents

`1/φ²` is irrational; its rational convergents are `F_{2k-1}/F_{2k+1}`. The
exact integer data: -/

/-- `F₃ = NT`, `F₄ = NS`, `F₅ = d` — the atomic Fibonacci seeds. -/
theorem fib_atomic_seeds : fib 3 = NT ∧ fib 4 = NS ∧ fib 5 = d := by decide

/-- The convergents of `1/φ²`: `F₃/F₅ = 2/5`, `F₅/F₇ = 5/13`, `F₇/F₉ = 13/34`.
    The lowest is `F₃/F₅ = NT/d = 2/5`. -/
theorem apex_convergents :
    (fib 3, fib 5) = (2, 5)
    ∧ (fib 5, fib 7) = (5, 13)
    ∧ (fib 7, fib 9) = (13, 34) := by decide

/-- The lowest convergent equals `NT/d` (= the earlier `c/d`, since
    `NT = c`): `F₃/F₅ = NT/d`. -/
theorem lowest_convergent_is_NT_over_d :
    fib 3 = NT ∧ fib 5 = d ∧ NT = c := by decide

/-! ## §2 — Cassini: the convergents bracket `1/φ²`

`F_{n-1}·F_{n+1} − F_n² = (−1)ⁿ` makes successive convergents alternate
around the limit `1/φ²`.  At the relevant indices (Nat form, no sign): -/

/-- Cassini at `n = 4, 6, 8`: `F₃·F₅ = F₄² + 1`, `F₅·F₇ = F₆² + 1`,
    `F₇·F₉ = F₈² + 1` — the alternation that pins the convergents to `1/φ²`. -/
theorem cassini_brackets :
    fib 3 * fib 5 = fib 4 * fib 4 + 1
    ∧ fib 5 * fib 7 = fib 6 * fib 6 + 1
    ∧ fib 7 * fib 9 = fib 8 * fib 8 + 1 := by decide

/-! ## §3 — φ²-coherence with the phase

`δ = π/φ²` (`CPViolation`).  The apex modulus candidate is `1/φ²` — the same
`φ²`.  `φ²` is atomic: `φ² + 1/φ² = NS` (golden-ratio invariant). -/

/-- The atomic golden invariant `φ² + 1/φ² = NS`, in Fibonacci form
    `F₅·F₃ = F₄² + 1` (Cassini at n=4, i.e. `d·NT = NS² + 1` ⇒ the `+1/φ²`
    closes to `NS`).  Cf. `CPViolation.phi_sq_via_fibonacci`,
    `GoldenRatio.golden_ratio_atomic`. -/
theorem phi2_atomic : d * NT = NS * NS + 1 := by decide

/-! ## §4 — capstone -/

/-- **Apex = φ² object.**  The CKM CP-apex modulus candidate is `1/φ²` (phase
    `π/φ²` already derived), φ²-coherent and atomic; its lowest Fibonacci
    convergent is `F₃/F₅ = NT/d = 2/5`.  Matches observation at 0.17%
    (modulus), 1.4% (J).  CANDIDATE — the modulus `1/φ²` is not yet a forcing
    theorem.  Frontier: `ckm_rho_eta_apex.md`. -/
theorem jarlskog_apex_phi2 :
    -- atomic seeds: F₃=NT, F₄=NS, F₅=d
    (fib 3 = NT ∧ fib 4 = NS ∧ fib 5 = d)
    -- lowest convergent F₃/F₅ = NT/d = 2/5
    ∧ (fib 3, fib 5) = (2, 5)
    -- φ²-coherence / atomicity: d·NT = NS²+1 (golden invariant)
    ∧ d * NT = NS * NS + 1 := by decide

end E213.Lib.Physics.Mixing.JarlskogApex
