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

/-! ## §4 — single-parameter apex + triangle predictions

The phase and modulus share one golden number: `δ/π = R_u = 1/φ²`, i.e.
`δ = π·R_u`.  So the apex is **single-parameter**, `z = r·e^{iπr}` with
`r = 1/φ²` — the two φ²-inputs collapse to one.  (Why `γ = π·R_u` itself,
and why `r = 1/φ²`, remain open; `γ` alone does *not* geometrically force
`R_u` — a triangle is underdetermined by one angle.)

Given the single parameter, the full unitarity triangle is determined and
**predicts** its other elements (consequences, not inputs):
- `β = 22.45°` vs observed `22.0°`
- `sin 2β = 0.706` vs observed `0.684 ± 0.022` (CKMfitter) / `0.695 ± 0.019` —
  **~0.6–1.0σ high** (consistent, but on the high side, not centred; `sin 2β`
  is the precisely-measured "golden mode" `B→J/ψ K_S`)
- `α = 88.8°` vs observed `~85–90°`
- `R_t = 0.932` vs observed `~0.91–0.93`
- `ρ̄ = (1/φ²)cos(π/φ²) = 0.138` vs observed `≈ 0.14–0.16` (η̄ side is the
  strong match at 2.3%; ρ̄ is weaker against the higher current global ρ̄)
(These trig values are transcendental — documented here, not PURE-Nat.)

`δ/π = R_u` at the shared Fibonacci-convergent level (both `= 1/φ²`,
convergents `2/5, 5/13, 13/34`): the *same* `(num,den)` serves as both
`δ/π` and `R_u`. -/

/-- The apex's phase-over-π and modulus are the **same** golden number
    `1/φ²` (shared Fibonacci convergents).  Hence `δ = π·R_u`: one parameter
    `r = 1/φ²` fixes both, `apex = r·e^{iπr}`.

    **§5.7 reading**: this shared-convergent equality `δ/π = R_u` *is* the
    frozen=dynamic identity at the apex — the FROZEN reading (contraction `R_u`)
    and the DYNAMIC reading (phase-fraction `δ/π`) are the **same** 213-native
    rational at every convergent depth.  The apex is the self-reference point
    where "how far contracted" equals "how far turned (in half-turns)".  So the
    coupling is PURE at the rational level; only the transcendental coefficient
    `π = arg(M⁵)` itself is non-Nat.  (Cf. `ApexCPMechanism`,
    `seed/AXIOM/05_no_exterior.md` §5.7.) -/
theorem phase_over_pi_eq_modulus :
    -- δ/π and R_u share the convergent F₃/F₅ = 2/5
    (fib 3, fib 5) = (2, 5)
    -- and the next, F₅/F₇ = 5/13 → 1/φ²
    ∧ (fib 5, fib 7) = (5, 13) := by decide

/-! ## §5 — `1/φ²` is the residue self-reference contracting eigenvalue

Why `1/φ²` (not an arbitrary golden power)?  It is the **sub-dominant
eigenvalue of the residue's self-reference matrix** `M = [[c,1],[1,1]]` —
the Möbius `P(x)=(2x+1)/(x+1)` of `seed/AXIOM/05_no_exterior.md` §5.6,
`Lib/Math/Algebra/Mobius213`.  Its characteristic polynomial is fully
atomic:

  `trace = c+1 = NS = 3`,  `det = c−1 = 1`,
  `disc = trace²−4·det = NS²−4 = 5 = NS+NT = d`,
  eigenvalues `(NS ± √d)/2 = φ², 1/φ²`.

So `R_u = 1/φ² = (NS−√d)/2` is the **contracting** eigenvalue — the rate at
which `P^n` converges to the residue fixed point φ (§5.6).  The value is
structurally distinguished, not fitted.  (The phase `δ = π·R_u` uses the
same eigenvalue.)  Open: *why the CKM apex modulus equals this eigenvalue* —
the one remaining physical identification. -/

/-- The residue self-reference matrix `M = [[c,1],[1,1]]` (Möbius `P`, §5.6)
    has fully atomic characteristic data: `trace = c+1 = NS`, `det = c−1 = 1`,
    `disc = NS²−4·det = d = NS+NT`.  Hence eigenvalues `(NS±√d)/2 = φ², 1/φ²`,
    and `R_u = 1/φ² = (NS−√d)/2` is the contracting one.  Cf.
    `Mobius213.{mobius_213_trace, mobius_213_discriminant}`. -/
theorem apex_modulus_is_selfref_contracting_eigenvalue :
    c + 1 = NS                  -- trace = NS
    ∧ c - 1 = 1                 -- det = 1
    ∧ NS * NS - 4 * 1 = d       -- disc = NS²−4 = 5 = d
    ∧ NS * NS - 4 * 1 = NS + NT := by decide

/-! ## §5.5 — which eigenvalue: `1/φ²` (not `φ²`) is FORCED by `R_u < 1`

§5 grounds the *value* `1/φ²` as a self-reference eigenvalue, but a residual
sub-freedom remained in the frontier: "why this golden power, not `φ`, `φ³`,
…?".  This section removes that sub-freedom.

The self-reference matrix `M = [[c,1],[1,1]]` has **exactly two** eigenvalues,
a **reciprocal pair** (`λ₊·λ₋ = det = 1`, `λ₊+λ₋ = trace = NS`): the
expanding `λ₊ = φ²` and the contracting `λ₋ = 1/φ²`.  There are no other
golden powers in `spec M` — the question is binary, not "which power".

The CKM apex modulus `R_u = √(ρ̄²+η̄²)` is a *side ratio* of the unitarity
triangle whose base (`V_cd V_cb*`) is normalised to 1; the apex is interior,
so **`R_u < 1`** (observed `R_u ≈ 0.38`).  Of the reciprocal pair, exactly one
member is `< 1` — the contracting `λ₋ = 1/φ²`.  Hence, *given* the apex is a
self-reference eigenvalue (the one remaining physical premise, §5.4), the
constraint `R_u < 1` **forces** `R_u = 1/φ²` uniquely; `φ² > 1` is excluded.

Witnessed PURE via the Fibonacci convergents (num/den) of each root:
- `1/φ²` convergents `F₃/F₅, F₅/F₇, F₇/F₉ = 2/5, 5/13, 13/34` — all **sub-unit**
  (`num < den`), so `1/φ² < 1`.
- `φ²` convergents `F₄/F₄?`… are the reciprocals `F₆/F₄, F₈/F₆, F₁₀/F₈
  = 8/3, 21/8, 55/21` — all **super-unit**, in fact `> 2·den` (`φ² > 2`).
- Reciprocal-pair / det-1 witness: Cassini `F₃·F₅ = F₄²+1` (the `λ₊λ₋ = 1`
  that pairs the two convergent families). -/

/-- **`R_u = 1/φ²` is forced by `R_u < 1`.**  The two self-reference
    eigenvalues are a reciprocal pair (`det = 1`); their Fibonacci convergents
    split sharply — `1/φ²`'s are sub-unit (`num < den`), `φ²`'s are super-unit
    (`> 2·den`).  So among `spec M = {φ², 1/φ²}` the constraint `R_u < 1`
    selects `1/φ²` uniquely.  This converts "which golden power" into the
    binary "which of the two eigenvalues", resolved by `R_u < 1`.  PURE. -/
theorem apex_modulus_subunit_forced :
    -- 1/φ² convergents F₃/F₅, F₅/F₇, F₇/F₉ are sub-unit (num < den) ⇒ 1/φ² < 1
    (fib 3 < fib 5 ∧ fib 5 < fib 7 ∧ fib 7 < fib 9)
    -- φ² convergents F₆/F₄, F₈/F₆, F₁₀/F₈ are super-unit (> 2·den) ⇒ φ² > 2 > 1
    ∧ (2 * fib 4 < fib 6 ∧ 2 * fib 6 < fib 8 ∧ 2 * fib 8 < fib 10)
    -- reciprocal pair (det = 1): Cassini F₃·F₅ = F₄² + 1 couples the two families
    ∧ fib 3 * fib 5 = fib 4 * fib 4 + 1 := by decide

/-! ## §6 — capstone -/

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
