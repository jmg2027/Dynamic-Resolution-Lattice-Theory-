import E213.Lib.Physics.AlphaEM.Bare

/-!
# sin²θ_W = α_em/α_2 — same simplicial pattern (0 axioms)

DRLT formula:
  sin²θ_W(M_Z) = α_em / α_2 = 30 / (30 + 10π²)

  At M_Z (bare DRLT):
    1/α_em(M_Z) = 30 + 10π² ≈ 128.696
    1/α_2 = 30
    → sin²θ_W = 30/128.696 ≈ 0.2331

  Measurement-Lens reading (PDG MS-bar): 0.2312 ± 0.0001
  Two Lens readings differ by 0.82% (DRLT bare above);
  same running gap as α_em, structurally expected.

## Structural form

  sin²θ_W = 1/α_2 / (1/α_em(bare))
         = 30 / (30 + 60·ζ(2))
         = 1 / (1 + 2·ζ(2))

  All from {NT, ζ(2)}: 30 = 12·NT·5/4, 60 = 12·NT·5/2 = c·NS·NT·d.

  Same simplicial atoms as α_em IR — *direct ratio* of two
  prior-derived quantities.

## Bracket

  At N = 10:
    sin²θ_W ∈ [30/(30+60·upper(10)), 30/(30+60·S(10))]
            ≈ [0.2326, 0.2439]
    Bare DRLT 0.2331 ∈ bracket ✓
    Observed 0.2312 just outside — running gap signature.
-/

namespace E213.Lib.Physics.YangMills.WeinbergAngle

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Physics.Basel.Bound

/-- sin²θ_W lower bracket: 30/(30 + 60·upper(N)). -/
def sin2_W_lower (N : Nat) : (Nat × Nat) :=
  let u := upper N
  -- (30·u.den) / (30·u.den + 60·u.num)
  (30 * u.2, 30 * u.2 + 60 * u.1)

/-- sin²θ_W upper bracket: 30/(30 + 60·S(N)). -/
def sin2_W_upper (N : Nat) : (Nat × Nat) :=
  let s := S N
  (30 * s.2, 30 * s.2 + 60 * s.1)

/-- ★ Capstone — sin²θ_W same pattern + running gap signature ★
    Bare value bracketed at modest N.  Observed below bracket,
    same as 1/α_em IR running case.
    Both share identical "running" structure that DRLT primitives
    don't yet capture. -/
theorem weinberg_pattern_capstone :
    -- N=3 endpoints
    sin2_W_lower 3 = (30 * 108, 30 * 108 + 60 * 183)
    ∧ sin2_W_upper 3 = (30 * 36, 30 * 36 + 60 * 49)
    -- Bare 0.2331 in bracket at N=10
    ∧ (let lo := sin2_W_lower 10
       let hi := sin2_W_upper 10
       lo.1 * 10000 < 2331 * lo.2
       ∧ 2331 * hi.2 < hi.1 * 10000)
    -- Observed 0.2312 below bare (running signature)
    ∧ (let lo := sin2_W_lower 10
       2312 * lo.2 < 10000 * lo.1)
    -- Same atomic primitives
    ∧ (12 * NT * 5 = 30 * 4)
    ∧ (NS = 3) ∧ (NT = 2) ∧ (d = 5) := by decide

/-! ## Closure of running gap — Class B α_GUT leak

The "running gap" identified above (observed 0.2312 below bare
0.2331) is now closed via Hunter Methodology Lesson L3:

  sin²θ_W = (30 / (30 + 60·ζ(2))) · (1 − α_GUT / NS)
          = 0.2331074 · (1 − 0.024317/3)
          = 0.231218

  Measurement-Lens reading (PDG MS-bar) = 0.23121 ± 0.00012
  (520 ppm uncertainty)
  |Δ|        ≈ 35 ppm  ★ (was 8200 ppm — 234× tighter; 0.07σ)

The Class B leak coefficient k = NS = 3 is the simplest atomic
count (number of S-type chiral channels).  The "running gap"
phenomenon — the shift between bare-lattice reading and
higher-resolution Lens reading — is exactly an α_GUT-scale
shift of magnitude 1/NS, a lattice-internal depth effect.
-/

/-- ★★ sin²θ_W tighter atomic skeleton (35 ppm, 234× tighter).
    Class B α_GUT leak with k = NS, on top of the existing
    30/(30+60·ζ(2)) Class C base. -/
theorem sin2_W_v2_atomic :
    NS = 3 ∧ NT = 2 ∧ d = 5
    -- Class C base prefactor: 30 = 12·NT·5/4 (atomic via Basel S(NT))
    ∧ (12 * NT * 5 = 30 * 4) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## The 35 ppm claim, made arithmetic (typed π², program E9)

The Class-B closure above was docstring numerics; here it is integer
arithmetic on the typed input `pi2_e10 = 98696044011` (π²×10¹⁰, the
`PiFiveGap` convention).  Exact rationals:

  sin²θ_W(bare) = wA/wB,   wA = 30·10¹⁰,  wB = wA + 10·pi2_e10
  leak factor   = wD/wC,   wC = 75·pi2_e10 (= NS/α_GUT scale),
                           wD = wC − 6·10¹⁰   (1 − α_GUT/NS)
  sin²θ_W(v2)   = (wA·wD)/(wB·wC) = 0.2312179…

vs observed 0.23121(12): the corrected-value gap is **[30, 35] ppm**
(`v2_gap_ppm_bracket`) and sits inside the ±1σ window (0.07σ,
`v2_within_observed_window`), while the bare value is outside it
(`bare_outside_observed_window`) — the running-gap statement and its
Class-B closure are now theorems, not prose. -/

/-- π² × 10¹⁰ (quoted integer input, `PiFiveGap` convention). -/
def pi2_e10 : Nat := 98696044011

/-- Bare numerator: 30 × 10¹⁰. -/
def wA : Nat := 300000000000

/-- Bare denominator: 30·10¹⁰ + 10·π²·10¹⁰  (= (30+10π²)×10¹⁰). -/
def wB : Nat := wA + 10 * pi2_e10

/-- Leak denominator: 75·π²·10¹⁰  (the NS/α_GUT = 75π²/6 scale ×6·10¹⁰). -/
def wC : Nat := 75 * pi2_e10

/-- Leak numerator: wC − 6·10¹⁰  (i.e. 1 − α_GUT/NS = 1 − 6/(75π²)). -/
def wD : Nat := wC - 60000000000

/-- Observed sin²θ_W × 10⁷ (PDG MS-bar central 0.23121). -/
def sin2_W_obs_e7 : Nat := 2312100

/-- ★ The corrected value, exactly: ⌊(wA·wD)·10⁷/(wB·wC)⌋ = 2312179,
    i.e. sin²θ_W(v2) = 0.2312179…  (bare was 0.2331073). -/
theorem v2_value_e7 : 10000000 * (wA * wD) / (wB * wC) = 2312179 := by
  decide

/-- ★ **The 35 ppm claim as a theorem** — the corrected-value gap to the
    observed central is in [30, 35] ppm (cross-multiplied on the exact
    e7 floor: gap = 79×10⁻⁷). -/
theorem v2_gap_ppm_bracket :
    30 * sin2_W_obs_e7 ≤ 79 * 1000000
    ∧ 79 * 1000000 ≤ 35 * sin2_W_obs_e7 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The corrected value sits INSIDE the observed ±1σ window
    (σ = 12×10⁻⁵ = 1200×10⁻⁷; gap 79 ≪ 1200 — 0.07σ). -/
theorem v2_within_observed_window :
    10000000 * (wA * wD) / (wB * wC) - sin2_W_obs_e7 < 1200 := by
  decide

/-- The BARE value sits OUTSIDE the same window
    (bare − obs = 18973×10⁻⁷ > 1200×10⁻⁷ = 1σ): the running gap is
    real, and closed by the Class-B leak, both as arithmetic. -/
theorem bare_outside_observed_window :
    1200 < 10000000 * wA / wB - sin2_W_obs_e7 := by
  decide

/-- ★★ E9 capstone — the typed running-gap bundle: exact corrected
    value, [30,35] ppm agreement, inside-1σ (corrected) vs
    outside-1σ (bare). -/
theorem weinberg_running_gap_typed_core :
    (10000000 * (wA * wD) / (wB * wC) = 2312179)
    ∧ (30 * sin2_W_obs_e7 ≤ 79 * 1000000
       ∧ 79 * 1000000 ≤ 35 * sin2_W_obs_e7)
    ∧ (10000000 * (wA * wD) / (wB * wC) - sin2_W_obs_e7 < 1200)
    ∧ (1200 < 10000000 * wA / wB - sin2_W_obs_e7) :=
  ⟨v2_value_e7, v2_gap_ppm_bracket, v2_within_observed_window,
   bare_outside_observed_window⟩

end E213.Lib.Physics.YangMills.WeinbergAngle
