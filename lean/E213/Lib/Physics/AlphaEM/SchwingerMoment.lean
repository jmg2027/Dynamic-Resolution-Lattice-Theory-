/-!
# Schwinger moment — a_e leading = α/2π, the first g−2 contact (∅-axiom)

The electron anomalous magnetic moment's leading QED term is a *clean
ratio of objects DRLT already derives*: `a_e = α/(2π)`.  This module is
the first contact with the (g−2) sector (program Track **E10**,
`research-notes/frontiers/research_program_year_horizon.md`): the leading
prediction as pure integer arithmetic, the agreement with measurement
bracketed at [0.1%, 0.2%], and the residual *identified* (docstring) with
the known second-order coefficient — the next DRLT reading target.

Typed inputs (quoted integers, the `PiFiveGap` pattern):
  `pi_e9       = 3141592654`    (π × 10⁹)
  `invAlpha_e9 = 137035999084`  (1/α_em × 10⁹ — DRLT ppb-level central,
                                 `AlphaEM.invAlphaEm_precision_theorem`)
  `a_e_obs_e9  = 1159652`       (observed a_e × 10⁹ ≈ 1.159652×10⁻³)

Arithmetic core:
  a_e^Schwinger × 10⁹ = 10²⁷ / (2·pi_e9·invAlpha_e9) = **1161409**
  gap = 1161409 − 1159652 = 1757  (prediction ABOVE observation)
  relative gap = 1757/1159652 ≈ 0.152% ∈ [0.1%, 0.2%]  (theorem below)

The residual is not noise: the known QED second-order term is
`C₂·(α/π)²` with `C₂ = −0.32848…`, numerically `−1.772×10⁻⁶` — the
measured gap `−1.757×10⁻⁶` matches it to ~0.8%.  So the bracketed gap is
the *shadow of C₂*; deriving `C₂ = 197/144 + π²/12 − (π²ln2)/2 + 3ζ(3)/4`
internally (ζ(3) machinery: `Real213/Zeta3Cut`) is the named next rung.
-/

namespace E213.Lib.Physics.AlphaEM.SchwingerMoment

/-- π × 10⁹ (quoted integer input, same convention as `PiFiveGap`). -/
def pi_e9 : Nat := 3141592654

/-- 1/α_em × 10⁹ (ppb-level central value; the DRLT-derived quantity). -/
def invAlpha_e9 : Nat := 137035999084

/-- Observed a_e × 10⁹ (quoted measurement). -/
def a_e_obs_e9 : Nat := 1159652

/-- The Schwinger prediction a_e × 10⁹ = ⌊10²⁷ / (2π·(1/α))⌋. -/
def a_e_schwinger_e9 : Nat := 10 ^ 27 / (2 * pi_e9 * invAlpha_e9)

/-- ★ The leading-order value: a_e^Schwinger = 1161409 × 10⁻⁹. -/
theorem schwinger_value : a_e_schwinger_e9 = 1161409 := by decide

/-- The prediction sits above the observation (the C₂ term is negative). -/
theorem prediction_above_observation : a_e_obs_e9 < a_e_schwinger_e9 := by
  decide

/-- The gap, exactly: 1757 × 10⁻⁹. -/
theorem gap_value : a_e_schwinger_e9 - a_e_obs_e9 = 1757 := by decide

/-- ★ **Agreement bracket** — the leading DRLT prediction agrees with
    the measured a_e to within [0.1%, 0.2%] (cross-multiplied):
    `a_e_obs ≤ 1000·gap` and `1000·gap ≤ 2·a_e_obs`. -/
theorem agreement_bracket :
    a_e_obs_e9 ≤ 1000 * (a_e_schwinger_e9 - a_e_obs_e9)
    ∧ 1000 * (a_e_schwinger_e9 - a_e_obs_e9) ≤ 2 * a_e_obs_e9 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ★★ Capstone — the g−2 first-contact bundle: the leading value, its
    sign relative to observation, the exact gap, and the [0.1%, 0.2%]
    agreement bracket (the gap being the C₂ shadow, next rung). -/
theorem schwinger_first_contact :
    (a_e_schwinger_e9 = 1161409)
    ∧ (a_e_obs_e9 < a_e_schwinger_e9)
    ∧ (a_e_schwinger_e9 - a_e_obs_e9 = 1757)
    ∧ (a_e_obs_e9 ≤ 1000 * (a_e_schwinger_e9 - a_e_obs_e9)
       ∧ 1000 * (a_e_schwinger_e9 - a_e_obs_e9) ≤ 2 * a_e_obs_e9) :=
  ⟨schwinger_value, prediction_above_observation, gap_value,
   agreement_bracket⟩

end E213.Lib.Physics.AlphaEM.SchwingerMoment
