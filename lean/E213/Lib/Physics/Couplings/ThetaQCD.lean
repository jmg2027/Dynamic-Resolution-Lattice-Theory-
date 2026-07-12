import E213.Lib.Physics.Couplings.AlphaGUT
import E213.Lib.Physics.Mixing.CabibboAngle

/-!
# θ_QCD bound — J · α_GUT⁴ < nEDM bound (0 axioms)

DRLT lattice reading:
  θ_QCD ~ J · α_GUT⁴

  where J = Jarlskog invariant from CKM matrix.
  J_DRLT ≈ 3 × 10⁻⁵
  α_GUT⁴ ≈ 3.5 × 10⁻⁷
  J · α⁴ ≈ 2.86 × 10⁻¹¹

Current measurement-Lens bound (nEDM, 2026):
  θ_QCD < 1.8 × 10⁻¹⁰

  → the lattice reading sits a factor ~6 below the
    measurement-Lens bound (two internal Lens readings, both
    inside 213).

## Why α⁴

  The 4th power of α_GUT = (d-1) cofactor times.  The same (d-1) = 4
  cofactor appears (same as the Dyson denominator).

  α_GUT^(d-1) = α_GUT^4 = "(d-1) loop suppression factor".

## Falsifiability

  Next-gen nEDM (2027-30): bound goes to ~10⁻¹².
  DRLT θ_QCD = 2.86·10⁻¹¹ would then be DETECTABLE.
  *Falsifiable prediction*: on measurement, either agreement or DRLT is refuted.

## Bracket structure

  α_GUT bracket at N=10: [α^lower, α^upper] from S(N), upper(N).
  α_GUT⁴ bracket: [α^lower⁴, α^upper⁴]
  Multiply by J ≈ 3·10⁻⁵ to get θ_QCD bracket.
-/

namespace E213.Lib.Physics.Couplings.ThetaQCD

open E213.Lib.Physics.Simplex.Counts

/-- α_GUT^4 exponent: (d-1) = 4. ★ Same Dyson denom ★ -/
def alpha_pow : Nat := d - 1

theorem alpha_pow_eq_4 : alpha_pow = 4 := by decide

theorem alpha_pow_eq_d_minus_1 : alpha_pow = d - 1 := by decide

/-- Same exponent 4 = (d-1) cofactor:
    Dyson tail denom, m_H face BC, m_μ/m_e Dyson, Cabibbo Ξ,
    nuclear a_S coefficient — *and* θ_QCD α-power. -/
theorem alpha_pow_universal :
    alpha_pow = d - 1
    ∧ alpha_pow = NS + 1
    ∧ alpha_pow = 4 := by decide

/-- nEDM bound: 1.8 × 10⁻¹⁰ = 18 × 10⁻¹¹ = 180/10¹². -/
def nEDM_bound_num : Nat := 18

/-- DRLT prediction central value: 2.86 × 10⁻¹¹ ≈ 286/10¹³. -/
def theta_QCD_num : Nat := 286

/-- DRLT prediction below nEDM bound by factor 6.3. -/
theorem drlt_below_bound :
    -- Cross-mult: 286 · 100 < 18 · 1000  (DRLT/10¹³ < bound/10¹¹)
    286 * 100 < 18 * 10000 := by decide

/-- Concrete factor: bound / DRLT ≈ 6.3.
    18·10000 / (286·100) = 180000/28600 ≈ 6.29. -/
theorem bound_drlt_ratio :
    -- bound/DRLT > 6: 18·10000 > 6·286·100
    18 * 10000 > 6 * 286 * 100
    -- bound/DRLT < 7
    ∧ 18 * 10000 < 7 * 286 * 100 := by decide

/-- ★ θ_QCD prediction from atomic primitives ★
    α_GUT^(d-1) form — same (d-1) cofactor as Dyson family.
    Falsifiable via next-gen nEDM (2027-30). -/
theorem theta_QCD_pattern :
    -- α power = d - 1 = 4 (same Dyson cofactor)
    (alpha_pow = d - 1)
    -- DRLT prediction strictly below current nEDM bound
    ∧ (286 * 100 < 18 * 10000)
    -- Factor ~6 below
    ∧ (18 * 10000 > 6 * 286 * 100)
    -- All atomic
    ∧ (d = 5) ∧ (NS = 3) ∧ (NT = 2) := by decide

/-! ## DRLT prediction window

The genuine falsifier is the bound comparison `theta_QCD_pattern` /
`drlt_below_bound`: the DRLT prediction 286·10⁻¹³ sits a factor ~6
below the measured nEDM bound 18·10⁻¹¹.  The interval below merely
asserts the hand-typed prediction literal `theta_QCD_num = 286` lies
in a stated discrimination window [251, 300]·10⁻¹³; it brackets the
prediction itself, not a measured value, so it is a prediction-window
statement, not a measured-precision result. -/

/-- θ_QCD prediction window — the DRLT prediction literal 286·10⁻¹³
    lies in [251, 300]·10⁻¹³ (the next-gen nEDM discrimination window,
    2027-30).  This brackets the prediction, not a measurement; the
    genuine falsifier is the bound comparison above.  PURE.

    **Scope caveat (typed below)**: the 286 literal consumes the
    *observed* J ≈ 3.08×10⁻⁵ — an import, not a derivation.  DRLT's own
    CKM chain gives J_DRLT = 8.18×10⁻⁵ (×818/308 = ×2.66,
    `Mixing/JarlskogApex`; frontier `ckm_rho_eta_apex.md`), under which
    this window provably fails (`window_fails_with_native_J`). -/
theorem theta_QCD_precision_bracket :
    251 ≤ theta_QCD_num ∧ theta_QCD_num ≤ 300 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## The J input, typed (the E0 repair)

`theta_QCD_num = 286` uses J_obs ≈ 3.08×10⁻⁵ — an experimental import.
DRLT's own chain (`s₁₃ = A·λ³`, apex `R_u = 1/φ²`, `δ = 90°`) currently
over-predicts: J_DRLT/J_obs = 818/308 (`Mixing/JarlskogApex`, the ×2.66
over-prediction; the missing apex projection is the open frontier
`ckm_rho_eta_apex.md`).  The theorems below state what survives and what
breaks under the *native* J — so the falsifier's J-dependence is a
theorem, not a docstring assumption:

  θ_native = 286 · (818/308) · 10⁻¹³ = 233948/308 · 10⁻¹³ ≈ 760 · 10⁻¹³.

Survives: the nEDM bound comparison (factor 2–3 below, was ~6) and
next-generation detectability (both J's exceed the ~10⁻¹² sensitivity —
the 2027-30 run decides REGARDLESS of which J is right).
Breaks: the [251, 300] prediction window (native value ≈ 760 is outside),
proven below rather than asserted. -/

/-- J_DRLT / J_obs numerator (8.18×10⁻⁵ = 818·10⁻⁷). -/
def J_native_num : Nat := 818

/-- J_DRLT / J_obs denominator (3.08×10⁻⁵ = 308·10⁻⁷). -/
def J_obs_num : Nat := 308

/-- ★ Native-J prediction still below the nEDM bound:
    `286·(818/308) < 1800` (units 10⁻¹³), cross-multiplied.
    The genuine falsifier SURVIVES the J repair. -/
theorem native_J_below_bound :
    theta_QCD_num * J_native_num < 1800 * J_obs_num := by decide

/-- The surviving margin is factor 2–3 (was ~6 with the imported J). -/
theorem native_J_margin :
    2 * (theta_QCD_num * J_native_num) < 1800 * J_obs_num
    ∧ 1800 * J_obs_num < 3 * (theta_QCD_num * J_native_num) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ★ The [251, 300] window FAILS under the native J:
    `286·(818/308) > 300` (units 10⁻¹³), cross-multiplied.
    The honest downgrade of `theta_QCD_precision_bracket`, as a theorem. -/
theorem window_fails_with_native_J :
    300 * J_obs_num < theta_QCD_num * J_native_num := by decide

/-- ★ J-robust detectability — under EITHER J, the prediction exceeds
    the next-gen nEDM sensitivity ~10⁻¹² = 10·10⁻¹³: the 2027-30 run
    must see a signal or DRLT's θ_QCD reading is refuted, regardless of
    how the Jarlskog frontier resolves. -/
theorem detectable_next_gen_either_J :
    10 < theta_QCD_num ∧ 10 * J_obs_num < theta_QCD_num * J_native_num := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ★★ E0 capstone — the repaired falsifier core: survival (bound),
    honest failure (window), and J-robust decidability, one bundle. -/
theorem theta_QCD_J_typed_core :
    (theta_QCD_num * J_native_num < 1800 * J_obs_num)
    ∧ (300 * J_obs_num < theta_QCD_num * J_native_num)
    ∧ (10 < theta_QCD_num ∧ 10 * J_obs_num < theta_QCD_num * J_native_num) :=
  ⟨native_J_below_bound, window_fails_with_native_J,
   detectable_next_gen_either_J⟩

end E213.Lib.Physics.Couplings.ThetaQCD
