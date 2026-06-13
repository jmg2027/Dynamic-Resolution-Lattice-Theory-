import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2TraceRecurrence
import E213.Meta.Int213.Order
import E213.Meta.Int213.OrderMul
import E213.Meta.Nat.PolyNatMTactic

/-!
# The finite-order spectrum of the modular family — uniform, all moduli at once

`CyclotomicTraceDegree.crystallographic_restriction` records the
crystallographic wall as a totient census over `range 13` (`decide`).  This
file proves the **uniform matrix statement** for every `M ∈ SL(2,ℤ)` and every
exponent: a finite-order integer rotation has order in `{1, 2, 3, 4, 6}` —
equivalently, **every period of the modular family divides 12**
(`finite_order_divides_twelve`).

The proof is the trace trichotomy, all rungs from `Mat2TraceRecurrence`'s one
engine `tr(Mⁿ⁺²) = tr·tr(Mⁿ⁺¹) − det·tr(Mⁿ)`:

  * `tr ≥ 3` — the trace strictly grows from the floor 2
    (`trace_mono_of_ge_three`, generalizing `GoldenAperiodic.golden_trace_mono`
    off `t = 3`): no return (`aperiodic_of_tr_ge_three`);
  * `tr ≤ −3` — the square `M²` has `tr(M²) = tr² − 2 ≥ 7`: no return either
    (`no_finite_order_of_tr_le_neg_three`);
  * `tr = ±2` — parabolic: the closed form `Mᵏ = I + k·(M − I)`
    (`parabolic_pow`) forces `M = I` (resp. `M² = I`) at any finite order;
  * `tr ∈ {0, ±1}` — elliptic, unconditional orders from Cayley–Hamilton:
    `M² = −I` (`tr 0`), `M³ = −I` (`tr 1`), `M³ = I` (`tr −1`).

Capstones: ★★★ `finite_order_spectrum` (`M^{n+1} = I` ⟹ `M = I ∨ M² = I ∨
M³ = I ∨ M⁴ = I ∨ M⁶ = I`) and ★★★ `finite_order_divides_twelve`
(`M^{n+1} = I ⟹ M¹² = I`).  The instances `S⁴ = I`, `U⁶ = I`
(`HyperbolicEllipticTrace`) realize orders 4 and 6; `golden_aperiodic` sits
just past the wall at `tr = 3`.  Six is the **last finite period** of the
integer rotation family — the ∀-form's finite side: every modulus the lattice
world can bring has period dividing 12, and the continuous rotation's period
is realized by none of them (the escape's effective quantification is the
measure hypothesis, `ExpLog/PiMeasureModulus.PiHalfMeasure`).

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ModularGeometry.FiniteOrderSpectrum

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace.Mat2 (mul tr det I negI S U)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2CayleyHamilton (charComb cayley_hamilton)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Assoc (mul_assoc)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2TraceRecurrence (pow trace_recurrence)
open E213.Meta.Int213.Order
open E213.Meta.Int213 (zero_add add_comm zero_mul mul_one mul_eq_zero mul_nonneg)
open E213.Meta.Int213.PolyIntM (one_mulZ mul_zeroZ)
open E213.Meta.Int213.OrderMul (mul_le_mul_right_nonneg mul_le_mul_left_nonneg)

private theorem add_zero' (a : Int) : a + 0 = a := by
  rw [add_comm]; exact zero_add a

/-! ## §1 — power algebra -/

theorem I_mul (A : Mat2) : mul I A = A := by
  rcases A with ⟨a, b, c, d⟩
  show Mat2.mk (1*a + 0*c) (1*b + 0*d) (0*a + 1*c) (0*b + 1*d) = Mat2.mk a b c d
  have e1 : (1:Int)*a + 0*c = a := by rw [one_mulZ, zero_mul]; exact add_zero' a
  have e2 : (1:Int)*b + 0*d = b := by rw [one_mulZ, zero_mul]; exact add_zero' b
  have e3 : (0:Int)*a + 1*c = c := by rw [zero_mul, one_mulZ]; exact zero_add c
  have e4 : (0:Int)*b + 1*d = d := by rw [zero_mul, one_mulZ]; exact zero_add d
  rw [e1, e2, e3, e4]

theorem mul_I (A : Mat2) : mul A I = A := by
  rcases A with ⟨a, b, c, d⟩
  show Mat2.mk (a*1 + b*0) (a*0 + b*1) (c*1 + d*0) (c*0 + d*1) = Mat2.mk a b c d
  have e1 : a*1 + b*0 = a := by rw [mul_one, mul_zeroZ]; exact add_zero' a
  have e2 : a*0 + b*1 = b := by rw [mul_zeroZ, mul_one]; exact zero_add b
  have e3 : c*1 + d*0 = c := by rw [mul_one, mul_zeroZ]; exact add_zero' c
  have e4 : c*0 + d*1 = d := by rw [mul_zeroZ, mul_one]; exact zero_add d
  rw [e1, e2, e3, e4]

theorem pow_one (M : Mat2) : pow M 1 = M := I_mul M

theorem pow_add (M : Mat2) (a : Nat) : ∀ b, pow M (a + b) = mul (pow M a) (pow M b)
  | 0 => (mul_I (pow M a)).symm
  | b+1 => by
      show mul (pow M (a + b)) M = mul (pow M a) (mul (pow M b) M)
      rw [pow_add M a b, mul_assoc]

theorem pow_pow (M : Mat2) (a : Nat) : ∀ b, pow (pow M a) b = pow M (a * b)
  | 0 => by rw [Nat.mul_zero]; rfl
  | b+1 => by
      show mul (pow (pow M a) b) (pow M a) = pow M (a * (b+1))
      rw [pow_pow M a b, ← pow_add M (a*b) a, Nat.mul_succ]

theorem pow_I : ∀ n, pow I n = I
  | 0 => rfl
  | n+1 => by show mul (pow I n) I = I; rw [pow_I n, mul_I]

theorem det_mul (A B : Mat2) : det (mul A B) = det A * det B := by
  rcases A with ⟨a, b, c, d⟩
  rcases B with ⟨e, f, g, h⟩
  show (a*e + b*g) * (c*f + d*h) - (a*f + b*h) * (c*e + d*g)
      = (a*d - b*c) * (e*h - f*g)
  ring_intZ

/-- `tr(M²) = tr² − 2·det` (the `n = 0` shadow of the trace recurrence,
    component-direct). -/
theorem tr_sq (M : Mat2) : tr (mul M M) = tr M * tr M - 2 * det M := by
  rcases M with ⟨a, b, c, d⟩
  show (a*a + b*c) + (c*b + d*d) = (a + d) * (a + d) - 2 * (a*d - b*c)
  ring_intZ

theorem tr_I : tr (I : Mat2) = 2 := by decide

theorem negI_mul_negI : mul negI negI = I := by decide

/-! ## §2 — the hyperbolic wall (`|tr| ≥ 3` has no return) -/

/-- ★★ **Trace growth above the wall**: `det = 1`, `tr ≥ 3` ⟹ the iterate's
    trace strictly climbs from the floor 2 (generalizes
    `GoldenAperiodic.golden_trace_mono` from `t = 3` to all `t ≥ 3`). -/
theorem trace_mono_of_ge_three (M : Mat2) (hdet : det M = 1) (htr : 3 ≤ tr M) :
    ∀ n, (2 : Int) ≤ tr (pow M n) ∧ tr (pow M n) < tr (pow M (n + 1)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [show tr (pow M 0) = 2 from tr_I]; exact le_refl 2
    · rw [show tr (pow M 0) = 2 from tr_I, show pow M 1 = M from pow_one M]
      exact lt_of_lt_of_le (by decide : (2:Int) < 3) htr
  | succ n ih =>
    obtain ⟨hle, hlt⟩ := ih
    have hle' : (2 : Int) ≤ tr (pow M (n + 1)) := le_of_lt (lt_of_le_of_lt hle hlt)
    refine ⟨hle', ?_⟩
    have p1 : (0 : Int) < tr (pow M (n + 1)) - tr (pow M n) := sub_pos_of_lt hlt
    have p2 : (0 : Int) < tr (pow M (n + 1)) := lt_of_lt_of_le (by decide) hle'
    have key : tr (pow M (n + 2)) - tr (pow M (n + 1))
        = ((tr (pow M (n + 1)) - tr (pow M n)) + tr (pow M (n + 1)))
          + (tr M - 3) * tr (pow M (n + 1)) := by
      rw [trace_recurrence M n, hdet]; ring_intZ
    have hXY := add_lt_add_right p1 (tr (pow M (n + 1)))
    rw [zero_add] at hXY
    have hpos1 : (0 : Int)
        < (tr (pow M (n + 1)) - tr (pow M n)) + tr (pow M (n + 1)) :=
      lt_trans p2 hXY
    have hY : (0 : Int) ≤ (tr M - 3) * tr (pow M (n + 1)) :=
      mul_nonneg (le_zero_of_nonneg (sub_nonneg_of_le htr)) (le_of_lt p2)
    have hsum : ((tr (pow M (n + 1)) - tr (pow M n)) + tr (pow M (n + 1))) + 0
        ≤ ((tr (pow M (n + 1)) - tr (pow M n)) + tr (pow M (n + 1)))
          + (tr M - 3) * tr (pow M (n + 1)) :=
      add_le_add_left hY _
    rw [add_zero' ((tr (pow M (n + 1)) - tr (pow M n)) + tr (pow M (n + 1)))] at hsum
    have hpos : (0 : Int) < ((tr (pow M (n + 1)) - tr (pow M n)) + tr (pow M (n + 1)))
        + (tr M - 3) * tr (pow M (n + 1)) := lt_of_lt_of_le hpos1 hsum
    rw [← key] at hpos
    exact lt_of_sub_pos hpos

/-- ★★ No return above the wall: `det = 1`, `tr ≥ 3` ⟹ `Mⁿ⁺¹ ≠ I`. -/
theorem aperiodic_of_tr_ge_three (M : Mat2) (hdet : det M = 1) (htr : 3 ≤ tr M)
    (n : Nat) : pow M (n + 1) ≠ I := by
  intro hEq
  have h2 : (2 : Int) < tr (pow M (n + 1)) :=
    lt_of_le_of_lt (trace_mono_of_ge_three M hdet htr n).1
      (trace_mono_of_ge_three M hdet htr n).2
  rw [hEq, tr_I] at h2
  exact lt_irrefl 2 h2

/-- Below the wall the square climbs: `tr ≤ −3` ⟹ `3 ≤ tr(M²)`
    (`tr(M²) = tr² − 2 ≥ 7`). -/
theorem tr_sq_ge_three_of_le_neg_three (M : Mat2) (hdet : det M = 1)
    (htr : tr M ≤ -3) : 3 ≤ tr (mul M M) := by
  have hneg : (3 : Int) ≤ -(tr M) := le_of_neg_le_neg (by
    rw [show -(-(tr M)) = tr M from by ring_intZ]; exact htr)
  have h0 : (0 : Int) ≤ -(tr M) := le_trans (by decide) hneg
  have h1 : (3 : Int) * 3 ≤ 3 * (-(tr M)) := mul_le_mul_left_nonneg hneg 3 (by decide)
  have h2 : (3 : Int) * (-(tr M)) ≤ (-(tr M)) * (-(tr M)) :=
    mul_le_mul_right_nonneg hneg (-(tr M)) h0
  have h9 : (9 : Int) ≤ tr M * tr M := by
    have := le_trans h1 h2
    rw [show ((3:Int) * 3) = 9 from by decide,
        show (-(tr M)) * (-(tr M)) = tr M * tr M from by ring_intZ] at this
    exact this
  have h7 : (9 : Int) + (-2) ≤ tr M * tr M + (-2) := add_le_add_right h9 (-2)
  rw [tr_sq M, hdet]
  rw [show ((9:Int) + (-2)) = 7 from by decide] at h7
  have : (7 : Int) ≤ tr M * tr M - 2 := h7
  exact le_trans (by decide : (3:Int) ≤ 7)
    (by rw [show tr M * tr M - 2 * 1 = tr M * tr M - 2 from by ring_intZ]; exact this)

/-- ★★ No return below the wall either: `det = 1`, `tr ≤ −3` ⟹ `Mⁿ⁺¹ ≠ I`
    (the square has `tr ≥ 7` and inherits the finite order). -/
theorem no_finite_order_of_tr_le_neg_three (M : Mat2) (hdet : det M = 1)
    (htr : tr M ≤ -3) (n : Nat) : pow M (n + 1) ≠ I := by
  intro hEq
  have hdet2 : det (mul M M) = 1 := by
    rw [det_mul, hdet]; decide
  have htr2 : 3 ≤ tr (mul M M) := tr_sq_ge_three_of_le_neg_three M hdet htr
  have hsq : pow M 2 = mul M M := by
    show mul (mul I M) M = mul M M
    rw [I_mul]
  have h2n : pow (mul M M) (n + 1) = I := by
    rw [← hsq, pow_pow M 2 (n+1)]
    have e : 2 * (n + 1) = (n + 1) + (n + 1) := by ring_nat
    rw [e, pow_add M (n+1) (n+1), hEq, mul_I]
  exact aperiodic_of_tr_ge_three (mul M M) hdet2 htr2 n h2n

/-! ## §3 — the elliptic orders (unconditional, from Cayley–Hamilton) -/

/-- `tr = 0` ⟹ `M² = −I` (Cayley–Hamilton with the trace gone). -/
theorem sq_eq_negI_of_tr_zero (M : Mat2) (hdet : det M = 1) (htr : tr M = 0) :
    mul M M = negI := by
  rw [cayley_hamilton]
  show Mat2.mk (tr M * M.a - det M) (tr M * M.b) (tr M * M.c) (tr M * M.d - det M)
      = negI
  rw [htr, hdet]
  show Mat2.mk ((0:Int) * M.a - 1) (0 * M.b) (0 * M.c) (0 * M.d - 1)
      = Mat2.mk (-1) 0 0 (-1)
  have e1 : (0:Int) * M.a - 1 = -1 := by rw [zero_mul]; decide
  have e2 : (0:Int) * M.b = 0 := zero_mul M.b
  have e3 : (0:Int) * M.c = 0 := zero_mul M.c
  have e4 : (0:Int) * M.d - 1 = -1 := by rw [zero_mul]; decide
  rw [e1, e2, e3, e4]

/-- ★ `tr = 0` ⟹ `M⁴ = I` (the Gaussian axis, `S`-type). -/
theorem order_four_of_tr_zero (M : Mat2) (hdet : det M = 1) (htr : tr M = 0) :
    pow M 4 = I := by
  have h2 : pow M 2 = mul M M := by
    show mul (mul I M) M = mul M M; rw [I_mul]
  have e : pow M 4 = mul (pow M 2) (pow M 2) := pow_add M 2 2
  rw [e, h2, sq_eq_negI_of_tr_zero M hdet htr, negI_mul_negI]

private theorem cube_entries (M : Mat2) (hdet : det M = 1) :
    ∀ t₀ : Int, tr M = t₀ →
    pow M 3 = Mat2.mk
      ((t₀*t₀ - 1) * M.a - t₀)
      ((t₀*t₀ - 1) * M.b)
      ((t₀*t₀ - 1) * M.c)
      ((t₀*t₀ - 1) * M.d - t₀) := by
  intro t₀ htr
  have h2 : pow M 2 = mul M M := by
    show mul (mul I M) M = mul M M; rw [I_mul]
  have h3 : pow M 3 = mul (mul M M) M := by
    show mul (pow M 2) M = mul (mul M M) M
    rw [h2]
  rw [h3, cayley_hamilton]
  rcases M with ⟨a, b, c, d⟩
  have htr' : a + d = t₀ := htr
  have hdet' : a*d - b*c = 1 := hdet
  show Mat2.mk
      (((a+d)*a - (a*d - b*c))*a + ((a+d)*b)*c)
      (((a+d)*a - (a*d - b*c))*b + ((a+d)*b)*d)
      (((a+d)*c)*a + ((a+d)*d - (a*d - b*c))*c)
      (((a+d)*c)*b + ((a+d)*d - (a*d - b*c))*d)
      = Mat2.mk ((t₀*t₀ - 1) * a - t₀) ((t₀*t₀ - 1) * b) ((t₀*t₀ - 1) * c)
          ((t₀*t₀ - 1) * d - t₀)
  have e1 : ((a+d)*a - (a*d - b*c))*a + ((a+d)*b)*c
      = (a+d)*(a+d)*a - (a*d - b*c)*a - (a+d)*(a*d - b*c) := by ring_intZ
  have e2 : ((a+d)*a - (a*d - b*c))*b + ((a+d)*b)*d
      = ((a+d)*(a+d) - (a*d - b*c)) * b := by ring_intZ
  have e3 : ((a+d)*c)*a + ((a+d)*d - (a*d - b*c))*c
      = ((a+d)*(a+d) - (a*d - b*c)) * c := by ring_intZ
  have e4 : ((a+d)*c)*b + ((a+d)*d - (a*d - b*c))*d
      = (a+d)*(a+d)*d - (a*d - b*c)*d - (a+d)*(a*d - b*c) := by ring_intZ
  rw [e1, e2, e3, e4, htr', hdet']
  have f1 : t₀*t₀*a - 1*a - t₀*1 = (t₀*t₀ - 1)*a - t₀ := by
    rw [one_mulZ, mul_one]; ring_intZ
  have f2 : t₀*t₀*d - 1*d - t₀*1 = (t₀*t₀ - 1)*d - t₀ := by
    rw [one_mulZ, mul_one]; ring_intZ
  rw [f1, f2]

/-- `tr = 1` ⟹ `M³ = −I`. -/
theorem cube_eq_negI_of_tr_one (M : Mat2) (hdet : det M = 1) (htr : tr M = 1) :
    pow M 3 = negI := by
  rw [cube_entries M hdet 1 htr]
  show Mat2.mk (((1:Int)*1 - 1) * M.a - 1) ((1*1 - 1) * M.b) ((1*1 - 1) * M.c)
      ((1*1 - 1) * M.d - 1) = Mat2.mk (-1) 0 0 (-1)
  have hc : ((1:Int)*1 - 1) = 0 := by decide
  have e1 : ((1:Int)*1 - 1) * M.a - 1 = -1 := by rw [hc, zero_mul]; decide
  have e2 : ((1:Int)*1 - 1) * M.b = 0 := by rw [hc, zero_mul]
  have e3 : ((1:Int)*1 - 1) * M.c = 0 := by rw [hc, zero_mul]
  have e4 : ((1:Int)*1 - 1) * M.d - 1 = -1 := by rw [hc, zero_mul]; decide
  rw [e1, e2, e3, e4]

/-- ★ `tr = 1` ⟹ `M⁶ = I` (the Eisenstein axis, `U`-type — the LAST finite
    period of the family). -/
theorem order_six_of_tr_one (M : Mat2) (hdet : det M = 1) (htr : tr M = 1) :
    pow M 6 = I := by
  have e : pow M 6 = mul (pow M 3) (pow M 3) := pow_add M 3 3
  rw [e, cube_eq_negI_of_tr_one M hdet htr, negI_mul_negI]

/-- ★ `tr = −1` ⟹ `M³ = I`. -/
theorem order_three_of_tr_neg_one (M : Mat2) (hdet : det M = 1)
    (htr : tr M = -1) : pow M 3 = I := by
  rw [cube_entries M hdet (-1) htr]
  show Mat2.mk (((-1:Int)*(-1) - 1) * M.a - (-1)) (((-1:Int)*(-1) - 1) * M.b)
      (((-1:Int)*(-1) - 1) * M.c) (((-1:Int)*(-1) - 1) * M.d - (-1))
      = Mat2.mk 1 0 0 1
  have hc : ((-1:Int)*(-1) - 1) = 0 := by decide
  have e1 : ((-1:Int)*(-1) - 1) * M.a - (-1) = 1 := by rw [hc, zero_mul]; decide
  have e2 : ((-1:Int)*(-1) - 1) * M.b = 0 := by rw [hc, zero_mul]
  have e3 : ((-1:Int)*(-1) - 1) * M.c = 0 := by rw [hc, zero_mul]
  have e4 : ((-1:Int)*(-1) - 1) * M.d - (-1) = 1 := by rw [hc, zero_mul]; decide
  rw [e1, e2, e3, e4]

/-! ## §4 — the parabolic edge (`tr = ±2`) -/

/-- **Parabolic closed form**: `tr = 2`, `det = 1` ⟹
    `Mᵏ = I + k·(M − I)`, componentwise over ℤ. -/
theorem parabolic_pow (M : Mat2) (hdet : det M = 1) (htr : tr M = 2) :
    ∀ k : Nat, pow M k = Mat2.mk
      (1 + (Int.ofNat k) * (M.a - 1)) ((Int.ofNat k) * M.b)
      ((Int.ofNat k) * M.c) (1 + (Int.ofNat k) * (M.d - 1))
  | 0 => by
      show I = Mat2.mk (1 + (0:Int) * (M.a - 1)) ((0:Int) * M.b) ((0:Int) * M.c)
          (1 + (0:Int) * (M.d - 1))
      have e1 : (1:Int) + 0 * (M.a - 1) = 1 := by rw [zero_mul]; decide
      have e2 : (0:Int) * M.b = 0 := zero_mul M.b
      have e3 : (0:Int) * M.c = 0 := zero_mul M.c
      have e4 : (1:Int) + 0 * (M.d - 1) = 1 := by rw [zero_mul]; decide
      rw [e1, e2, e3, e4]
      rfl
  | k+1 => by
      show mul (pow M k) M = _
      rw [parabolic_pow M hdet htr k]
      rcases M with ⟨a, b, c, d⟩
      have htr' : a + d = 2 := htr
      have hdet' : a*d - b*c = 1 := hdet
      have hK : (Int.ofNat (k+1)) = Int.ofNat k + 1 := rfl
      show Mat2.mk
          ((1 + (Int.ofNat k) * (a - 1))*a + ((Int.ofNat k) * b)*c)
          ((1 + (Int.ofNat k) * (a - 1))*b + ((Int.ofNat k) * b)*d)
          (((Int.ofNat k) * c)*a + (1 + (Int.ofNat k) * (d - 1))*c)
          (((Int.ofNat k) * c)*b + (1 + (Int.ofNat k) * (d - 1))*d)
          = Mat2.mk (1 + (Int.ofNat (k+1)) * (a - 1)) ((Int.ofNat (k+1)) * b)
              ((Int.ofNat (k+1)) * c) (1 + (Int.ofNat (k+1)) * (d - 1))
      rw [hK]
      have e1 : (1 + (Int.ofNat k) * (a - 1))*a + ((Int.ofNat k) * b)*c
          = a + (Int.ofNat k) * (a * (a + d) - a - (a*d - b*c)) := by ring_intZ
      have e2 : (1 + (Int.ofNat k) * (a - 1))*b + ((Int.ofNat k) * b)*d
          = b + (Int.ofNat k) * b * ((a + d) - 1) := by ring_intZ
      have e3 : ((Int.ofNat k) * c)*a + (1 + (Int.ofNat k) * (d - 1))*c
          = c + (Int.ofNat k) * c * ((a + d) - 1) := by ring_intZ
      have e4 : ((Int.ofNat k) * c)*b + (1 + (Int.ofNat k) * (d - 1))*d
          = d + (Int.ofNat k) * (d * (a + d) - d - (a*d - b*c)) := by ring_intZ
      rw [e1, e2, e3, e4, htr', hdet']
      have f1 : a + (Int.ofNat k) * (a * 2 - a - 1)
          = 1 + ((Int.ofNat k) + 1) * (a - 1) := by ring_intZ
      have f2 : b + (Int.ofNat k) * b * (2 - 1) = ((Int.ofNat k) + 1) * b := by ring_intZ
      have f3 : c + (Int.ofNat k) * c * (2 - 1) = ((Int.ofNat k) + 1) * c := by ring_intZ
      have f4 : d + (Int.ofNat k) * (d * 2 - d - 1)
          = 1 + ((Int.ofNat k) + 1) * (d - 1) := by ring_intZ
      rw [f1, f2, f3, f4]

private theorem ofNat_succ_ne_zero (n : Nat) : (Int.ofNat (n+1)) ≠ 0 := by
  intro h
  exact Nat.noConfusion (Int.ofNat.inj h)

private theorem factor_zero {n : Nat} {x : Int}
    (h : (Int.ofNat (n+1)) * x = 0) : x = 0 := by
  rcases mul_eq_zero h with hK | hx
  · exact absurd hK (ofNat_succ_ne_zero n)
  · exact hx

/-- ★ **Parabolic rigidity**: `tr = 2`, `det = 1`, any finite order ⟹ `M = I`
    (the shear `I + k(M−I)` returns only if it never left). -/
theorem parabolic_eq_I (M : Mat2) (hdet : det M = 1) (htr : tr M = 2)
    (n : Nat) (h : pow M (n+1) = I) : M = I := by
  rw [parabolic_pow M hdet htr (n+1)] at h
  have ha : 1 + (Int.ofNat (n+1)) * (M.a - 1) = 1 := congrArg Mat2.a h
  have hb : (Int.ofNat (n+1)) * M.b = 0 := congrArg Mat2.b h
  have hc : (Int.ofNat (n+1)) * M.c = 0 := congrArg Mat2.c h
  have hb0 : M.b = 0 := factor_zero hb
  have hc0 : M.c = 0 := factor_zero hc
  have haz : (Int.ofNat (n+1)) * (M.a - 1) = 0 := by
    have e : (Int.ofNat (n+1)) * (M.a - 1)
        = (1 + (Int.ofNat (n+1)) * (M.a - 1)) - 1 := by ring_intZ
    rw [e, ha]
    decide
  have ha1 : M.a = 1 := by
    have := factor_zero haz
    have e : M.a = (M.a - 1) + 1 := by ring_intZ
    rw [e, this]; decide
  have hd1 : M.d = 1 := by
    have htr' : M.a + M.d = 2 := htr
    have e : M.d = (M.a + M.d) - M.a := by ring_intZ
    rw [e, htr', ha1]; decide
  rcases M with ⟨a, b, c, d⟩
  show Mat2.mk a b c d = Mat2.mk 1 0 0 1
  rw [show a = (1:Int) from ha1, show b = (0:Int) from hb0,
      show c = (0:Int) from hc0, show d = (1:Int) from hd1]

/-- ★ `tr = −2`, `det = 1`, any finite order ⟹ `M² = I` (the square is
    parabolic with `tr(M²) = 2` and inherits the order). -/
theorem sq_eq_I_of_tr_neg_two (M : Mat2) (hdet : det M = 1) (htr : tr M = -2)
    (n : Nat) (h : pow M (n+1) = I) : mul M M = I := by
  have hdet2 : det (mul M M) = 1 := by rw [det_mul, hdet]; decide
  have htr2 : tr (mul M M) = 2 := by
    rw [tr_sq M, htr, hdet]; decide
  have hsq : pow M 2 = mul M M := by
    show mul (mul I M) M = mul M M; rw [I_mul]
  have h2n : pow (mul M M) (n+1) = I := by
    rw [← hsq, pow_pow M 2 (n+1)]
    have e : 2 * (n + 1) = (n + 1) + (n + 1) := by ring_nat
    rw [e, pow_add M (n+1) (n+1), h, mul_I]
  exact parabolic_eq_I (mul M M) hdet2 htr2 n h2n

/-! ## §5 — capstones -/

private theorem le_two_of_lt_two_int {t : Int} (h : t - 2 < 0) : t ≤ 2 := by
  have h1 : (t - 2) + 1 ≤ 0 := h
  have h2 : ((t - 2) + 1) + 1 ≤ 0 + 1 := add_le_add_right h1 1
  have e1 : ((t - 2) + 1) + 1 = t := by ring_intZ
  have e2 : (0 : Int) + 1 = 1 := by ring_intZ
  rw [e1, e2] at h2
  exact le_trans h2 (by decide)

/-- ★★★ **The finite-order spectrum of `SL(2,ℤ)`, uniform.**  Any integer
    matrix of determinant 1 with ANY finite order satisfies one of
    `M = I`, `M² = I`, `M³ = I`, `M⁴ = I`, `M⁶ = I` — the crystallographic
    restriction as a single structural theorem (every `n`, every `M`),
    upgrading the range-13 totient census
    (`CyclotomicTraceDegree.crystallographic_restriction`).  The trace
    trichotomy: `|tr| ≥ 3` never returns; `tr = ±2` is parabolic rigidity;
    `tr ∈ {0, ±1}` are the Gaussian/Eisenstein elliptic orders. -/
theorem finite_order_spectrum (M : Mat2) (hdet : det M = 1) (n : Nat)
    (h : pow M (n+1) = I) :
    M = I ∨ mul M M = I ∨ pow M 3 = I ∨ pow M 4 = I ∨ pow M 6 = I := by
  rcases pos_zero_or_neg (tr M - 2) with hpos | hz | hneg
  · -- tr ≥ 3: impossible
    have h3 : (3 : Int) ≤ tr M := by
      have h1 : (0 : Int) + 1 ≤ tr M - 2 := hpos
      have h2 := add_le_add_right h1 2
      have e1 : ((0:Int) + 1) + 2 = 3 := by decide
      have e2 : (tr M - 2) + 2 = tr M := by ring_intZ
      rw [e1, e2] at h2
      exact h2
    exact absurd h (aperiodic_of_tr_ge_three M hdet h3 n)
  · -- tr = 2: parabolic
    exact Or.inl (parabolic_eq_I M hdet (eq_of_sub_eq_zero hz) n h)
  · rcases pos_zero_or_neg (tr M + 2) with hpos2 | hz2 | hneg2
    · -- −1 ≤ tr ≤ 1: the elliptic window
      rcases pos_zero_or_neg (tr M) with htp | htz | htn
      · -- 0 < tr ≤ 1 ⟹ tr = 1
        have h1le : (1 : Int) ≤ tr M := by
          have : (0 : Int) + 1 ≤ tr M := htp
          rw [show (0:Int) + 1 = 1 from by decide] at this
          exact this
        have hle1 : tr M ≤ 1 := by
          have h2le : tr M ≤ 2 := le_two_of_lt_two_int hneg
          -- tr ≤ 2 ∧ tr ≠ 2 (hneg strict) ⟹ tr ≤ 1
          have h1 : tr M + 1 ≤ 2 := by
            have := hneg  -- (tr M − 2) < 0 i.e. (tr M − 2) + 1 ≤ 0
            have h' : (tr M - 2) + 1 ≤ 0 := this
            have h'' := add_le_add_right h' 2
            have e1 : ((tr M - 2) + 1) + 2 = tr M + 1 := by ring_intZ
            have e2 : (0 : Int) + 2 = 2 := by decide
            rw [e1, e2] at h''
            exact h''
          have h2 := add_le_add_right h1 (-1)
          have e1 : (tr M + 1) + (-1) = tr M := by ring_intZ
          have e2 : (2 : Int) + (-1) = 1 := by decide
          rw [e1, e2] at h2
          exact h2
        have ht1 : tr M = 1 := le_antisymm hle1 h1le
        exact Or.inr (Or.inr (Or.inr (Or.inr (order_six_of_tr_one M hdet ht1))))
      · -- tr = 0
        exact Or.inr (Or.inr (Or.inr (Or.inl (order_four_of_tr_zero M hdet htz))))
      · -- −1 ≤ tr < 0 ⟹ tr = −1
        have hlem1 : tr M ≤ -1 := by
          have h' : tr M + 1 ≤ 0 := htn
          have h2 := add_le_add_right h' (-1)
          have e1 : (tr M + 1) + (-1) = tr M := by ring_intZ
          have e2 : (0 : Int) + (-1) = -1 := by decide
          rw [e1, e2] at h2
          exact h2
        have hgem1 : (-1 : Int) ≤ tr M := by
          have h' : (0 : Int) + 1 ≤ tr M + 2 := hpos2
          have h2 := add_le_add_right h' (-2)
          have e1 : ((0:Int) + 1) + (-2) = -1 := by decide
          have e2 : (tr M + 2) + (-2) = tr M := by ring_intZ
          rw [e1, e2] at h2
          exact h2
        have htm1 : tr M = -1 := le_antisymm hlem1 hgem1
        exact Or.inr (Or.inr (Or.inl (order_three_of_tr_neg_one M hdet htm1)))
    · -- tr = −2
      have htm2 : tr M = -2 := by
        have := eq_of_sub_eq_zero (a := tr M) (b := -2) (by
          rw [show tr M - (-2) = tr M + 2 from by ring_intZ]; exact hz2)
        exact this
      exact Or.inr (Or.inl (sq_eq_I_of_tr_neg_two M hdet htm2 n h))
    · -- tr ≤ −3: impossible
      have h3 : tr M ≤ -3 := by
        have h' : (tr M + 2) + 1 ≤ 0 := hneg2
        have h2 := add_le_add_right h' (-3)
        have e1 : ((tr M + 2) + 1) + (-3) = tr M := by ring_intZ
        have e2 : (0 : Int) + (-3) = -3 := by decide
        rw [e1, e2] at h2
        exact h2
      exact absurd h (no_finite_order_of_tr_le_neg_three M hdet h3 n)

/-- ★★★ **Every period of the modular family divides 12.**  `det M = 1`,
    `Mⁿ⁺¹ = I` ⟹ `M¹² = I` — six is the last finite period; the integer
    rotation family closes at `lcm{1,2,3,4,6} = 12`, and the continuous
    rotation's full period is realized by none of its members (`S⁴ = I`,
    `U⁶ = I` realize the top orders; `golden_aperiodic` sits just past the
    trace wall). -/
theorem finite_order_divides_twelve (M : Mat2) (hdet : det M = 1) (n : Nat)
    (h : pow M (n+1) = I) : pow M 12 = I := by
  rcases finite_order_spectrum M hdet n h with h1 | h2 | h3 | h4 | h6
  · rw [h1]; exact pow_I 12
  · have hsq : pow M 2 = mul M M := by
      show mul (mul I M) M = mul M M; rw [I_mul]
    have e : pow M 12 = pow (pow M 2) 6 := by
      rw [pow_pow M 2 6]
    rw [e, hsq, h2]; exact pow_I 6
  · have e : pow M 12 = pow (pow M 3) 4 := by rw [pow_pow M 3 4]
    rw [e, h3]; exact pow_I 4
  · have e : pow M 12 = pow (pow M 4) 3 := by rw [pow_pow M 4 3]
    rw [e, h4]; exact pow_I 3
  · have e : pow M 12 = pow (pow M 6) 2 := by rw [pow_pow M 6 2]
    rw [e, h6]; exact pow_I 2

/-! ## §6 — the forbidden five-fold axis + the realized orders -/

/-- ★★★ **No five-fold symmetry.**  `det M = 1`, `M⁵ = I` ⟹ `M = I` — the
    crystallographic restriction's crown jewel: a 2D integer lattice admits no
    rotation of order 5 (the pentagon / quasicrystal-forbidden axis,
    `PentagonGoldenTrace`).  By `finite_order_spectrum` the order lands in
    `{1,2,3,4,6}`, each coprime to 5, so `M⁵ = I` collapses it to the
    identity. -/
theorem no_order_five (M : Mat2) (hdet : det M = 1) (h : pow M 5 = I) : M = I := by
  have e51 : pow M 5 = mul (pow M 4) M := rfl
  have e52 : pow M 5 = mul (pow M 3) (pow M 2) := pow_add M 3 2
  rcases finite_order_spectrum M hdet 4 h with h1 | h2 | h3 | h4 | h6
  · exact h1
  · -- M² = I ⟹ M⁴ = I ⟹ M⁵ = M⁴·M = M ⟹ M = I
    have hp2 : pow M 2 = I := by
      show mul (mul I M) M = I; rw [I_mul]; exact h2
    have hp4 : pow M 4 = I := by rw [pow_add M 2 2, hp2, I_mul]
    have key : mul (pow M 4) M = I := e51 ▸ h
    rw [hp4, I_mul] at key; exact key
  · -- M³ = I ⟹ M² = M⁵ = I, then M = M²·M·(M²)⁻¹ collapses: M³ = M²·M ⟹ M = I
    have hp2 : pow M 2 = I := by rw [e52, h3, I_mul] at h; exact h
    have key : mul (pow M 2) M = I := h3
    rw [hp2, I_mul] at key; exact key
  · -- M⁴ = I ⟹ M⁵ = M⁴·M = M ⟹ M = I
    rw [e51, h4, I_mul] at h; exact h
  · -- M⁶ = I, M⁵ = I ⟹ M⁶ = M⁵·M = M ⟹ M = I
    have e6 : pow M 6 = mul (pow M 5) M := rfl
    rw [h, I_mul] at e6
    rw [e6] at h6; exact h6

/-- ★★★ **No seven-fold symmetry** either (`det M = 1`, `M⁷ = I` ⟹ `M = I`):
    7 is coprime to every realized order `{2,3,4,6}`, so the same collapse runs.
    Together with `no_order_five`, the only *prime* orders in `SL(2,ℤ)` are 2
    and 3 (`PSL(2,ℤ) = ℤ₂ ∗ ℤ₃`). -/
theorem no_order_seven (M : Mat2) (hdet : det M = 1) (h : pow M 7 = I) : M = I := by
  have e7 : pow M 7 = mul (pow M 6) M := rfl
  have e73 : pow M 7 = mul (pow M 4) (pow M 3) := pow_add M 4 3
  have e74 : pow M 7 = mul (pow M 3) (pow M 4) := pow_add M 3 4
  have e76 : pow M 7 = mul (pow M 6) (pow M 1) := pow_add M 6 1
  rcases finite_order_spectrum M hdet 6 h with h1 | h2 | h3 | h4 | h6
  · exact h1
  · -- M² = I ⟹ M⁶ = I ⟹ M⁷ = M⁶·M = M
    have hp2 : pow M 2 = I := by
      show mul (mul I M) M = I; rw [I_mul]; exact h2
    have hp6 : pow M 6 = I := by
      rw [show (6:Nat) = 2 + 2 + 2 from rfl, pow_add M (2+2) 2, pow_add M 2 2,
          hp2, I_mul, I_mul]
    rw [e7, hp6, I_mul] at h; exact h
  · -- M³ = I ⟹ M⁶ = I ⟹ M⁷ = M
    have hp6 : pow M 6 = I := by
      rw [show (6:Nat) = 3 + 3 from rfl, pow_add M 3 3, h3, I_mul]
    rw [e7, hp6, I_mul] at h; exact h
  · -- M⁴ = I ⟹ M⁷ = M⁴·M³ = M³, and M⁸ = (M⁴)² = I ⟹ M³·M⁴ ... use M⁴=I twice:
    -- M⁷ = M⁴·M³ = M³ = I, and M⁴ = M³·M = M ⟹ M = I
    have hp3 : pow M 3 = I := by rw [e73, h4, I_mul] at h; exact h
    have key : mul (pow M 3) M = I := h4
    rw [hp3, I_mul] at key; exact key
  · -- M⁶ = I ⟹ M⁷ = M⁶·M = M
    rw [e76, h6, I_mul, pow_one] at h; exact h

/-- ★ **Order 4 is realized exactly** by the Gaussian generator `S`: `S⁴ = I`
    while `S, S², S³ ≠ I`. -/
theorem exact_order_four :
    pow S 4 = I ∧ pow S 1 ≠ I ∧ pow S 2 ≠ I ∧ pow S 3 ≠ I := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- ★ **Order 6 is realized exactly** by the Eisenstein generator `U`: `U⁶ = I`
    while `U, …, U⁵ ≠ I`. -/
theorem exact_order_six :
    pow U 6 = I ∧ pow U 1 ≠ I ∧ pow U 2 ≠ I ∧ pow U 3 ≠ I
    ∧ pow U 4 ≠ I ∧ pow U 5 ≠ I := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★ **The crystallographic spectrum, two-sided.**  Bundles:

    1. every finite order in `SL(2,ℤ)` lands in `{1,2,3,4,6}`
       (`finite_order_spectrum`);
    2. orders 4 and 6 are realized exactly (`S`, `U`);
    3. order 5 is **forbidden** (`no_order_five`) — the pentagon axis.

    The finite-order spectrum of the integer modular family is exactly
    `{1,2,3,4,6}`; five is the first forbidden order, the quasicrystal /
    golden axis the lattice cannot close.  (`golden_aperiodic` shows the
    hyperbolic `G` has no finite order at all — the continuous escape.) -/
theorem crystallographic_spectrum :
    (∀ (M : Mat2) (n : Nat), det M = 1 → pow M (n+1) = I →
        M = I ∨ mul M M = I ∨ pow M 3 = I ∨ pow M 4 = I ∨ pow M 6 = I)
    ∧ (pow S 4 = I ∧ pow S 2 ≠ I)
    ∧ (pow U 6 = I ∧ pow U 3 ≠ I ∧ pow U 2 ≠ I)
    ∧ (∀ (M : Mat2), det M = 1 → pow M 5 = I → M = I) :=
  ⟨fun M n hdet h => finite_order_spectrum M hdet n h,
   ⟨by decide, by decide⟩,
   ⟨by decide, by decide, by decide⟩,
   fun M hdet h => no_order_five M hdet h⟩

end E213.Lib.Math.NumberSystems.Real213.ModularGeometry.FiniteOrderSpectrum
