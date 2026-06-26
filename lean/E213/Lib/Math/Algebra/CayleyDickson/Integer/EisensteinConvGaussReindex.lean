import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvGaussFrobenius
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvCongruence
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussCube
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiagOne
import E213.Lib.Math.NumberTheory.EulerTheorem
import E213.Meta.Nat.MulMod213

/-!
# The `t ↦ tq%p` reindex — closing the Gauss-sum Frobenius congruence (∅-axiom)

★★★★★ `gauss_pow_modEq_closed` : the **closed Frobenius congruence** for the cubic Gauss sum —

  `g(χ)^{⋆q}(k) ≡ χ(q) · χ̄(k)   (mod ofInt q)`   for a prime `q ≡ 2 (mod 3)`, `q` a unit mod `p`, `k<p`.

The starting point `gauss_pow_modEq_conj` (`g(χ)^{⋆q} ≡ Σ_t χ̄(t)·e_{tq%p}`) is a sum weighted by the
**indicator** basis vectors `e_{(tq)%p}` — so at a fixed coefficient `k` only the unique `t` with
`(tq)%p = k` survives.  That `t` is `t₀ = (q⁻¹·k) mod p` (`q⁻¹ = aInv q p`, the Bezout inverse), pinned
by `aInv_spec` (existence) and `cancel_unit` (uniqueness/injectivity).  So the sum collapses to a single
character value `χ̄(t₀)` (`gauss_conj_reindex_collapse`), which the multiplicativity `chiOmega_mul` splits
as `χ̄((q⁻¹·k)%p) = χ̄(q⁻¹)·χ̄(k) = χ(q)·χ̄(k)`.

No permutation-sum machinery is needed: the indicator collapse replaces the classical "reindex the whole
sum" step with a single-term extraction.  ∅-axiom up to allowed `propext`.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvGaussReindex

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvBasis (basis)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow (convPow convPow_succ)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv conv_scalar_left conv_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvCongruence (conv_modEq_left)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm (conv_comm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussCube (gaussConj_eq_charConj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussOffDiagOne (gauss_conj_norm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinNormConv (Yfun)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss gaussConj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvGaussFrobenius (gauss_pow_modEq_conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange sum_single)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (one mul_one)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (conj_mul conj_conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega_mul_conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul (chiOmega_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiReindex (chiOmega_ne_zero)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel (one_mul_zomega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (chiOmega_zero_of_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm (conj_zero)
open E213.Lib.Math.NumberTheory.ModArith.CubicCharFp (cubicChar)
open E213.Lib.Math.NumberTheory.EulerTheorem (aInv aInv_spec cancel_unit)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure)
open E213.Meta.Algebra213.Ring213 (mul_zero mul_assoc)

/-- The reindex target `t₀ = (q⁻¹·k) mod p` lands the basis indicator on `k`: `(t₀·q) mod p = k`.
    `q⁻¹·k·q = k·(q·q⁻¹) ≡ k·1 = k (mod p)` (`aInv_spec` + the mul-mod laws).  ∅-axiom. -/
private theorem reindex_idx (p q : Nat) (hp : 1 < p) (hq : gcd213 q p = 1) {k : Nat} (hk : k < p) :
    ((aInv q p * k) % p * q) % p = k := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  rw [← mul_mod_left_pure (aInv q p * k) q p,
      show aInv q p * k * q = k * (q * aInv q p) from by
        rw [Nat.mul_comm (aInv q p) k, Nat.mul_assoc, Nat.mul_comm (aInv q p) q],
      mul_mod_right_pure k (q * aInv q p) p, aInv_spec hppos hq,
      Nat.mod_eq_of_lt hp, Nat.mul_one, Nat.mod_eq_of_lt hk]

/-- ★★★★ **The indicator reindex collapse** — for `q` a unit mod `p` (`gcd(q,p)=1`) and `k < p`,

      `Σ_{t<p} χ̄(t)·e_{(t·q)%p}(k) = χ̄((q⁻¹·k) mod p)`.

    The basis vector `e_{(tq)%p}` is the indicator `δ_{k,(tq)%p}`, so only the unique `t₀ = (q⁻¹·k)%p`
    with `(t₀·q)%p = k` (`reindex_idx`) contributes; injectivity of `t ↦ (tq)%p` (`cancel_unit`) kills the
    rest.  The `t ↦ tq%p` reindex of the Gauss-sum Frobenius, done by single-term extraction.
    ∅-axiom up to allowed `propext`. -/
theorem gauss_conj_reindex_collapse (p m x q : Nat) (hp : 1 < p) (hq : gcd213 q p = 1)
    {k : Nat} (hk : k < p) :
    sumRange (fun t => conj (chiOmega p m x t) * basis ((t * q) % p) k) p
      = conj (chiOmega p m x ((aInv q p * k) % p)) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  have ht0lt : (aInv q p * k) % p < p := Nat.mod_lt _ hppos
  have hidx : ((aInv q p * k) % p * q) % p = k := reindex_idx p q hp hq hk
  rw [sum_single p ((aInv q p * k) % p) ht0lt
      (fun t => conj (chiOmega p m x t) * basis ((t * q) % p) k)
      (fun t htlt htne => by
        show conj (chiOmega p m x t) * (if k = (t * q) % p then one else 0) = 0
        have hne : (t * q) % p ≠ k := by
          intro he
          apply htne
          have h2 : (q * t) % p = (q * ((aInv q p * k) % p)) % p := by
            rw [Nat.mul_comm q t, Nat.mul_comm q ((aInv q p * k) % p), he, hidx]
          have hcanc := cancel_unit hp hq h2 ht0lt
          rwa [Nat.mod_eq_of_lt htlt] at hcanc
        rw [if_neg (fun h => hne h.symm), mul_zero])]
  show conj (chiOmega p m x ((aInv q p * k) % p)) * (if k = ((aInv q p * k) % p * q) % p then one else 0)
      = conj (chiOmega p m x ((aInv q p * k) % p))
  rw [hidx, if_pos rfl, mul_one]

/-- ★★★★★ **The closed Gauss-sum Frobenius congruence (reindex form)** — for a prime `q ≡ 2 (mod 3)`
    that is a unit mod `p` and `k < p`,

      `g(χ)^{⋆q}(k) ≡ χ̄((q⁻¹·k) mod p)   (mod ofInt q)`.

    `gauss_pow_modEq_conj` reduces `g(χ)^{⋆q}(k)` to `Σ_t χ̄(t)·e_{tq%p}(k)`, and
    `gauss_conj_reindex_collapse` collapses that indicator-weighted sum to the single surviving term
    `χ̄((q⁻¹·k)%p)`.  This is the `t↦tq%p` reindex **done** — the Frobenius congruence in closed form,
    one multiplicative split (`chiOmega_mul`) away from `χ(q)·χ̄(k)`.  ∅-axiom up to allowed `propext`. -/
theorem gauss_pow_modEq_reindexed (p m x q : Nat) (hp : 1 < p) (hq3 : q % 3 = 2)
    (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) (hcop : gcd213 q p = 1) {k : Nat} (hk : k < p) :
    ModEq (ofInt ((q : Nat) : Int)) (convPow p (gauss p m x) q k)
      (conj (chiOmega p m x ((aInv q p * k) % p))) := by
  have h := gauss_pow_modEq_conj p m x q hq3 hqr hk
  rwa [gauss_conj_reindex_collapse p m x q hp hcop hk] at h

/-! ## The multiplicative split — `χ̄((q⁻¹·k)%p) = χ(q)·χ̄(k)` -/

/-- `χ_ω(1) = 1` for `1 < p` — the trivial value (`1 % p ≠ 0`, `cubicChar(1) = 1^m % p = 1`). -/
private theorem chiOmega_one (p m x : Nat) (hp : 1 < p) :
    chiOmega p m x 1 = ofInt 1 := by
  have h0 : ¬ ((1 : Nat) % p = 0) := by rw [Nat.mod_eq_of_lt hp]; decide
  have hc : cubicChar p m 1 = 1 := by show 1 ^ m % p = 1; rw [Nat.one_pow, Nat.mod_eq_of_lt hp]
  unfold chiOmega
  rw [if_neg h0, if_pos hc]

/-- ★★★★ **The reindex multiplicative split** — for units `q, k` (`0 < q, k < p`, `p > 3`),

      `χ̄((q⁻¹·k) mod p) = χ(q) · χ̄(k)`.

    `χ((q⁻¹·k)%p) = χ(q⁻¹)·χ(k)` (`chiOmega_mul`), `conj` distributes (`conj_mul`), and
    `conj χ(q⁻¹) = χ(q)` because `χ(q⁻¹) = conj χ(q)` (both invert `χ(q)`: `χ(q⁻¹)·χ(q) = χ(1) = 1`
    and `χ(q)·conj χ(q) = 1`).  Splits the collapsed Frobenius term into the `χ(q)·g(χ̄)` form.
    ∅-axiom up to allowed `propext`. -/
theorem char_conj_reindex_split {d : ZOmega} {p m x q k : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d (ZOmega.ZOmega.Omega) (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hq : gcd213 q p = 1) (hq1 : 0 < q) (hqlt : q < p) (hk1 : 0 < k) (hklt : k < p) :
    conj (chiOmega p m x ((aInv q p * k) % p)) = chiOmega p m x q * conj (chiOmega p m x k) := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hp)
  have hqilt : aInv q p % p < p := Nat.mod_lt _ hppos
  -- `q⁻¹ = aInv q p % p` is a unit: `(q⁻¹·q)%p = 1`, so `q⁻¹ ≠ 0`
  have hqiq : (aInv q p % p * q) % p = 1 := by
    rw [← mul_mod_left_pure (aInv q p) q p, Nat.mul_comm (aInv q p) q, aInv_spec hppos hq,
        Nat.mod_eq_of_lt hp]
  have hqipos : 0 < aInv q p % p := by
    rcases Nat.eq_zero_or_pos (aInv q p % p) with h0 | h
    · rw [h0, Nat.zero_mul, Nat.zero_mod] at hqiq; exact absurd hqiq (by decide)
    · exact h
  -- `χ(q⁻¹) = conj χ(q)`
  have hD : chiOmega p m x (aInv q p % p) = conj (chiOmega p m x q) := by
    have hmul : chiOmega p m x (aInv q p % p) * chiOmega p m x q = ofInt 1 := by
      rw [chiOmega_mul hp hp3 hpr h3m hdn hω hx hqipos hqilt hq1 hqlt, hqiq]
      exact chiOmega_one p m x hp
    calc chiOmega p m x (aInv q p % p)
        = chiOmega p m x (aInv q p % p) * ofInt 1 := (mul_one _).symm
      _ = chiOmega p m x (aInv q p % p) * (chiOmega p m x q * conj (chiOmega p m x q)) := by
          rw [chiOmega_mul_conj p m x q (chiOmega_ne_zero p m x q hq1 hqlt)]
      _ = chiOmega p m x (aInv q p % p) * chiOmega p m x q * conj (chiOmega p m x q) :=
          (mul_assoc _ _ _).symm
      _ = ofInt 1 * conj (chiOmega p m x q) := by rw [hmul]
      _ = conj (chiOmega p m x q) := one_mul_zomega _
  rw [show (aInv q p * k) % p = (aInv q p % p * k) % p from mul_mod_left_pure (aInv q p) k p,
      ← chiOmega_mul hp hp3 hpr h3m hdn hω hx hqipos hqilt hk1 hklt, conj_mul, hD, conj_conj]

/-- ★★★★★ **The closed Gauss-sum Frobenius congruence (factored form)** — for a prime `q ≡ 2 (mod 3)`
    that is a unit mod `p` (`p > 3`) and a unit coefficient `k` (`0 < k < p`),

      `g(χ)^{⋆q}(k) ≡ χ(q) · χ̄(k)   (mod ofInt q)`.

    `gauss_pow_modEq_reindexed` gives the collapsed term `χ̄((q⁻¹·k)%p)`; `char_conj_reindex_split`
    factors it as `χ(q)·χ̄(k)`.  Coefficient-wise this is `g(χ)^{⋆q} ≡ χ(q)·g(χ̄) (mod q)` (with
    `g(χ̄)(k) = χ̄(k)`) — **the classical Frobenius congruence of the cubic Gauss sum**, the engine of
    the cubic reciprocity law.  ∅-axiom up to allowed `propext`. -/
theorem gauss_pow_modEq_factored {d : ZOmega} {p m x q : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d (ZOmega.ZOmega.Omega) (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hq3 : q % 3 = 2) (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) (hcop : gcd213 q p = 1)
    (hq1 : 0 < q) (hqlt : q < p) {k : Nat} (hk1 : 0 < k) (hklt : k < p) :
    ModEq (ofInt ((q : Nat) : Int)) (convPow p (gauss p m x) q k)
      (chiOmega p m x q * conj (chiOmega p m x k)) := by
  have h := gauss_pow_modEq_reindexed p m x q hp hq3 hqr hcop hklt
  rwa [char_conj_reindex_split hp hp3 hpr h3m hdn hω hx hcop hq1 hqlt hk1 hklt] at h

/-- ★★★★★ **The closed Gauss-sum Frobenius congruence (all coefficients)** — `gauss_pow_modEq_factored`
    extended to every coefficient `k < p`, the full group-ring congruence

      `g(χ)^{⋆q} ≡ χ(q) · g(χ̄)   (mod ofInt q)`   coefficient-wise (`g(χ̄)(k) = χ̄(k) = conj χ(k)`).

    The `0 < k` case is `gauss_pow_modEq_factored`; at `k = 0` both sides vanish (`χ(0) = 0`, and the
    collapse term `χ̄((q⁻¹·0)%p) = χ̄(0) = 0`).  This is the form the cubic-reciprocity law consumes —
    propagated through products by `EisensteinConvCongruence.conv_modEq_left`.  ∅-axiom up to allowed
    `propext`. -/
theorem gauss_pow_modEq_factored_all {d : ZOmega} {p m x q : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d (ZOmega.ZOmega.Omega) (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hq3 : q % 3 = 2) (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) (hcop : gcd213 q p = 1)
    (hq1 : 0 < q) (hqlt : q < p) {k : Nat} (hk : k < p) :
    ModEq (ofInt ((q : Nat) : Int)) (convPow p (gauss p m x) q k)
      (chiOmega p m x q * conj (chiOmega p m x k)) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hc0 : chiOmega p m x 0 = 0 := chiOmega_zero_of_dvd p m x 0 ⟨0, rfl⟩
    have hcol := gauss_pow_modEq_reindexed p m x q hp hq3 hqr hcop hk
    rw [show (aInv q p * 0) % p = 0 from by rw [Nat.mul_zero, Nat.zero_mod], hc0, conj_zero] at hcol
    rwa [hc0, conj_zero, mul_zero]
  · exact gauss_pow_modEq_factored hp hp3 hpr h3m hdn hω hx hq3 hqr hcop hq1 hqlt hkpos hk

/-! ## Bridging the Frobenius RHS `g(χ̄)` to the norm factor `gaussConj` -/

/-- The reflection index is an involution on `[0,p)`: `(p − (p−k)%p) % p = k` for `k < p`. -/
private theorem refl_idx {p k : Nat} (hp : 0 < p) (hk : k < p) : (p - (p - k) % p) % p = k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0; rw [Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (Nat.sub_lt hp hkpos), Nat.sub_sub_self (Nat.le_of_lt hk),
        Nat.mod_eq_of_lt hk]

/-- ★★★★ **The Frobenius RHS is the norm factor, reflected** — `conj χ(k) = gaussConj((p−k)%p)` for
    `k < p`.  The Frobenius congruence's right factor `g(χ̄)(k) = conj χ(k)` (the **character-conjugate**
    Gauss sum) and the norm's right factor `gaussConj(j) = conj χ((p−j)%p)` (the **ring-conjugate**)
    differ only by the reflection `j ↦ (p−j)%p` (an involution, `refl_idx`).  This is the bridge that
    feeds the Frobenius output `χ(q)·g(χ̄)` into the Gauss-sum norm `g ⋆ gaussConj = Yfun`
    (`gauss_conj_norm`) for the reciprocity-law assembly.  ∅-axiom up to allowed `propext`. -/
theorem charConj_eq_gaussConj_reflect (p m x k : Nat) (hp : 0 < p) (hk : k < p) :
    conj (chiOmega p m x k) = gaussConj p m x ((p - k) % p) := by
  show conj (chiOmega p m x k) = conj (chiOmega p m x ((p - (p - k) % p) % p))
  rw [refl_idx hp hk]

/-- ★★★★★ **The Frobenius congruence pushed one power up** — for a prime `q ≡ 2 (mod 3)`, unit mod `p`,
    and `k < p`,

      `g(χ)^{⋆(q+1)}(k) ≡ χ(q) · (g(χ̄) ⋆ g(χ))(k)   (mod ofInt q)`,

    where `g(χ̄) = fun i ↦ conj χ(i)` is the character-conjugate Gauss sum.  `convPow_succ` opens
    `g^{⋆(q+1)} = g^{⋆q} ⋆ g`; `conv_modEq_left` replaces `g^{⋆q}` by its Frobenius value
    `χ(q)·g(χ̄)` (`gauss_pow_modEq_factored_all`, all coefficients); `conv_scalar_left` pulls the
    constant `χ(q)` out of the convolution.  The on-path step toward computing `g^{⋆N}` two ways for the
    reciprocity law: the RHS `g(χ̄)⋆g` is the Gauss-sum norm (evaluable via
    `charConj_eq_gaussConj_reflect` + `gauss_conj_norm`).  ∅-axiom up to allowed `propext`. -/
theorem gauss_pow_succ_modEq {d : ZOmega} {p m x q : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d (ZOmega.ZOmega.Omega) (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hq3 : q % 3 = 2) (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q) (hcop : gcd213 q p = 1)
    (hq1 : 0 < q) (hqlt : q < p) {k : Nat} (hk : k < p) :
    ModEq (ofInt ((q : Nat) : Int)) (convPow p (gauss p m x) (q + 1) k)
      (chiOmega p m x q
        * conv p (fun i => conj (chiOmega p m x i)) (gauss p m x) k) := by
  rw [convPow_succ]
  have h1 := conv_modEq_left p (gauss p m x) k
    (fun i hi => gauss_pow_modEq_factored_all hp hp3 hpr h3m hdn hω hx hq3 hqr hcop hq1 hqlt hi)
  rwa [conv_scalar_left p (chiOmega p m x q) (fun i => conj (chiOmega p m x i)) (gauss p m x) k] at h1

/-- ★★★★★ **The Frobenius congruence at `q+1`, evaluated** — for a prime `q ≡ 2 (mod 3)`, unit mod `p`,
    and `k < p`,

      `g(χ)^{⋆(q+1)}(k) ≡ χ(q) · Yfun(k)   (mod ofInt q)`,

    where `Yfun(k) = (p−1)` at `k=0`, `−1` otherwise (in `ℤ[ζ_p]`, `Yfun ↦ p` at `e_0`, `↦ 0` else).
    Evaluates the norm RHS of `gauss_pow_succ_modEq`: the character-conjugate Gauss sum `g(χ̄)` equals
    the ring-conjugate `gaussConj` (`gaussConj_eq_charConj`, since `χ(−1)=1`), so
    `g(χ̄)⋆g = gaussConj⋆g = g⋆gaussConj = Yfun` (`conv_comm` + `gauss_conj_norm`).  This is the
    Frobenius side of the cubic-reciprocity `g^{⋆N}`-comparison, in closed form.  ∅-axiom up to allowed
    `propext`. -/
theorem gauss_pow_succ_modEq_Yfun {d : ZOmega} {p m x q : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d (ZOmega.ZOmega.Omega) (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hq3 : q % 3 = 2) (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q)
    (hcop : gcd213 q p = 1) (hq1 : 0 < q) (hqlt : q < p) {k : Nat} (hk : k < p) :
    ModEq (ofInt ((q : Nat) : Int)) (convPow p (gauss p m x) (q + 1) k)
      (chiOmega p m x q * Yfun p k) := by
  have hpp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  have heq : conv p (fun i => conj (chiOmega p m x i)) (gauss p m x) k = Yfun p k := by
    rw [conv_congr p k hpp
          (fun i hi => (gaussConj_eq_charConj hp hp3 hpr h3m hm1 hdn hω hx hi).symm)
          (fun _ _ => rfl),
        conv_comm p (gaussConj p m x) (gauss p m x) hk]
    exact gauss_conj_norm hp hp3 hpr h3m hm1 hdn hω hx hk
  have hsucc := gauss_pow_succ_modEq hp hp3 hpr h3m hdn hω hx hq3 hqr hcop hq1 hqlt hk
  rwa [heq] at hsucc

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvGaussReindex
