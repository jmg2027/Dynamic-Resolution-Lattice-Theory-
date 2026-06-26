import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitFermat
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrime
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNormLaw
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd

/-!
# The split residue symbol `(π/π')₃ = J^{s+1}` is μ₃-valued (∅-axiom)

★★★★★ `split_residue_cube_one` : for an Eisenstein prime `π'` of prime norm `pr = 3(s+1)+1 ≡ 1 (mod 3)`
(with `ω ≡ x' mod π'`),

  `(J^{s+1})³ = J^{3(s+1)} ≡ 1   (mod π')`        (`J = jacobiSum p m x`),

so the cubic residue symbol `(π/π')₃ := J^{s+1} mod π'` is a genuine cube root of unity in
`𝔽_{p'} = ℤ[ω]/(π')`.  The split analog of `residue_symbol_exists` (inert).

Proof: the `𝔽_{p'}` Fermat `split_fermat` gives `J^{pr} ≡ J (mod π')`; `pow_succ` writes
`J^{pr} = J^{3(s+1)}·J`, so `J^{3(s+1)}·J ≡ 1·J`, and right-cancelling `J` — a **unit mod `π'`** since
`π' ∤ J` (else `pr = ‖π'‖² ∣ ‖J‖² = p`, impossible for distinct primes `pr < p`) — in the domain
`ℤ[ω]/(π')` (`residue_no_zero_divisors`) gives `J^{3(s+1)} ≡ 1`.  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitResidueSymbol

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (jacobiSum)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNormLaw (jacobi_norm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd (normSq_dvd_of_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrime (residue_no_zero_divisors)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitFermat (split_fermat)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd (ofInt_one_mul)
open E213.Lib.Math.NumberTheory.PolyRoot (int_dvd_to_nat)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow pow_succ)
open E213.Meta.Algebra213.Ring213 (add_mul neg_mul add_zero)

/-- **Right cancellation in `𝔽_{p'} = ℤ[ω]/(π')`** — `α·γ ≡ β·γ (mod π')` with `γ ≢ 0` and `‖π'‖² = pr`
    prime forces `α ≡ β (mod π')`.  `(α−β)·γ ≡ 0` + `residue_no_zero_divisors` + `γ ≢ 0`.  ∅-axiom. -/
theorem modEq_cancel_right {π α β γ : ZOmega} {pr : Nat}
    (hprr : ∀ m, m ∣ pr → m = 1 ∨ m = pr) (hpr1 : 1 < pr) (hπnorm : π.normSq = (pr : Int))
    (hγ : ¬ ModEq π γ 0) (h : ModEq π (α * γ) (β * γ)) : ModEq π α β := by
  have hfact : ModEq π ((α + -β) * γ) 0 := by
    show π ∣ ((α + -β) * γ + -0)
    rw [show (-(0 : ZOmega)) = 0 from by decide, add_zero, add_mul, neg_mul]
    exact h
  rcases residue_no_zero_divisors hprr hpr1 hπnorm hfact with hab | hg
  · show π ∣ (α + -β)
    have h2 : π ∣ ((α + -β) + -0) := hab
    rwa [show (-(0 : ZOmega)) = 0 from by decide, add_zero] at h2
  · exact absurd hg hγ

/-- **The Jacobi sum is a unit mod a coprime prime `π'`** — `J ≢ 0 (mod π')` for an Eisenstein prime
    `π'` of norm `pr` with `1 < pr < p`.  If `π' ∣ J` then `pr = ‖π'‖² ∣ ‖J‖² = p` (`normSq_dvd_of_dvd`
    + `jacobi_norm`), impossible for distinct primes `pr < p`.  ∅-axiom. -/
theorem jacobi_ne_zero_mod_pi {d : ZOmega} {p m x pr : Nat} {π : ZOmega} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hπnorm : π.normSq = (pr : Int)) (hpr1 : 1 < pr) (hprlt : pr < p) :
    ¬ ModEq π (jacobiSum p m x) 0 := by
  intro h
  have hdvd : π ∣ jacobiSum p m x := by
    have h2 : π ∣ (jacobiSum p m x + -0) := h
    rwa [show (-(0 : ZOmega)) = 0 from by decide, add_zero] at h2
  obtain ⟨c, hc⟩ := hdvd
  have hnorm : π.normSq ∣ (jacobiSum p m x).normSq := normSq_dvd_of_dvd π (jacobiSum p m x) c hc
  rw [hπnorm, jacobi_norm hp hp3 hpr h3m hm1 hdn hω hx] at hnorm
  have hnat : pr ∣ p := by
    have hh := int_dvd_to_nat pr (p : Int) hnorm
    rwa [Int.natAbs_ofNat] at hh
  rcases hpr pr hnat with h1 | hpeq
  · exact absurd h1 (Nat.ne_of_gt hpr1)
  · exact absurd hpeq (Nat.ne_of_lt hprlt)

/-- ★★★★★ **The split residue symbol is μ₃-valued** — `J^{3(s+1)} ≡ 1 (mod π')` for an Eisenstein prime
    `π'` of norm `pr = 3(s+1)+1` (`ω ≡ x' mod π'`), `1 < pr < p`.  So `(π/π')₃ := J^{s+1} mod π'` is a
    cube root of unity in `𝔽_{p'}`.  `split_fermat` (`J^{pr} ≡ J`) + right-cancel `J` (`jacobi_ne_zero`
    + `modEq_cancel_right`).  ∅-axiom (PURE). -/
theorem split_residue_cube_one {d : ZOmega} {p m x pr s : Nat} {π' : ZOmega} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hprr : ∀ k, k ∣ pr → k = 1 ∨ k = pr) (hpr1 : 1 < pr) (hprlt : pr < p)
    (hπ'norm : π'.normSq = (pr : Int)) {x' : Int} (hπ'ω : ModEq π' Omega (ofInt x'))
    (hs : pr = 3 * (s + 1) + 1) :
    ModEq π' (pow (jacobiSum p m x) (3 * (s + 1))) (ofInt 1) := by
  have hJne : ¬ ModEq π' (jacobiSum p m x) 0 :=
    jacobi_ne_zero_mod_pi hp hp3 hpr h3m hm1 hdn hω hx hπ'norm hpr1 hprlt
  have hferm := split_fermat hpr1 hprr hπ'norm hπ'ω (jacobiSum p m x)
  rw [hs, pow_succ] at hferm
  have hJ1 : ModEq π' (pow (jacobiSum p m x) (3 * (s + 1)) * jacobiSum p m x)
      (ofInt 1 * jacobiSum p m x) := by rwa [ofInt_one_mul]
  exact modEq_cancel_right hprr hpr1 hπ'norm hJne hJ1

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitResidueSymbol
