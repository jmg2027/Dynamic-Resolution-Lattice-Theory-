import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitResidueSymbol

/-!
# The split-prime cross-modulus synthesis — relation B by swapped instantiation (∅-axiom)

For the split case of cubic reciprocity (BOTH primes Eisenstein, `π` of norm `p`, `π'` of norm `pr`,
both `≡ 1 (mod 3)`), the cross-modulus law `(π/π')₃ = (π'/π)₃` is assembled from **two symmetric**
conjugate-symbol relations + a combination (Ireland–Rosen ch. 9 / Xu REU 2021 §4):

- **relation A** (mod `π'`): `split_conj_residue_relation` for the first prime —
  `J̄^{m'} ≡ χ̄(pr)·J^{m'} (mod π')`,  `J = jacobiSum p m x`,  `m' = (pr−1)/3`.
- **relation B** (mod `π` = `d`): the **same theorem with the two primes swapped** —
  `J₂̄^{m} ≡ χ̄₂(p)·J₂^{m} (mod d)`,  `J₂ = jacobiSum pr m₂ x₂`,  `m = (p−1)/3`.

`split_conj_residue_relation` is generic in the prime data `(d, p, m, x)` and the second prime
`π'` (its setup `x'`/`hπ'ω` is a hypothesis, exactly as the first prime's `x`/`hω`/`hx`).  So relation B
is a pure **instantiation** with the roles of the two primes exchanged — the second prime supplies the
character data, the first prime `d` becomes the modulus.  The relaxation of `pr < p` to `pr ≠ p`
(`EisensteinCubicReciprocitySplit` chain) is what lets relations A and B coexist: A needs the first
prime as the unit argument, B needs the second — neither ordering can hold for both.  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicReciprocitySplit

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (jacobiSum)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitResidueSymbol
  (split_conj_residue_relation)
open E213.Tactic.NatHelper (gcd213 sub_add_cancel)

/-- ★★★★★ **Relation B — the conjugate-symbol relation for the second prime (mod `d = π`).**

    `(conj J₂)^m ≡ conj (χ₂(p)) · J₂^m   (mod d)`,    `J₂ = jacobiSum pr m₂ x₂`,  `χ₂ = chiOmega pr m₂ x₂`,
    `m = (p−1)/3`.

    This is `split_conj_residue_relation` instantiated with the two primes **swapped**: the second prime
    `(d₂, pr, m₂, x₂)` plays the character role, the first prime `d` (norm `p`) plays the modulus role.
    All hypotheses are the symmetric mirror of relation A's; the only arithmetic is `m = (m−1)+1` and
    `p = 3·m+1` (from `3·m = p−1`).  ∅-axiom (PURE). -/
theorem split_conj_residue_relation_B {d d₂ : ZOmega} {p m x pr m₂ x₂ : Nat}
    (hp : 1 < p) (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hp3mod : p % 3 = 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (hpr1 : 1 < pr) (hpr3 : 3 < pr) (hprr : ∀ k, k ∣ pr → k = 1 ∨ k = pr)
    (h3m₂ : 3 * m₂ = pr - 1) (hm1₂ : 1 ≤ m₂) (hdn₂ : d₂.normSq = (pr : Int))
    (hω₂ : ModEq d₂ Omega (ofInt ((x₂ : Nat) : Int))) (hx₂ : pr ∣ (x₂ * x₂ + x₂ + 1))
    (hcop : gcd213 p pr = 1) (hne : p ≠ pr) :
    ModEq d (pow (conj (jacobiSum pr m₂ x₂)) m)
      (conj (chiOmega pr m₂ x₂ p) * pow (jacobiSum pr m₂ x₂) m) := by
  -- write `m = (m−1) + 1` and `p = 3·m + 1`
  have hsB : (m - 1) + 1 = m := sub_add_cancel hm1
  have hs : p = 3 * ((m - 1) + 1) + 1 := by
    rw [hsB, h3m, sub_add_cancel (Nat.le_of_lt hp)]
  -- swapped application: char prime = (d₂, pr, m₂, x₂), modulus prime = d (norm p), unit arg = p
  have hB := split_conj_residue_relation (d := d₂) (p := pr) (m := m₂) (x := x₂) (pr := p)
    (s := m - 1) (π' := d) (x' := ((x : Nat) : Int))
    hpr1 hpr3 hprr h3m₂ hm1₂ hdn₂ hω₂ hx₂ hp3mod hpr hcop hp hne hdn hω hs
  rwa [hsB] at hB

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicReciprocitySplit
