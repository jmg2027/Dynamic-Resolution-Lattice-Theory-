import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitResidueSymbol
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharNormSplit
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinMu3Lift
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpGen

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
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (Omega2)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitResidueSymbol
  (split_conj_residue_relation split_residue_symbol_exists)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharNormSplit (chiOmega_eq_eisChar_gen)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNormLaw (jacobi_norm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep (mul_conj_self)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicChar (pow_mul_distrib)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (trans mul_left mul_right)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinMu3Lift (mu3_eq_of_modEq_pi)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpGen (chiOmega_unit_value_gen)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (mul_comm)
open E213.Meta.Algebra213.Ring213 (mul_assoc)
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

/-- ★★★★★ **Norm-multiplicativity of the rational character** — `χ_{d₂}(p) ≡ J^{m₂}·(conj J)^{m₂}
    (mod d₂)`, where `J = jacobiSum p m x` is the (primary) prime of norm `p` and `d₂` is the modulus
    prime of norm `pr` (character `chiOmega pr m₂ x₂`).  The rational character of `p = N(J)` factors as
    the product of the residue symbols of `J` and `conj J` at `d₂`:  `χ_{d₂}(p) ≡ pow (ofInt p) m₂`
    (`chiOmega_eq_eisChar_gen`, `¬ pr ∣ p`) `= pow (J·conj J) m₂` (`ofInt p = J·conj J` via `jacobi_norm`
    + `mul_conj_self`) `= J^{m₂}·(conj J)^{m₂}` (`pow_mul_distrib`).  Brick 8 of the synthesis.
    ∅-axiom (PURE). -/
theorem char_norm_mult {d d₂ : ZOmega} {p m x pr m₂ x₂ : Nat}
    (hp : 1 < p) (hp3 : 3 < p) (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hpr1 : 1 < pr) (hprr : ∀ k, k ∣ pr → k = 1 ∨ k = pr)
    (h3m₂ : 3 * m₂ = pr - 1) (hdn₂ : d₂.normSq = (pr : Int))
    (hω₂ : ModEq d₂ Omega (ofInt ((x₂ : Nat) : Int))) (hx₂ : pr ∣ (x₂ * x₂ + x₂ + 1))
    (hnprp : ¬ pr ∣ p) :
    ModEq d₂ (chiOmega pr m₂ x₂ p)
      (pow (jacobiSum p m x) m₂ * pow (conj (jacobiSum p m x)) m₂) := by
  have hofp : jacobiSum p m x * conj (jacobiSum p m x) = ofInt ((p : Nat) : Int) := by
    rw [mul_conj_self, jacobi_norm hp hp3 hpr h3m hm1 hdn hω hx]
  have hpow : pow (ofInt ((p : Nat) : Int)) m₂
      = pow (jacobiSum p m x) m₂ * pow (conj (jacobiSum p m x)) m₂ := by
    rw [← hofp, pow_mul_distrib]
  have h1 := chiOmega_eq_eisChar_gen (d := d₂) (p := pr) (m := m₂) (x := x₂) (t := p)
    hpr1 hprr h3m₂ hdn₂ hω₂ hx₂ hnprp
  rwa [hpow] at h1

/-- ★★★★★ **The μ₃ reciprocity algebra** — the finite-group step that closes the cross-modulus synthesis.
    For cube roots of unity `A, S, C, E` with the two symmetric relations

      `C = conj E · A²`   and   `E = conj C · S²`,

    necessarily `A = S`.  (Mathematically: `conj E = C·S` from the second relation — `conj(S²)=S` for μ₃ —
    so `C = C·S·A²`, cancel `C`, and `S·A² = 1` gives `S = A^{-2} = A`.)  A finite check over the `3⁴`
    literal assignments — contradictory assignments killed by `hI`/`hII`, the rest forced to `A = S`.
    ∅-axiom (PURE; `decide` on ℤ[ω] literals). -/
theorem mu3_reciprocity_algebra {A S C E : ZOmega}
    (hA : A = ofInt 1 ∨ A = Omega ∨ A = Omega2) (hS : S = ofInt 1 ∨ S = Omega ∨ S = Omega2)
    (hC : C = ofInt 1 ∨ C = Omega ∨ C = Omega2) (hE : E = ofInt 1 ∨ E = Omega ∨ E = Omega2)
    (hI : C = conj E * (A * A)) (hII : E = conj C * (S * S)) : A = S := by
  rcases hA with rfl | rfl | rfl <;> rcases hS with rfl | rfl | rfl <;>
    rcases hC with rfl | rfl | rfl <;> rcases hE with rfl | rfl | rfl <;>
    first
      | rfl
      | (exact absurd hI (by decide))
      | (exact absurd hII (by decide))

/-- ★★★★★ **Relation B's residue symbol is μ₃-valued (mod `d = π`).**  `(π'/π)₃ := J₂^m mod d` is one of
    `1, ω, ω²` — the swapped instantiation of `split_residue_symbol_exists` (second prime as character
    data, first prime `d` as modulus).  Gives `(π'/π)₃` as a well-defined cube root of unity, the mirror
    of `(π/π')₃` from `split_residue_symbol_exists`.  ∅-axiom (PURE). -/
theorem split_residue_symbol_exists_B {d d₂ : ZOmega} {p m x pr m₂ x₂ : Nat}
    (hp : 1 < p) (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hpr1 : 1 < pr) (hpr3 : 3 < pr) (hprr : ∀ k, k ∣ pr → k = 1 ∨ k = pr)
    (h3m₂ : 3 * m₂ = pr - 1) (hm1₂ : 1 ≤ m₂) (hdn₂ : d₂.normSq = (pr : Int))
    (hω₂ : ModEq d₂ Omega (ofInt ((x₂ : Nat) : Int))) (hx₂ : pr ∣ (x₂ * x₂ + x₂ + 1))
    (hne : p ≠ pr) :
    ModEq d (pow (jacobiSum pr m₂ x₂) m) (ofInt 1)
      ∨ ModEq d (pow (jacobiSum pr m₂ x₂) m) Omega
      ∨ ModEq d (pow (jacobiSum pr m₂ x₂) m) Omega2 := by
  have hsB : (m - 1) + 1 = m := sub_add_cancel hm1
  have hs : p = 3 * ((m - 1) + 1) + 1 := by
    rw [hsB, h3m, sub_add_cancel (Nat.le_of_lt hp)]
  have hB := split_residue_symbol_exists (d := d₂) (p := pr) (m := m₂) (x := x₂) (pr := p)
    (s := m - 1) (π' := d) (x' := ((x : Nat) : Int))
    hpr1 hpr3 hprr h3m₂ hm1₂ hdn₂ hω₂ hx₂ hpr hp hne hdn hω hs
  rwa [hsB] at hB

/-- `conj` of a μ₃ literal is a μ₃ literal (`conj ω = ω²`, `conj ω² = ω`). -/
private theorem mu3_conj {X : ZOmega} (h : X = ofInt 1 ∨ X = Omega ∨ X = Omega2) :
    conj X = ofInt 1 ∨ conj X = Omega ∨ conj X = Omega2 := by
  rcases h with rfl | rfl | rfl
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inr (by decide))
  · exact Or.inr (Or.inl (by decide))

/-- The product of two μ₃ literals is a μ₃ literal (`μ₃` is closed under `·`). -/
private theorem mu3_mul {X Y : ZOmega} (hX : X = ofInt 1 ∨ X = Omega ∨ X = Omega2)
    (hY : Y = ofInt 1 ∨ Y = Omega ∨ Y = Omega2) :
    X * Y = ofInt 1 ∨ X * Y = Omega ∨ X * Y = Omega2 := by
  rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl <;>
    first
      | exact Or.inl (by decide)
      | exact Or.inr (Or.inl (by decide))
      | exact Or.inr (Or.inr (by decide))

/-- **The combination of one half into an element equation** — from the conjugate-symbol relation
    `b ≡ conj E · a (mod π_mod)` (`a = J^k`, `b = (conj J)^k`), the norm-multiplicativity `C ≡ a·b`, and
    the symbol's literal value `a ≡ A`, derive the element equation `C = conj E · A²` (both sides μ₃
    literals, pinned by `mu3_eq_of_modEq_pi`).  Used for both halves (I) and (II).  ∅-axiom (PURE). -/
private theorem combine_relation {πm Jx Echar Cchar A : ZOmega} {n k : Nat}
    (hn3 : 3 < n) (hnorm : πm.normSq = (n : Int))
    (hCμ3 : Cchar = ofInt 1 ∨ Cchar = Omega ∨ Cchar = Omega2)
    (hEμ3 : Echar = ofInt 1 ∨ Echar = Omega ∨ Echar = Omega2)
    (hAμ3 : A = ofInt 1 ∨ A = Omega ∨ A = Omega2)
    (hrel : ModEq πm (pow (conj Jx) k) (conj Echar * pow Jx k))
    (hcnm : ModEq πm Cchar (pow Jx k * pow (conj Jx) k))
    (hAdef : ModEq πm (pow Jx k) A) :
    Cchar = conj Echar * (A * A) := by
  have hbA : ModEq πm (pow (conj Jx) k) (conj Echar * A) :=
    trans hrel (mul_left hAdef (conj Echar))
  have hC1 : ModEq πm Cchar (A * (conj Echar * A)) :=
    trans hcnm (trans (mul_right hAdef (pow (conj Jx) k)) (mul_left hbA A))
  have heq : A * (conj Echar * A) = conj Echar * (A * A) := by
    calc A * (conj Echar * A) = (A * conj Echar) * A := (mul_assoc A (conj Echar) A).symm
      _ = (conj Echar * A) * A := by rw [mul_comm A (conj Echar)]
      _ = conj Echar * (A * A) := mul_assoc (conj Echar) A A
  rw [heq] at hC1
  exact mu3_eq_of_modEq_pi hn3 hnorm hCμ3 (mu3_mul (mu3_conj hEμ3) (mu3_mul hAμ3 hAμ3)) hC1

/-- ★★★★★ **CUBIC RECIPROCITY — the split case.**  For two distinct primary Eisenstein primes
    `J = jacobiSum p m x` (norm `p`, modulus `d`) and `J₂ = jacobiSum pr m₂ x₂` (norm `pr`, modulus `d₂`),
    both `≡ 1 (mod 3)`, the cubic residue symbols are **equal**:

      `(J/J₂)₃ = (J₂/J)₃`,    i.e.    `A = S`   for   `J^{m₂} ≡ A (mod d₂)`,  `J₂^{m} ≡ S (mod d)`.

    Assembled from the two symmetric halves: relation A (`split_conj_residue_relation`, mod `d₂`) +
    norm-mult (`char_norm_mult`, mod `d₂`) give `C = conj E · A²` (`combine_relation`); the swapped pair
    (relation B + swapped norm-mult, mod `d`) give `E = conj C · S²`; `mu3_reciprocity_algebra` closes
    `A = S`.  `C = χ_{d₂}(p)`, `E = χ_d(pr)` are the rational characters (μ₃ literals).

    **No proof-assistant formalization of cubic reciprocity exists anywhere** — this is novel.
    ∅-axiom (PURE). -/
theorem split_cubic_reciprocity {d d₂ : ZOmega} {p m x pr m₂ x₂ : Nat}
    (hp : 1 < p) (hp3 : 3 < p) (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hp3mod : p % 3 = 1) (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1))
    (hpr1 : 1 < pr) (hpr3 : 3 < pr) (hprr : ∀ k, k ∣ pr → k = 1 ∨ k = pr) (h3m₂ : 3 * m₂ = pr - 1)
    (hm1₂ : 1 ≤ m₂) (hpr3mod : pr % 3 = 1) (hdn₂ : d₂.normSq = (pr : Int))
    (hω₂ : ModEq d₂ Omega (ofInt ((x₂ : Nat) : Int))) (hx₂ : pr ∣ (x₂ * x₂ + x₂ + 1))
    (hcopA : gcd213 pr p = 1) (hcopB : gcd213 p pr = 1) (hnppr : ¬ p ∣ pr) (hnprp : ¬ pr ∣ p)
    {A S : ZOmega}
    (hAμ3 : A = ofInt 1 ∨ A = Omega ∨ A = Omega2)
    (hAdef : ModEq d₂ (pow (jacobiSum p m x) m₂) A)
    (hSμ3 : S = ofInt 1 ∨ S = Omega ∨ S = Omega2)
    (hSdef : ModEq d (pow (jacobiSum pr m₂ x₂) m) S) :
    A = S := by
  have hne : p ≠ pr := fun h => hnprp ⟨1, by rw [h]; exact (Nat.mul_one pr).symm⟩
  have hprne : pr ≠ p := fun h => hnppr ⟨1, by rw [h]; exact (Nat.mul_one p).symm⟩
  -- the two rational characters (μ₃ literals)
  have hEμ3 : chiOmega p m x pr = ofInt 1 ∨ chiOmega p m x pr = Omega ∨ chiOmega p m x pr = Omega2 :=
    chiOmega_unit_value_gen p m x pr hp hnppr
  have hCμ3 : chiOmega pr m₂ x₂ p = ofInt 1 ∨ chiOmega pr m₂ x₂ p = Omega ∨ chiOmega pr m₂ x₂ p = Omega2 :=
    chiOmega_unit_value_gen pr m₂ x₂ p hpr1 hnprp
  -- equation (I):  C = conj E · A²   (mod d₂)
  have hmB₂ : (m₂ - 1) + 1 = m₂ := sub_add_cancel hm1₂
  have hsA : pr = 3 * ((m₂ - 1) + 1) + 1 := by
    rw [hmB₂, h3m₂, sub_add_cancel (Nat.le_of_lt hpr1)]
  have hrelA := split_conj_residue_relation (d := d) (p := p) (m := m) (x := x) (pr := pr)
    (s := m₂ - 1) (π' := d₂) (x' := ((x₂ : Nat) : Int))
    hp hp3 hpr h3m hm1 hdn hω hx hpr3mod hprr hcopA hpr1 hprne hdn₂ hω₂ hsA
  rw [hmB₂] at hrelA
  have hcnm₁ := char_norm_mult hp hp3 hpr h3m hm1 hdn hω hx hpr1 hprr h3m₂ hdn₂ hω₂ hx₂ hnprp
  have hI : chiOmega pr m₂ x₂ p = conj (chiOmega p m x pr) * (A * A) :=
    combine_relation hpr3 hdn₂ hCμ3 hEμ3 hAμ3 hrelA hcnm₁ hAdef
  -- equation (II):  E = conj C · S²   (mod d) — the swapped pair
  have hrelB := split_conj_residue_relation_B hp hpr h3m hm1 hp3mod hdn hω hx
    hpr1 hpr3 hprr h3m₂ hm1₂ hdn₂ hω₂ hx₂ hcopB hne
  have hcnm₂ := char_norm_mult hpr1 hpr3 hprr h3m₂ hm1₂ hdn₂ hω₂ hx₂ hp hpr h3m hdn hω hx hnppr
  have hII : chiOmega p m x pr = conj (chiOmega pr m₂ x₂ p) * (S * S) :=
    combine_relation hp3 hdn hEμ3 hCμ3 hSμ3 hrelB hcnm₂ hSdef
  exact mu3_reciprocity_algebra hAμ3 hSμ3 hCμ3 hEμ3 hI hII

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicReciprocitySplit
