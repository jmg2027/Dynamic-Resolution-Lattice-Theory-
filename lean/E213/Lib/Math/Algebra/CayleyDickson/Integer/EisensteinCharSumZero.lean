import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel
import E213.Lib.Math.Combinatorics.Permutations
import E213.Lib.Math.NumberTheory.EulerTheorem
import E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot
import E213.Lib.Math.NumberTheory.ModArith.CubicResidue

/-!
# Cubic-character orthogonality over `𝔽_p*` — `Σ_t χ_ω(t) = 0` (∅-axiom)

The character sum of the cubic character over a unit list vanishes.  For a non-cubic-residue `a`
(`χ_ω(a) ≠ 1`) and a list `L` of units that the multiplication map `t ↦ (a·t) mod p` **permutes**
(`LPerm L (L.map …)`),

  `Σ_{t∈L} χ_ω(t) = 0`.

The argument is the classical one: scaling invariance.  `Σ χ_ω(t)` is unchanged by reindexing along the
permutation (`chiListSum_lperm`), and the scaled sum factors as `χ_ω(a)·Σ χ_ω(t)` (`chiListSum_map_factor`,
via `chiOmega_mul`).  So `Σ = χ_ω(a)·Σ`, and `χ_ω(a) ≠ 1` in the integral domain `ℤ[ω]` forces `Σ = 0`
(`EisensteinScaleCancel.scale_fixed_eq_zero`).

This is the `𝔽_p`-residue character orthogonality (the `Σ_t χ_ω(t) = 0` that the exponent-side
`chiExp_sum` could not reach), and the engine of the Jacobi-sum norm law `N(J) = p`.  The unit list
+ permutation hypotheses are
supplied by `EulerTheorem.totativeList` / `lperm_image` and a primitive root.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumZero

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega chiOmega_ne_one)
open E213.Lib.Math.NumberTheory.ModArith.CubicCharFp (cubicChar cubicChar_one_iff_cube)
open E213.Lib.Math.NumberTheory.ModArith.CubicResidue (cube_pow_iff_three_dvd_exp)
open E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot (exists_primitive_root)
open E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle (not_dvd_g)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (prime_coprime)
open E213.Lib.Math.NumberTheory.EulerTheorem
  (totativeList totativeList_pos totativeList_le totativeList_coprime totative_lt_n lperm_image)
open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Meta.Nat.NatDiv213 (mul_mod_self_pure)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul (chiOmega_mul)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel (scale_fixed_eq_zero)
open E213.Lib.Math.Combinatorics.Permutations (LPerm)
open E213.Meta.Algebra213.Ring213 (mul_zero mul_add add_left_comm)

/-- `Σ_{t ∈ L} χ_ω(t)` — the cubic character summed over a list. -/
def chiListSum (p m x : Nat) : List Nat → ZOmega
  | [] => 0
  | t :: l => chiOmega p m x t + chiListSum p m x l

/-- ★★★ **The character sum is permutation-invariant** — `LPerm l₁ l₂ ⟹ Σ_{l₁} χ_ω = Σ_{l₂} χ_ω`.
    Induction on the permutation; the `swap` case is `add_left_comm`.  ∅-axiom. -/
theorem chiListSum_lperm (p m x : Nat) {l₁ l₂ : List Nat} (h : LPerm l₁ l₂) :
    chiListSum p m x l₁ = chiListSum p m x l₂ := by
  induction h with
  | nil => rfl
  | cons a _ ih =>
      show chiOmega p m x a + chiListSum p m x _ = chiOmega p m x a + chiListSum p m x _
      rw [ih]
  | swap a b l =>
      show chiOmega p m x b + (chiOmega p m x a + chiListSum p m x l)
         = chiOmega p m x a + (chiOmega p m x b + chiListSum p m x l)
      rw [add_left_comm]
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- ★★★★ **The scaled character sum factors** — `Σ_t χ_ω((a·t) mod p) = χ_ω(a)·Σ_t χ_ω(t)` for a unit
    `a` and a list `L` of units.  Termwise `χ_ω((a·t)%p) = χ_ω(a)·χ_ω(t)` (`chiOmega_mul`) + `mul_add`.
    ∅-axiom. -/
theorem chiListSum_map_factor {d : ZOmega} {p m x a : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (ha1 : 0 < a) (halt : a < p) :
    ∀ (L : List Nat), (∀ t, t ∈ L → 0 < t ∧ t < p) →
      chiListSum p m x (L.map (fun t => (a * t) % p)) = chiOmega p m x a * chiListSum p m x L := by
  intro L
  induction L with
  | nil => intro _; show (0 : ZOmega) = chiOmega p m x a * 0; rw [mul_zero]
  | cons t l ih =>
      intro hmem
      have ht := hmem t (List.Mem.head l)
      have hl : ∀ s, s ∈ l → 0 < s ∧ s < p := fun s hs => hmem s (List.Mem.tail t hs)
      show chiOmega p m x ((a * t) % p) + chiListSum p m x (l.map (fun t => (a * t) % p))
         = chiOmega p m x a * (chiOmega p m x t + chiListSum p m x l)
      rw [ih hl, ← chiOmega_mul hp hp3 hpr h3m hdn hω hx ha1 halt ht.1 ht.2, mul_add]

/-- ★★★★★ **Cubic-character orthogonality over a unit list** — `Σ_{t∈L} χ_ω(t) = 0` whenever the
    multiplication map `t ↦ (a·t) mod p` permutes `L` (`hLperm`) for a **non-residue** `a`
    (`χ_ω(a) ≠ 1`).  `Σ = χ_ω(a)·Σ` by permutation-invariance + factoring; `χ_ω(a) ≠ 1` in the domain
    `ℤ[ω]` forces `Σ = 0`.  The `𝔽_p` character orthogonality powering `N(J) = p`.  ∅-axiom. -/
theorem chiListSum_scale_zero {d : ZOmega} {p m x a : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hdn : d.normSq = (p : Int))
    (hω : ModEq d Omega (ofInt ((x : Nat) : Int))) (hx : p ∣ (x * x + x + 1))
    (ha1 : 0 < a) (halt : a < p) (hanr : chiOmega p m x a ≠ ofInt 1)
    {L : List Nat} (hLunit : ∀ t, t ∈ L → 0 < t ∧ t < p)
    (hLperm : LPerm L (L.map (fun t => (a * t) % p))) :
    chiListSum p m x L = 0 := by
  have hfix : chiOmega p m x a * chiListSum p m x L = chiListSum p m x L := by
    rw [← chiListSum_map_factor hp hp3 hpr h3m hdn hω hx ha1 halt L hLunit]
    exact (chiListSum_lperm p m x hLperm).symm
  exact scale_fixed_eq_zero hanr hfix

/-- ★★★★★ **Cubic-character orthogonality (unconditional)** — `Σ_{t ∈ totativeList p} χ_ω(t) = 0` for a
    prime `p ≡ 1 mod 3` with `p > 3`.  A **primitive root** `g` is a non-cubic-residue (`g = g¹`, a cube
    iff `3 ∣ 1`, false — `cube_pow_iff_three_dvd_exp`), so `χ_ω(g) ≠ 1` (`chiOmega_ne_one`); and `g`
    permutes the totatives by multiplication (`lperm_image`).  `chiListSum_scale_zero` then gives the
    vanishing.  This is the full `𝔽_p*` character orthogonality `Σ χ_ω = 0`, the engine of `N(J) = p`
   .  ∅-axiom. -/
theorem chiListSum_totatives_zero {d : ZOmega} {p m x : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) :
    chiListSum p m x (totativeList p) = 0 := by
  have hppos : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
  obtain ⟨g, hg1, hgle, hord⟩ := exists_primitive_root p hp hpr
  have hglt : g < p := Nat.lt_of_le_of_lt hgle (Nat.sub_lt hppos Nat.zero_lt_one)
  have hgcd : gcd213 g p = 1 := by rw [gcd213_comm]; exact prime_coprime p g hpr (not_dvd_g g p hg1 hglt)
  -- `g` is not a cubic residue, so `χ_ω(g) ≠ 1`
  have hnot31 : ¬ (3 ∣ 1) := by
    intro hc
    obtain ⟨c, hcc⟩ := hc
    have h0 : (1 : Nat) % 3 = 0 := by rw [hcc]; exact mul_mod_self_pure 3 c
    exact absurd h0 (by decide)
  have hg1pow : g ^ 1 % p = g := by rw [Nat.pow_one, Nat.mod_eq_of_lt hglt]
  have hcne : cubicChar p m g ≠ 1 := by
    intro hc1
    obtain ⟨y, hy1, hylt, hy3⟩ := (cubicChar_one_iff_cube p m g hp hpr h3m hm1 hg1 hglt).mp hc1
    have : ∃ y, 1 ≤ y ∧ y < p ∧ y ^ 3 % p = g ^ 1 % p := ⟨y, hy1, hylt, by rw [hg1pow]; exact hy3⟩
    exact hnot31 ((cube_pow_iff_three_dvd_exp p m g hp hpr h3m hm1 hg1 hgle hord 1).mp this)
  have hanr : chiOmega p m x g ≠ ofInt 1 := chiOmega_ne_one p m x g hg1 hglt hcne
  -- `g` permutes the totatives; each totative is a unit
  have hLperm : LPerm (totativeList p) ((totativeList p).map (fun t => (g * t) % p)) :=
    lperm_image hp hgcd
  have hLunit : ∀ t, t ∈ totativeList p → 0 < t ∧ t < p := fun t ht =>
    ⟨totativeList_pos ht,
     totative_lt_n hp (totativeList_coprime ht) (totativeList_pos ht) (totativeList_le ht)⟩
  exact chiListSum_scale_zero hp hp3 hpr h3m hdn hω hx hg1 hglt hanr hLunit hLperm

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumZero
