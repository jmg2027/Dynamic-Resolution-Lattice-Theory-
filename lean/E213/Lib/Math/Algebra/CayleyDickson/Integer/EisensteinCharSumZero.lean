import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFpMul
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinScaleCancel
import E213.Lib.Math.Combinatorics.Permutations

/-!
# Cubic-character orthogonality over `𝔽_p*` — `Σ_t χ_ω(t) = 0` (∅-axiom, Phase A3)

The character sum of the cubic character over a unit list vanishes.  For a non-cubic-residue `a`
(`χ_ω(a) ≠ 1`) and a list `L` of units that the multiplication map `t ↦ (a·t) mod p` **permutes**
(`LPerm L (L.map …)`),

  `Σ_{t∈L} χ_ω(t) = 0`.

The argument is the classical one: scaling invariance.  `Σ χ_ω(t)` is unchanged by reindexing along the
permutation (`chiListSum_lperm`), and the scaled sum factors as `χ_ω(a)·Σ χ_ω(t)` (`chiListSum_map_factor`,
via `chiOmega_mul`).  So `Σ = χ_ω(a)·Σ`, and `χ_ω(a) ≠ 1` in the integral domain `ℤ[ω]` forces `Σ = 0`
(`EisensteinScaleCancel.scale_fixed_eq_zero`).

This is the `𝔽_p`-residue character orthogonality (the `Σ_t χ_ω(t) = 0` that the exponent-side
`chiExp_sum` could not reach), and the engine of the Jacobi-sum norm law `N(J) = p` (Phase A3,
`research-notes/frontiers/higher_reciprocity_roadmap.md`).  The unit list + permutation hypotheses are
supplied by `EulerTheorem.totativeList` / `lperm_image` and a primitive root.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumZero

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
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

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumZero
