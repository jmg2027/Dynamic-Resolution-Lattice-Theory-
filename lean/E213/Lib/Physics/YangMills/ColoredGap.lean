import E213.Lib.Physics.YangMills.Gap
import E213.Lib.Math.Combinatorics.IntGridSum
import E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteLichnerowicz
import E213.Meta.Int213.Bound

/-!
# Yang–Mills colored-mode spectral positivity — the spectral face of confinement (∅-axiom)

`Gap.lean` closes the **mass gap**: the gauge-lattice Hodge Laplacian `Δ₀ = lap` of
`K_{3,2}^{(c=2)}` has the exact spectrum `{0, 4, 4, 6, 10}` (complete eigenbasis,
`eigenbasis_independent : det = -30 ≠ 0`), so the smallest nonzero eigenvalue is
`massGap = c·min(NS,NT) = 4`.

This file builds the next confinement brick: **colored-mode positivity** — the
operator inequality

> `⟨Δ₀f, Δ₀f⟩ ≥ massGap · ⟨Δ₀f, f⟩`   for **every** integer configuration `f`

(`colored_rayleigh_ge`), i.e. `Δ₀(Δ₀ − massGap·I) ⪰ 0` as a quadratic form on the
whole space, with **no** mean-zero restriction and **no** continuum.  The content is
the explicit sum-of-squares certificate (`colored_form_identity`)

> `⟨Δ₀f,Δ₀f⟩ − 4·⟨Δ₀f,f⟩ = 2·(2(f₀+f₁+f₂) − 3(f₃+f₄))² + 6·(f₃−f₄)²`.

The two squares are exactly the two **gapped** directions of the forced spectrum: the
cross/top mode `vTop` (reads `2` on spatial, `−3` on temporal, `λ = 10 ⇒ 10²−4·10 = 60`)
and the temporal-difference mode `vTemp` (`f₃−f₄`, `λ = 6 ⇒ 6²−4·6 = 12`); the kernel
`vVac` (`λ=0`) and the spatial-difference modes (`λ=4`, `λ²−4λ = 0`) contribute nothing.
`λ²−4λ ≥ 0` for every `λ ∈ {0,4,6,10}` is precisely why the certificate is a *positive*
combination, and the coefficients `2, 6` are forced by completing the square on `Δ₀²−4Δ₀`.

The corollary `colored_gap`: **every colored (nonzero-eigenvalue) excitation costs energy
`≥ massGap`** — feeding the SOS into the abstract Lichnerowicz mechanism
(`DiscreteLichnerowicz.lichnerowicz_abstract`) reproves the gap *spectrally* for an
arbitrary eigenfunction, not only on the exhibited basis.

## What this is and is not (no-exterior discipline, `seed/AXIOM/05_no_exterior.md` §5.4)

This is the **spectral** face of confinement: colored modes are gapped, the singlet
vacuum is the unique zero-energy state.  It is *not* a continuum area law `⟨W⟩ ∼
exp(−σ·Area)` — on the abstract bipartite complex `K_{3,2}` there is no embedding, hence
no enclosed "area" and no absolute string tension to state (§5.1).  The area-law face
stays genuinely open (`research-notes/frontiers/yang_mills_confinement.md`); honestly,
no internal handle on it has been found.  All theorems here are ∅-axiom.
-/

namespace E213.Lib.Physics.YangMills.ColoredGap

open E213.Meta.Int213
open E213.Lib.Physics.YangMills.Gap (lap mulVec massGap IsEigenpair)
open E213.Lib.Physics.Simplex.Counts (NS NT d)
open E213.Lib.Math.Combinatorics.IntGridSum (gridSumZ gridSumZ_congr gridSumZ_mul_left)
open E213.Lib.Math.Geometry.DiscreteCurvature.DiscreteLichnerowicz (lichnerowicz_abstract)

/-! ## §1 — The sum-of-squares certificate for `Δ₀² − massGap·Δ₀` -/

/-- ★ **The colored-mode SOS certificate.**  For every integer configuration `f` over the
    five gauge-lattice vertices,

      `⟨Δ₀f,Δ₀f⟩ − massGap·⟨Δ₀f,f⟩ = 2·(2(f₀+f₁+f₂) − 3(f₃+f₄))² + 6·(f₃−f₄)²`.

    The right side is a manifestly non-negative combination of the two gapped eigen-
    directions (`vTop` cross mode, `vTemp` temporal difference); the proof is the explicit
    `Δ₀ = lap` action at each vertex (`rfl`) followed by `ring_intZ`. -/
theorem colored_form_identity (f : Nat → Int) :
    gridSumZ d (fun i => mulVec d lap f i * mulVec d lap f i)
      - massGap * gridSumZ d (fun i => mulVec d lap f i * f i)
    = 2 * ((2 * (f 0 + f 1 + f 2) - 3 * (f 3 + f 4))
            * (2 * (f 0 + f 1 + f 2) - 3 * (f 3 + f 4)))
      + 6 * ((f 3 - f 4) * (f 3 - f 4)) := by
  -- `Int.add_zero` (core) carries `propext`; rebuild it from the pure `Int213` API.
  have hz : ∀ a : Int, a + 0 = a := fun a => (add_comm a 0).trans (zero_add a)
  -- The explicit `Δ₀ = lap` action at each vertex.  `mulVec` `rfl`-reduces to a literal-
  -- coefficient sum; strip the `0·f` / `0 +` noise with the pure zero lemmas so `ring_intZ`
  -- (which compares canonical forms, not up-to-zero) sees the clean linear combinations.
  have e0 : mulVec d lap f 0 = 4 * f 0 + (-2) * f 3 + (-2) * f 4 := by
    show (0:Int) + 4 * f 0 + 0 * f 1 + 0 * f 2 + (-2) * f 3 + (-2) * f 4 = _
    rw [zero_mul, zero_mul, zero_add, hz, hz]
  have e1 : mulVec d lap f 1 = 4 * f 1 + (-2) * f 3 + (-2) * f 4 := by
    show (0:Int) + 0 * f 0 + 4 * f 1 + 0 * f 2 + (-2) * f 3 + (-2) * f 4 = _
    rw [zero_mul, zero_mul, zero_add, zero_add, hz]
  have e2 : mulVec d lap f 2 = 4 * f 2 + (-2) * f 3 + (-2) * f 4 := by
    show (0:Int) + 0 * f 0 + 0 * f 1 + 4 * f 2 + (-2) * f 3 + (-2) * f 4 = _
    rw [zero_mul, zero_mul, zero_add, zero_add, zero_add]
  have e3 : mulVec d lap f 3 = (-2) * f 0 + (-2) * f 1 + (-2) * f 2 + 6 * f 3 := by
    show (0:Int) + (-2) * f 0 + (-2) * f 1 + (-2) * f 2 + 6 * f 3 + 0 * f 4 = _
    rw [zero_mul, zero_add, hz]
  have e4 : mulVec d lap f 4 = (-2) * f 0 + (-2) * f 1 + (-2) * f 2 + 6 * f 4 := by
    show (0:Int) + (-2) * f 0 + (-2) * f 1 + (-2) * f 2 + 0 * f 3 + 6 * f 4 = _
    rw [zero_mul, zero_add, hz]
  have hsq : gridSumZ d (fun i => mulVec d lap f i * mulVec d lap f i)
      = mulVec d lap f 0 * mulVec d lap f 0 + mulVec d lap f 1 * mulVec d lap f 1
        + mulVec d lap f 2 * mulVec d lap f 2 + mulVec d lap f 3 * mulVec d lap f 3
        + mulVec d lap f 4 * mulVec d lap f 4 := by
    show (0:Int) + mulVec d lap f 0 * mulVec d lap f 0 + mulVec d lap f 1 * mulVec d lap f 1
        + mulVec d lap f 2 * mulVec d lap f 2 + mulVec d lap f 3 * mulVec d lap f 3
        + mulVec d lap f 4 * mulVec d lap f 4 = _
    rw [zero_add]
  have hcr : gridSumZ d (fun i => mulVec d lap f i * f i)
      = mulVec d lap f 0 * f 0 + mulVec d lap f 1 * f 1 + mulVec d lap f 2 * f 2
        + mulVec d lap f 3 * f 3 + mulVec d lap f 4 * f 4 := by
    show (0:Int) + mulVec d lap f 0 * f 0 + mulVec d lap f 1 * f 1 + mulVec d lap f 2 * f 2
        + mulVec d lap f 3 * f 3 + mulVec d lap f 4 * f 4 = _
    rw [zero_add]
  rw [hsq, hcr, e0, e1, e2, e3, e4, show massGap = (4 : Int) from rfl]
  ring_intZ

/-! ## §2 — Colored positivity and the spectral gap -/

/-- ★★ **Colored-mode positivity (Rayleigh form).**  `⟨Δ₀f,Δ₀f⟩ ≥ massGap·⟨Δ₀f,f⟩` for
    every `f` — the operator inequality `Δ₀(Δ₀ − massGap·I) ⪰ 0`, ∅-axiom, via the SOS
    certificate.  This is the spectral face of confinement: the gap is paid by *every*
    configuration, not only the exhibited eigenbasis. -/
theorem colored_rayleigh_ge (f : Nat → Int) :
    massGap * gridSumZ d (fun i => mulVec d lap f i * f i)
      ≤ gridSumZ d (fun i => mulVec d lap f i * mulVec d lap f i) := by
  have hnn : (0 : Int) ≤ 2 * ((2 * (f 0 + f 1 + f 2) - 3 * (f 3 + f 4))
                  * (2 * (f 0 + f 1 + f 2) - 3 * (f 3 + f 4)))
              + 6 * ((f 3 - f 4) * (f 3 - f 4)) :=
    add_nonneg (mul_nonneg (by decide) (int_sq_nonneg _))
               (mul_nonneg (by decide) (int_sq_nonneg _))
  have h0 : (0 : Int) ≤ gridSumZ d (fun i => mulVec d lap f i * mulVec d lap f i)
      - massGap * gridSumZ d (fun i => mulVec d lap f i * f i) :=
    (colored_form_identity f).symm ▸ hnn
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero h0)

/-- ★★★ **The colored gap, spectrally.**  Any eigenfunction `Δ₀v = λ·v` with `λ > 0`
    (a colored excitation) and `Σ v² > 0` has eigenvalue `λ ≥ massGap = 4`.  The SOS
    operator inequality feeds the abstract Lichnerowicz mechanism: `λ²·N = ⟨Δ₀v,Δ₀v⟩ ≥
    massGap·⟨Δ₀v,v⟩ = massGap·λ·N`, hence `massGap ≤ λ`.  This reproves the mass gap for an
    *arbitrary* eigenfunction (not only the five exhibited basis vectors). -/
theorem colored_gap (lam : Int) (v : Nat → Int)
    (hlam : 0 < lam) (hv : 0 < gridSumZ d (fun i => v i * v i))
    (heig : IsEigenpair lam v) :
    massGap ≤ lam := by
  have hL : gridSumZ d (fun i => mulVec d lap v i * mulVec d lap v i)
      = lam * lam * gridSumZ d (fun i => v i * v i) := by
    rw [show gridSumZ d (fun i => mulVec d lap v i * mulVec d lap v i)
          = gridSumZ d (fun i => lam * lam * (v i * v i)) from
        gridSumZ_congr d _ _ (fun i hi => by rw [heig i hi]; ring_intZ),
        gridSumZ_mul_left]
  have hR : gridSumZ d (fun i => mulVec d lap v i * v i)
      = lam * gridSumZ d (fun i => v i * v i) := by
    rw [show gridSumZ d (fun i => mulVec d lap v i * v i)
          = gridSumZ d (fun i => lam * (v i * v i)) from
        gridSumZ_congr d _ _ (fun i hi => by rw [heig i hi]; ring_intZ),
        gridSumZ_mul_left]
  have hineq := colored_rayleigh_ge v
  rw [hL, hR] at hineq
  have hCD : massGap * (lam * gridSumZ d (fun i => v i * v i))
      ≤ lam * (lam * gridSumZ d (fun i => v i * v i)) := by
    rw [show lam * (lam * gridSumZ d (fun i => v i * v i))
          = lam * lam * gridSumZ d (fun i => v i * v i) from by ring_intZ]
    exact hineq
  exact lichnerowicz_abstract hv hlam hCD

/-! ## §3 — Master statement -/

/-- ★★★★★ **Yang–Mills colored-mode positivity — 213 confinement brick.**  ∅-axiom.

    (i) The SOS certificate `Δ₀² − massGap·Δ₀ = 2·(top)² + 6·(temp)²`;
    (ii) colored positivity `⟨Δ₀f,Δ₀f⟩ ≥ massGap·⟨Δ₀f,f⟩` for every `f`;
    (iii) every colored eigenfunction has eigenvalue `≥ massGap = 4`.

    The spectral face of confinement: colored modes are gapped, the singlet vacuum is the
    unique zero-energy state.  The continuum area-law face stays open (no embedding, no
    enclosed area on the abstract `K_{3,2}` complex — `yang_mills_confinement.md`). -/
theorem colored_confinement_master :
    (∀ f : Nat → Int,
      gridSumZ d (fun i => mulVec d lap f i * mulVec d lap f i)
        - massGap * gridSumZ d (fun i => mulVec d lap f i * f i)
      = 2 * ((2 * (f 0 + f 1 + f 2) - 3 * (f 3 + f 4))
              * (2 * (f 0 + f 1 + f 2) - 3 * (f 3 + f 4)))
        + 6 * ((f 3 - f 4) * (f 3 - f 4)))
    ∧ (∀ f : Nat → Int,
        massGap * gridSumZ d (fun i => mulVec d lap f i * f i)
          ≤ gridSumZ d (fun i => mulVec d lap f i * mulVec d lap f i))
    ∧ (∀ (lam : Int) (v : Nat → Int), 0 < lam →
        0 < gridSumZ d (fun i => v i * v i) → IsEigenpair lam v → massGap ≤ lam) :=
  ⟨colored_form_identity, colored_rayleigh_ge, colored_gap⟩

end E213.Lib.Physics.YangMills.ColoredGap
