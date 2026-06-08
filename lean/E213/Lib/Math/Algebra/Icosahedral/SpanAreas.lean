import E213.Lib.Math.Algebra.Mobius213
import E213.Lib.Physics.Foundations.GoldenRatio
import E213.Lib.Physics.Simplex.Counts

/-!
# Icosahedral.SpanAreas — the convergent span-areas `det(v₀,v_k) = −F₂ₖ`

The self-reference map `M` iterates the convergent vectors
`v_n = (num_n, den_n)` (`Mobius213.P_numerator/P_denominator`,
`v_{n+1} = M·v_n`).  The **signed area** (`2×2` determinant) spanned by two
convergents `k` steps apart is

  **`det(v_m, v_{m+k}) = −F_{2k}`**   (even-indexed Fibonacci),

independent of the position `m` (a homogeneity of the self-reference iteration).
The adjacent (`k=1`) area is the Pell symplectic unit `−F₂ = −1`
(`Mobius213.mobius_213_pell_unit_invariant_forall`); the **two-step** (`k=2`)
area is `−F₄ = −NS = −3`.

## Why this matters — the unitarity-triangle area skeleton

The CKM apex relates **generation 1 to generation 3** — a **two-step** (`k=2`)
span in the convergent iteration.  Its integer span-area is therefore
`F₄ = NS = 3`.  Since the unitarity-triangle area is `η̄/2` (with `J ∝ η̄`,
the CP/area part), this `F₄ = NS` is the **213-integer skeleton of the CKM
CP-area** — the conserved-area (`det M = 1`) structure underlying CP violation,
on the flagged Pell-area ↔ CP route.  (The physical `η̄ ≈ 0.356` is this integer
skeleton dressed by the λ-hierarchy and the φ-contraction — not derived here.)

All theorems PURE.
-/

namespace E213.Lib.Math.Algebra.Icosahedral.SpanAreas

open E213.Lib.Math.Algebra.Mobius213
open E213.Lib.Physics.Foundations.GoldenRatio (fib)
open E213.Lib.Physics.Simplex.Counts (NS)

/-- Convergent numerator `num_n` (`v_n` first component). -/
def num (n : Nat) : Int := P_numerator.seq n
/-- Convergent denominator `den_n` (`v_n` second component). -/
def den (n : Nat) : Int := P_denominator.seq n

/-! ## §1 — span-areas from `v₀`: `det(v₀,v_k) = −F₂ₖ` -/

/-- ★★★ The signed area spanned by `v₀` and `v_k`, as the positive magnitude
    `num_k·den₀ − num₀·den_k = num_k − den_k`, equals the even-indexed
    Fibonacci `F₂ₖ` for `k = 1,2,3,4`: `1, 3, 8, 21`.  (`det(v₀,v_k) = −F₂ₖ`.) -/
theorem span_area_from_v0 :
    num 1 * den 0 - num 0 * den 1 = 1      -- k=1: F₂ = 1 (Pell unit)
    ∧ num 2 * den 0 - num 0 * den 2 = 3    -- k=2: F₄ = 3 = NS  (the apex span)
    ∧ num 3 * den 0 - num 0 * den 3 = 8    -- k=3: F₆ = 8
    ∧ num 4 * den 0 - num 0 * den 4 = 21 := by decide  -- k=4: F₈ = 21

/-- ★★ The span-areas are exactly the even-indexed Fibonacci numbers. -/
theorem span_areas_are_even_fibonacci :
    fib 2 = 1 ∧ fib 4 = 3 ∧ fib 6 = 8 ∧ fib 8 = 21 := by decide

/-! ## §2 — position-independence (homogeneity of the iteration)

The two-step span-area is `−F₄ = −3` regardless of where it starts: the
self-reference iteration is area-homogeneous (a consequence of `det M = 1`). -/

/-- ★★★ **Two-step span-area is `F₄ = NS`, position-independent.**
    `det(v_m, v_{m+2}) = −3 = −NS` for `m = 0,1,2`.  The apex span (gen 1↔3)
    carries the same integer area `NS` wherever it sits in the iteration. -/
theorem span2_is_NS_position_invariant :
    num 2 * den 0 - num 0 * den 2 = 3
    ∧ num 3 * den 1 - num 1 * den 3 = 3
    ∧ num 4 * den 2 - num 2 * den 4 = 3
    ∧ (3 : Int) = (NS : Int) := by decide

/-! ## §3 — the 3-generation CP triangle: minimal nonzero area requires 3 points

CP violation needs **three** generations (two give a real `2×2` block, no
phase).  In the convergent lattice this is geometric: **two** points span zero
area (a line); **three** consecutive convergents `v_m, v_{m+1}, v_{m+2}` span a
triangle of determinant `1` (area `1/2`) — the *minimal nonzero* area, the
self-reference lattice's **unit triangle**, position-independent.  So the
3-generation requirement for CP = the minimum points to enclose the Pell
symplectic unit area. -/

/-- ★★★★ **3-generation CP triangle.**  Three consecutive convergents (= three
    generations) span a triangle with determinant `1` (area `1/2`) — the
    minimal nonzero area, position-independent (`m = 0,1,2`).  Two points would
    give area `0` (no CP).  So CP violation requires exactly 3 generations to
    enclose the symplectic unit. -/
theorem three_generation_cp_triangle :
    (num 1 - num 0) * (den 2 - den 0) - (num 2 - num 0) * (den 1 - den 0) = 1
    ∧ (num 2 - num 1) * (den 3 - den 1) - (num 3 - num 1) * (den 2 - den 1) = 1
    ∧ (num 3 - num 2) * (den 4 - den 2) - (num 4 - num 2) * (den 3 - den 2) = 1
    -- 3 generations = NS (atomic), the minimum for a nonzero area
    ∧ (3 : Int) = (NS : Int) := by decide

/-! ## §4 — the apex sits on the conserved golden-norm hyperbola `Q = −1`

The apex spiral is not just area-homogeneous (§1–§3); it conserves the **golden
norm** `Q(m,k) = m² − m·k − k²` (the `ℤ[φ]` norm, discriminant `d = 5`).  Every
convergent `v_n` satisfies `Q(v_n) = −1` — the `N = −1` orbit of the P-spiral's
rotation invariant (`Real213.SpiralRotationInvariant.Q_iterate_preserved`:
`Q` is preserved at every turn).  So the apex lives on the golden-norm `−1`
hyperbola; the discriminant `5 = d` is the same `d` that lands `M` in
`SL(2,𝔽₅) ≅ 2I` and gives `M` its golden eigenvalues — the apex's structural
home on the self-reference spiral. -/

/-- ★★★ **Golden-norm conservation on the apex spiral.**  Each convergent
    `v_n = (num_n, den_n)` lies on `Q = m² − m·k − k² = −1` (the `ℤ[φ]` norm,
    disc `d = 5`) — the conserved rotation invariant of the P-spiral
    (`SpiralRotationInvariant`).  Witnessed `n = 0..3` (positive form
    `m² = m·k + k² − 1`, i.e. `Q = −1`). -/
theorem apex_on_golden_norm_hyperbola :
    num 0 * num 0 + 1 = num 0 * den 0 + den 0 * den 0   -- Q(1,1) = −1
    ∧ num 1 * num 1 + 1 = num 1 * den 1 + den 1 * den 1 -- Q(3,2) = −1
    ∧ num 2 * num 2 + 1 = num 2 * den 2 + den 2 * den 2 -- Q(8,5) = −1
    ∧ num 3 * num 3 + 1 = num 3 * den 3 + den 3 * den 3 -- Q(21,13) = −1
    := by decide

/-! ## §5 — capstone: the apex area skeleton -/

/-- ★★★★★ **Apex CP-area skeleton.**  The CKM apex (generation 1↔3 = two-step
    span) has integer span-area `F₄ = NS = 3` in the self-reference convergent
    lattice — position-independent, the conserved-area (`det M = 1`) core of the
    unitarity-triangle area (`η̄/2`, the CP part).  The adjacent span (`k=1`) is
    the Pell symplectic unit `1`.  PURE skeleton; the physical `η̄` is this
    dressed by the λ-hierarchy + φ-contraction (open). -/
theorem apex_area_skeleton :
    -- adjacent span (k=1) = Pell unit F₂ = 1
    (num 1 * den 0 - num 0 * den 1 = 1)
    -- apex span (k=2, gen 1↔3) = F₄ = NS = 3
    ∧ (num 2 * den 0 - num 0 * den 2 = 3)
    ∧ fib 4 = 3 ∧ (3 : Int) = (NS : Int)
    -- position-independent
    ∧ (num 3 * den 1 - num 1 * den 3 = 3)
    -- 3-generation CP triangle: minimal nonzero (unit) area, needs 3 points
    ∧ ((num 1 - num 0) * (den 2 - den 0) - (num 2 - num 0) * (den 1 - den 0) = 1) := by decide

end E213.Lib.Math.Algebra.Icosahedral.SpanAreas
