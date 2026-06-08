import E213.Meta.Int213
import E213.Meta.Int213.Bound
import E213.Meta.Int213.PolyIntMTactic
import E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci

/-!
# Bakry–Émery curvature of the complete bipartite graph `K_{a,b}` — the DRLT core (∅-axiom)

The general bipartite case `K_{a,b}` (`a = |A|`, `b = |B|`), of which `K_{3,2}` is the
repo's central lattice.  Curvature is read at an `A`-vertex (the `B`-vertex case is the
`a ↔ b` mirror).  Unlike the star `K_{1,b}` (`BakryEmery.lean` §4, `a = 1`, second shell
empty), `a ≥ 2` has a genuine **second shell**: the centre `v ∈ A` → its `b` neighbours
in `B` → their `a−1` *other* `A`-neighbours.

Working **relative to the centre** (translation-invariance of `Γ`/`Γ₂`) eliminates the
centre value: `x j = w_j − c` are the `B`-values, `y i = u_i − c` the other-`A` values
(`nb = b` of the former, `na = a−1` of the latter).  Then the centre Laplacian
`X = Σ x_j`, `Γ(centre) = Σ x_j²`, a `B`-vertex `w_j` reads `Lf(w_j) = Y − a·x_j`
(`Y = Σ y_i`, `a = na+1`), and the closed form is

  `gamma2 = (3a−b)·gammaC + 2X² + b·Q_y − 4XY`        (`Q_y = Σ y_i²`)   — `kab_bochner`.

Completing the square over the **free second shell** `y` (`kab_shell_sos`):

  `b·gamma2 = b(3a−b)·gammaC + (2b−4a+4)·X² + Σ_i (b·y_i − 2X)²`,

the last term a manifest SOS.  Hence:

  · `b ≥ 2a−2` (`2b−4a+4 ≥ 0`): `b·gamma2 ≥ b(3a−b)·gammaC` directly — `CD((3a−b)/2, ∞)`
    with **no** Cauchy–Schwarz (`kab_cd_wide`);
  · `b ≤ 2a−2`: the `X²` coefficient is negative, needing the discrete Cauchy–Schwarz
    `X² ≤ b·gammaC` to reach `CD((b−a+4)/2, ∞)`.

Overall the `A`-vertex curvature is `min(3a−b, b−a+4)/2`, reducing to the star's `3−b`
at `a = 1` (`BakryEmery.lean` §4).  All `∅`-axiom.
-/

namespace E213.Lib.Math.Geometry.GeometrizationConjecture.BakryEmeryBipartite

open E213.Meta.Int213
open E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci (gridSumZ
  gridSumZ_succ gridSumZ_congr gridSumZ_add gridSumZ_sub gridSumZ_mul_left gridSumZ_const
  gridSumZ_nonneg)

/-! ## §1 — the two-shell Γ-calculus at an `A`-vertex (centred coordinates) -/

/-- Centre Laplacian `X = Σ_{j<nb} x_j` (the `B`-values relative to the centre). -/
def kabLapC (nb : Nat) (x : Nat → Int) : Int := gridSumZ nb x

/-- Centre carré du champ (scaled `2Γ`) `Σ_{j<nb} x_j²`. -/
def kabGammaC (nb : Nat) (x : Nat → Int) : Int := gridSumZ nb (fun j => x j * x j)

/-- Laplacian at a `B`-vertex `w_j`: `Lf(w_j) = Y − a·x_j` (`a = na+1` neighbours: the
    centre + the `na` other `A`-vertices), `Y = Σ y_i`. -/
def kabLapB (na : Nat) (x y : Nat → Int) (j : Nat) : Int :=
  gridSumZ na y - ((na : Int) + 1) * x j

/-- Carré du champ (scaled `2Γ`) at a `B`-vertex `w_j`: centre edge `x_j²` plus the
    other-`A` edges `Σ_i (y_i − x_j)²`. -/
def kabGammaB (na : Nat) (x y : Nat → Int) (j : Nat) : Int :=
  x j * x j + gridSumZ na (fun i => (y i - x j) * (y i - x j))

/-- Iterated carré du champ (scaled `4Γ₂`) at the centre `A`-vertex. -/
def kabGamma2C (na nb : Nat) (x y : Nat → Int) : Int :=
  gridSumZ nb (fun j => kabGammaB na x y j - kabGammaC nb x)
    - 2 * gridSumZ nb (fun j => x j * (kabLapB na x y j - kabLapC nb x))

/-- Per-`B`-vertex expansion of the other-`A` carré du champ:
    `Σ_i (y_i − x_j)² = Σ_i y_i² − 2 x_j·Y + na·x_j²`. -/
theorem kab_inner (na : Nat) (x y : Nat → Int) (j : Nat) :
    gridSumZ na (fun i => (y i - x j) * (y i - x j))
      = gridSumZ na (fun i => y i * y i) - 2 * x j * gridSumZ na y
        + (na : Int) * (x j * x j) := by
  rw [show gridSumZ na (fun i => (y i - x j) * (y i - x j))
        = gridSumZ na (fun i => y i * y i - 2 * x j * y i + x j * x j) from
      gridSumZ_congr na _ _ (fun i _ => by ring_intZ),
      gridSumZ_add, gridSumZ_sub, gridSumZ_mul_left, gridSumZ_const]

/-! ## §2 — the two-shell Bochner closed form -/

/-- Piece A: `Σ_j (Γ(w_j) − Γ(centre)) = nb·Q_y − 2·X·Y + (1 + na − nb)·gammaC`. -/
theorem kab_pieceA (na nb : Nat) (x y : Nat → Int) :
    gridSumZ nb (fun j => kabGammaB na x y j - kabGammaC nb x)
      = (nb : Int) * gridSumZ na (fun i => y i * y i)
        - 2 * gridSumZ nb x * gridSumZ na y
        + (1 + (na : Int) - (nb : Int)) * gridSumZ nb (fun j => x j * x j) := by
  rw [show gridSumZ nb (fun j => kabGammaB na x y j - kabGammaC nb x)
        = gridSumZ nb (fun j =>
            (gridSumZ na (fun i => y i * y i) - 2 * gridSumZ na y * x j
              + ((na : Int) + 1) * (x j * x j))
            - gridSumZ nb (fun j => x j * x j)) from
      gridSumZ_congr nb _ _ (fun j _ => by
        unfold kabGammaB kabGammaC
        rw [kab_inner]; ring_intZ),
      gridSumZ_sub, gridSumZ_add, gridSumZ_sub, gridSumZ_const, gridSumZ_const,
      gridSumZ_mul_left, gridSumZ_mul_left]
  ring_intZ

/-- Piece B: `Σ_j x_j·(Lf(w_j) − Lf(centre)) = X·Y − X² − (na+1)·gammaC`. -/
theorem kab_pieceB (na nb : Nat) (x y : Nat → Int) :
    gridSumZ nb (fun j => x j * (kabLapB na x y j - kabLapC nb x))
      = gridSumZ nb x * gridSumZ na y - gridSumZ nb x * gridSumZ nb x
        - ((na : Int) + 1) * gridSumZ nb (fun j => x j * x j) := by
  rw [show gridSumZ nb (fun j => x j * (kabLapB na x y j - kabLapC nb x))
        = gridSumZ nb (fun j => gridSumZ na y * x j
            - ((na : Int) + 1) * (x j * x j) - gridSumZ nb x * x j) from
      gridSumZ_congr nb _ _ (fun j _ => by unfold kabLapB kabLapC; ring_intZ),
      gridSumZ_sub, gridSumZ_sub, gridSumZ_mul_left, gridSumZ_mul_left, gridSumZ_mul_left]
  ring_intZ

/-- ★★★★★ **Two-shell Bochner closed form for `K_{a,b}` at an `A`-vertex** (`a = na+1`,
    `b = nb`):

      `gamma2 = (3a − b)·gammaC + 2·X² + b·Q_y − 4·X·Y`.

    The clean `c`-free form (centred coordinates); `Q_y = Σ y_i²`, `X = Σ x_j`,
    `Y = Σ y_i`.  Reduces to the star `BakryEmery` §4 at `na = 0` (`Q_y = Y = 0`,
    `gamma2 = (3 − b)·gammaC + 2X²`).  Pure `gridSumZ` linearity + `ring_intZ`. -/
theorem kab_bochner (na nb : Nat) (x y : Nat → Int) :
    kabGamma2C na nb x y
      = (3 * (na : Int) + 3 - (nb : Int)) * kabGammaC nb x
        + 2 * (kabLapC nb x * kabLapC nb x)
        + (nb : Int) * gridSumZ na (fun i => y i * y i)
        - 4 * (kabLapC nb x * gridSumZ na y) := by
  unfold kabGamma2C
  rw [kab_pieceA, kab_pieceB]
  unfold kabGammaC kabLapC
  ring_intZ

/-! ## §3 — completing the square over the free second shell -/

/-- The second-shell sum of squares `Σ_i (b·y_i − 2X)²` (the `Γ₂` minimum over the free
    other-`A` values is at `b·y_i = 2X`). -/
def kabShellGap (na nb : Nat) (x y : Nat → Int) : Int :=
  gridSumZ na (fun i => ((nb : Int) * y i - 2 * kabLapC nb x)
                        * ((nb : Int) * y i - 2 * kabLapC nb x))

/-- `kabShellGap ≥ 0` — a grid sum of squares. -/
theorem kabShellGap_nonneg (na nb : Nat) (x y : Nat → Int) : 0 ≤ kabShellGap na nb x y :=
  gridSumZ_nonneg na _ (fun _ _ => int_sq_nonneg _)

/-- ★★★★★ **Second-shell completion of square.**  Clearing the `1/b` of the second-shell
    minimization:

      `b·gamma2 = b(3a−b)·gammaC + (2b−4a+4)·X² + Σ_i (b·y_i − 2X)²`.

    The last term is the manifest SOS; its minimum `0` (at `b·y_i = 2X`) is the worst
    case over the free second shell, so the curvature bound is governed by the
    `X²`-coefficient `2b−4a+4`. -/
theorem kab_shell_sos (na nb : Nat) (x y : Nat → Int) :
    (nb : Int) * kabGamma2C na nb x y
      = (nb : Int) * (3 * (na : Int) + 3 - (nb : Int)) * kabGammaC nb x
        + (2 * (nb : Int) - 4 * (na : Int)) * (kabLapC nb x * kabLapC nb x)
        + kabShellGap na nb x y := by
  have hShell : kabShellGap na nb x y
      = (nb : Int) * (nb : Int) * gridSumZ na (fun i => y i * y i)
        - 4 * (nb : Int) * kabLapC nb x * gridSumZ na y
        + (na : Int) * (4 * (kabLapC nb x * kabLapC nb x)) := by
    unfold kabShellGap
    rw [show gridSumZ na (fun i => ((nb : Int) * y i - 2 * kabLapC nb x)
                                   * ((nb : Int) * y i - 2 * kabLapC nb x))
          = gridSumZ na (fun i => (nb : Int) * (nb : Int) * (y i * y i)
              - 4 * (nb : Int) * kabLapC nb x * y i
              + 4 * (kabLapC nb x * kabLapC nb x)) from
        gridSumZ_congr na _ _ (fun i _ => by ring_intZ),
        gridSumZ_add, gridSumZ_sub, gridSumZ_mul_left, gridSumZ_mul_left, gridSumZ_const]
  rw [hShell, kab_bochner]; ring_intZ

/-! ## §4 — the curvature-dimension bound (wide regime `b ≥ 2a−2`) -/

/-- ★★★★★ **`K_{a,b}` is `CD((3a−b)/2, ∞)` at an `A`-vertex when `b ≥ 2a−2`** (`b`-scaled:
    `b·gamma2 ≥ b(3a−b)·gammaC`).  In this "wide" regime the `X²`-coefficient `2b−4a+4 ≥ 0`,
    so the bound follows from `kab_shell_sos` with **no** Cauchy–Schwarz — both the
    `X²`-term and the shell SOS are non-negative.  (Narrow `b < 2a−2`, incl. the DRLT
    `K_{3,2}`, needs the discrete Cauchy–Schwarz `X² ≤ b·gammaC` — Phase 3b.)  At `a = 1`
    (`na = 0`) this is the star centre `CD((3−b)/2,∞)` (`BakryEmery` §4). -/
theorem kab_cd_wide (na nb : Nat) (x y : Nat → Int)
    (hwide : 2 * (na : Int) ≤ (nb : Int)) :
    (nb : Int) * (3 * (na : Int) + 3 - (nb : Int)) * kabGammaC nb x
      ≤ (nb : Int) * kabGamma2C na nb x y := by
  have hcoef : (0 : Int) ≤ 2 * (nb : Int) - 4 * (na : Int) := by
    have h := OrderMul.mul_le_mul_left_nonneg hwide 2 (by decide)
    rw [show (2 : Int) * (2 * (na : Int)) = 4 * (na : Int) from by ring_intZ] at h
    exact Order.le_zero_of_nonneg (Order.sub_nonneg_of_le h)
  rw [kab_shell_sos]
  apply Order.le_of_sub_nonneg
  rw [show (nb : Int) * (3 * (na : Int) + 3 - (nb : Int)) * kabGammaC nb x
        + (2 * (nb : Int) - 4 * (na : Int)) * (kabLapC nb x * kabLapC nb x)
        + kabShellGap na nb x y
        - (nb : Int) * (3 * (na : Int) + 3 - (nb : Int)) * kabGammaC nb x
        = (2 * (nb : Int) - 4 * (na : Int)) * (kabLapC nb x * kabLapC nb x)
          + kabShellGap na nb x y from by ring_intZ]
  have hX : (0 : Int) ≤ (2 * (nb : Int) - 4 * (na : Int)) * (kabLapC nb x * kabLapC nb x) := by
    have h := OrderMul.mul_le_mul_right_nonneg hcoef (kabLapC nb x * kabLapC nb x)
      (int_sq_nonneg _)
    rwa [zero_mul] at h
  exact Order.nonneg_of_le_zero (add_nonneg hX (kabShellGap_nonneg na nb x y))

/-! ## §5 — the narrow regime `b ≤ 2a−2` via discrete Cauchy–Schwarz -/

/-- ★★★★ **Discrete Cauchy–Schwarz** (power-mean): `(Σ a)² ≤ n·Σ a²`.  By induction; the
    step gap is `[n·Σ a² − (Σa)²]` (the inductive hypothesis) plus `Σ_j (a_j − aₙ)²`, a sum
    of squares (`kab_inner`).  Reusable. -/
theorem cauchy_schwarz_gridZ (n : Nat) (a : Nat → Int) :
    gridSumZ n a * gridSumZ n a ≤ (n : Int) * gridSumZ n (fun i => a i * a i) := by
  induction n with
  | zero => exact Order.le_refl _
  | succ m ih =>
    rw [gridSumZ_succ, gridSumZ_succ]
    apply Order.le_of_sub_nonneg
    have e : (((m + 1 : Nat)) : Int) * (gridSumZ m (fun i => a i * a i) + a m * a m)
            - (gridSumZ m a + a m) * (gridSumZ m a + a m)
          = ((m : Int) * gridSumZ m (fun i => a i * a i) - gridSumZ m a * gridSumZ m a)
            + gridSumZ m (fun i => (a i - a m) * (a i - a m)) := by
      have hcast : (((m + 1 : Nat)) : Int) = (m : Int) + 1 := rfl
      rw [hcast, kab_inner m a a m]; ring_intZ
    rw [e]
    exact Order.nonneg_of_le_zero (add_nonneg
      (Order.le_zero_of_nonneg (Order.sub_nonneg_of_le ih))
      (gridSumZ_nonneg m _ (fun _ _ => int_sq_nonneg _)))

/-- ★★★★★ **`K_{a,b}` is `CD((b−a+4)/2, ∞)` at an `A`-vertex when `b ≤ 2a−2`** (`b`-scaled:
    `b·gamma2 ≥ b(b−a+4)·gammaC`, `b−a+4 = nb−na+3`).  In this "narrow" regime the
    `X²`-coefficient `2b−4a+4 ≤ 0`; the difference `b·gamma2 − b(b−a+4)·gammaC` rearranges
    to `(4a−2b)·(b·gammaC − X²) + shellGap`, a product of two non-negatives (the discrete
    Cauchy–Schwarz `X² ≤ b·gammaC` gives `b·gammaC − X² ≥ 0`) plus the shell SOS.  Includes
    the DRLT core `K_{3,2}` (`a=3, b=2`: `CD(3/2, ∞)`).  Together with `kab_cd_wide` the
    `A`-vertex curvature is `min(3a−b, b−a+4)/2`. -/
theorem kab_cd_narrow (na nb : Nat) (x y : Nat → Int)
    (hnar : (nb : Int) ≤ 2 * (na : Int)) :
    (nb : Int) * ((nb : Int) - (na : Int) + 3) * kabGammaC nb x
      ≤ (nb : Int) * kabGamma2C na nb x y := by
  have hCS : kabLapC nb x * kabLapC nb x ≤ (nb : Int) * kabGammaC nb x :=
    cauchy_schwarz_gridZ nb x
  have hc : (0 : Int) ≤ 4 * (na : Int) - 2 * (nb : Int) := by
    have h := OrderMul.mul_le_mul_left_nonneg hnar 2 (by decide)
    rw [show (2 : Int) * (2 * (na : Int)) = 4 * (na : Int) from by ring_intZ] at h
    exact Order.le_zero_of_nonneg (Order.sub_nonneg_of_le h)
  have hprod : (0 : Int) ≤ (4 * (na : Int) - 2 * (nb : Int))
      * ((nb : Int) * kabGammaC nb x - kabLapC nb x * kabLapC nb x) := by
    have h2 : (0 : Int) ≤ (nb : Int) * kabGammaC nb x - kabLapC nb x * kabLapC nb x :=
      Order.le_zero_of_nonneg (Order.sub_nonneg_of_le hCS)
    have h := OrderMul.mul_le_mul_right_nonneg hc
      ((nb : Int) * kabGammaC nb x - kabLapC nb x * kabLapC nb x) h2
    rwa [zero_mul] at h
  rw [kab_shell_sos]
  apply Order.le_of_sub_nonneg
  rw [show (nb : Int) * (3 * (na : Int) + 3 - (nb : Int)) * kabGammaC nb x
        + (2 * (nb : Int) - 4 * (na : Int)) * (kabLapC nb x * kabLapC nb x)
        + kabShellGap na nb x y
        - (nb : Int) * ((nb : Int) - (na : Int) + 3) * kabGammaC nb x
        = (4 * (na : Int) - 2 * (nb : Int))
            * ((nb : Int) * kabGammaC nb x - kabLapC nb x * kabLapC nb x)
          + kabShellGap na nb x y from by ring_intZ]
  exact Order.nonneg_of_le_zero (add_nonneg hprod (kabShellGap_nonneg na nb x y))

end E213.Lib.Math.Geometry.GeometrizationConjecture.BakryEmeryBipartite
