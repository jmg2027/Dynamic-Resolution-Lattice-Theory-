import E213.Meta.Int213
import E213.Meta.Int213.Bound
import E213.Meta.Int213.PolyIntMTactic

/-!
# Discrete Bakry–Émery Γ-calculus + the Bochner identity — A6 core, rung 6 (∅-axiom)

The fourth curvature frame (after Forman `DiscreteRicci`, Gauss–Bonnet
`DiscreteGaussBonnet`, Ollivier `OllivierRicci`): **Bakry–Émery** curvature via the
carré-du-champ iteration — the discrete Bochner formula.  This is the algebraic
heart of the smooth Bochner identity `½Δ|∇f|² = |Hess f|² + Ric(∇f,∇f)` made into a
finite polynomial identity over `ℤ`, so the curvature lower bound `CD(K,N)` is a
sum-of-squares fact, not a tensor computation.

**The Γ-calculus.**  For the graph Laplacian `Lf(x) = Σ_{y∼x}(f(y)−f(x))`:

  * carré du champ `Γ(f)(x) = ½ Σ_{y∼x}(f(y)−f(x))²`;
  * iterated `Γ₂(f)(x) = ½ L(Γ f)(x) − Γ(f, Lf)(x)`.

`CD(K,N)` (Bakry–Émery curvature `≥ K`, dimension `≤ N`): `Γ₂(f) ≥ K·Γ(f) +
(1/N)(Lf)²`.  Everything below is scaled to clear denominators (`gamma… = 2Γ`,
`gamma2… = 4Γ₂`), so the operators are integer polynomials in the local stencil and
the identities are `ring_intZ`.

**Two curvatures, matching the Ollivier trichotomy.**

  * the flat line / large cycle is `CD(0,2)` — the Bochner `Γ₂` is an exact
    weighted sum of squared Laplacians (`bochner_line`), so `Γ₂ ≥ ½(Lf)²` and
    `Γ₂ ≥ 0`: curvature `0`, matching Forman/Ollivier/Gauss–Bonnet flat (a cycle is
    `2`-regular, `vertexCurv = 0`);
  * the triangle `C₃` is `CD(5/2, ∞)` — `Γ₂(f) = (5/2)Γ(f) + ½(f₁−f₂)²`
    (`bochner_triangle`), curvature `5/2 > 0`, matching Ollivier `κ = ½ > 0` and
    Forman `+2`: the complete graph `K₃` value `(n+2)/2`.

Stencil-parametrised (à la `ConformalCurvature`): no index arithmetic, the operators
take the neighbourhood values directly.  All zero-axiom.
-/

namespace E213.Lib.Math.Geometry.GeometrizationConjecture.BakryEmery

open E213.Meta.Int213

/-! ## §1 — the line `ℤ` (or large cycle): local Γ-calculus on a radius-2 stencil

At a vertex `x` with neighbourhood values `a = f(x−2)`, `b = f(x−1)`, `c = f(x)`,
`d = f(x+1)`, `e = f(x+2)`.  Each vertex `v` reads `lapL (left v) (val v) (right v)`. -/

/-- Graph Laplacian at a vertex of value `c` with neighbours `l, r`: `Lf = l + r − 2c`. -/
def lapL (l c r : Int) : Int := l + r - 2 * c

/-- Carré du champ (scaled `2Γ`) at a vertex of value `c` with neighbours `l, r`:
    `2Γ(f) = (l−c)² + (r−c)²`. -/
def gammaL (l c r : Int) : Int := (l - c) * (l - c) + (r - c) * (r - c)

/-- Iterated carré du champ (scaled `4Γ₂`) at the centre `c` of the stencil
    `a,b,c,d,e`: `4Γ₂ = L(2Γ)(x) − 2·(2Γ)(f, Lf)(x)`.  The two neighbours of `x` are
    `b` (left) and `d` (right); `Γ` at them reaches `a` and `e`. -/
def gamma2L (a b c d e : Int) : Int :=
  (gammaL a b c + gammaL c d e - 2 * gammaL b c d)
    - 2 * ((d - c) * (lapL c d e - lapL b c d)
         + (b - c) * (lapL a b c - lapL b c d))

/-- ★★★★★ **Discrete Bochner identity (flat line).**  The iterated carré du champ is
    an exact weighted sum of squared Laplacians:

      `4Γ₂(f)(x) = (Lf(x−1))² + 2·(Lf(x))² + (Lf(x+1))²`.

    The discrete incarnation of `½Δ|∇f|² = |Hess f|² + Ric(∇f,∇f)` with `Ric = 0`
    (flat): there is no negative curvature term, only squares — so the line has
    Bakry–Émery curvature `0`.  Pure `ring_intZ`. -/
theorem bochner_line (a b c d e : Int) :
    gamma2L a b c d e
      = lapL a b c * lapL a b c
        + 2 * (lapL b c d * lapL b c d)
        + lapL c d e * lapL c d e := by
  unfold gamma2L gammaL lapL
  ring_intZ

/-- ★★★★ **`Γ₂ ≥ 0` on the line** (the Bochner sum-of-squares).  Immediate from
    `bochner_line`: a sum of squares is non-negative. -/
theorem gamma2_line_nonneg (a b c d e : Int) : 0 ≤ gamma2L a b c d e := by
  rw [bochner_line]
  have hm : (0 : Int) ≤ 2 * (lapL b c d * lapL b c d) := by
    rw [show (2 : Int) * (lapL b c d * lapL b c d)
          = lapL b c d * lapL b c d + lapL b c d * lapL b c d from by ring_intZ]
    exact add_nonneg (int_sq_nonneg _) (int_sq_nonneg _)
  exact add_nonneg (add_nonneg (int_sq_nonneg _) hm) (int_sq_nonneg _)

/-- ★★★★★ **`CD(0,2)` on the line.**  From the Bochner identity `Γ₂ = ½(Lf)² +
    ¼(Lf(x−1))² + ¼(Lf(x+1))² ≥ ½(Lf)²`, i.e. (scaled) `4Γ₂ ≥ 2·(Lf)²`: the discrete
    line satisfies the curvature-dimension condition with curvature `0`, dimension
    `2`. -/
theorem cd_0_2_line (a b c d e : Int) :
    2 * (lapL b c d * lapL b c d) ≤ gamma2L a b c d e := by
  rw [bochner_line]
  apply Order.le_of_sub_nonneg
  rw [show (lapL a b c * lapL a b c + 2 * (lapL b c d * lapL b c d)
            + lapL c d e * lapL c d e) - 2 * (lapL b c d * lapL b c d)
        = lapL a b c * lapL a b c + lapL c d e * lapL c d e from by ring_intZ]
  exact Order.nonneg_of_le_zero (add_nonneg (int_sq_nonneg _) (int_sq_nonneg _))

/-! ## §2 — the triangle `C₃` (`= K₃`): positive Bakry–Émery curvature

Vertices `0,1,2` with values `f0,f1,f2`; every vertex is adjacent to the other two
(`C₃ = K₃`).  By symmetry the curvature is read at vertex `0`.  Here the radius-2
neighbourhood wraps (`x±2 ≡ x∓1` mod `3`), which is exactly what turns the flat
`Γ₂ = SOS` into a positive-curvature `Γ₂ = (5/2)Γ + SOS`. -/

/-- Triangle Laplacian at a vertex of value `a` with the other two vertices `b, c`. -/
def lapTri (a b c : Int) : Int := b + c - 2 * a

/-- Triangle carré du champ (scaled `2Γ`) at vertex value `a`, neighbours `b, c`. -/
def gammaTri (a b c : Int) : Int := (b - a) * (b - a) + (c - a) * (c - a)

/-- Iterated carré du champ (scaled `4Γ₂`) at vertex `0` of the triangle `(f0,f1,f2)`.
    Vertex `0`'s neighbours are `1,2`; `Γ`/`L` at vertex `1` read `(f1; f2,f0)` and at
    vertex `2` read `(f2; f0,f1)` (cyclic). -/
def gamma2Tri (f0 f1 f2 : Int) : Int :=
  (gammaTri f1 f2 f0 + gammaTri f2 f0 f1 - 2 * gammaTri f0 f1 f2)
    - 2 * ((f1 - f0) * (lapTri f1 f2 f0 - lapTri f0 f1 f2)
         + (f2 - f0) * (lapTri f2 f0 f1 - lapTri f0 f1 f2))

/-- ★★★★★ **Discrete Bochner identity (triangle).**  At a vertex of `C₃`:

      `4Γ₂(f) = 5·(2Γ(f)) + 2·(f₁−f₂)²`,  i.e.  `Γ₂(f) = (5/2)·Γ(f) + ½(f₁−f₂)²`.

    The positive curvature term `(5/2)Γ` is forced by the wrapped neighbourhood — the
    discrete `Ric = (5/2) > 0`.  Matches the complete-graph `K₃` Bakry–Émery curvature
    `(n+2)/2 = 5/2`.  Pure `ring_intZ`. -/
theorem bochner_triangle (f0 f1 f2 : Int) :
    gamma2Tri f0 f1 f2
      = 5 * gammaTri f0 f1 f2 + 2 * ((f1 - f2) * (f1 - f2)) := by
  unfold gamma2Tri gammaTri lapTri
  ring_intZ

/-- ★★★★★ **`CD(5/2, ∞)` for the triangle** (positive Bakry–Émery curvature).  From
    `bochner_triangle`, `4Γ₂(f) = 5·(2Γ(f)) + 2(f₁−f₂)² ≥ 5·(2Γ(f))`, i.e.
    `Γ₂(f) ≥ (5/2)Γ(f)`: the triangle is positively curved (`K = 5/2`), the
    Bakry–Émery counterpart of Ollivier `κ = ½ > 0` and Forman `+2`. -/
theorem cd_triangle (f0 f1 f2 : Int) :
    5 * gammaTri f0 f1 f2 ≤ gamma2Tri f0 f1 f2 := by
  rw [bochner_triangle]
  apply Order.le_of_sub_nonneg
  rw [show (5 * gammaTri f0 f1 f2 + 2 * ((f1 - f2) * (f1 - f2)))
          - 5 * gammaTri f0 f1 f2 = 2 * ((f1 - f2) * (f1 - f2)) from by ring_intZ]
  rw [show (2 : Int) * ((f1 - f2) * (f1 - f2))
        = (f1 - f2) * (f1 - f2) + (f1 - f2) * (f1 - f2) from by ring_intZ]
  exact Order.nonneg_of_le_zero (add_nonneg (int_sq_nonneg _) (int_sq_nonneg _))

/-- `gammaTri ≥ 0` (the carré du champ is a sum of squares) — so `CD(5/2,∞)` is a
    genuine positive lower bound, not vacuous. -/
theorem gammaTri_nonneg (f0 f1 f2 : Int) : 0 ≤ gammaTri f0 f1 f2 := by
  unfold gammaTri
  exact add_nonneg (int_sq_nonneg _) (int_sq_nonneg _)

end E213.Lib.Math.Geometry.GeometrizationConjecture.BakryEmery
