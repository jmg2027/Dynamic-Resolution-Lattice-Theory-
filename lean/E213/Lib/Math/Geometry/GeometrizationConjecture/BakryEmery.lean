import E213.Meta.Int213
import E213.Meta.Int213.Bound
import E213.Meta.Int213.PolyIntMTactic
import E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci

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
open E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci (gridSumZ
  gridSumZ_succ gridSumZ_congr gridSumZ_add gridSumZ_sub gridSumZ_mul_left
  gridSumZ_const gridSumZ_nonneg gridSumZ_zero_fn)

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

/-! ## §3 — the complete graph `K_m` for general `m`: `CD((m+2)/2, ∞)`

The triangle `K₃` of §2 is the `m = 3` case of the complete graph `K_m`; this
section discharges the whole family at once, parametric in the vertex count.
Model `K_m` as a **centre vertex** (value `c`) joined to `k = m − 1` **neighbour
vertices** (values `b 0, …, b (k−1)`), every pair of which is also adjacent.  This
"centre + `k` neighbours" presentation keeps the centre value `c` a single
variable and the neighbour sum a clean `gridSumZ k`; crucially it makes the
positive-curvature term a **full double sum of squared differences** (the diagonal
`(b j − b j)² = 0` vanishes on its own, so no index has to be excluded — the wall
that the §2 hand computation sidestepped only for `m = 3`).

The Γ-calculus at the centre, all scaled (`gammaC… = 2Γ`, `gamma2C… = 4Γ₂`):

  * Laplacian `lapC = Σ_j (b j − c)` (= `B − k·c`, `B = Σ b`);
  * carré du champ `gammaC = Σ_j (b j − c)²`;
  * a neighbour `j` is adjacent to the centre **and** every other neighbour, so its
    Laplacian/`Γ` read `(c − b j)` together with `Σ_{j'}(b j' − b j)`;
  * `gamma2C = Σ_j (gammaNbr j − gammaC) − 2 Σ_j (b j − c)(lapNbr j − lapC)`.

The closed form (`bochner_complete`) is `gamma2C = (k+3)·gammaC + sosGap`, where
`sosGap = Σ_j Σ_{j'} (b j' − b j)² ≥ 0` is the manifest sum of squares — the exact
generalization of §2's `bochner_triangle` `4Γ₂ = 5·(2Γ) + 2(f₁−f₂)²` (`m = 3`,
`k = 2`: `k+3 = 5` and `sosGap = 2(b₀−b₁)²`).  Hence `gamma2C ≥ (k+3)·gammaC`, i.e.
`4Γ₂ ≥ (m+2)·2Γ` ⟺ `Γ₂ ≥ ((m+2)/2)·Γ`: the complete graph `K_m` is
`CD((m+2)/2, ∞)`, the textbook Bakry–Émery curvature of `K_m`. -/

/-- Centre Laplacian of `K_m`: `Σ_{j<k} (b j − c)`. -/
def lapC (k : Nat) (b : Nat → Int) (c : Int) : Int :=
  gridSumZ k (fun j => b j - c)

/-- Centre carré du champ (scaled `2Γ`): `Σ_{j<k} (b j − c)²`. -/
def gammaC (k : Nat) (b : Nat → Int) (c : Int) : Int :=
  gridSumZ k (fun j => (b j - c) * (b j - c))

/-- Laplacian at neighbour `j`: the centre edge `(c − b j)` plus the edges to the
    other neighbours `Σ_{j'<k} (b j' − b j)`. -/
def lapNbr (k : Nat) (b : Nat → Int) (c : Int) (j : Nat) : Int :=
  (c - b j) + gridSumZ k (fun j' => b j' - b j)

/-- Carré du champ (scaled `2Γ`) at neighbour `j`: centre edge squared plus the
    other-neighbour edges squared. -/
def gammaNbr (k : Nat) (b : Nat → Int) (c : Int) (j : Nat) : Int :=
  (c - b j) * (c - b j) + gridSumZ k (fun j' => (b j' - b j) * (b j' - b j))

/-- Iterated carré du champ (scaled `4Γ₂`) at the centre. -/
def gamma2C (k : Nat) (b : Nat → Int) (c : Int) : Int :=
  gridSumZ k (fun j => gammaNbr k b c j - gammaC k b c)
    - 2 * gridSumZ k (fun j => (b j - c) * (lapNbr k b c j - lapC k b c))

/-- The positive-curvature sum-of-squares term: `Σ_{j<k} Σ_{j'<k} (b j' − b j)²`. -/
def sosGap (k : Nat) (b : Nat → Int) : Int :=
  gridSumZ k (fun j => gridSumZ k (fun j' => (b j' - b j) * (b j' - b j)))

/-- `sosGap ≥ 0` — a double grid sum of squares. -/
theorem sosGap_nonneg (k : Nat) (b : Nat → Int) : 0 ≤ sosGap k b :=
  gridSumZ_nonneg k _ (fun _ _ => gridSumZ_nonneg k _ (fun _ _ => int_sq_nonneg _))

/-- The neighbour-minus-centre Laplacian gap collapses: `lapNbr j − lapC =
    −(k+1)(b j − c)` (= `−m·(b j − c)`, the `K_m` Laplacian difference). -/
theorem lapNbr_sub_lapC (k : Nat) (b : Nat → Int) (c : Int) (j : Nat) :
    lapNbr k b c j - lapC k b c = -((k : Int) + 1) * (b j - c) := by
  unfold lapNbr lapC
  rw [gridSumZ_sub, gridSumZ_const, gridSumZ_sub, gridSumZ_const]
  ring_intZ

/-- Sum of the neighbour carrés du champ: `Σ_j gammaNbr j = gammaC + sosGap`. -/
theorem sum_gammaNbr (k : Nat) (b : Nat → Int) (c : Int) :
    gridSumZ k (fun j => gammaNbr k b c j) = gammaC k b c + sosGap k b := by
  unfold gammaNbr
  rw [gridSumZ_add,
      gridSumZ_congr k (fun j => (c - b j) * (c - b j))
        (fun j => (b j - c) * (b j - c)) (fun _ _ => by dsimp only; ring_intZ)]
  rfl

/-- ★★★★★ **Discrete Bochner identity for the complete graph `K_m`** (`m = k+1`):

      `4Γ₂(f) = (k+3)·(2Γ(f)) + Σ_j Σ_{j'} (b j' − b j)²`,

    i.e. `gamma2C = (k+3)·gammaC + sosGap`.  The positive-curvature coefficient
    `k + 3 = m + 2` is forced by the all-to-all adjacency, and the remainder is a
    manifest sum of squares.  Generalizes `bochner_triangle` (`k = 2`: `k+3 = 5`,
    `sosGap = 2(b₀−b₁)²`).  Pure `gridSumZ` linearity + `ring_intZ`. -/
theorem bochner_complete (k : Nat) (b : Nat → Int) (c : Int) :
    gamma2C k b c = ((k : Int) + 3) * gammaC k b c + sosGap k b := by
  have hterm2 : gridSumZ k (fun j => (b j - c) * (lapNbr k b c j - lapC k b c))
      = -((k : Int) + 1) * gammaC k b c := by
    have hcongr : gridSumZ k (fun j => (b j - c) * (lapNbr k b c j - lapC k b c))
        = gridSumZ k (fun j => -((k : Int) + 1) * ((b j - c) * (b j - c))) :=
      gridSumZ_congr k _ _ (fun j _ => by rw [lapNbr_sub_lapC]; ring_intZ)
    rw [hcongr, gridSumZ_mul_left]
    rfl
  have hterm1 : gridSumZ k (fun j => gammaNbr k b c j - gammaC k b c)
      = gammaC k b c + sosGap k b - (k : Int) * gammaC k b c := by
    rw [gridSumZ_sub, sum_gammaNbr, gridSumZ_const]
  unfold gamma2C
  rw [hterm1, hterm2]
  ring_intZ

/-- ★★★★★ **`CD((m+2)/2, ∞)` for the complete graph `K_m`** (`m = k+1`): the
    Bakry–Émery curvature lower bound `Γ₂ ≥ ((m+2)/2)·Γ`, in scaled form
    `gamma2C ≥ (k+3)·gammaC`.  Immediate from `bochner_complete` + `sosGap ≥ 0`.
    Specializes to the triangle `cd_triangle` (`k = 2`, `k+3 = 5`) and is the
    general-`m` Bakry–Émery counterpart of the Forman / Gauss–Bonnet / Ollivier
    sign↔topology results. -/
theorem cd_complete_graph (k : Nat) (b : Nat → Int) (c : Int) :
    ((k : Int) + 3) * gammaC k b c ≤ gamma2C k b c := by
  rw [bochner_complete]
  apply Order.le_of_sub_nonneg
  rw [show ((k : Int) + 3) * gammaC k b c + sosGap k b - ((k : Int) + 3) * gammaC k b c
        = sosGap k b from by ring_intZ]
  exact Order.nonneg_of_le_zero (sosGap_nonneg k b)

/-- `gammaC ≥ 0` (the centre carré du champ is a sum of squares) — so
    `CD((m+2)/2,∞)` is a genuine positive lower bound, not vacuous. -/
theorem gammaC_nonneg (k : Nat) (b : Nat → Int) (c : Int) : 0 ≤ gammaC k b c :=
  gridSumZ_nonneg k _ (fun _ _ => int_sq_nonneg _)

/-- The SOS gap vanishes when all neighbour values coincide: every difference
    `b j' − b j = 0`, so the double sum is a sum of zeros. -/
theorem sosGap_eq_zero_of_const (k : Nat) (b : Nat → Int)
    (hb : ∀ i j, i < k → j < k → b i = b j) : sosGap k b = 0 := by
  unfold sosGap
  have hinner : ∀ j, j < k →
      gridSumZ k (fun j' => (b j' - b j) * (b j' - b j)) = 0 := by
    intro j hj
    rw [gridSumZ_congr k _ (fun _ => (0 : Int))
          (fun j' hj' => by
            have hz : b j' - b j = 0 := by rw [hb j' j hj' hj]; exact add_neg_cancel (b j)
            show (b j' - b j) * (b j' - b j) = 0
            rw [hz]; exact zero_mul 0)]
    exact gridSumZ_zero_fn k
  rw [gridSumZ_congr k _ (fun _ => (0 : Int)) (fun j hj => hinner j hj)]
  exact gridSumZ_zero_fn k

/-- ★★★★ **The `CD((m+2)/2, ∞)` bound is sharp** — attained with equality on any
    "constant-neighbour" configuration (`sosGap = 0`): `gamma2C = (k+3)·gammaC`
    exactly.  So `(m+2)/2` is the *actual* Bakry–Émery curvature of `K_m`, not
    merely a lower bound — the bound `cd_complete_graph` cannot be improved.  (The
    witness is non-vacuous: take `b` constant `≠ c`, then `gammaC = k·(b−c)² > 0`.) -/
theorem cd_complete_graph_sharp (k : Nat) (b : Nat → Int) (c : Int)
    (hb : ∀ i j, i < k → j < k → b i = b j) :
    gamma2C k b c = ((k : Int) + 3) * gammaC k b c := by
  rw [bochner_complete, sosGap_eq_zero_of_const k b hb, Int.add_zero]

/-- The constant-`0` neighbour configuration (centre `c = 1`) has `gammaC = k` — non-vacuous
    (`> 0` for `k ≥ 1`), the witness that makes `CD((m+2)/2,∞)` a *tight* bound. -/
theorem complete_graph_gammaC_witness (k : Nat) : gammaC k (fun _ => 0) 1 = (k : Int) := by
  show gridSumZ k (fun _ => ((0:Int) - 1) * ((0:Int) - 1)) = (k : Int)
  exact Eq.trans (Eq.trans
    (gridSumZ_congr k (fun _ => ((0:Int) - 1) * ((0:Int) - 1)) (fun _ => (1:Int))
      (fun _ _ => by dsimp only; ring_intZ))
    (gridSumZ_const k 1)) (mul_one (k : Int))

/-- ★★★★ **The Bakry–Émery curvature of `K_m` is exactly `(m+2)/2`** — the optimal Lin–Yau curvature.
    The lower bound `CD((m+2)/2,∞)` (`cd_complete_graph`) is *attained with equality* on the constant-`0`
    neighbour configuration, which has `gammaC = k > 0` (`k = m−1 ≥ 1`).  So no larger curvature constant
    is a universal lower bound: `(m+2)/2` is the genuine Bakry–Émery (Lin–Yau optimal) curvature of `K_m`,
    not merely a bound. -/
theorem lin_yau_curvature_complete (k : Nat) (hk : 1 ≤ k) :
    0 < gammaC k (fun _ => 0) 1
    ∧ gamma2C k (fun _ => 0) 1 = ((k : Int) + 3) * gammaC k (fun _ => 0) 1 := by
  refine ⟨?_, cd_complete_graph_sharp k (fun _ => 0) 1 (fun _ _ _ _ => rfl)⟩
  rw [complete_graph_gammaC_witness]
  exact Order.lt_of_lt_of_le (by decide) (OrderMul.ofNat_le_of_le hk)

/-! ## §4 — the bipartite star `K_{1,b}`: `CD((3−b)/2, ∞)` at the centre

The first bipartite case `K_{a,b}` with `a = 1`: a **centre** vertex (value `c`)
joined to `b = k` **leaves** (values `b 0, …, b (k−1)`), with **no leaf–leaf edges**
(`K_{1,b}` is the star `S_b`, triangle-free).  The centre operators are exactly those
of §3 (`lapC`, `gammaC` — the centre Laplacian / carré du champ are graph-independent);
only the *leaf* operators change: a leaf's **sole** neighbour is the centre, so
`lapLeaf = c − b j`, `gammaLeaf = (c − b j)²` carry **no** other-neighbour sum (the
`K_m` neighbours were mutually adjacent; star leaves are not).

The closed form (`bochner_star`) is `gamma2Star = (3 − b)·gammaC + 2·lapC²`, with
`2·lapC² ≥ 0` the manifest SOS — so the star centre is `CD((3−b)/2, ∞)`.  Sign
trichotomy in the leaf count `b = k`:

  · `b ≤ 2` → `(3−b)/2 > 0` (positively curved — a short path through the centre);
  · `b = 3` → flat;
  · `b ≥ 4` → `(3−b)/2 < 0` (**negatively curved** — a hub with many leaves, like a
    tree), matching the double-star Ollivier `κ = −2/3 < 0` (`OllivierRicci` §6).

Contrast `K_m` (`CD((m+2)/2,∞) > 0`, ever more positive): adding the leaf–leaf edges
(turning the star into a clique) flips the curvature from negative to positive — the
clustering the Bakry–Émery `Γ₂` measures.  General `K_{a,b}` (`a ≥ 2`) needs a
second-shell (`a−1` other `A`-vertices) optimization and is left open. -/

/-- Leaf Laplacian in `K_{1,b}`: a leaf's only neighbour is the centre, `Lf = c − b j`. -/
def lapLeaf (b : Nat → Int) (c : Int) (j : Nat) : Int := c - b j

/-- Leaf carré du champ (scaled `2Γ`) in `K_{1,b}`: `(c − b j)²` (one edge only). -/
def gammaLeaf (b : Nat → Int) (c : Int) (j : Nat) : Int := (c - b j) * (c - b j)

/-- Iterated carré du champ (scaled `4Γ₂`) at the star centre — same shape as
    `gamma2C` but with the leaf operators (no leaf–leaf term). -/
def gamma2Star (k : Nat) (b : Nat → Int) (c : Int) : Int :=
  gridSumZ k (fun j => gammaLeaf b c j - gammaC k b c)
    - 2 * gridSumZ k (fun j => (b j - c) * (lapLeaf b c j - lapC k b c))

/-- ★★★★★ **Discrete Bochner identity for the star `K_{1,b}`** (`b = k` leaves):

      `4Γ₂(f) = (3 − b)·(2Γ(f)) + 2·(Lf at centre)²`,  i.e.  `gamma2Star = (3−b)·gammaC
      + 2·lapC²`.

    The curvature coefficient `3 − b` *decreases* with the leaf count (vs `K_m`'s
    `k + 3` which increases) — a hub is increasingly negatively curved.  Pure
    `gridSumZ` linearity + `ring_intZ`. -/
theorem bochner_star (k : Nat) (b : Nat → Int) (c : Int) :
    gamma2Star k b c = (3 - (k : Int)) * gammaC k b c + 2 * (lapC k b c * lapC k b c) := by
  have hA : gridSumZ k (fun j => gammaLeaf b c j - gammaC k b c)
      = (1 - (k : Int)) * gammaC k b c := by
    rw [gridSumZ_sub,
        show gridSumZ k (fun j => gammaLeaf b c j) = gammaC k b c from
          gridSumZ_congr k _ (fun j => (b j - c) * (b j - c))
            (fun j _ => by dsimp only; unfold gammaLeaf; ring_intZ),
        show gridSumZ k (fun _ => gammaC k b c) = (k : Int) * gammaC k b c from
          gridSumZ_const k _]
    ring_intZ
  have hB : gridSumZ k (fun j => (b j - c) * (lapLeaf b c j - lapC k b c))
      = (-1) * gammaC k b c - lapC k b c * lapC k b c := by
    rw [show gridSumZ k (fun j => (b j - c) * (lapLeaf b c j - lapC k b c))
          = gridSumZ k (fun j => (-1) * ((b j - c) * (b j - c))
              - lapC k b c * (b j - c)) from
        gridSumZ_congr k _ _ (fun j _ => by unfold lapLeaf; ring_intZ),
        gridSumZ_sub, gridSumZ_mul_left, gridSumZ_mul_left]
    rfl
  unfold gamma2Star
  rw [hA, hB]; ring_intZ

/-- ★★★★★ **`CD((3−b)/2, ∞)` for the star `K_{1,b}`.**  From `bochner_star`, the
    residual `2·lapC² ≥ 0`, so `gamma2Star ≥ (3−b)·gammaC`.  Negative coefficient for
    `b ≥ 4` — a genuine *negative* curvature lower bound (the hub case). -/
theorem cd_star (k : Nat) (b : Nat → Int) (c : Int) :
    (3 - (k : Int)) * gammaC k b c ≤ gamma2Star k b c := by
  rw [bochner_star]
  apply Order.le_of_sub_nonneg
  rw [show (3 - (k : Int)) * gammaC k b c + 2 * (lapC k b c * lapC k b c)
        - (3 - (k : Int)) * gammaC k b c = 2 * (lapC k b c * lapC k b c) from by ring_intZ]
  have h2 : (0 : Int) ≤ 2 * (lapC k b c * lapC k b c) := by
    rw [show (2 : Int) * (lapC k b c * lapC k b c)
          = lapC k b c * lapC k b c + lapC k b c * lapC k b c from by ring_intZ]
    exact add_nonneg (int_sq_nonneg _) (int_sq_nonneg _)
  exact Order.nonneg_of_le_zero h2

/-- The star curvature coefficient `3 − b` is **negative for `b ≥ 4`** — the centre of a
    large star is negatively curved, the Bakry–Émery counterpart of the double-star
    Ollivier `κ < 0` (a hub/tree, like hyperbolic space), opposite the clique `K_m`. -/
theorem star_negatively_curved (k : Nat) (hk : 4 ≤ k) : (3 : Int) - (k : Int) < 0 := by
  have h4 : (4 : Int) ≤ (k : Int) := OrderMul.ofNat_le_of_le hk
  have h3k : (3 : Int) < (k : Int) := Order.lt_of_lt_of_le (by decide) h4
  apply Order.lt_of_sub_pos
  rw [show (0 : Int) - (3 - (k : Int)) = (k : Int) - 3 from by ring_intZ]
  exact Order.sub_pos_of_lt h3k

end E213.Lib.Math.Geometry.GeometrizationConjecture.BakryEmery
