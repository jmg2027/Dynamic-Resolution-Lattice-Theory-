import E213.Meta.Int213
import E213.Meta.Int213.PolyIntMTactic
import E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci

/-!
# General-`n` tensor calculus I: Christoffel symbols of the first kind (∅-axiom)

The smooth Ricci-flow core needs the Riemannian curvature tensor of an **arbitrary**
metric `g_{ij}` — Christoffel symbols, then Riemann/Ricci as index sums
(`ricci_flow_smooth_core.md`).  The conformal sidestep (`ConformalCurvature.lean`) reached
the *conformally-flat* curvature in general `n`; this file opens the **general-metric**
tensor calculus, starting with the part that needs **no metric inverse** (hence no
division): the **Christoffel symbols of the first kind**

  `Γ_{kij} = ½(∂_i g_{kj} + ∂_j g_{ki} − ∂_k g_{ij})`.

Everything is **dimension-free** — the indices `i,j,k,…` are arbitrary `Nat`, and the metric
enters only through its derivative tensor `dg a b c = ∂_a g_{bc}` (an arbitrary `Int`-valued
function, symmetric in its last two slots because `g` is symmetric).  These are the genuine
general-`n` tensor identities (scaled `×2` to stay over ℤ), `∅`-axiom (`ring_intZ`):

  · `chris1_symm`         — `Γ_{kij} = Γ_{kji}` (symmetric in the lower pair);
  · `chris1_metric_compat`— `Γ_{kij} + Γ_{jik} = ∂_i g_{kj}` (metric compatibility `∇g = 0`,
    the relation that recovers the metric derivative from the Christoffels);
  · `chris1_flat`         — a constant metric (`dg ≡ 0`) has `Γ ≡ 0`.

The second-kind `Γ^l_{ij} = g^{lm}Γ_{mij}` and the Riemann/Ricci tensors need the metric
**inverse** `g^{lm}` (adjugate/`det` over ℤ) + second derivatives — the next rungs.
-/

namespace E213.Lib.Math.Geometry.TensorCalculus

open E213.Meta.Int213
open E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci (gridSumZ
  gridSumZ_congr gridSumZ_add gridSumZ_sub gridSumZ_mul_left gridSumZ_fubini
  gridSumZ_delta_weight gridSumZ_zero_fn)

/-- **Christoffel symbol of the first kind**, scaled `×2` (to stay over ℤ):
    `2·Γ_{kij} = ∂_i g_{kj} + ∂_j g_{ki} − ∂_k g_{ij}`, read off the metric-derivative tensor
    `dg a b c = ∂_a g_{bc}`.  Dimension-free: `i,j,k` arbitrary. -/
def chris1x2 (dg : Nat → Nat → Nat → Int) (k i j : Nat) : Int :=
  dg i k j + dg j k i - dg k i j

/-- ★★★★★ **Lower-pair symmetry** `Γ_{kij} = Γ_{kji}` — the torsion-free property of the
    Levi-Civita connection, from the symmetry of the metric `∂_k g_{ij} = ∂_k g_{ji}`.
    Holds in every dimension. -/
theorem chris1_symm (dg : Nat → Nat → Nat → Int)
    (hsym : ∀ a b c, dg a b c = dg a c b) (k i j : Nat) :
    chris1x2 dg k i j = chris1x2 dg k j i := by
  unfold chris1x2; rw [hsym k i j]; ring_intZ

/-- ★★★★★ **Metric compatibility** `Γ_{kij} + Γ_{jik} = ∂_i g_{kj}` (scaled: `= 2·∂_i g_{kj}`)
    — the identity `∇g = 0` that *defines* the Levi-Civita connection: the two Christoffels
    obtained by lowering the differentiated index reconstruct the metric derivative.  The
    algebraic heart of "the connection is metric".  Holds in every dimension. -/
theorem chris1_metric_compat (dg : Nat → Nat → Nat → Int)
    (hsym : ∀ a b c, dg a b c = dg a c b) (k i j : Nat) :
    chris1x2 dg k i j + chris1x2 dg j i k = 2 * dg i k j := by
  unfold chris1x2
  rw [hsym j k i, hsym k i j, hsym i j k]; ring_intZ

/-- ★★★ **Flat metric ⟹ no connection.**  A constant metric (`dg ≡ 0`, all derivatives
    vanish) has vanishing Christoffel symbols — the connection is trivial, the manifold flat
    (no curvature can arise from `Γ`). -/
theorem chris1_flat (k i j : Nat) : chris1x2 (fun _ _ _ => 0) k i j = 0 := by
  unfold chris1x2; show (0 : Int) + 0 - 0 = 0; decide

/-! ## §2 — Christoffel symbols of the second kind (the metric inverse, over ℤ)

The second kind `Γ^l_{ij} = g^{lm}Γ_{mij}` raises an index with the inverse metric `g^{lm}`.
Over ℤ the inverse carries a `det g` denominator (`g^{lm} = adj(g)^{lm}/det g`), so we work
with the **`det`-scaled** second kind `2·det·Γ^l_{ij} = Σ_m adj(g)^{lm}·(2Γ_{mij})`, a
polynomial index sum (`adj` the adjugate, `gridSumZ` the sum over `m < n`).  The defining
property of the inverse — `g·adj = det·I`, i.e. `Σ_l g_{pl} adj^{lm} = det·δ_p^m` — is taken
as the abstract hypothesis `hadj`, exactly as the first kind took the metric symmetry. -/

/-- The **`det`-scaled second-kind** Christoffel `2·det·Γ^l_{ij} = Σ_{m<n} adj^{lm}·2Γ_{mij}`
    (raise the lower index of the first kind with the adjugate). -/
def chris2xDet (n : Nat) (adj : Nat → Nat → Int) (dg : Nat → Nat → Nat → Int)
    (l i j : Nat) : Int :=
  gridSumZ n (fun m => adj l m * chris1x2 dg m i j)

/-- ★★★★ **Lower-pair symmetry of the second kind** `Γ^l_{ij} = Γ^l_{ji}` — inherited from
    the first-kind symmetry, summed against the adjugate. -/
theorem chris2_symm (n : Nat) (adj : Nat → Nat → Int) (dg : Nat → Nat → Nat → Int)
    (hsym : ∀ a b c, dg a b c = dg a c b) (l i j : Nat) :
    chris2xDet n adj dg l i j = chris2xDet n adj dg l j i :=
  gridSumZ_congr n _ _ (fun m _ => by rw [chris1_symm dg hsym m i j])

/-- ★★★★★ **Raising then lowering recovers the first kind** (`g·Γ²·= det·Γ¹`):
    `Σ_l g_{pl}·(2·det·Γ^l_{ij}) = det·(2Γ_{pij})`, the consistency of the metric inverse
    `g·adj = det·I` (`hadj`).  This is the algebraic content of "`Γ^l` is `Γ_l` with the index
    raised by `g^{-1}`" — `∅`-axiom (`gridSumZ` linearity + Fubini + the Kronecker collapse
    `gridSumZ_delta_weight`). -/
theorem chris2_lower (n : Nat) (g adj : Nat → Nat → Int) (dg : Nat → Nat → Nat → Int)
    (det : Int) (p i j : Nat) (hp : p < n)
    (hadj : ∀ m, gridSumZ n (fun l => g p l * adj l m) = det * (if m = p then 1 else 0)) :
    gridSumZ n (fun l => g p l * chris2xDet n adj dg l i j)
      = det * chris1x2 dg p i j := by
  have hpull : gridSumZ n (fun l => g p l * chris2xDet n adj dg l i j)
      = gridSumZ n (fun l => gridSumZ n (fun m =>
          chris1x2 dg m i j * (g p l * adj l m))) := by
    apply gridSumZ_congr; intro l _
    unfold chris2xDet
    rw [← gridSumZ_mul_left]
    apply gridSumZ_congr; intro m _
    ring_intZ
  rw [hpull, gridSumZ_fubini]
  have hcollapse : gridSumZ n (fun m => gridSumZ n (fun l =>
        chris1x2 dg m i j * (g p l * adj l m)))
      = gridSumZ n (fun m => (if m = p then (1 : Int) else 0) * (det * chris1x2 dg m i j)) := by
    apply gridSumZ_congr; intro m _
    rw [gridSumZ_mul_left, hadj m]
    ring_intZ
  rw [hcollapse, gridSumZ_delta_weight n p (fun m => det * chris1x2 dg m i j) hp]

/-! ## §3 — the Riemann curvature tensor

The curvature `R^l_{ijk} = ∂_j Γ^l_{ik} − ∂_k Γ^l_{ij} + Σ_m(Γ^l_{jm}Γ^m_{ik} − Γ^l_{km}Γ^m_{ij})`
— the obstruction to `∇` being flat, built from the connection coefficients `Gam l i j = Γ^l_{ij}`
(second kind) and their derivative `dGamma a l i k = ∂_a Γ^l_{ik}` (both abstract here, exactly
as the metric entered §1 through `dg`).  The `ΓΓ` contractions are `gridSumZ` sums over `m`.
Dimension-free.  Two defining facts:

  · `riem_antisym_jk` — `R^l_{ijk} = −R^l_{ikj}` (antisymmetry in the last pair, the curvature
    `2`-form structure — `[∇_j, ∇_k]` is antisymmetric);
  · `riem_flat` — a flat connection (`Γ ≡ 0`, `∂Γ ≡ 0`) has `R ≡ 0`: no curvature.

The further symmetries (first Bianchi, pair symmetry) and `Ric = Σ_k R^k_{ikj}` need the
metric structure relating `Γ` to `g` (§1–§2) — the next rungs toward the Ricci tensor. -/

/-- The Riemann curvature `R^l_{ijk}` from the connection `Gam l i j = Γ^l_{ij}` and its
    derivative `dGamma a l i k = ∂_a Γ^l_{ik}`. -/
def riemUp (n : Nat) (dGamma : Nat → Nat → Nat → Nat → Int) (Gam : Nat → Nat → Nat → Int)
    (l i j k : Nat) : Int :=
  (dGamma j l i k + gridSumZ n (fun m => Gam l j m * Gam m i k))
    - (dGamma k l i j + gridSumZ n (fun m => Gam l k m * Gam m i j))

/-- ★★★★★ **Riemann antisymmetry in the last pair** `R^l_{ijk} = −R^l_{ikj}` — the curvature
    is the antisymmetric commutator `[∇_j, ∇_k]`; swapping `j ↔ k` negates it by construction.
    Holds in every dimension, for any connection. -/
theorem riem_antisym_jk (n : Nat) (dGamma : Nat → Nat → Nat → Nat → Int)
    (Gam : Nat → Nat → Nat → Int) (l i j k : Nat) :
    riemUp n dGamma Gam l i j k = -(riemUp n dGamma Gam l i k j) := by
  unfold riemUp; ring_intZ

/-- ★★★★ **Flat connection ⟹ no curvature.**  A vanishing connection (`Γ ≡ 0`, `∂Γ ≡ 0`)
    has `R ≡ 0` — the manifold is flat, no curvature obstruction.  (`Γ ≡ 0` is the constant-
    metric case of §1, `chris1_flat`.) -/
theorem riem_flat (n l i j k : Nat) :
    riemUp n (fun _ _ _ _ => 0) (fun _ _ _ => 0) l i j k = 0 := by
  unfold riemUp
  rw [gridSumZ_congr n _ (fun _ => (0 : Int)) (fun m _ => by show (0 : Int) * 0 = 0; decide),
      gridSumZ_congr n _ (fun _ => (0 : Int)) (fun m _ => by show (0 : Int) * 0 = 0; decide),
      gridSumZ_zero_fn]
  show (0 : Int) + 0 - (0 + 0) = 0; decide

/-! ## §4 — the Ricci tensor (contraction of Riemann) -/

/-- The **Ricci tensor** `Ric_{ik} = Σ_l R^l_{ilk}` — the trace of the Riemann tensor on its
    upper index against the second lower index. -/
def ricciFromRiem (n : Nat) (dGamma : Nat → Nat → Nat → Nat → Int)
    (Gam : Nat → Nat → Nat → Int) (i k : Nat) : Int :=
  gridSumZ n (fun l => riemUp n dGamma Gam l i l k)

/-- ★★★★ **Flat ⟹ Ricci-flat.**  A flat connection (`Γ ≡ 0`, `∂Γ ≡ 0`) has vanishing Ricci
    curvature — the contraction of `riem_flat`.  Ricci-flatness is the Einstein vacuum
    condition; the flat metric satisfies it trivially. -/
theorem ricci_flat (n i k : Nat) :
    ricciFromRiem n (fun _ _ _ _ => 0) (fun _ _ _ => 0) i k = 0 := by
  unfold ricciFromRiem
  rw [gridSumZ_congr n _ (fun _ => (0 : Int)) (fun l _ => riem_flat n l i l k),
      gridSumZ_zero_fn]

/-- Pure cyclic-cancellation `A − B + B − C + C − A = 0` (the per-`m` Bianchi summand after
    the connection symmetry), avoiding `ring_intZ`'s zero-polynomial gap. -/
private theorem hexcancel (A B C : Int) : A - B + B - C + C - A = 0 := by
  rw [sub_add_cancel_int A B, sub_add_cancel_int A C, Order.sub_self_zero]

/-- ★★★★★ **First Bianchi identity** `R^l_{ijk} + R^l_{jki} + R^l_{kij} = 0` (cyclic in the
    lower triple), for a **torsion-free** connection (`Gam` symmetric in its lower pair `hGam`,
    hence `∂Γ` symmetric there `hdG`).  The fundamental algebraic curvature symmetry: the `∂Γ`
    terms cancel pairwise via `hdG`, the six `ΓΓ` contractions combine into one `gridSumZ` whose
    summand cancels per-`m` via `hGam`.  Dimension-free, `∅`-axiom. -/
theorem riem_bianchi1 (n : Nat) (dGamma : Nat → Nat → Nat → Nat → Int)
    (Gam : Nat → Nat → Nat → Int)
    (hGam : ∀ l a b, Gam l a b = Gam l b a)
    (hdG : ∀ a l b c, dGamma a l b c = dGamma a l c b) (l i j k : Nat) :
    riemUp n dGamma Gam l i j k + riemUp n dGamma Gam l j k i
      + riemUp n dGamma Gam l k i j = 0 := by
  have hScomb :
      gridSumZ n (fun m => Gam l j m * Gam m i k)
        - gridSumZ n (fun m => Gam l k m * Gam m i j)
        + gridSumZ n (fun m => Gam l k m * Gam m j i)
        - gridSumZ n (fun m => Gam l i m * Gam m j k)
        + gridSumZ n (fun m => Gam l i m * Gam m k j)
        - gridSumZ n (fun m => Gam l j m * Gam m k i) = 0 := by
    rw [← gridSumZ_sub, ← gridSumZ_add, ← gridSumZ_sub, ← gridSumZ_add, ← gridSumZ_sub,
        gridSumZ_congr n _ (fun _ => (0 : Int))
          (fun m _ => by
            dsimp only; rw [hGam m i k, hGam m i j, hGam m j k]; exact hexcancel _ _ _)]
    exact gridSumZ_zero_fn n
  unfold riemUp
  rw [hdG j l i k, hdG k l i j, hdG i l j k, ← hScomb]
  ring_intZ

/-! ## §5 — the metric-tied Riemann symmetries (the curvature 2-jet)

The *algebraic* symmetries of the Riemann tensor are pointwise; in normal coordinates at a
point (`Γ = 0` there, the `ΓΓ` terms drop) the lowered Riemann is the metric **2-jet** part

  `2·R_{iklj} = ∂_i∂_j g_{kl} + ∂_k∂_l g_{ij} − ∂_i∂_l g_{kj} − ∂_k∂_j g_{il}`,

read off `ddg a b c d = ∂_a∂_b g_{cd}` (symmetric in `(a,b)` since `∂∂` commute, `hd`; and in
`(c,d)` since `g` is symmetric, `hg`).  Its four defining symmetries follow from `hd`/`hg`,
dimension-free, `∅`-axiom — the metric-tied symmetries the abstract §3 `riemUp` could not see. -/

/-- The lowered linearized Riemann tensor (×2) from the metric 2-jet `ddg a b c d = ∂_a∂_b g_{cd}`. -/
def riemLow (ddg : Nat → Nat → Nat → Nat → Int) (i k l j : Nat) : Int :=
  ddg i j k l + ddg k l i j - ddg i l k j - ddg k j i l

/-- ★★★★★ **Antisymmetry in the first pair** `R_{iklj} = −R_{kilj}` — pure (`ring_intZ`). -/
theorem riemLow_antisym_ik (ddg : Nat → Nat → Nat → Nat → Int) (i k l j : Nat) :
    riemLow ddg i k l j = -(riemLow ddg k i l j) := by
  unfold riemLow; ring_intZ

/-- ★★★★★ **Antisymmetry in the second pair** `R_{iklj} = −R_{ikjl}` — pure (`ring_intZ`). -/
theorem riemLow_antisym_lj (ddg : Nat → Nat → Nat → Nat → Int) (i k l j : Nat) :
    riemLow ddg i k l j = -(riemLow ddg i k j l) := by
  unfold riemLow; ring_intZ

/-- ★★★★★ **Pair symmetry** `R_{iklj} = R_{ljik}` — needs both metric-2-jet symmetries: `∂∂`
    commutativity (`hd`) and metric symmetry (`hg`).  The block-symmetry of the curvature
    operator. -/
theorem riemLow_pair_symm (ddg : Nat → Nat → Nat → Nat → Int)
    (hd : ∀ a b c d, ddg a b c d = ddg b a c d)
    (hg : ∀ a b c d, ddg a b c d = ddg a b d c) (i k l j : Nat) :
    riemLow ddg i k l j = riemLow ddg l j i k := by
  unfold riemLow
  rw [hd l k j i, hg k l j i, hd j i l k, hg i j l k, hd l i j k, hg i l j k,
      hd j k l i, hg k j l i]
  ring_intZ

/-- ★★★★★ **First Bianchi identity (metric form)** `R_{iklj} + R_{iljk} + R_{ijkl} = 0`,
    stated as `R_{iklj} + R_{iljk} = −R_{ijkl}` (moved-over, non-zero both sides — sidesteps
    `ring_intZ`'s zero-polynomial gap).  The cyclic-sum symmetry of the curvature `2`-jet,
    from `hd`/`hg`.  Completes the **four** Riemann symmetries. -/
theorem riemLow_bianchi1 (ddg : Nat → Nat → Nat → Nat → Int)
    (hd : ∀ a b c d, ddg a b c d = ddg b a c d)
    (hg : ∀ a b c d, ddg a b c d = ddg a b d c) (i k l j : Nat) :
    riemLow ddg i k l j + riemLow ddg i l j k = -(riemLow ddg i j k l) := by
  unfold riemLow
  rw [hg i j l k, hd l k i j, hg i l j k, hd j k i l, hg i k j l, hd j l i k]
  ring_intZ

end E213.Lib.Math.Geometry.TensorCalculus
