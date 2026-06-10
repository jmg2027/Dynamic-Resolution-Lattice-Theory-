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
  gridSumZ_congr gridSumZ_mul_left gridSumZ_fubini gridSumZ_delta_weight)

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

end E213.Lib.Math.Geometry.TensorCalculus
