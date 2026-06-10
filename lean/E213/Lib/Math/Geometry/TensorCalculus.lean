import E213.Meta.Int213
import E213.Meta.Int213.PolyIntMTactic

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

end E213.Lib.Math.Geometry.TensorCalculus
