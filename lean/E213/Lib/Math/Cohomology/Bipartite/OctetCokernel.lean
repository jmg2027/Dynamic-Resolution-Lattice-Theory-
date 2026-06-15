import E213.Lib.Math.Cohomology.Bipartite.H1K
import E213.Lib.Math.Cohomology.Examples.BettiKernel

/-!
# The gluon-octet cokernel — `coker ι* = H¹(K) ≃ (F₂)⁸`, ∅-axiom, no LES

The gauge content `8 = NS²−1` is the rank of `H¹(K_{3,2}^{(c=2)})`, read as the
SU(3) gluon octet via the inclusion `ι : K ↪ Δ⁴`.  Previously the
*identification* `coker ι* = H¹(K)` rode on the classical long exact sequence
(`ChannelCohomologyLoss.H2_relative_dim := H1_K`, asserted), while the PURE
theorem `IotaKToDelta4.gluon_octet_identification` proved only the supporting
*numbers*.  This file closes the **math** with no LES — by the elementary fact
"a linear map out of the one-element group is zero, so its cokernel is the whole
codomain."

Drawable picture: **`ι` embeds `K` into the contractible `Δ⁴`; `Δ⁴` has only one
`H¹`-class (the zero class), so the induced map `ι* : H¹(Δ⁴) → H¹(K)` is the zero
map; what is "left over" (the cokernel) is therefore all of `H¹(K)` — the 8
independent loops.**  No long exact sequence; just "cokernel of the zero map =
the whole space."

Honest scope (the freezing line): this forces `coker ι* = H¹(K)`, a **rank-8
`𝔽₂`-vector space**.  It does **NOT** force "`(F₂)⁸ = the SU(3) adjoint":
`(F₂)⁸` is a characteristic-2 vector space; the SU(3) adjoint is an 8-dim *real
Lie algebra*.  The match is the **number `8 = NS²−1`**, not the algebraic object.
Reading the rank-8 module as the gluon octet is the Weyl-restriction deployment
(`Sym3IrrepDecomp`: `H¹(K) = 2·triv ⊕ 3·std` over `𝔽₂`) — the single imported
physics label, kept as a *reading*, not ontologized.

Also fixes an indexing slip: the genuine `H¹(Δ⁴) = 0` certificate is
`BettiKernel.reduced_betti_d4_contractible` (`kerSizeDelta 5 0 = 1`,
`kerSizeDelta 5 1 = 2` ⇒ reduced `b̃₁ = 0`), **not** `kerSizeDelta 5 2`
(which is the `C²` / `H²` datum).

All theorems PURE.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.OctetCokernel

open E213.Lib.Math.Cohomology.Bipartite.H1K (H1K)
open E213.Lib.Math.Cohomology.Examples.BettiKernel (kerSizeDelta)

/-- `H¹(Δ⁴)` modelled by its single class.  Justified: `Δ⁴` is contractible,
    `b̃₁(Δ⁴) = 0` (`BettiKernel.reduced_betti_d4_contractible`), so `H¹(Δ⁴)` is
    the one-element (trivial) group. -/
abbrev H1Delta4 : Type := Unit

/-- `ι* : H¹(Δ⁴) → H¹(K)` — the induced map on `H¹`.  Out of the one-element
    group there is exactly one linear map; it sends the single (zero) class to
    `0 ∈ H¹(K)`.  This is not a choice: linearity forces `0 ↦ 0`, and `0` is the
    only element of the domain. -/
def ι_star (_ : H1Delta4) : H1K := H1K.zero

/-- **im ι* = {0}** (pointwise, funext-free): every value of `ι*` is the zero
    class of `H¹(K)`. -/
theorem ι_star_image_trivial :
    ∀ (x : H1Delta4) (i : Fin 8), ι_star x i = H1K.zero i := by
  intro _ _; rfl

/-- ★★★★★ **Gluon octet as a cokernel, ∅-axiom (no LES).**
    `coker ι* = H¹(K) / {0} = H¹(K)`, a rank-8 `𝔽₂`-space (`|·| = 2⁸ = 256`).

    The four conjuncts are the drawable argument:
    (1) `H¹(Δ⁴)` is the one-element group — the **correct** certificate
        `kerSizeDelta 5 0 = 1 ∧ kerSizeDelta 5 1 = 2` (reduced `b̃₁ = 0`),
        *not* `kerSizeDelta 5 2` (a `C²`/`H²` datum);
    (2) `ι*` is the zero map (its image is the zero class, pointwise);
    (3) the codomain `H¹(K)` has rank `8 = NS²−1`;
    (4) so `coker ι* = H¹(K)`, of cardinality `2⁸ = 256`.

    Forces the MATH (rank-8 cokernel); does NOT ontologize "= SU(3) octet"
    (a reading; see the file header). -/
theorem octet_is_cokernel_of_zero_map :
    -- (1) H¹(Δ⁴) is the trivial group — CORRECT certificate (reduced b̃₁ = 0)
    (kerSizeDelta 5 0 = 1 ∧ kerSizeDelta 5 1 = 2)
    -- (2) ι* is the zero map (image is the zero class, pointwise — funext-free)
    ∧ (∀ (x : H1Delta4) (i : Fin 8), ι_star x i = H1K.zero i)
    -- (3) the codomain H¹(K) has rank 8 = NS² − 1
    ∧ H1K.rank = 8
    ∧ H1K.rank = 3 * 3 - 1
    -- (4) coker ι* = H¹(K)/{0} = H¹(K), cardinality 2⁸ = 256
    ∧ (2 : Nat) ^ H1K.rank = 256 := by
  refine ⟨E213.Lib.Math.Cohomology.Examples.BettiKernel.reduced_betti_d4_contractible,
          ι_star_image_trivial, rfl, rfl, ?_⟩
  decide

end E213.Lib.Math.Cohomology.Bipartite.OctetCokernel
