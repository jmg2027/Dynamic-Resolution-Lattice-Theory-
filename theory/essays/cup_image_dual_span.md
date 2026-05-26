# Cup-image dual span — when c ψ-discriminators pin H²_enr

The c ψ-discriminators on `K_{NS, NT}^{(c)}` SPAN the dual of
`H²_enr / cup-image` exactly when every face cochain reduces,
modulo (im δ¹ + PRIMARY cup-image), to its canonical c-dim
`weighted_e_sum` representative.  Not an existence claim about
an abstract dim — a concrete decomposition identity.

## 213-native answer

For c layers, define the c-dim subspace
`weighted_e_sum c b := Σ_m (b m) · e_face_layer m` of
`EnrichedFaceVal c` (a face cochain supported only at `(0, 0, m')`
carrying value `b m'`;
`V33EnrichedParametricDualSpan.weighted_e_sum`).  Every face
cochain v has the projection-residual split

```
v = weighted_e_sum c (m ↦ ψ_m v) ⊕ residual,   ψ_m(residual) = false ∀m
```

(`psi_canonical_decomposition`).  The first summand carries
exactly the ψ-vector; the second lives in the joint ψ-kernel.

The SPAN claim is the second movement: the residual lies in
(im δ¹ + PRIMARY cup-image-span).  When it holds, the c
indicators `e_face_layer m` form a basis of `H²_enr / cup-image`
and the c functionals `ψ_m` form the dual basis.

## Derivation

Surjectivity of the ψ-vector map
`Ψ : EnrichedFaceVal c → (Fin c → Bool)` is constructive: for
any target b, `weighted_e_sum c b` realises it
(`psi_layer_weighted_e_sum`).  Linearity (`psi_layer_linear`,
lifted through `psiNatPos` from `Infrastructure.BoolXORFold`)
makes the residual identity collapse to
`ψ_m(v) ⊕ ψ_m(v) = false`.

The PRIMARY restriction is forced.  The full cup-image-span —
closing `cupOpp_param α β` over arbitrary α, β under F₂-XOR — is
the entire `EnrichedFaceVal c`, because single-edge cups along
face diagonals reproduce every face indicator: for diagonal pair
(a, b) of face (s, t, m), `cupOpp_param e_a e_b = e_face_(s,t,m)`.
Witness: `psi_layer_arbitrary_cup_not_kill`
(`ψ_0(e_0 ∪ e_4) = true`).  Hence `InPrimaryCupSpanPlusBoundary`
admits constructors only for δ¹σ, starS-cup, incidT-cup, XOR —
matching exactly the kill theorems in
`V33EnrichedParametric.parametric_bottom_layer_full_kill_capstone`.

## 9-block disjointness as the cross-layer closure

The disjoint-layer factorisation
(`theory/essays/disjoint_layers_as_direct_sum.md`) has a
syntactic shadow: edge indices in `K_{3,3}^{(c)}` are `9·m + r`
with m the layer and r < 9 the in-layer position.  Distinct
layers give disjoint `[9m, 9m + 9)` blocks.  The Nat.beq lemma
`nine_block_disjoint` formalises this exactly:
`Nat.beq (9·a + r₁) (9·b + r₂) = false` when `a ≠ b`,
`r₁, r₂ < 9` (case-split on `a ⋚ b`; both branches reduce via
`Nat.add_lt_add_left` + `Nat.mul_succ` + `Nat.mul_le_mul_left`).

Lifted: `starS i m` evaluates false on every layer-m' edge with
m ≠ m' (`starS_layer_disjoint`).  Lifted again: the cross-layer
primary cup vanishes face-by-face
(`cupOpp_starS_cross_layer_zero`); ψ_{m'} sums nine zeros to
false (`psi_layer_starCup_cross_layer`).  All UNCONDITIONAL —
the soundness `InPrimary ⊆ joint ψ-kernel` no longer depends on
cross-layer hypotheses.  The incidT branch needs
`Bool.and_false` explicitly because the false factor lands on
the right of `&&` (`Bool.and` matches first arg); a syntactic
asymmetry of Lean's reduction, not a structural one.

## Conditional / unconditional separation — both directions now closed

`primary_cup_span_soundness_on_layer` combines unconditional
cross-layer (closed above) with the on-layer hypothesis
`ψ_m(starS i m ∪ β) = false` (and T-analogue) for each m.  At
c = 1, `Fin 1` forces `m = ⟨0, _⟩`, the on-layer hypothesis
collapses to the proven bottom-layer kill, and
`primary_cup_span_soundness_c1` is unconditional.  Direction B's
`parametric_arbitrary_m_full_kill_capstone` extends the kill to
every layer, giving `primary_cup_span_soundness_all_c` —
**EASY direction closed unconditionally at every c**.

The HARD direction (joint ψ-kernel ⊆ `InPrimary`) is closed too
(2026-05-25).  At c = 1, `joint_psi_kernel_subset_primary_c1`
exhibits 8 explicit primary cup-product generators
`g_1, …, g_8` spanning the dim-8 ψ-kernel (6 row pair-differences
from `cupOpp(starS i 0, e_edge ⋯)` + 2 column pair-differences
from `cupOpp(e_edge ⋯, incidT 0 0)`).  Every face cochain v with
`ψ_0(v) = 0` decomposes as `v = ⊕ᵢ b_i · g_i` with coefficients
`b_1 … b_6` reading off v's six "free" face values and `b_7, b_8`
being 3-term XORs that absorb the ψ-kernel constraint at position
(1, 0).

The lift to ∀c uses **layer-promotion**:
`promote_face : EnrichedFaceVal 1 → EnrichedFaceVal c` (supported
only at layer m) preserves the InPrimary structure constructor-by-
constructor.  `xor_aggregate` composes the c layer-m promotes into
a full reconstruction of v.  `joint_psi_kernel_subset_primary`
discharges the HARD direction at arbitrary c.

`parametric_dual_span_unconditional` and
`codim_upper_bound_unconditional` are the resulting unconditional
capstones.

## Dual function

The classical reading packages "cup-image codim = c" as a
topological invariant of the enriched 2-complex requiring
calculation.  The 213 reading factors the same number along the
disjoint-layer decomposition: each layer contributes one ψ_m
direction, c layers contribute c independent functionals, codim
is layered counting not invariant calculation.  SPAN-ness is
the syntactic realisation — every v reduces to a canonical
representative.  Same equation, different reduction depths.

## Cross-frame

The same fact appears in four readings.  **Combinatorial**:
`9·m + r` blocks tile edge indices.  **Categorical**: enriched
complex direct-sums over c layers
(`theory/essays/disjoint_layers_as_direct_sum.md`).
**Cohomological**: c ψ-functionals span the cup-image
annihilator (this essay).  **Algebraic**: c independent Massey-4
witnesses (`psi_layer_rep4_eq_true_c{2..12}`).  All four are
syntactic projections of the disjoint-layer factorisation;
nothing is added when moving between them, only the reading
depth changes.

## Closed (2026-05-25)

Both pieces previously open are now closed:

  · **Direction B on-layer**: ψ_m kills `starS i m ∪ β` at
    layer m for arbitrary m via `nat_decide_add_left_assoc{1,2}`
    cancellation, packaged in
    `parametric_arbitrary_m_full_kill_capstone`.
  · **Per-layer completeness**: joint ψ-kernel ⊆ `InPrimary`
    closed at c = 1 via 8 explicit primary cup-product
    generators (`joint_psi_kernel_subset_primary_c1`); lifted
    to ∀c via `promote_face`/`promote_edge` constructor-by-
    constructor preservation (`promote_in_primary`) and
    `xor_aggregate` aggregation
    (`joint_psi_kernel_subset_primary`).

The `codim ≤ c` upper bound at every Stern-Brocot position
against the PRIMARY cup-image is UNCONDITIONAL via
`parametric_dual_span_unconditional` and
`codim_upper_bound_unconditional`.

## The thing to point at

`psi_canonical_decomposition c v s t m'`.  For any face cochain
v, this is the concrete identity
`v(s,t,m') = weighted_e_sum(s,t,m') ⊕ residual(s,t,m')` —
9c equations per v, each a single F₂-XOR.  The SPAN claim now
asserts unconditionally that the residual is reachable from
cup-image + coboundary at every c.
