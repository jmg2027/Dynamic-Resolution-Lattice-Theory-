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

## Conditional / unconditional separation

`primary_cup_span_soundness_on_layer` combines unconditional
cross-layer (closed above) with the on-layer hypothesis
`ψ_m(starS i m ∪ β) = false` (and T-analogue) for each m.  The
on-layer hypothesis is Direction B's remaining work — extend
`psi_layer_kills_cupOpp_S{i}star_left_at_bottom` from
`m = ⟨0, _⟩` to arbitrary m, via targeted `nat_beq_add_left`
placement.

At c = 1, `Fin 1` forces `m = ⟨0, _⟩`, the on-layer hypothesis
collapses to the proven bottom-layer kill, and
`primary_cup_span_soundness_c1` is UNCONDITIONAL.

The conditional capstone `parametric_dual_span_capstone` closes
the SPAN side under the per-layer completeness hypothesis
(joint ψ-kernel ⊆ `InPrimary`).  This is the second open piece
— the substantive cup-image dim calculation at single-layer
K_{3,3}.  Layer-disjointness then lifts to ∀c.

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

## Open frontier

Two pieces remain for unconditional `codim ≤ c`:

  · **Direction B on-layer**: ψ_m kills `starS i m ∪ β` at
    layer m for arbitrary m, via Nat.beq cancellation over
    `9·m + …` offsets.  Cross-layer cases already closed.
  · **Per-layer completeness**: joint ψ-kernel ⊆ `InPrimary` at
    single-layer K_{3,3}.  Reduces to a finite F₂-rank
    calculation; lifts to ∀c by layer-disjointness.

## The thing to point at

`psi_canonical_decomposition c v s t m'`.  For any face cochain
v, this is the concrete identity
`v(s,t,m') = weighted_e_sum(s,t,m') ⊕ residual(s,t,m')` —
9c equations per v, each a single F₂-XOR.  The SPAN claim
asserts the residual is reachable from cup-image + coboundary.
Half closed (cross-layer + c = 1), half open (on-layer +
completeness).
