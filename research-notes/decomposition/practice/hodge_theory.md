# Decomposition: Hodge theory (the (p,q) bigrading, ⋆, harmonic forms, polarization, the Hodge conjecture)

*213-decomposition per `../README.md` (model v7.1). The hypothesis to **test**, NOT re-skin `de_rham.md`:
Hodge theory is the calculus's **fold-height axis REFINED into a two-index (p,q) bigrading, with the
Hodge star = the q=±1 duality involution**. `de_rham.md` grounded the single-graded `H*_dR = ker d/im d`
residue (one height-grade `n`). Hodge theory does NOT add a height-grade — it **splits the grade `n` into
two coordinates `(p,q)` with `p+q=n`** by reading the same fold-height through a complex-structure Lens
`J` (`J²=−1`), one count for the holomorphic half and one for the antiholomorphic half. Concretely:
(i) **the Hodge decomposition `H^n(X,ℂ)=⊕_{p+q=n}H^{p,q}`** = the single height-grade of `de_rham.md`
RESOLVED into a `(p,q)` bigrading by the complex-structure reading; (ii) **the Hodge star
`⋆ : H^{p,q}→H^{n−p,n−q}`** = the q=±1 complement-swap / Poincaré-duality involution, the SAME `⋆⋆=id`
of `homology.md`/`de_rham.md` REFINED to the signed `⋆²=−1` complex structure on the odd grades;
(iii) **harmonic forms (`Δ=dd*+d*d`, harmonic `= ker Δ`)** = the q=+1 Laplacian-kernel fixed point, the
SAME `ker δ` residue tied to `graph_theory.md`'s `λ₀=0`; (iv) **the Hodge decomposition theorem (each
class has a UNIQUE harmonic representative)** = the **fold-to-normal-form** of a cohomology class
(harmonic rep = the canonical normal form, `raw_initial`-style); (v) **polarization `(Q,J)`** = the
symplectic cup-pairing armed with the Weil operator `J = i^{p−q}`; (vi) **the Hodge conjecture** = the
named open obstruction (which `(p,p)` rational classes are algebraic). NEW DATUM over `de_rham.md`: the
height-grade BIGRADES (height read through `J`), and the duality `⋆` becomes the signed complex structure
— NO new primitive, de Rham's `H*` with the height bigraded and the duality involution signed.*

## The decomposition (C / Reading / Residue, q=±1)

- **Construction `C`** — the **same simplex/nesting** `homology.md`/`de_rham.md` read: an `n`-cell is
  `n+1` distinguished vertices; a `k`-form is the `k`-cochain `Cochain n k = Fin (binom n k) → Bool` on
  `k`-subsets (`Cohomology/Cochain/Core`). `C` carries its two read-off axes — a **fold-height** (grade
  `k`) and a **direction/orientation bit** (the `(−1)^i` removal sign). Hodge theory adds NO new `C`: it
  equips the *same* cochain space with a **complex-structure reading `J`** (`J²=−1`, the order-2
  difference-sign as a metric operator) that bigrades the one height-axis. Nothing smooth-manifold enters:
  no `Ω^{p,q}` bundle, no Dolbeault `∂̄`-complex, no Kähler metric — the construction is the combinatorial
  cochain complex `Λ(Δ⁴)` plus the integer-signed star.

- **Reading `L↑↑` (the bigraded height + complex-structure reading)** — `de_rham.md`'s coboundary `L↑`
  (`delta : Cᵏ→Cᵏ⁺¹`, the height-axis run UP) is here read THROUGH the complex structure `J`: the single
  height-count `n` is split into `(p,q)` by which half of the `J`-eigenspace a form sits in. The Lean
  shadow of `J` is the **signed Hodge star** — `SignedHodgeStar.starSign`/`starStar` (the `Int`-signed
  `⋆` on all `2⁴=16` forms of `Λ(Fin 4)`) and its `2×2` model `SignedStarC4.J = [[0,−1],[1,0]]`. The
  Weil operator `J` acting as `i^{p−q}` IS this reading: it distinguishes `H^{p,q}` from `H^{q,p}` by the
  sign of `p−q`. So the (p,q) bigrading is NOT a new axis — it is `de_rham.md`'s fold-height read with one
  extra bit (the `J`-eigenvalue), exactly as `integers.md` read the count with a swap-bit to get sign.

- **Residue — `q=±1` (the README's residue tag), two faces that are one:**
  1. *Duality face (q=−1 ONCE → involution).* The Hodge star `⋆ : H^{p,q}→H^{n−p,n−q}` is the
     complement-swap, the SAME `⋆⋆=id` of `homology.md`/`de_rham.md` — but Hodge theory REFINES it to the
     **signed** star where `⋆²=(−1)^{k(n−k)}`, so on the odd grades `⋆²=−1`: the direction-bit applied
     once at a two-step composite (`q=−1`), squaring to `+1` (involution) on the even grades and generating
     `C₄≅ℤ[i]` on the odd grades — the complex structure itself. Lean: `SignedStarC4.signed_star_sq_neg_I`,
     `SignedHodgeStar.star_star_eq_sign`. This is Poincaré duality (`PoincareDuality.poincare_duality_delta4`).
  2. *Harmonic / normal-form face (q=+1 → fixed point).* The Laplacian `Δ=dd*+d*d` (with `d*=⋆d⋆` the
     codifferential, `Hodge/Delta.codiff`) has a kernel; **harmonic `= ker Δ`** is the q=+1 fixed point of
     the diffusion reading — the SAME `ker δ` residue as `de_rham.md`/`homology.md`, the SAME `λ₀=0`
     constant kernel as `graph_theory.md`'s Laplacian. The **Hodge decomposition theorem** (each class has
     a unique harmonic representative) = the q=+1 **fold-to-normal-form**: the harmonic rep is the canonical
     normal form of a cohomology class, exactly `raw_initial`'s "the read-op picks the unique normal form".

## Re-seeing — ⟨C | L⟩

```
   Hodge decomp  H^n = ⊕_{p+q=n} H^{p,q}  =  ⟨ simplex cochains | L↑ READ THROUGH J ⟩
                                            = de_rham's ONE height-grade n SPLIT by the J-eigenvalue (p−q)
   Hodge star ⋆ : H^{p,q}→H^{n−p,n−q}      =  q=±1 complement-swap, signed: ⋆²=(−1)^{k(n−k)}
                                            = homology/de_rham's ⋆⋆=id REFINED to the signed complex structure
   ⋆²=−1 on odd grades  (J²=−I)            =  the direction-bit q=−1 once → C₄≅ℤ[i] (SignedStarC4.J)
   codifferential d* = ⋆d⋆                 =  L↓ conjugated by the duality ⋆ (Hodge/Delta.codiff_5_2)
   Laplacian Δ = dd*+d*d, harmonic=ker Δ   =  q=+1 Laplacian-kernel fixed point  (= graph_theory's λ₀=0)
   "unique harmonic representative"         =  the FOLD-TO-NORMAL-FORM of a class (raw_initial-style)
   polarization (Q,J): J∈O(Q), Q·J ≻ 0     =  symplectic cup-pairing + the Weil operator (HodgeRiemannJ)
   Hodge index  σ(H²)=(1+2h^{2,0}, h^{1,1}−1) = the (p,q) grade-additive signature (KahlerGradeStructure)
   Hodge conjecture                         =  named OPEN obstruction: which (p,p)∩H^{2p}(X,ℚ) are algebraic
```

The whole of Hodge theory is **`de_rham.md`'s one reading (`L↑`) read through one extra bit (`J`), plus
the duality `⋆` signed** — no new primitive. Set against the notes it refines:

| classical Hodge object | = the 213 reading | already in note | Lean anchor |
|---|---|---|---|
| Hodge decomposition `⊕H^{p,q}` | de Rham's height-grade `n` SPLIT by the `J`-eigenvalue `p−q` | `de_rham.md` (`H*_dR=ker d/im d`) | `KahlerGradeStructure` (h^{2,0}/h^{1,1} grade split) |
| Hodge star `⋆` (signed) | `q=±1` complement-swap, `⋆²=(−1)^{k(n−k)}` | `de_rham.md`/`homology.md` (`⋆⋆=id`) | `SignedStarC4.signed_star_sq_neg_I`, `SignedHodgeStar.star_star_eq_sign` |
| `⋆²=−1` = complex structure `i` | the direction-bit `q=−1` once → `C₄≅ℤ[i]` | `parity.md`/`determinant.md` (`q=−1` sign) | `SignedStarC4.signed_hodge_is_cp_i`, `CPHodgeStructure.cp_i_is_hodge_complex_structure` |
| Poincaré duality `H^k≅H^{n−k}` | the `⋆` complement bijection | `de_rham.md` (cap = `⋆`) | `PoincareDuality.poincare_duality_delta4` |
| codifferential `d*=⋆d⋆`, Laplacian `Δ` | `L↓` conjugated by `⋆`; diffusion reading | `de_rham.md` (`d`/`∂`), `graph_theory.md` (`L=D−A`) | `Hodge/Delta.codiff_5_2`, `phase_CB_capstone` |
| harmonic `= ker Δ`; unique harmonic rep | `q=+1` Laplacian-kernel fixed point; fold-to-normal-form | `graph_theory.md` (`λ₀=0`), `category_theory.md` (`raw_initial`) | `graph_theory` `closed_const`; (conceptual on `Δ`) |
| polarization `(Q,J)`, Hodge–Riemann | symplectic cup + Weil operator `J=i^{p−q}` | `de_rham.md` (cup), `lie_theory.md` (symplectic) | `HodgeRiemannJ.polarization_forces_maximal_cp` |
| Hodge index signature | the `(p,q)` grade-additive count | `homology.md` (Betti), `de_rham.md` (surfaces) | `KahlerGradeStructure.hodge_index_master_theorem` |

Hodge theory consumes BOTH of `C`'s axes (height to set `p+q=n`, direction to sign `⋆` and split the
`J`-eigenspaces) — exactly as `de_rham.md` found, because Hodge theory IS de Rham's `H*` with the height
bigraded and the duality signed.

## LEVERAGE — does Hodge theory REFINE de Rham's height into a (p,q) bigrading without a new primitive?

**Verdict: PREDICTION + PARTIAL (one located break) — and a genuine REFINEMENT, not a re-skin: the new
datum (height bigraded by `J`; `⋆` signed to the complex structure) is grounded by a substantial
∅-axiom Hodge corpus the calculus had not yet decomposed.** The discrete spine is BUILT and PURE; the
analytic harmonic-projector + the Hodge conjecture are the named open legs. Leg by leg, honest.

**(1) ★ The Hodge star is BUILT at the cochain level — `⋆` and `⋆⋆=id`, PURE.** `Hodge/Star.hodgeStar n k m`
is the complement-of-subset cochain map `(⋆σ)(T)=σ(complement T)` (10/0 PURE), and `Hodge/Involution`
proves `⋆⋆=id` on Δ⁴ (`hodge_sq_v0_5`, `phase_CB_hodge_involution`, 11/0). This is `de_rham.md`'s
`⋆⋆=id` verbatim — the q=±1 complement-swap. **Poincaré duality `H^k≅H^{n−k}` IS this `⋆`** — built as
`PoincareDuality.poincare_duality_delta4` (2/0 PURE), the `⋆⋆=id` involution rebadged at all 5 Δ⁴ strata,
with `dim_symmetry_delta4` (`binom 5 k = binom 5 (5−k)`).

**(2) ★★ The signed star REFINES `⋆` to the complex structure — `⋆²=−1`, `C₄≅ℤ[i]`, the (p,q)-defining
`J`, PURE.** This is the new datum's load-bearing leg. In ℤ/2 the sign `(−1)^{k(n−k)}` collapses so
`⋆²=+1` (the de Rham involution); Hodge theory's content is the **signed** `⋆` where on the odd grades
`⋆²=−1`. Built two ways: (a) `SignedHodgeStar.star_star_eq_sign` (12/0 PURE) — the genuine `Int` operator
on all `2⁴=16` forms of `Λ(Fin 4)`, `⋆∘⋆=(−1)^{k(n−k)}`, with `⋆²=−1` at grades `1,3`
(`star_sq_neg_one_grade1/3`, `hodge_i_order_four`); (b) the `2×2` model `SignedStarC4.J=[[0,−1],[1,0]]`,
`J²=−I`, `J⁴=I` (`signed_star_sq_neg_I`), `ℤ[J]≅ℤ[i]` with `(aI+bJ)(cI+dJ)=(ac−bd)I+(ad+bc)J` the Gaussian
product and `det=a²+b²=N(a+bi)` (`signed_star_ring_is_gaussian`, `signed_star_norm_is_det`, 10/0). The
capstone `signed_hodge_is_cp_i` identifies the cohomological complex structure with the algebraic `i`.
**This is exactly the Weil operator `J=i^{p−q}` that defines the (p,q) bigrading**: it acts as the
order-4 complex structure that splits each `H^n` into `J`-eigenspaces. The parity readout
`CPHodgeStructure.star_sq_minus_one_at_1_3` (5/0) shows `⋆²=−1` exactly at grades `1,3` of the `(d−1)=4`
simplex, with the `parity_wall_at_n5` honest caveat (the `n=5` vertex-count convention collapses the sign).

**(3) ★ The (p,q) bigrading / Hodge decomposition is grounded at the Hodge-index level — the grade split
`(1+2h^{2,0}, h^{1,1}−1)`, PURE.** `KahlerGradeStructure` carries the abstract `(p,q)` grade data:
`KahlerGradeData ⟨h20, h11, h11_pos⟩` with `pos=1+2·h^{2,0}` (Kähler grade 0 + holo-2-form pairs `(α,ᾱ)`)
and `neg=h^{1,1}−1`, and `hodge_index_master_theorem` (5/0 PURE) derives the Hodge-index signature
`σ(H²)=(1+2h^{2,0}, h^{1,1}−1)` STRUCTURALLY from the grade axioms, instantiated on ℙ², ℙ¹×ℙ¹, T²×T²
(matching the per-surface `HodgeIndex*` capstones). The non-degeneracy `pos+neg=b₂`
(`hodge_index_full_rank`) IS Poincaré duality re-read on the bigrading. So the `H^{p,q}` decomposition is
present as **the grade-additive count `b_n=Σ_{p+q=n} h^{p,q}`** — de Rham's single Betti number `b_n` SPLIT
into the `(p,q)` table — not as a named eigenspace-decomposition operator (that needs the harmonic
projector, leg 4).

**(4) Harmonic forms / Laplacian = q=+1 kernel fixed point; the unique-rep theorem = fold-to-normal-form
(PARTIAL — codifferential built, full Δ-projector conceptual).** The codifferential `d*=⋆d⋆` is BUILT —
`Hodge/Delta.codiff_5_2 = hodgeStar∘delta∘hodgeStar` (7/0 PURE), with the docstring naming the Laplacian
`Δ=δ·codiff+codiff·δ` and "harmonic cochains satisfy `Δσ=0`". The conceptual content is exact and ties to
prior notes: **harmonic `= ker Δ` = the q=+1 Laplacian-kernel fixed point = `graph_theory.md`'s `λ₀=0`
constant kernel** (`GraphConnectivity.closed_const`, the dim-1 q=+1 kernel) and **`ergodic_theory.md`'s
invariant-functions-constant** — one `q=+1` kernel across three fields. The **Hodge decomposition theorem**
("every cohomology class has a UNIQUE harmonic representative") is the q=+1 **fold-to-normal-form**: the
harmonic rep IS the canonical normal form of a `ker d/im d` class, the literal analogue of
`category_theory.md`/`curry_howard.md`'s `raw_initial`/`dhom_unique_pointwise` ("the fold picks the unique
normal form") and `FreeReduction`'s `{t//Irreducible t}` normal-form subtype. **Located gap:** the full
finite-dimensional `Δ`-as-`ker`-projector theorem (`H ≅ ker Δ` as a proved iso) is NOT built — only
`codiff` and `⋆⋆=id` and `phase_CB_capstone` (the operators are well-defined PURE on Δ⁴); the
harmonic-projection isomorphism is the `Real213`/inner-product residue (needs a positive-definite metric
pairing to project, the same smooth-metric gap `de_rham.md`/`curvature.md` hit).

**(5) ★ Polarization `(Q,J)` / Hodge–Riemann = symplectic cup + Weil operator, PURE.** `HodgeRiemannJ`
builds the genuine polarization on `H¹=Λ¹⊕Λ³`: the symplectic cup form `Q=[[0,1],[−1,0]]` (`Qᵀ=−Q`), `J`
a `Q`-isometry `Jᵀ Q J=Q` (`J_is_Q_isometry`, the Hodge–Riemann identity `Q(Ja,Jb)=Q(a,b)`), and the
positive Hermitian form `h=Q·J=I≻0` (`hodge_riemann_positive`, HR2 positivity). `polarization_forces_maximal_cp`
(7/0 PURE) bundles `(J²=−I, J∈O(Q), Q·J≻0)`. So `(Q,J)` is a real Kähler/Hermitian pair — the Lefschetz
positivity content of a polarized Hodge structure, on the discrete cochain complex.

**(6) The bigraded physics deployment — generations as `Λ²(ℝ³)`, the Yukawa carries `J`, PURE.**
`BigradedYukawa` (4/0 PURE) makes the bigrading literal in the DRLT branch: `generations_are_exterior_grade`
shows `N_gen=C(NS,NT)=dim Λ²(ℝ³)=3` is a genuine cohomology grade (the spatial factor of the bigrading),
tensored with the internal `Λ*(ℂ⁵)` carrying the signed `J` — `Λ^{NT}(ℝ^{NS})⊗Λ*(ℂ^d)` joined by
`d=NS+NT=5`. This is the calculus's bigrading reading deployed onto a falsifiable physics structure (the
CP phase forced to `90°` via the `HodgeRiemannJ` polarization).

**Honest boundary — Lean-built vs conceptual.**
- *Lean-built (∅-axiom, scanned PURE):* (a) `⋆` + `⋆⋆=id` (`Star` 10/0, `Involution` 11/0); (b) Poincaré
  duality `H^k≅H^{n−k}` (`PoincareDuality` 2/0); (c) the SIGNED `⋆²=−1` complex structure / Weil `J`
  (`SignedHodgeStar` 12/0, `SignedStarC4` 10/0, `CPHodgeStructure` 5/0); (d) codifferential `d*=⋆d⋆`
  (`Hodge/Delta` 7/0); (e) polarization `(Q,J)` + Hodge–Riemann positivity (`HodgeRiemannJ` 7/0); (f) the
  `(p,q)` grade-additive Hodge-index signature (`KahlerGradeStructure` 5/0); (g) the bigraded physics
  deployment (`BigradedYukawa` 4/0); (h) the de Rham residue `H*=ker/im` inherited (`BettiKernel` 11/0).
- *Conceptual-only / the precise missing legs:* (i) the **harmonic-projection isomorphism** `H^n≅ker Δ`
  as a proved theorem (the `codiff`/`Δ` operators are built and PURE, but the full `Δ`-kernel-equals-
  cohomology projector needs a positive-definite metric pairing — the `Real213`/smooth-metric residue);
  (ii) the **named `H^{p,q}` eigenspace decomposition operator** (the grade COUNT is built via
  `KahlerGradeData`; the projection of `H^n(X,ℂ)` onto its `J`-eigenspaces as a constructed operator is
  not); (iii) the **Lefschetz operators `L=∧ω`, `Λ`, and the `sl₂`-action / Hard Lefschetz** are ABSENT
  (grep-confirmed: no `L_operator`/`Lambda`/`sl2`/`hard_lefschetz`/`primitive`-decomposition in the
  cohomology tree — only the polarization `J` and `Q` are built, not the raising/lowering pair); (iv) the
  **Hodge conjecture** itself (which `(p,p)∩H^{2p}(X,ℚ)` are algebraic cycle classes) is a named OPEN
  obstruction — the `HodgeConjecture/` directory builds intersection forms / signatures / Hodge-index /
  CS-bridges, NOT a proof or disproof; the conjecture is the q=−1 escape-style obstruction "which rational
  Hodge classes are in the image of the cycle map", unbuilt.

So: **PREDICTION + PARTIAL — the (p,q)-bigrading refinement and the signed `⋆` complex structure are
grounded ∅-axiom (the new datum cashed); the harmonic projector, the Lefschetz `sl₂`, and the Hodge
conjecture are the named open legs, the `Real213`-cut/algebraic-cycle residues.**

## Revelation (refinement: Hodge theory = de Rham's H* with the height BIGRADED by J + the duality SIGNED)

**Forcing — the (p,q) bigrading is FORCED by adding ONE bit (the `J`-eigenvalue) to de Rham's height,
not a new axis.** `de_rham.md` established the single fold-height grade `n` (`H*_dR=ker d/im d`). Hodge
theory does not add a second height — it reads that ONE height through the complex-structure Lens `J`
(`J²=−1`), and the `J`-eigenvalue `i^{p−q}` splits each grade `n` into the `(p,q)` table with `p+q=n`.
This is the EXACT move `integers.md` made (read the count through a swap-bit to get sign) and
`golden_ratio.md`/`spectral.md` made (read the count through a multiplier to get `q=±1`), one level up:
the bigrading is the height-axis read with a direction-refinement, and the Lean witness that the
refinement is real is `SignedStarC4.signed_star_sq_neg_I` (`⋆²=−1` — the bit that de Rham's ℤ/2 star
loses). So the calculus needs no "(p,q)-grading" primitive — it is fold-height (de Rham's axis) `⊗`
the `J`-eigenvalue (the direction sub-readout, README model v4), the cleanest confirmation that the
direction bit and the fold-height axis COMBINE rather than being two separate machines.

**Collapse — the Hodge star, Poincaré duality, the codifferential, and the harmonic kernel are ONE
q=±1 reading, not four operators.** The signed `⋆` on `C` generates all four: (a) `⋆⋆=id` on even grades
= Poincaré duality (`poincare_duality_delta4`); (b) `⋆²=−1` on odd grades = the complex structure `J`
that defines the bigrading (`signed_hodge_is_cp_i`); (c) `d*=⋆d⋆` = `L↓` conjugated by `⋆`
(`codiff_5_2`); (d) `Δ=dd*+d*d`, harmonic `=ker Δ` = the q=+1 fixed point. The README's "one character
read four ways" (det = scalar/Aut-invariant/loop/`∂`-down) gains its Hodge reading: the SAME direction
bit read as Poincaré-self-duality (`q=−1` once, involutive on even grades) AND as the complex structure
(`q=−1` once, `C₄` on odd grades) AND as the codifferential (the duality conjugating the boundary) AND as
the harmonic q=+1 kernel — `⋆²=±1` IS the README's `q=±1` tag selecting involution (`+1`, even grades) vs
complex structure (`−1`, odd grades) at the two-step composite, exactly `homology.md`'s "`∂²=0` vs `⋆⋆=id`
are the two poles of `q=±1`" now SIGNED so the odd-grade pole is `ℤ[i]`, not just `+1`.

**Residue surfaced — the unique harmonic representative IS the fold-to-normal-form, and the Hodge
conjecture is the q=−1 escape it cannot reach.** The Hodge decomposition theorem ("each `ker d/im d`
class has a unique harmonic rep") is the q=+1 fold-to-normal-form (`raw_initial`-style: the read-op picks
the canonical representative of a quotient, the same shape as `FreeReduction`'s normal-form subtype). And
the **Hodge conjecture** sits at the q=−1 escape corner: it asks whether every rational `(p,p)`-class is
algebraic — i.e. whether the cycle-class map is SURJECTIVE onto the rational `J`-invariant lattice. That
surjection question is the SAME shape as the surjection-failure the calculus keeps finding at q=−1
(`object1_not_surjective`): "is the residue (rational Hodge classes not obviously algebraic) in the image
of a construction (algebraic cycles)?" — unresolved, the named open obstruction, not a 213 primitive gap.

**EXTEND-by-refinement; no new axis; the interior model v7.1 holds.** Hodge theory adds the (p,q)
bigrading as fold-height `⊗` `J`-eigenvalue (no new primitive) and the signed `⋆` as the README's
direction-bit at a two-step composite (`q=±1` selecting involution vs complex structure). The two
load-bearing invariants (the character/duality and the `q=±1` residue) absorb it; the genuine absences —
the harmonic projector (smooth-metric residue), the Lefschetz `sl₂` (unbuilt), and the Hodge conjecture
(q=−1 surjection obstruction) — are located precisely, the complex-geometry twin of `de_rham.md`'s
smooth-form-bundle residue.

## Note for the technique

- **Hodge theory vindicates "the direction bit and the fold-height axis COMBINE" — the deepest use of
  model v4's two `C`-axes together.** `de_rham.md` used height (degree) and direction (face sign)
  separately; Hodge theory reads them as ONE bigrading: `(p,q)` = height `⊗` the `J`-eigenvalue. The
  signed `⋆²=−1` (`SignedStarC4`/`SignedHodgeStar`) is the Lean proof that the combination is real, not
  formal — the bit de Rham's ℤ/2 star throws away is exactly the complex structure that bigrades.
- **The signed `⋆` SHARPENS `homology.md`'s `q=±1` two-pole story.** `homology.md` noted `∂²=0` (`q=−1`
  nilpotent) vs `⋆⋆=id` (`q=+1` involutive). Hodge theory shows the `⋆`-pole is itself `q=±1`-graded:
  `⋆²=+1` (even grades, plain involution) vs `⋆²=−1` (odd grades, the complex structure `C₄≅ℤ[i]`). So the
  involutive pole is not monolithic — the signed star splits it, and the `−1` half is where the bigrading
  and the CP phase `i` live (`signed_hodge_is_cp_i`).
- **The harmonic representative is the cleanest "fold-to-normal-form" instance outside the foundations.**
  `category_theory.md`/`curry_howard.md` grounded `raw_initial`/`dhom_unique_pointwise` as "the fold picks
  the unique normal form". Hodge's "unique harmonic representative" is the SAME statement on cohomology
  classes — the q=+1 canonical-form pick — tying the harmonic kernel to `graph_theory.md`'s `λ₀=0` and
  `ergodic_theory.md`'s invariant-constant. One q=+1 fixed point across four fields.
- **The break is located, not new: the harmonic projector + Lefschetz `sl₂` + the Hodge conjecture.** The
  smooth harmonic-projection iso `H≅ker Δ` is the `Real213`/metric residue shared with
  `de_rham.md`/`curvature.md`; the Lefschetz raising/lowering `sl₂` is genuinely unbuilt (only `J`/`Q` are);
  the Hodge conjecture is the q=−1 surjection obstruction (cycle map onto rational Hodge classes), a named
  open problem, not a missing 213 primitive.

---

### Verified Lean anchors (file : line : theorem — all grep-verified on `lean/E213`; purity via `tools/scan_axioms.py` this session)

| Leg | Theorem (file : line : name) | Status |
|---|---|---|
| ★ Hodge `⋆` at cochain level (complement map `(⋆σ)(T)=σ(comp T)`) | `Lib/Math/Cohomology/Hodge/Star.lean:65 : hodgeStar` (`:74 hodge_vertex0_n3_at_12`) | **PURE, scanned 10/0** ✓ |
| ★ `⋆⋆=id` involution on Δ⁴ | `Lib/Math/Cohomology/Hodge/Involution.lean:49 : hodge_sq_v0_5`, `:69 phase_CB_hodge_involution` | **PURE, scanned 11/0** ✓ |
| ★ Poincaré duality `H^k≅H^{n−k}` (= `⋆` bijection, all 5 strata) | `Lib/Math/Cohomology/HodgeConjecture/Structure/PoincareDuality.lean:52 : poincare_duality_delta4`, `:67 dim_symmetry_delta4` | **PURE, scanned 2/0** ✓ |
| ★★ SIGNED `⋆²=−1` complex structure (operator on 16 forms, `⋆⋆=(−1)^{k(n−k)}`) | `Lib/Physics/Mixing/SignedHodgeStar.lean:85 : star_star_eq_sign`, `:106 hodge_i_order_four` | **PURE, scanned 12/0** ✓ |
| ★★ signed star `J=[[0,−1],[1,0]]`, `J²=−I`, `ℤ[J]≅ℤ[i]` (the Weil `J=i^{p−q}`) | `Lib/Math/Cohomology/Hodge/SignedStarC4.lean:69 : signed_star_sq_neg_I`, `:94 signed_star_ring_is_gaussian`, `:125 signed_hodge_is_cp_i` | **PURE, scanned 10/0** ✓ |
| ★ `⋆²=−1` exactly at grades 1,3 of `(d−1)=4` simplex (parity readout) | `Lib/Physics/Mixing/CPHodgeStructure.lean:68 : star_sq_minus_one_at_1_3`, `:108 cp_i_is_hodge_complex_structure` | **PURE, scanned 5/0** ✓ |
| ★ codifferential `d*=⋆δ⋆`, Laplacian `Δ=δ·codiff+codiff·δ`, harmonic=`ker Δ` | `Lib/Math/Cohomology/Hodge/Delta.lean:34 : codiff_5_2`, `:69 phase_CB_capstone` | **PURE, scanned 7/0** ✓ (Laplacian/harmonic named in docstring; full Δ-projector conceptual) |
| ★ polarization `(Q,J)`: `J∈O(Q)`, `Q·J=I≻0` (Hodge–Riemann) | `Lib/Math/Cohomology/Hodge/HodgeRiemannJ.lean:73 : J_is_Q_isometry`, `:82 hodge_riemann_positive`, `:112 polarization_forces_maximal_cp` | **PURE, scanned 7/0** ✓ |
| ★ (p,q) grade-additive Hodge index `σ=(1+2h^{2,0}, h^{1,1}−1)` | `Lib/Math/Cohomology/HodgeConjecture/Pairing/KahlerGradeStructure.lean:80 : KahlerGradeData`, `:112 hodge_index_full_rank`, `:192 hodge_index_master_theorem` | **PURE, scanned 5/0** ✓ (`hodge_index_master_theorem` PURE) |
| bigraded physics deployment: generations `=Λ²(ℝ³)`, Yukawa carries `J` | `Lib/Physics/Mixing/BigradedYukawa.lean:56 : generations_are_exterior_grade`; `bigraded_yukawa_capstone` | **PURE, scanned 4/0** ✓ |
| `H*=ker d/im d` residue inherited (Δ⁴ contractible ⇒ empty) | `Lib/Math/Cohomology/Examples/BettiKernel.lean:42 : kerSizeDelta`, `:52 kerSize_5_1`, `:63 reduced_betti_d4_contractible` | **PURE, scanned 11/0** ✓ (via `de_rham.md`/`homology.md`) |
| `⋆⋆=id` universal on Δ⁴ (the involution, q=±1 once) | `Lib/Math/Cohomology/Delta/V4Capstone.lean:53 : hodge_involution_universal_delta4` (`:41 dsq_zero_universal_delta4`) | **PURE, scanned 5/0** ✓ (via `de_rham.md`) |
| harmonic = q=+1 Laplacian-kernel fixed point (cross-frame) | `graph_theory.md` (`GraphConnectivity.closed_const`, `λ₀=0`), `ergodic_theory.md` (invariant=constant) | prior, ∅-axiom ✓ |
| fold-to-normal-form (unique harmonic rep, cross-frame) | `category_theory.md`/`curry_howard.md` (`raw_initial`, `dhom_unique_pointwise`), `FreeReduction` | prior, ∅-axiom ✓ |
| cross-frame | `de_rham.md` (`H*_dR=ker d/im d`, `⋆⋆=id`, `delta`), `homology.md` (`q=±1` two poles, `∂²=0`/`⋆⋆=id`), `parity.md`/`determinant.md` (`q=−1` sign), `golden_ratio.md`/`spectral.md` (`q=±1` multiplier) | prior, ∅-axiom ✓ |

### Dropped / flagged (honest)

- **No harmonic-projection isomorphism `H^n(X) ≅ ker Δ` as a proved theorem.** The Hodge star `⋆`, the
  codifferential `d*=⋆δ⋆`, and the Laplacian `Δ=dd*+d*d` are built and PURE (`Hodge/Delta`,
  `phase_CB_capstone`); the **full theorem that `ker Δ` is a unique set of representatives for `ker d/im d`**
  is NOT — it needs a positive-definite inner-product pairing to project, the same `Real213`/smooth-metric
  residue `de_rham.md` (no smooth `Ω^k` bundle) and `curvature.md` (no smooth metric) flag. Conceptual leg,
  cited as the q=+1 fold-to-normal-form; not asserted as a built iso.
- **No Lefschetz operators / `sl₂`-action / Hard Lefschetz** — grep-confirmed ABSENT in the cohomology
  tree (no `L=∧ω` raising, no `Λ` lowering, no `sl2`/`hard_lefschetz`/primitive-decomposition; the only
  "primitive" hits are number-theoretic primitive roots, unrelated). Only the polarization `J` and the
  symplectic `Q` are built (`HodgeRiemannJ`). The Lefschetz `sl₂` structure on `⊕H^k` is the named open
  leg; do not cite it.
- **No named `H^{p,q}` eigenspace-decomposition OPERATOR.** The `(p,q)` grade COUNT (`h^{p,q}` table,
  `b_n=Σh^{p,q}`) is built via `KahlerGradeData`/`hodge_index_master_theorem`; the construction projecting
  `H^n(X,ℂ)` onto its `J`-eigenspaces `H^{p,q}` as an operator is not — same shape as the missing harmonic
  projector. The bigrading is grounded as a count + the defining `J` (`SignedStarC4`), not as a built
  direct-sum decomposition.
- **The Hodge conjecture is NOT proved or disproved** — the `HodgeConjecture/` directory (despite the name)
  builds intersection forms, signatures, Hodge-index, Hodge–Riemann, and stat-mech/CS bridges (Ising/Potts/
  SpinGlass/MLDecoder), NOT a resolution of the conjecture. Framed as the q=−1 surjection obstruction
  (cycle-class map onto rational `(p,p)` Hodge classes), a named open problem, not a 213 primitive gap.
- **`n=5` vs `n=4` convention caveat (already in-repo, honest).** The ℤ/2 cochain star uses the `n=5`
  vertex-count where `(−1)^{k(5−k)}` is always `+1` (no complex structure); the signed `⋆²=−1` complex
  structure appears at the actual dimension `n=d−1=4` with `ℤ`-coefficients (`CPHodgeStructure.parity_wall_at_n5`,
  `SignedHodgeStar.dim_eq_four`). Both are cited correctly: `Star`/`Involution`/`PoincareDuality` are the
  unsigned ℤ/2 `⋆⋆=id`; `SignedStarC4`/`SignedHodgeStar`/`CPHodgeStructure` are the signed `⋆²=−1`.
- **Purity note**: `hodgeStar`/`phase_CB_hodge_involution` (Star 10/0, Involution 11/0),
  `signed_star_sq_neg_I`/`signed_hodge_is_cp_i` (SignedStarC4 10/0), `star_star_eq_sign`/`hodge_i_order_four`
  (SignedHodgeStar 12/0), `star_sq_minus_one_at_1_3`/`cp_i_is_hodge_complex_structure` (CPHodgeStructure 5/0),
  `codiff_5_2`/`phase_CB_capstone` (Hodge/Delta 7/0), `polarization_forces_maximal_cp` (HodgeRiemannJ 7/0),
  `hodge_index_master_theorem` (KahlerGradeStructure 5/0), `poincare_duality_delta4` (PoincareDuality 2/0),
  `generations_are_exterior_grade` (BigradedYukawa 4/0), `reduced_betti_d4_contractible` (BettiKernel 11/0)
  all freshly scanned PURE via `tools/scan_axioms.py` in this session.
