# Linalg213 "chiral compression rank ≤ 5" rebuild (the open capstone)

Companion to `research-notes/frontiers/genuine_hodge_rebuild.md` — same
honesty contract. Unlike the other notes here, nothing bogus was *welded*
to a famous name; the issue is a **genuinely open `-- TODO`** plus one
concrete instance, where the *universal* statement must be pinned
precisely so it is neither a triviality dressed up as deep, nor left
vague.

## 1. What the current state is (no fakery, but imprecise)

  · `Rank.lean` ends with `-- TODO (open, Linalg213 capstone): rank(Gram
    vs) ≤ 5.` — the universal claim is **unproven**.
  · `Rank5Concrete.lean` proves **one concrete instance**
    (`rank_5_concrete_instance`): the 6 vectors `e₀,…,e₄, (1,1,1,1,1)` in
    `Vec 5` carry the explicit Int dependence `(−1,−1,−1,−1,−1,+1)`,
    `decide`-checked to give the zero combination. Honest, but a single
    witness — it does not establish the universal bound.
  · The risk to guard against: stating the universal claim as
    "**∀ vs : Fin N → Vec 5, rank ≤ 5**" and proving it trivially, then
    presenting that triviality as a deep "compression theorem". Over a
    field, `dim ≤ 5` because the *ambient* space is 5-dimensional — a
    one-line dimension count, not Paper 1's intended content.

## 2. The genuine content (stated precisely)

`Vec 5 := Fin 5 → Nat` (with Int coefficients, since ℕ cannot cancel:
`Rank.lean §IntCoeffs`). Three statements must be kept distinct:

  (i) **Ambient bound (a triviality).** Any family `vs : Fin N → Vec 5`
      spans a subspace of the 5-dimensional ambient space, so its rank is
      `≤ 5`. True by dimension; if formalised, it must be **labelled a
      triviality**, not a capstone.

  (ii) **Linear-dependence above ambient (the real reachable claim).**
      The non-trivial, honest form: **any `N ≥ 6` vectors in `Vec 5` are
      linearly dependent over ℤ** — there exist Int coefficients, not all
      zero, with `Σ cᵢ vᵢ = 0` (`linComb_isZero = true`). This is the
      pigeonhole / Steinitz content: more vectors than dimensions ⟹ a
      relation. `Rank5Concrete` is the `N = 6` witness; the genuine
      theorem is the `∀ N ≥ 6, ∀ vs` existence of a dependence.

  (iii) **The intended "chiral compression" statement.** Paper 1's
      chiral split is `Vec 5 = VecS ⊕ VecT`, `NS + NT = 3 + 2 = 5`
      (`Chiral.combine_proj_eq`, `phase_L4_capstone`). The compression
      claim with teeth is: **the Gram matrix `Gram vs` of any family has
      rank ≤ 5, with equality detected by Gram non-degeneracy**, and the
      rank is `≤ NS + NT` — i.e. the `5` is *sourced* from the chiral
      `NS + NT`, not from a bare ambient dimension. The non-trivial part
      is the **Gram-rank = span-rank** bridge (the Gram matrix `Gᵢⱼ =
      ⟨vᵢ, vⱼ⟩` has the same rank as the family), which is a real linear-
      algebra theorem, not a dimension count.

So the precise capstone target = **(ii) + (iii)**: every family in
`Vec 5` is `5`-compressible, the `5 = NS + NT` is chiral-sourced, and
Gram-rank witnesses it. State (i) only as the trivial bound it is.

## 3. The 213-native obstruction (honest)

The substrate **does** have the pieces — this is reachable, unlike the
geometrization / cork notes:
  · `Vector.lean` (`Vec d`, standard basis), `Span.lean` (constructive
    `vec5_basis_span`: every `v` is `Σ v(k)·e_k`), `Rank.lean` (`IntCoeffs`,
    `linComb`, `linComb_isZero`), `Gram.lean` (the Gram matrix), and the
    determinant tower (`DetN`, `Laplace`, `PermSign`, `CayleyHamilton`).
What is missing is the **general rank theory** the `-- TODO` calls for:
  · no proven "Gram-rank = number of linearly independent rows/columns";
  · no Steinitz exchange / "N > d ⟹ dependent" as a *universal* over `N`
    and over arbitrary `vs` (only the `N=6` concrete instance and the
    bounded `{−1,0,1}²` LI check `e0_e1_LI_bounded`);
  · ℕ-valued entries with Int coefficients make the "no cancellation"
    bookkeeping the actual labour (this is why `Rank.lean` lifts to Int).

## 4. Staged plan

**Stage 1 — generalize the concrete instance to ∀ (the reachable
capstone).** Prove: **for every `vs : Fin 6 → Vec 5` there exist Int
coefficients `cs`, not all zero, with `linComb_isZero cs vs = true`.**
Path: 6 vectors in a 5-dim ambient ⟹ the `5×6` matrix has a non-trivial
integer kernel. Constructively, over ℤ this is a Smith-normal-form /
explicit-cofactor argument; for the ∅-axiom substrate, the cleanest route
is via the determinant tower: build the `5×5` minors (`DetN`, `Laplace`,
`PermSign`) and exhibit the kernel vector as signed maximal minors
(Cramer-style cofactor expansion gives an explicit dependence). This
generalizes `rank_5_concrete_instance` from one `vs` to all `vs`.

**Stage 2 — Gram-rank = span-rank bridge.** Using `Gram.lean`, prove the
Gram matrix `Gᵢⱼ = ⟨vᵢ,vⱼ⟩` of a family has rank equal to the family's
span dimension (over ℚ/Int): the family is dependent ⟺ `det(Gram) = 0`
for the maximal square Gram. This is the genuine "rank ≤ 5 detected by
Gram" — the non-trivial linear algebra. Cite `DetZeroCol`, `RowDependence`.

**Stage 3 — universal `∀ N, ∀ vs : Fin N → Vec 5, rank ≤ 5`.** Lift Stage
1 from `N = 6` to all `N` by Steinitz exchange (any independent subset has
size `≤ 5`; any larger family contains a dependence). This closes the
`-- TODO` in `Rank.lean`. The bound `5` is the *ambient* dimension — at
this stage state clearly that the bound itself is the dimension count, and
that the **content** is the constructive Int kernel (Stage 1) + the Gram
witness (Stage 2), not the inequality `5 ≤ 5`.

**Stage 4 — chiral-sourced `5 = NS + NT`.** Tie the bound to the chiral
decomposition: `rank ≤ dim(VecS) + dim(VecT) = NS + NT = 3 + 2`
(`Chiral.phase_L4_capstone`), so the compression rank is *sourced from the
spectrum*, not a free `5`. This is the Paper 1 statement in full.

## 5. Honest scope

  · The **ambient bound `rank ≤ 5`** is, by itself, a **triviality** (the
    ambient space is 5-dimensional). It must never be presented as a deep
    result; the depth is in the constructive Int kernel and the Gram
    bridge.
  · `rank_5_concrete_instance` (`Rank5Concrete.lean`) is a **proven single
    witness** (`N = 6`), explicitly *not* the universal claim — the file
    says so.
  · `vec5_basis_span` (`Span.lean`) and `Chiral.combine_proj_eq` are
    **proven** (the basis decomposition and the chiral split). The
    universal rank-≤-5 / Gram-rank theorems are **open** (`-- TODO`).
  · Steinitz exchange and Gram-rank=span-rank are **classical theorems**;
    here they are open *in the ∅-axiom Int-coefficient substrate* and are
    the reachable Stage-1/2/3 work.

## 6. Cross-references (genuine kept seams)

  · `lean/E213/Lib/Math/Algebra/Linalg213/Rank.lean` (the `-- TODO`,
    `IntCoeffs`, `linComb`, `linComb_isZero`, `e0_e1_LI_bounded`)
  · `lean/E213/Lib/Math/Algebra/Linalg213/Rank5Concrete.lean`
    (`rank_5_concrete_instance` — the `N=6` witness to generalize)
  · `lean/E213/Lib/Math/Algebra/Linalg213/Span.lean` (`vec5_basis_span`)
  · `lean/E213/Lib/Math/Algebra/Linalg213/Chiral.lean`
    (`phase_L4_capstone`, `combine_proj_eq` — the `5 = NS + NT` source)
  · `lean/E213/Lib/Math/Algebra/Linalg213/Gram.lean` (Gram matrix — Stage 2)
  · `lean/E213/Lib/Math/Algebra/Linalg213/` det tower: `DetN.lean`,
    `Laplace.lean`, `PermSign.lean`, `DetZeroCol.lean`, `RowDependence.lean`
    (Stage 1/2 machinery)
  · `lean/E213/Lib/Math/Algebra/Linalg213/INDEX.md` (sub-tree map)
