# Session Handoff

## Anchor results on `main`

### c-multiplicity counter for K_{NS,NT}^{(c)}

  · **Simple-cycle face complex**: cup-image codim `= 1` independent
    of `c`.  `(c−1)`-codim hypothesis falsified.
  · **Enriched 2-complex** (multi-multiplicity face cycles): codim
    `≥ c` parametric in `c : Nat`.  c independent ψ-discriminators
    (one per mult layer); each kills its layer's primary cup-image.
  · **Bottom-layer bilateral kill**: ψ_0 kills `cupOpp_param (starS i) β`
    and `cupOpp_param α (incidT j)` for all i, j ∈ Fin 3 and any
    `c ≥ 1`.
  · **Arbitrary-m bilateral kill**: ψ_m kills both for every layer
    `m : Fin c` (Direction B closure 2026-05-24).
  · **Massey realisation**: parametric η-cochains `eta_ab_layer`,
    `eta_cd_layer` give `ψ_0(rep₄) = 1` at concrete c ∈ {2, …, 12}.

Anchors:
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33Indeterminacy.lean` —
    rep₄ ∉ principal indeterminacy at c=2 (ψ-discriminator)
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33c3Indeterminacy.lean` —
    same at c=3 (cross-frame)
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33Enriched.lean` —
    c=2 enriched, codim ≥ 2
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33c3Enriched.lean` —
    c=3 enriched, codim ≥ 3
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33EnrichedParametric.lean` —
    ∀c parametric codim ≥ c + concrete Massey witnesses c=2..12

### Mediant cohomology functor — Stern-Brocot Vandermonde decomposition

Every `K_{NS, NT}^{(c)}` cell-count factors through the Stern-Brocot
path via Vandermonde decomposition of the mediant:

  · `V(a+c, b+d) = V(a, b) + V(c, d)` — 2-term linear additivity
  · `E^m(a+c, b+d) = E^m(a, b) + E^m(a, d) + E^m(c, b) + E^m(c, d)`
    — 4-term Vandermonde
  · `F(a+c, b+d) = (binom a 2 + binom c 2 + a·c)
                  · (binom b 2 + binom d 2 + b·d)`
    — factored Vandermonde², expands to 9 products

Concrete K_{4,3} = K_{1,1} ⊕ K_{3,2} marquee instance verified at
`MediantCohomologyFunctor.K43_{vertex,edge,face}_from_mediant`.

Anchor: `lean/E213/Lib/Math/Cohomology/MediantCohomologyFunctor.lean`.

### K_{NS, NT}^{(c)} unified classification (Stern-Brocot lattice)

Every bipartite multigraph carries a unique 3-axis position in
the Möbius P lattice:

  · `(NS / gcd, NT / gcd)` — Stern-Brocot path (coprime reduction)
  · `gcd(NS, NT)` — scale factor
  · `c` — multiplicity layer count (cohomology c-counter)

Concrete classification:

  · K_{3,2}^{(c)}: (3, 2) on `Pseq seedZero` orbit (depth 2) — canonical anchor
  · K_{4,3}^{(c)}: (4, 3) mediant of (1, 1) and (3, 2) — tree interior
  · K_{5,3}^{(c)}: (5, 3) on `Pseq seedInf` orbit (depth 2)
  · K_{3,3}^{(c)}: (3, 3) = 3 · (1, 1) — scale-3 of Stern-Brocot root

Anchor: `lean/E213/Lib/Math/Cohomology/BipartiteStermBrocotClassification.lean`.

### K_{4,3}^(c=2) base structure

  · 7 vertices, 24 edges, 18 simple 4-cycle faces
  · All 6 S-row dependence relations proven
  · Cycle space dim = 6, H² ≥ F₂¹²

Anchor: `lean/E213/Lib/Math/Cohomology/Bipartite/V43.lean`.

### K_{3,3} ↔ Möbius P bridges

  · `Mobius213K33StateClass` — vertex state (3, 3) = NS · Pseq seedZero 1
  · `Mobius213K33c3StateClass` — edge multiplicity saturation (9, 9, 9) at c=3
  · `Mobius213K33Bridge` — numerical signature ↔ Möbius P invariants

### K_{3,2}^{(c=2)} local (2, 1, 3) signature at every point

Self-containment of the (2, 1, 3) atomic multiset across every
structural locus of K_{3,2}^{(c=2)}.

  · `is_213_multiset a b c := (a+b+c == 6) && (a·b·c == 6)`.  For
    positive naturals this uniquely characterises {1, 2, 3}.
  · Vertex signature: `(NT, 1, NS) = (2, 1, 3)` at S-side;
    `(NS, 1, NT) = (3, 1, 2)` at T-side.  Same multiset.
  · Edge / face signatures: uniform `(NT, 1, NS) = (2, 1, 3)`.
  · Master `local_213_at_every_point`: 5-conjunct capstone — the
    "3" is reproduced locally at every datum of K_{3,2}^{(c=2)},
    without external partition.

Anchor: `lean/E213/Lib/Math/Cohomology/Bipartite/V32LocalSignature.lean`.

### K_{2,1,3} tripartite cohomology + self-containment bridge

Cohomology of the complete tripartite K_{NT, det, NS} = K_{2,1,3}
(with rainbow triangle 2-cells filled) and cross-frame comparison
with K_{3,2}^{(c=2)}.

  · **Betti**: (b₀, b₁, b₂) = (1, 0, 0).  Cohomologically trivial
    above H⁰.  δ¹ surjective via direct-edge pivots (each rainbow
    triangle has a unique direct edge `c_{ij}` whose indicator
    is a δ¹-preimage of the triangle's indicator).
  · **Atomic-level duality**: |E(K_{3,2})| = 6 = |△(K_{2,1,3})|
    (preserved, cross-link `TripartiteK213.bipartite_edge_eq_tripartite_triangle`).
  · **Cohomology-level non-bridge**: b₁ = 8 vs b₁ = 0.  External
    tripartite extension cannot host the (2, 1, 3) "3" — the
    self-containment reading of K_{3,2}^{(c=2)} is the only
    viable cohomology-level path.

Anchors:
  · `lean/E213/Lib/Math/Cohomology/Tripartite/V213.lean` —
    cochain types + coboundaries
  · `lean/E213/Lib/Math/Cohomology/Tripartite/V213Betti.lean` —
    Betti capstone (b₁ = b₂ = 0)
  · `lean/E213/Lib/Math/Cohomology/Tripartite/V32V213CohomologyBridge.lean` —
    self_containment_cohomology_verdict
  · `lean/E213/Lib/Math/Cohomology/Tripartite.lean` — umbrella

### Möbius P symmetry species

Catalog of 36 symmetry species (algebraic / geometric / dynamics /
rep theory / invariants / arithmetic / iteration / extended).

Anchor: `lean/E213/Lib/Math/Mobius213/Px/` (8 modules).

## Infrastructure layer

  · `lean/E213/Lib/Math/Cohomology/Infrastructure/BoolXORFold.lean` —
    `xor_pair_swap`, `psiNatPos`, `psiNatPos_linear`,
    `psiNatPos_congr_all` (graph-agnostic, funext-free)
  · `lean/E213/Lib/Math/Cohomology/Infrastructure/NatBeqHelpers.lean` —
    `nat_beq_refl'`, `nat_succ_add`, `nat_beq_add_left` (Nat.beq
    left-cancellation); `nat_beq_add_left_assoc{1,2}` (Nat.beq reassoc
    + cancel); `nat_add_left_cancel_pure` (propext-free Nat
    cancellation); `nat_decide_add_left{,_assoc1,_assoc2}` (`==` /
    `decide`-flavoured cancellation, matches `e.val == k` surface form)

## ∅-axiom standard

All theorems on the c-counter, Stern-Brocot classification, K_{NS,NT}
state classes, and Möbius P bridges satisfy strict zero-axiom
(`#print axioms` empty).  No `propext`, `Quot.sound`, `Classical.choice`,
`native_decide`, or Mathlib imports.

Build: `cd lean && lake build` — clean.

## Active research directions

### Direction A — `K_{NS,NT}^{(c)}` Lean parametric framework

V33EnrichedParametric proves codim ≥ c parametrically in `c` at
NS = NT = 3.  The full `(NS, NT, c)` parametric framework requires:

  · Generic `Fin (NS.choose 2)` S-pair indexing
  · Per-layer face boundaries depending on (NS, NT)
  · Parametric `psi_layer` over arbitrary face spaces
  · Combinatorial bound `each layer-m edge ∈ (NS-1)(NT-1) layer-m faces`

V43 (K_{4,3}) and the upcoming V44, V53, V54 give concrete
instances; the abstract `K_{NS,NT}^{(c)}` framework would unify them.

### Direction B — Arbitrary-m parametric kill via Nat.beq cancellation [CLOSED 2026-05-24]

Generalised the bottom-layer S_i / T_j cup-image kills to ANY layer
`m : Fin c`.  ψ_m kills both `cupOpp_param (starS i m) β` and
`cupOpp_param α (incidT j m)` for arbitrary `c`, `m`, `i`, `j ∈ Fin 3`
and arbitrary edge cochain.

Closure path: the bridge lemmas
`starS_at_edge_idx_same_m` / `incidT_at_edge_idx_same_m` reduce
same-layer evaluations to layer-free Nat.beq disjunctions via
`nat_decide_add_left_assoc{1,2}` (cancels the `9·m.val` offset
without `Nat.add_assoc` loops).  Rest is 6- or 9-edge β case-bash.

Note on infrastructure: `e.val == k` on `Nat` desugars to
`decide (e.val = k)` via the generic `[DecidableEq α] ⇒ BEq α`
instance — *not* `Nat.beq`.  The cancellation lemmas therefore live
in the `decide` form (`nat_decide_add_left_*`); the `Nat.beq` forms
remain in `NatBeqHelpers` for callers that emit that surface form.

Anchor: `V33EnrichedParametric.parametric_arbitrary_m_full_kill_capstone`
(7 new PURE theorems in §20, all strict ∅-axiom).

### Direction C — Cup-image dim upper bound

Current parametric result: codim ≥ c.  Upper bound `codim ≤ c`
requires explicit cup-image dim calculation — show that the c
ψ-discriminators SPAN the H²_enr / cup-image dual.

### Direction D — Pell-orbit and Stern-Brocot K_{NS, NT} witnesses

Stern-Brocot classification handles (3, 2), (4, 3), (5, 3), (3, 3).
Extending to (8, 5), (5, 4), (7, 4), (13, 8) gives the next layer
of the Möbius P lattice.  Each requires a Lean reachable witness
+ cohomology structural theorems.

### Direction E — Mediant cohomology functor [count level CLOSED]

The Stern-Brocot result `(4, 3) = (1, 1) ⊕ (3, 2)` lifted to a
**Vandermonde decomposition** of every `K_{NS, NT}^{(c)}` cell-count
quantity (V, E, F) via mediant.

Closed at the count level (22 PURE) in
`lean/E213/Lib/Math/Cohomology/MediantCohomologyFunctor.lean`:

  · `binom_add_2` (combinatorial heart, Vandermonde-2 for `binom n 2`)
  · `vertexCount_mediant` (2-term additive)
  · `edgeCount_mediant` (4-term Vandermonde)
  · `faceCount_mediant_factored` (Vandermonde²)
  · `K43_{vertex,edge,face}_from_mediant` (concrete (1,1)⊕(3,2)=(4,3))
  · `countTriple_mediant_decomposition` (3-component algebra law)
  · `mediant_cohomology_functor_capstone` (7-conjunct master)

Cross-link: K_{4,3} counts (7 vertices, 24 edges, 18 faces) recovered
from `V43.K43_{vertex,edge,simple_face}_count` via the mediant.

**Next layer** (open): lift from cell-count Vandermonde to actual
cochain-space / Massey-class decomposition.  Requires identifying
the 4 edge classes and 9 face classes as concrete sub-cochain
sub-spaces of `K_{NS₁+NS₂, NT₁+NT₂}^{(c)}` and proving the cup-product
algebra of `K_{a+c, b+d}` factors through the 4×9 = 36 mediant
sub-cells.

### Direction T — Bipartite-tripartite self-containment at K_{3,2}^{(c=2)}

`K_{3,2}^{(c=2)}` does NOT require a separate tripartite extension.
Every structural element (vertex / edge / face / cycle space /
Möbius P / Pell point) carries both '2' and '3' of the (2, 1, 3)
atomic signature simultaneously.

**Option II VERIFIED (2026-05-24)**: cohomology of external
tripartite `K_{2,1,3}` formalised; result (b₀, b₁, b₂) = (1, 0, 0)
shows cohomology-level duality FAILS (b₁ = 0 vs K_{3,2}^{(c=2)}'s
b₁ = 8).  Structural negative for external extension.

**Option I VERIFIED (2026-05-24)**: `V32LocalSignature.lean` —
master `local_213_at_every_point` (5-conjunct capstone), 15 PURE
total.  The (2, 1, 3) atomic multiset is reproduced at every
vertex, edge, and face of K_{3,2}^{(c=2)}; the "3" lives locally,
not in an external partition.

Together I + II close Direction T: the self-containment reading
of K_{3,2}^{(c=2)} is structurally established (positive: local
signature at every point) and the external extension reading is
structurally refuted (negative: b₁ mismatch).

Anchor: `research-notes/G146_K32_bipartite_tripartite_self_containment.md`.

## Anchor docs

  · `seed/AXIOM/05_no_exterior.md` §5, §8.4 — boot
  · `theory/math/cohomology/k_nm_c_classification.md` — c-counter resolution + Stern-Brocot classification (promoted from G143 + G145)
  · `theory/math/mobius213_p_orbit_closure.md` — P-orbit naturalness boundary (promoted from G146 P-orbit + Px catalog)
  · `theory/essays/bipartite_tripartite_self_containment.md` — K_{3,2}^{(c=2)} self-containment (essay, Lean Option I deferred from G146)
  · `theory/essays/{c_counter_as_layer_count,disjoint_layers_as_direct_sum,stern_brocot_as_universal_lattice,p_orbit_naturalness_boundary,vandermonde_mediant_counts}.md` — cross-cutting essays
  · `theory/math/cohomology/k_nm_c_classification.md` §"Mediant cohomology functor (count level)" — Direction E count-level closure (Vandermonde of V/E/F)
  · `theory/math/cohomology/tripartite_self_containment.md` — Direction T closure: K_{2,1,3} Betti (1,0,0) + V32LocalSignature local-(2,1,3) framework + cross-frame verdict (atomic preserved, cohomology breach)
  · `lean/E213/ARCHITECTURE.md` — layer spec
  · `theory/INDEX.md` — book map
  · `STRICT_ZERO_AXIOM.md` — PURE catalog

## Status

c-counter resolved structurally as multiplicity-layer count.
Lean formalization complete at K_{3,3}^(c=2/c=3) and parametric ∀c.
K_{4,3} base in place.  Universal K_{NS, NT}^{(c)} parametric
Lean theorem remains the open frontier.

Möbius P canonical equivalence (G139) merged with 36 symmetry
species catalog.  Px subdirectory structure consolidated.
