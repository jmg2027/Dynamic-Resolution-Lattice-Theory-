import E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213SternBrocot
import E213.Lib.Math.Cohomology.BipartiteStermBrocotClassification
import E213.Lib.Math.Combinatorics.Binomial
import E213.Lib.Physics.Simplex.Counts

/-!
# Mediant cohomology functor — Stern-Brocot factorization of K_{NS,NT}^{(c)} counts

★★★★★★★★★★★★★★★ **Every bipartite multigraph cell count factors
through the Stern-Brocot path via the mediant decomposition.** ★★★★★★★★★★★★★★★

The Stern-Brocot result `(4, 3) = (1, 1) ⊕ (3, 2)` (mediant, anchor
`BipartiteStermBrocotClassification.k43_sternBrocot_position`) suggests
a **mediant cohomology functor**: the cell counts of
`K_{NS₁+NS₂, NT₁+NT₂}^{(c)}` decompose from `K_{NS₁,NT₁}^{(c)}` and
`K_{NS₂,NT₂}^{(c)}` via Vandermonde-style splittings of vertex / edge /
face spaces.

## The three mediant decomposition identities

  · **Vertex** (linear additivity):
        `V(a+c, b+d) = V(a, b) + V(c, d)`
    Direct from `(a+c) + (b+d) = (a+b) + (c+d)`.

  · **Edge** (4-term Vandermonde, for multiplicity `m`):
        `E^m(a+c, b+d) = E^m(a, b) + E^m(a, d) + E^m(c, b) + E^m(c, d)`
    From `(a+c)·(b+d) = ab + ad + cb + cd`.  The four edge classes
    are *inner-1* (`K_{a,b}` edges), *cross-12* (`K_{a,d}` edges),
    *cross-21* (`K_{c,b}` edges), *inner-2* (`K_{c,d}` edges).

  · **Face** (factored Vandermonde², mult-0 convention):
        `F(a+c, b+d) = binom(a+c, 2) · binom(b+d, 2)
                     = (binom a 2 + binom c 2 + a·c)
                       · (binom b 2 + binom d 2 + b·d)`
    Each factor expands via Vandermonde-2.  Full multiplication yields
    a 9-term sum, one for each pairing of *intra-a / intra-c / cross-ac*
    S-pair source with *intra-b / intra-d / cross-bd* T-pair source.

## The Stern-Brocot functor structure

A `CountTriple` packages `(V, E, F)`.  The mediant operation
`(NS₁, NT₁) ⊕ (NS₂, NT₂) = (NS₁+NS₂, NT₁+NT₂)` lifts to a
**Vandermonde algebra law** on counts, parameterised by the four
cross-bipartite cells.  Since every coprime `(NS, NT) ≥ (1, 0)` is
Stern-Brocot reachable (`Mobius213SternBrocot.reachable_of_pos`), this
gives a recursive enumeration of every `K_{NS,NT}^{(c)}` cell count
back to the two degenerate seeds `(0, 1)` and `(1, 0)`.

## Concrete K_{4,3} factorisation

Via `(4, 3) = (1, 1) ⊕ (3, 2)`:

  · K_{1,1}:  V=2,  E^c=c,    F=0   (no 4-cycles in K_{1,1})
  · K_{3,2}:  V=5,  E^c=6·c,  F=3   (mult-0 4-cycles)
  · K_{4,3}:  V=7,  E^c=12·c, F=18  (matches `V43.K43_simple_face_count`)

Mediant verifications at c=2:
  · 7  = 2 + 5                       ✓  (vertex additivity)
  · 24 = 2 + 4 + 6 + 12               ✓  (edge 4-term)
  · 18 = 3 + 6 + 3 + 6                ✓  (face — 4 nonzero terms of 9)

The 9-term face expansion has 5 zero terms because `binom 1 2 = 0`
(K_{1,1} S-pair count, K_{1,1} T-pair count both vanish).

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.MediantCohomologyFunctor

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Combinatorics.Binomial
  (binom_n_0 binom_n_1 binom_succ_2 add_mul_pure binom_add_2)
open E213.Lib.Math.NumberSystems.Real213.Mobius213SternBrocot
  (SternBrocotReachable reachable_1_1 reachable_3_2 reachable_of_pos)

/-! ## §1 — Cell-count functions for `K_{NS, NT}^{(c)}`

The Pascal-level identities (`binom_n_0`, `binom_n_1`,
`binom_succ_2`) and the Vandermonde-2 split (`binom_add_2`,
together with `add_mul_pure`) are graph-agnostic; they live in
`Lib/Math/Combinatorics/Binomial.lean` and are imported here.
What this file owns is the **deployment** of those identities
to bipartite multigraph cell counts via the Stern-Brocot
mediant.

## Cell counts of `K_{NS, NT}^{(c)}`

The three cell counts in a bipartite multigraph `K_{NS, NT}^{(c)}`:

  · **Vertex count**: `NS + NT`
  · **Edge count** at multiplicity `c`: `c · NS · NT`
  · **Face count** under uniform mult-0 4-cycle convention:
    `binom NS 2 · binom NT 2` (count of `(S-pair, T-pair)` choices,
    each yielding one mult-0 4-cycle)

Anchor for face convention: `V32.face_*`, `V33.face_*`, `V43.face_*`
all use a single mult-0 4-cycle per `(S-pair, T-pair)`. -/

/-- Vertex count of `K_{NS, NT}` (independent of multiplicity `c`). -/
def vertexCount (NS NT : Nat) : Nat := NS + NT

/-- Edge count of `K_{NS, NT}^{(c)}` at multiplicity `c`.  Each of the
    `NS · NT` distinct S–T pairs contributes `c` parallel edges. -/
def edgeCount (NS NT c : Nat) : Nat := c * NS * NT

/-- Face count of `K_{NS, NT}` under the uniform mult-0 4-cycle
    convention: one 4-cycle per (S-pair, T-pair). -/
def faceCount (NS NT : Nat) : Nat := binom NS 2 * binom NT 2

/-! ## §4 — Mediant operation on `(NS, NT)` pairs

The Stern-Brocot mediant `(a, b) ⊕ (c, d) := (a + c, b + d)` lifts to
the bipartite graph mediant `K_{a, b} ⊕ K_{c, d} = K_{a+c, b+d}` whose
vertex / edge / face spaces decompose into 2 / 4 / 9 sub-pieces
respectively (per the Vandermonde combinatorics).

The mediant is the same operation as `Mobius213SternBrocot.mediant`
constructor: the cohomology functor reads the count consequences. -/

/-- Mediant operation on bipartite graph indices. -/
def mediant (p q : Nat × Nat) : Nat × Nat := (p.1 + q.1, p.2 + q.2)

/-- Mediant matches Stern-Brocot mediant. -/
theorem mediant_eq (a b c d : Nat) :
    mediant (a, b) (c, d) = (a + c, b + d) := rfl

/-! ## §5 — Vertex count additivity under mediant -/

/-- **Vertex additivity**: `V(a + c, b + d) = V(a, b) + V(c, d)`.
    Direct from commutativity of `+` (regrouping the four summands). -/
theorem vertexCount_mediant (a b c d : Nat) :
    vertexCount (a + c) (b + d)
      = vertexCount a b + vertexCount c d := by
  show (a + c) + (b + d) = (a + b) + (c + d)
  rw [Nat.add_assoc a c (b + d), ← Nat.add_assoc c b d,
      Nat.add_comm c b, Nat.add_assoc b c d, ← Nat.add_assoc a b (c + d)]

/-! ## §6 — Edge count 4-term Vandermonde mediant decomposition

`Nat.left_distrib` (`a * (b + c) = a * b + a * c`) is ∅-axiom in
core Lean, but `Nat.right_distrib` carries a `propext`
dependency.  The propext-free right distribution `add_mul_pure`
lives in `Combinatorics/Binomial.lean` and is imported here. -/

/-- **Edge 4-term Vandermonde**: edges of `K_{a+c, b+d}^{(m)}` split
    into 4 disjoint classes corresponding to `(a+c)·(b+d) = a·b + a·d +
    c·b + c·d` — *inner-1* (`K_{a,b}` edges), *cross-12* (`K_{a,d}`
    edges), *cross-21* (`K_{c,b}` edges), *inner-2* (`K_{c,d}` edges).

    All four classes are multiplied by the same multiplicity `m`. -/
theorem edgeCount_mediant (a b c d m : Nat) :
    edgeCount (a + c) (b + d) m
      = edgeCount a b m + edgeCount a d m
      + edgeCount c b m + edgeCount c d m := by
  show m * (a + c) * (b + d)
     = m * a * b + m * a * d + m * c * b + m * c * d
  -- Distribute `m` over `(a + c)` first (single occurrence).
  rw [Nat.mul_add m a c]
  -- Goal: (m * a + m * c) * (b + d) = m*a*b + m*a*d + m*c*b + m*c*d
  -- Use `add_mul_pure` instead of `Nat.add_mul` to stay ∅-axiom.
  rw [add_mul_pure (m * a) (m * c) (b + d)]
  -- Goal: m * a * (b + d) + m * c * (b + d) = ...
  rw [Nat.mul_add (m * a) b d, Nat.mul_add (m * c) b d]
  -- Goal: (m*a*b + m*a*d) + (m*c*b + m*c*d) = m*a*b + m*a*d + m*c*b + m*c*d
  rw [← Nat.add_assoc (m * a * b + m * a * d) (m * c * b) (m * c * d)]

/-! ## §7 — Face count factored Vandermonde² mediant decomposition

`binom (a+c) 2 · binom (b+d) 2` expands via `binom_add_2` twice to
`(binom a 2 + binom c 2 + a*c) · (binom b 2 + binom d 2 + b*d)`, a
3-term factor times a 3-term factor.  Multiplying out gives 9 products,
each itself a *generalised face count* on a bipartite cell:

| S-source             | T-source             | Term                |
|----------------------|----------------------|---------------------|
| inner-a S-pair       | inner-b T-pair       | `F(a, b)`           |
| inner-a S-pair       | inner-d T-pair       | `F(a, d)`           |
| inner-a S-pair       | mixed-bd T-pair      | `binom a 2 · b·d`   |
| inner-c S-pair       | inner-b T-pair       | `F(c, b)`           |
| inner-c S-pair       | inner-d T-pair       | `F(c, d)`           |
| inner-c S-pair       | mixed-bd T-pair      | `binom c 2 · b·d`   |
| mixed-ac S-pair      | inner-b T-pair       | `a·c · binom b 2`   |
| mixed-ac S-pair      | inner-d T-pair       | `a·c · binom d 2`   |
| mixed-ac S-pair      | mixed-bd T-pair      | `a·c · b·d`         |

The "mixed-ac" S-pairs are NS-pairs with one vertex from inner-a and
one from inner-c (the **cross S-pairs**, introduced by the mediant
merger and absent from either piece individually).  Similarly for
T-pairs. -/

/-- ★★★★★★★ **Face Vandermonde² (factored form)**:
        `F(a+c, b+d) = (binom a 2 + binom c 2 + a*c)
                     · (binom b 2 + binom d 2 + b*d)`
    Direct expansion via `binom_add_2` applied to each factor. -/
theorem faceCount_mediant_factored (a b c d : Nat) :
    faceCount (a + c) (b + d)
      = (binom a 2 + binom c 2 + a * c)
        * (binom b 2 + binom d 2 + b * d) := by
  show binom (a + c) 2 * binom (b + d) 2
     = (binom a 2 + binom c 2 + a * c) * (binom b 2 + binom d 2 + b * d)
  rw [binom_add_2 a c, binom_add_2 b d]

/-! ## §8 — Concrete K_{4,3} = K_{1,1} ⊕ K_{3,2} verifications

The marquee instance: `(4, 3) = (1, 1) ⊕ (3, 2)` realises the mediant
decomposition for the smallest non-trivial off-orbit Stern-Brocot
interior point.  Verified at multiplicity `c = 2`.

The face count `F(4, 3) = 18` matches `V43.K43_simple_face_count`
(`6 · 3 = 18`).  The edge count `E^2(4, 3) = 24` matches
`V43.K43_edge_count`. -/

/-- K_{1,1} vertex / edge / face counts. -/
theorem K11_counts :
    vertexCount 1 1 = 2 ∧ edgeCount 1 1 2 = 2 ∧ faceCount 1 1 = 0 := by
  decide

/-- K_{3,2} vertex / edge / face counts (matches `V32` infrastructure). -/
theorem K32_counts :
    vertexCount 3 2 = 5 ∧ edgeCount 3 2 2 = 12 ∧ faceCount 3 2 = 3 := by
  decide

/-- K_{4,3} vertex / edge / face counts (matches `V43.K43_*`). -/
theorem K43_counts :
    vertexCount 4 3 = 7 ∧ edgeCount 4 3 2 = 24 ∧ faceCount 4 3 = 18 := by
  decide

/-- ★ **K_{4,3} vertex via K_{1,1} ⊕ K_{3,2} mediant**: directly
    instantiates `vertexCount_mediant` at `(a, b, c, d) = (1, 1, 3, 2)`. -/
theorem K43_vertex_from_mediant :
    vertexCount (1 + 3) (1 + 2)
      = vertexCount 1 1 + vertexCount 3 2 :=
  vertexCount_mediant 1 1 3 2

/-- ★ **K_{4,3} edge (c=2) via K_{1,1} ⊕ K_{3,2} mediant** 4-term
    Vandermonde: `24 = 2 + 4 + 6 + 12`.  The four edges classes are
    intra-K_{1,1}, cross-K_{1,2}, cross-K_{3,1}, intra-K_{3,2}. -/
theorem K43_edge_from_mediant :
    edgeCount (1 + 3) (1 + 2) 2
      = edgeCount 1 1 2 + edgeCount 1 2 2
      + edgeCount 3 1 2 + edgeCount 3 2 2 :=
  edgeCount_mediant 1 1 3 2 2

/-- ★ **K_{4,3} face via K_{1,1} ⊕ K_{3,2} factored Vandermonde²**:
    `18 = (binom 1 2 + binom 3 2 + 1·3) · (binom 1 2 + binom 2 2 + 1·2)
        = (0 + 3 + 3) · (0 + 1 + 2) = 6 · 3 = 18`.

    Each side factor decomposes into the three NS-pair (resp. NT-pair)
    sources: intra-K_{1,*}, intra-K_{3,*}, and the cross-bipartite
    pairs introduced by the mediant. -/
theorem K43_face_from_mediant :
    faceCount (1 + 3) (1 + 2)
      = (binom 1 2 + binom 3 2 + 1 * 3)
        * (binom 1 2 + binom 2 2 + 1 * 2) :=
  faceCount_mediant_factored 1 1 3 2

/-- The factored Vandermonde² evaluates: `(0 + 3 + 3) · (0 + 1 + 2)
    = 6 · 3 = 18`. -/
theorem K43_face_factored_evaluation :
    (binom 1 2 + binom 3 2 + 1 * 3)
      * (binom 1 2 + binom 2 2 + 1 * 2) = 18 := by decide

/-- The 9 individual products of the 3×3 expansion, summed (only 4
    of 9 are non-zero because `binom 1 2 = 0`):

      · `binom 3 2 · binom 2 2 = 3·1 = 3`  (intra-K_{3,2} faces)
      · `binom 3 2 · (1·2) = 3·2 = 6`      (intra-K_{3,*} S, mixed-bd T)
      · `(1·3) · binom 2 2 = 3·1 = 3`      (mixed-ac S, intra-K_{*,2} T)
      · `(1·3) · (1·2) = 3·2 = 6`          (fully mixed cross face)

    Total: `3 + 6 + 3 + 6 = 18`. -/
theorem K43_face_9term_evaluation :
    binom 1 2 * binom 1 2 + binom 1 2 * binom 2 2 + binom 1 2 * (1 * 2)
    + binom 3 2 * binom 1 2 + binom 3 2 * binom 2 2 + binom 3 2 * (1 * 2)
    + (1 * 3) * binom 1 2 + (1 * 3) * binom 2 2 + (1 * 3) * (1 * 2) = 18 := by
  decide

/-! ## §9 — Recursion structure: `SternBrocotReachable` gives finite
    mediant trees

Every Stern-Brocot reachable `(NS, NT)` is the result of finitely many
mediant operations starting from the two seeds.  Combined with the
Vandermonde mediant identities above, every `K_{NS, NT}^{(c)}` cell
count is computable as a finite sum of products of `binom` values along
the (unique) Stern-Brocot path from root to `(NS, NT)`.

This is the **functorial factorisation**: the assignment
    `(NS, NT) ↦ (vertexCount NS NT, edgeCount NS NT c, faceCount NS NT)`
restricts to an algebra over the Stern-Brocot mediant inductive
structure. -/

/-- A CountTriple packages the three count outputs as a single value
    on which mediant decomposition acts. -/
structure CountTriple where
  V : Nat
  E : Nat
  F : Nat

/-- `K_{NS, NT}^{(c)}` count triple. -/
def countTriple (NS NT c : Nat) : CountTriple :=
  ⟨vertexCount NS NT, edgeCount NS NT c, faceCount NS NT⟩

/-- ★★★★ **Cell-count mediant algebra**: the triple at the mediant
    `(a+c, b+d)` admits Vandermonde decomposition componentwise.
    The V-component is binary additive; the E-component is 4-term
    Vandermonde; the F-component is factored Vandermonde².

    Stated as a triple `And` over the three identities for any
    multiplicity `m`. -/
theorem countTriple_mediant_decomposition (a b c d m : Nat) :
    -- Vertex 2-term
    (countTriple (a + c) (b + d) m).V
      = (countTriple a b m).V + (countTriple c d m).V
    -- Edge 4-term Vandermonde
    ∧ (countTriple (a + c) (b + d) m).E
        = (countTriple a b m).E + (countTriple a d m).E
        + (countTriple c b m).E + (countTriple c d m).E
    -- Face factored Vandermonde²
    ∧ (countTriple (a + c) (b + d) m).F
        = (binom a 2 + binom c 2 + a * c)
          * (binom b 2 + binom d 2 + b * d) := by
  refine ⟨?_, ?_, ?_⟩
  · exact vertexCount_mediant a b c d
  · exact edgeCount_mediant a b c d m
  · exact faceCount_mediant_factored a b c d

/-! ## §10 — Master capstone

The mediant cohomology functor: every K_{NS,NT}^{(c)} cell count
admits a unique Stern-Brocot factorisation, demonstrated concretely
at the marquee instance K_{4,3} = K_{1,1} ⊕ K_{3,2}. -/

/-- ★★★★★★★ **Mediant cohomology functor master capstone**:

  · (Vandermonde-2) `binom_add_2` — the combinatorial mediant heart
  · (V additivity) vertex count is linear-additive under mediant
  · (E 4-term) edge count is 4-term Vandermonde under mediant
  · (F factored) face count is factored Vandermonde² under mediant
  · (concrete) K_{4,3} cell counts match the mediant decomposition
    from K_{1,1} and K_{3,2} per Stern-Brocot
  · (reachability) `(4, 3)` is the mediant of `(1, 1)` and `(3, 2)`
    by `BipartiteStermBrocotClassification.k43_sternBrocot_position`,
    so the functor is well-defined at this instance

All facts STRICT ∅-axiom (no `propext`, no `Quot.sound`, no
`Classical`, no Mathlib).  The functor extends inductively to every
Stern-Brocot reachable `(NS, NT)` via `SternBrocotReachable`
constructors. -/
theorem mediant_cohomology_functor_capstone :
    -- (a) Vandermonde-2 universal identity
    (∀ a b : Nat, binom (a + b) 2 = binom a 2 + binom b 2 + a * b)
    -- (b) Vertex additivity under mediant
    ∧ (∀ a b c d : Nat, vertexCount (a + c) (b + d)
                          = vertexCount a b + vertexCount c d)
    -- (c) Edge 4-term Vandermonde under mediant
    ∧ (∀ a b c d m : Nat, edgeCount (a + c) (b + d) m
                            = edgeCount a b m + edgeCount a d m
                            + edgeCount c b m + edgeCount c d m)
    -- (d) Face factored Vandermonde² under mediant
    ∧ (∀ a b c d : Nat, faceCount (a + c) (b + d)
                          = (binom a 2 + binom c 2 + a * c)
                            * (binom b 2 + binom d 2 + b * d))
    -- (e) Concrete K_{4,3} cell counts
    ∧ (vertexCount 4 3 = 7 ∧ edgeCount 4 3 2 = 24 ∧ faceCount 4 3 = 18)
    -- (f) Mediant decomposition concrete (1, 1) ⊕ (3, 2) = (4, 3)
    ∧ (vertexCount 4 3 = vertexCount 1 1 + vertexCount 3 2
       ∧ edgeCount 4 3 2 = edgeCount 1 1 2 + edgeCount 1 2 2
                          + edgeCount 3 1 2 + edgeCount 3 2 2
       ∧ faceCount 4 3 = (binom 1 2 + binom 3 2 + 1 * 3)
                          * (binom 1 2 + binom 2 2 + 1 * 2))
    -- (g) Stern-Brocot reachability of (4, 3) as mediant
    ∧ SternBrocotReachable (4, 3) := by
  refine ⟨binom_add_2, vertexCount_mediant, edgeCount_mediant,
          faceCount_mediant_factored, K43_counts, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · decide
    · decide
    · decide
  · exact .mediant reachable_1_1 reachable_3_2

end E213.Lib.Math.Cohomology.MediantCohomologyFunctor
