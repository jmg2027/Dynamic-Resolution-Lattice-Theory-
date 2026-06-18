# Genuine exotic-ℝ⁴ / Akbulut-cork rebuild (post-deletion of the bogus layer)

Companion to `research-notes/frontiers/genuine_hodge_rebuild.md` — same
honesty contract.

## 1. What was deleted & why bogus

The "Akbulut cork in 213" layer welded smooth-4-manifold names to `Nat`
parity arithmetic:

  · `corkTwist := (p + 1) % 2` — a `Nat`-parity flip presented as "the
    cork's boundary involution / twist". A `% 2` is not an involution of a
    contractible 4-manifold's boundary; it is `Bool` arithmetic.
  · the "cork" was a hardcoded literal, "exotic-ness" a `decide` on a
    parity, and the "doesn't extend to a diffeomorphism" obstruction was
    simply absent — there was no manifold, no boundary, no diffeomorphism.

A famous name welded to `(p+1)%2` is precisely the forcible-map the audit
removes.

## 2. The genuine content

  · **Exotic ℝ⁴**: a smooth 4-manifold homeomorphic but **not
    diffeomorphic** to standard `ℝ⁴`. ℝ⁴ is the *only* Euclidean space
    with exotic smooth structures, in fact uncountably many — the deepest
    result of 4-dimensional smooth topology, from **Freedman**
    (topological h-cobordism / classification of simply-connected
    topological 4-manifolds, 1982) combined with **Donaldson** (gauge
    theory / the diagonalizability obstruction on definite intersection
    forms, 1983).
  · **Akbulut cork**: a compact contractible smooth 4-manifold `C` with
    boundary, together with an involution `τ : ∂C → ∂C` of its boundary
    that **extends to a self-homeomorphism of `C` but does NOT extend to a
    self-diffeomorphism**. The cork theorem (Curtis–Freedman–Hsiang–Stong,
    Matveyev): any two homeomorphic-but-not-diffeomorphic simply-connected
    closed 4-manifolds differ by removing one such cork and regluing by
    `τ`. The cork *localises* exoticness into a contractible piece.

The load-bearing objects are: a **smooth structure**, an **intersection
form** (a unimodular symmetric bilinear form on `H₂`), Donaldson's
**definite-form diagonalisability** obstruction, and a **boundary
involution that fails to extend smoothly**.

## 3. The 213-native obstruction (brutally honest)

The substrate **has no smooth structures whatsoever** — and exotic ℝ⁴ is
*entirely* a statement about smooth vs. topological structure. Concretely:

  · No smooth manifold, no diffeomorphism, no homeomorphism, no boundary,
    no gauge theory, no anti-self-dual connection, no contractibility of a
    4-manifold. None of these exists in `Nat`/`Int`/graph/`Real213`.
  · The genuine seam that *does* exist is the **intersection-form**
    machinery on surfaces (`Cohomology/Surfaces/`): real unimodular
    symmetric forms, signatures, the `T⁴` form of signature `(3,3)`
    (`T2Squared/HodgeIndex.lean`). An intersection form is *one* ingredient
    of the 4-manifold story — but a form on its own carries no smooth
    structure and no diffeomorphism, so it cannot witness exoticness.

So exotic ℝ⁴ / the cork is **not reachable** in the current substrate.
What is reachable is honest finite-group / orbit combinatorics about the
*boundary symmetry* — with **no 4-manifold claim attached**.

## 4. Staged plan

**Stage 1 — honest Burnside / orbit combinatorics (NO 4-manifold claim).**
A cork's defining feature is a **boundary involution that acts on a finite
symmetric structure**. The substrate has a clean, genuine seam for finite
group actions and their orbit counts: `Combinatorics/Sym3OctetOrbits.lean`
(this is the surviving home of the `sym3OrbitCount = 60` work). It proves,
∅-axiom, by Burnside / Cauchy–Frobenius:
  · per-element fixed-cochain counts `|Fix(s)| = 32`, `|Fix(ρ)| = 4`;
  · `orbitCount = (256 + 3·32 + 2·4)/6 = 60` (`sym3_burnside_arithmetic`,
    `sym3_burnside_sum`);
  · inclusion–exclusion `|Fix(s)∪Fix(t)∪Fix(u)| = 3·32 − 3·4 + 4 = 88`
    (`transpFixedCount_eq_88`);
  · orbit-size decomposition `(4, 0, 28, 28)` (`suborbit_decomposition`).
Stage 1 = state this purely as **a finite group action and its orbit
structure** — a genuine theorem. Specifically, an **involution acting on
a finite ℤ/2-module**, with its fixed-set count, is the honest
combinatorial residue of "boundary involution acting on a structure". It
is *not* a cork; do not call it one.

**Stage 2 — involution / fixed-point combinatorics.** Isolate a single
involution `τ` (e.g. `M_S01`, with `M_S01² = Id` proved in
`OctetModule.lean`) and study the question "does `τ` extend to / commute
with a larger automorphism group?" purely group-theoretically. The
*combinatorial* obstruction "an involution of a substructure that does not
extend to an automorphism of the whole" is a genuine, reachable target —
and is the closest honest shadow of the cork's "extends topologically, not
smoothly". It captures **extends/doesn't-extend**, but at the level of
*group homomorphisms*, NOT diffeomorphisms.

**Stage 3 — unimodular-form arithmetic.** Build out
`Cohomology/Surfaces/` toward the genuine *arithmetic* side of 4-manifold
topology: classification of small unimodular symmetric bilinear forms by
rank / signature / definiteness, and the statement of Donaldson's
diagonalisability constraint *as an arithmetic fact about forms* (definite
unimodular forms realised by smooth simply-connected 4-manifolds are
diagonal). This is reachable as **pure form arithmetic**; it is NOT a
proof of Donaldson's theorem, which is gauge-theoretic.

**Stage 4 — research arc (may never be reachable here).** A 213-native
smooth-vs-topological structure distinction, a contractible 4-manifold, a
boundary 3-manifold with an involution, and a notion of "extends
smoothly". This is from-scratch differential/gauge topology in the
substrate — a very long arc, plausibly unreachable.

## 5. Honest scope

Nothing here proves, approaches, or witnesses the existence of exotic ℝ⁴
or an Akbulut cork.
  · `Sym3OctetOrbits.*` is a **proven ∅-axiom Burnside orbit count for a
    finite group action** — genuine combinatorics, no manifold content.
  · `OctetModule.M_S01_squared` etc. are **proven involution relations on
    a ℤ/2-module** — group theory, not boundary diffeomorphisms.
  · The `Surfaces/` intersection forms are **proven unimodular-form
    arithmetic** — one ingredient of 4-manifold topology, carrying no
    smooth structure.
  · Freedman's classification, Donaldson's theorem, the existence of
    exotic ℝ⁴, and the cork theorem are **classical mathematics, entirely
    open in this substrate** (no smooth manifold exists). No file may cite
    any 213 result as "exotic ℝ⁴", "Akbulut cork", or "Donaldson's
    theorem".

## 6. Cross-references (genuine kept seams)

  · `lean/E213/Lib/Math/Combinatorics/Sym3OctetOrbits.lean` (Stage 1 —
    Burnside orbit count `= 60`, fixed-set counts, orbit-size decomposition)
  · `lean/E213/Lib/Physics/Symmetry/OctetModule.lean` (the Sym(3) action,
    involution relations `s² = t² = (st)³ = e`, fixed subspace)
  · `lean/E213/Lib/Math/Cohomology/Surfaces/T2Squared/HodgeIndex.lean`
    (Stage 3 — `T⁴` intersection form, signature `(3,3)`)
  · `lean/E213/Lib/Math/Cohomology/Surfaces/` (intersection-form library,
    P1²/P2/T2 forms — unimodular-form arithmetic)
