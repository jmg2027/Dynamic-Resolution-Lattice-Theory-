# Cut equality and atomicity

In 213, two cuts are equal when they agree on the mediant
closure of the two Möbius seeds `(0, 1)` and `(1, 0)` — and on
canonical cuts that is unconditional pointwise equality.  The
matrix that generates the closure is the same matrix that
encodes atomicity.

## 213-native answer

A `Cut` is a `Nat → Nat → Bool` reading.  Two cuts `cx`, `cy`
are **equal** when they evaluate identically at every coordinate
that the Möbius matrix `P = [[2,1],[1,1]]` can write —
operationally, when

    `∀ (m, k), SternBrocotReachable (m, k) → cx m k = cy m k`

holds, together with `cx 0 0 = cy 0 0` at the single coordinate
the mediant closure cannot reach.  This is
`cutEq_iff_sternBrocotEq_and_zero` in
`Mobius213SternBrocot.lean`.

`SternBrocotReachable` is the inductive closure of `(0, 1)`,
`(1, 0)` under the mediant rule `(a, b) ⊕ (c, d) = (a+c, b+d)`.
The two extension lemmas `reachable_succ_fst` (mediant with
`seedInf`) and `reachable_succ_snd` (mediant with `seedZero`)
walk this closure across every pair with `m + k ≥ 1`
(`reachable_of_pos`).  The `(0, 0)` coordinate is structurally
absent — the constructors preserve `m + k ≥ 1`, so it sits
outside the mediant orbit.

## Derivation

Two readings converge.

**Combinatorial side.**  `Theory.Atomicity.Five.atomic_iff_five`
proves `5` is the unique Nat admitting an alive `2a + 3b`
decomposition.  `Theory.Atomicity.PairForcing` fixes
`(NS, NT) = (3, 2)`.  The pair `(3, 2)` is mediant-reachable as
`(2, 1) ⊕ (1, 1)`, i.e., `reachable_3_2` in
`Mobius213SternBrocot.lean`.

**Algebraic side.**  The Möbius matrix has
`(trace, det, disc) = (3, 1, 5) = (NS, NS−NT, NS+NT)`
(`Lib/Math/Algebra/Mobius213.lean` — `mobius_213_trace`,
`mobius_213_det`, `mobius_213_discriminant`).  Iterating P on
`(0, 1)` gives `(0, 1), (1, 1), (3, 2), (8, 5), ...` —
`Pseq seedZero n` from `Mobius213Equiv.lean`.  At depth 2 the
orbit hits `(NS, NT) = (3, 2)` exactly
(`orbits_hit_atoms_at_depth_2`).

The two readings meet in `disc_atom_orbit_master`
(`Mobius213AtomicityAnchor.lean`): the integer `5` is
simultaneously `NS + NT`, `disc(P) = trace² − 4·det`, `unique
atomic Nat`, and `(Pseq seedInf 2).1`.  And `(NS, NT)` is
mediant-reachable AND Pseq-reachable AND the orbit's depth-2
image of the rational `0/1`.

The cut framework's equivalence relation `cutEq` falls out as
the agreement of `cx`, `cy` at every position the matrix can
write.  Forward: if `cx m k = cy m k` everywhere, then in
particular at every reachable `(m, k)`, plus at `(0, 0)`.
Backward: `reachable_of_pos` covers everything except `(0, 0)`,
which the side condition fills.  The iff is `Iff.rfl`-clean
modulo the boundary.

For canonical cuts — anything built from `constCut a N` (whose
`(0, 0)` value is `decide (a · 0 ≤ N · 0) = true` regardless of
`a`, `N`) — the boundary condition is automatic.  This is
`validCutN_zero_zero`, `constCut_zero_zero`, and propagation
through `cutSumN`, `cutMul`.  On every `ValidCutN N` instance
(`validCutN_cutEq_iff_sternBrocotEq`), every signed cut built
from canonical components
(`signedEq_iff_sternBrocotEq_of_canonical`), and every
`cutSumN N`-derived cut, `cutEq` and `sternBrocotEq` are the
same relation.

## Dual function

This is not "213's version of pointwise equality, distinct from
the classical one".  Pointwise equality on `Nat → Nat → Bool`
agrees with mediant-orbit equality at every `(m, k)` the
framework's cuts actually distinguish — the mediant closure
gives back ℕ × ℕ minus a single boundary, and the boundary is
filled automatically on every canonical cut.  The classical
reading carries redundant packaging — "agree at coordinates the
matrix cannot reach" is the redundancy `sternBrocotEq` strips.
The Möbius P matrix is not a tool *applied to* equality; the
matrix's mediant closure IS what "agreement on cuts" means once
the redundancy is removed.

## Cross-frame convergence

The integer `5` shows up four ways simultaneously
(`disc_atom_orbit_master`): `disc(P)`, the unique atomic Nat,
`NS + NT`, and the first component of `Pseq seedInf 2`.  The
pair `(3, 2)` shows up three ways: `(NS, NT)`,
`SternBrocotReachable` constructor expression, and
`Pseq seedZero 2`.  The same `P` carries the canonical
equivalence (its mediant closure), the algebraic invariants
(trace/det/disc), the Pell unit cross-product on the orbit
(`Pseq_cross_pell_invariant` — Nat-side of
`mobius_213_pell_unit_invariant_forall`), and the fixed point
`φ²` (`Mobius213.lean` §3).

The fact that one matrix carries this much structure is not a
coincidence to admire.  It is what "Möbius P is the algebraic
representation of the residue's self-pointing fixed point"
(`seed/AXIOM/03_form.md` §3.5,
`seed/AXIOM/05_no_exterior.md` §5.6) becomes when read at the
level of cut equality.  The residue's self-pointing leaves the
forced triple `(NS, NT, d) = (3, 2, 5)` (read at presentation
`c = 2`, a free presentation parameter) and a matrix `P` whose
spectrum is `{φ², 1/φ²}`; "two cuts are equal" reads the same
matrix as a mediant operation.

## Open frontier

Different domains carry their own equality definitions that have
not been bridged:

  · `ZpSeqEquiv` on `Nat → Fin p` digit sequences
    (`Padic/SetoidFramework.lean`) — different domain.
    `Mobius213ModFive.lean`'s `P¹⁰ ≡ I (mod 5)` is the
    structural starting point for a mod-p analog but no Lean
    bridge exists yet.
  · `LensMap` (`Padic/SetoidFramework.lean`) is the categorical
    packaging of `respects ≈` morphisms; a `CutSetoid` version
    showing `cutSumN`, `cutMul`, `addN` as LensMaps is not done.
    Care needed to avoid `Quot.sound` (no quotient — bundled
    witnesses only).
  · `cutMulN N` parametric multiplication analog of `cutSumN N`
    is not yet implemented; Stern-Brocot congruence will follow
    once the cut-level closure exists.

The framework's `Adjacent` predicate on `DyadicBracket` already
gives function equality at the wall cut
(`adjacent_walls_match`), so its `sternBrocotEq` corollary is a
one-liner — not yet recorded as a separate theorem.
