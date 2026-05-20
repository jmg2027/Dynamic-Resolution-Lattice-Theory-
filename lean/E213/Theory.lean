import E213.Theory.Atomicity
import E213.Theory.CDDouble
import E213.Theory.Raw.API
import E213.Theory.RawCmpIndependence

/-! Spec-as-code entry point for `E213.Theory`.

  Theory ring (ARCHITECTURE.md) — the 213 axiom itself: `Raw` type
  + 4-clause definitional commitments (a, b, slash, slash_comm).
  Plus forced-shape proofs (Atomicity) and structural observables
  (depth, leaves, fold, swap).  Built on Term API (Tree machinery).
  Consumed by Lens.

  ## Three-direction uniqueness (per `seed/AXIOM/00_nature.md` §1.3)

  Raw's uniqueness is closed in three directions, all three being
  readings of the same self-consistency:

    * **Below** — nothing weaker than Raw is sufficient.
      `Meta/AxiomMinimality.lean` (+ Capstone): removing any of
      the 4 clauses collapses the framework.

    * **Sideways** — nothing distinct from Raw is needed.
      `Meta/UniversalLens/`: any distinguishability framework
      factors through Raw via an injective Lens view.

    * **Above** — Raw's own shape is forced.
      `Theory/Atomicity/*` (pure-ℕ, no Raw import):
      (NS, NT, d) = (3, 2, 5) is the only self-consistent fixed
      point under atomicity + arity constraints.

  None of the three directions stands "outside" 213; they are
  three internal readings of the residue's self-consistency.

  ## Sub-clusters

    * `Atomicity/`  — forced-shape proofs (Alive, ArityForcing,
                      Five, FiveHelpers, NonDecomposable,
                      PairForcing, PrimitiveSizes)
    * `Raw/`        — public Raw API (Core, Slash, Swap, SwapSlash,
                      Fold, Hom, Levels, Rec, Signed, Endomorphic)
                      + auxiliary (Congruence, ParenthesizationDistinct)
    * `CDDouble/`   — generic Order-4 Cayley-Dickson double mechanism
    * `RawCmpIndependence.lean` — axiom-independence of the cmp
                      choice (cmp is an encoding artifact per
                      §8a.1; any well-behaved order yields
                      isomorphic Raw types)
-/
