import E213.Theory.Raw
import E213.Theory.Atomicity

/-! # Theory layer public API

  Single import for downstream consumers.  Bundles the two
  parts of the 213 axiomatic commitment:

  ## TH-A — Raw axiom data

  The 213 commitment itself: `Raw` type + 4 clauses
  (`Raw.{a, b, slash, slash_comm}`) + the structural
  primitives that follow (`depth`, `leaves`, `fold`, `swap`,
  `rec`).  Sourced from `Theory.Raw`.

  Public names:
    * `Raw`, `Raw.a`, `Raw.b`
    * `Raw.slash`, `Raw.slash_comm`
    * `Raw.depth`, `Raw.leaves`
    * `Raw.fold`, `Raw.fold_a`, `Raw.fold_b`, `Raw.fold_slash`
    * `Raw.swap`, `Raw.swap_a`, `Raw.swap_b`, `Raw.swap_swap`
    * `Raw.swap_depth`, `Raw.swap_leaves`
    * `Raw.fold_eq_depth`, `Raw.fold_eq_leaves`
    * `Raw.fold_signed_swap`, `Raw.fold_swap_hom`
    * `Raw.rec` (eliminator)

  ## TH-B — Atomicity (forced shape uniqueness)

  Spec-compliance proof that the Raw shape is unique up to
  isomorphism: any abstract atomic structure with the right
  conditions must instantiate as the Raw axiom's choice
  (d=5, NS=3, NT=2, sizes {2,3}, alive (1,1), arity k=2).
  Sourced from `Theory.Atomicity`.

  Public names:
    * `Atomicity.Five.atomic_iff_five`
    * `Atomicity.Five.canonical_partition`
    * `Atomicity.Five.IsAlive`
    * `Atomicity.PairForcing.pair_forcing`
      (+ `atomic_23_iff_five`, `count_eq_one_iff`)
    * `Atomicity.NonDecomposable.non_decomposable_iff`
    * `Atomicity.ArityForcing.no_reachable_rel3`
      (+ `reachable3_only_object`)
    * `Atomicity.PrimitiveSizes.{pairSize, closureSize}`
      (+ `pairSize_nondecomposable`, `closureSize_nondecomposable`,
       `primitive_sizes_eq_nondecomposable`)
    * `Atomicity.Alive.alive_iff_odd_pair`
      (+ `Survives`, `BothSurvive`, `survives_iff_odd`)
    * `Atomicity.FiveHelpers.*` (helpers)

  ## Sealed (NOT API — direct import discouraged)

    * `Term.Internal.Tree.*` (Tree machinery — lives under
      `Term/Internal/Tree*.lean` with the `E213.Term.Internal`
      namespace umbrella, path-aligned 2026-05-15)

  Both halves of TH-A + TH-B are required for any Lens consumer.
-/
