# `Theory/Atomicity/` — Raw axiom shape forced uniqueness

Proofs that the Raw axiom's atomic structure (d=5, NS=3, NT=2,
primitive sizes {2, 3}, arity k=2, alive-pair (1, 1)) is the
**unique consistent choice** under abstract structural conditions.

## Theoretical role

Each file is a pure-ℕ theorem.  None of them imports
`Theory/Raw.lean` directly.  They are NOT consequences of Raw —
they are **structural forcings of Raw's shape** read at the ℕ
chart (cf. `seed/AXIOM/05_no_exterior.md` §5.1 — no
exterior standpoint; the forcing is internal to 213, expressed
through a Lens that does not yet name Raw).  The Theory Raw
axiom is then justified *because* it instantiates the unique
structure these theorems force.

## Files (10)

| File | Proof |
|---|---|
| `Five.lean`              | n = 2a + 3b alive-unique ⇔ n = 5 |
| `FiveHelpers.lean`       | Helper lemmas for `Five` |
| `PairForcing.lean`       | (2, 3) is the unique coprime pair with a unique atomic n |
| `NonDecomposable.lean`   | {2, 3} are exactly the non-decomposable integers ≥ 2 |
| `Alive.lean`             | "alive" predicate (both atom-multiplicities odd) |
| `AliveDerivation.lean`   | alive ⇔ clause-4 no-self-pair, derived (not posited) |
| `ArityForcing.lean`      | k = 2 is the unique non-degenerate, non-vacuous arity |
| `CombinatorialArity.lean` | combinatorial arity: `k ≥ 3` is vacuous over `Fin 2` base |
| `PrimitiveSizes.lean`    | atom set {pairSize=2, closureSize=3} from the axiom |
| `OrbitForcing.lean`      | Pell-Lucas coefficients `(NS, det) = (3, 1)` forced from atomic seeds + `L(2) = 7` (orbit dynamics layer) |

## Related files elsewhere

  - `Lib/Math/Combinatorics/Pigeonhole.lean` — universal Fin
    pigeonhole infrastructure (not atomicity-specific).
  - `Lib/Math/Foundations/ArityForcingGeneral.lean` — general
    `N < k` pigeonhole arity result (not atomicity-specific).

## Where to add new files

  - New shape-forcing theorem  → match the existing 1-theorem-per-
                                  file pattern, name by what
                                  parameter is forced
  - Helper lemma               → `<Theorem>Helpers.lean`
