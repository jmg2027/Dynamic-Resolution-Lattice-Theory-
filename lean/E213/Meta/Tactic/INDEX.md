# Kernel/Tactic/ — INDEX

213-native tactics + helper lemma collections.  Each `.lean` file
covers one *trajectory-vocabulary domain*.  All theorems verified
∅-axiom (no `propext`, no `Quot.sound`).

See `research-notes/G2_trajectory_principle.md` and
`G3_raw_as_universal_trajectory.md` for the unifying frame.

## Files (production)

| File | Topic | Theorems | Layer |
|---|---|---:|---|
| `Omega213.lean` | linear ℕ-arithmetic tactic | 1 macro | tactic |
| `Nat213.lean` | pure ℕ-arithmetic helpers (cancellation, sub/add, mul) | 13 | helper lemmas |
| `List213.lean` | propext-free `List` helpers (`append_nil`, `append_assoc`, `length_append`, `length_append_rev`, `length_map`) | 5 | helper lemmas |
| `Mod213.lean` | cohomological-trajectory primitives (parity, mod3, mod6, CRT) + parity bridges | 15 | trajectory primitives |
| `Fin213.lean` | `Fin` helpers (∅-axiom `Fin 0` elim) | 1 | type-specific helpers |
| `Pow213.lean` | power-of-2 + divisibility (∅-axiom replacements for `Nat.pow_lt_pow_of_lt`, `Nat.pow_dvd_pow`, `Nat.le_of_dvd`, `Nat.dvd_sub`) | 6 | trajectory composition |
| `QuadNorm.lean` | quadratic norm tactic | — | tactic |

## Documentation

  - `AXIOM_FREE_STATUS.md` — migration status, leak catalog,
                             methodology, full theorem list
  - `OMEGA213_MIGRATION.md` — original `omega → omega213` guide

## Tests

  - `Test/QuadNormTest.lean` — QuadNorm tactic tests

## Layering principle

Each file is *one* coherent topic.  Prefer extending an existing file
when the topic matches; create a new sibling when a *distinct
trajectory-vocabulary* emerges.

Examples of distinct topics that *would* warrant a new file:
  - `Int213.lean` — Int-arithmetic ∅-axiom helpers (Lean-core
    Int lemmas mostly bring propext; substantial replacement
    project — deferred)
  - `Bool213.lean` — Bool helpers if a substantial set accumulates
    beyond what `decide_eq_true/false` covers
  - `Mod213_pow.lean` — mod-of-power-of-2/3 cascade primitives
    (extending Mod213 for `mod (2^a · 3^b)` walks)

## Naming convention

`<Type>213.lean` for ∅-axiom helper modules over `<Type>`.  This
makes them grep-able and signals the strict-axiom guarantee.
