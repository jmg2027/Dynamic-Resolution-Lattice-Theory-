# UniverseChain — deductive chain Atomicity ⇒ N_U (∅-axiom)

This sub-tree gathers the (previously fragmented) ∅-axiom
theorems linking the **atomicity statement** to the **universe
constant** `N_U = 5²⁵`, in deductive order.

The content is *not new* — every theorem is a re-export or
trivial wrapper around an already-∅-axiom-proven result in
`Theory/Atomicity/`, `Lib/Physics/Simplex/Counts.lean`, or
`Lib/Physics/Foundations/NUniverse*.lean`.  The point of this
sub-tree is to make the chain *visible in one place*.

## Reading order

### Forward chain (Atomicity → N_U)

| File              | Step | Statement |
|-------------------|------|-----------|
| `Atomicity.lean`     | 1 | `Atomic n ⟺ n = 5` |
| `Decomposition.lean` | 2 | `5 = 2·1 + 3·1`, unique alive decomp |
| `PairAxes.lean`      | 3 | `NS = 3, NT = 2, NS + NT = d` |
| `Recursion.lean`     | 4 | `numV L = 5^L`; self-ref `L = d² = 25` |
| `Universe.lean`      | 5 | `N_U = d^(d²) = 5²⁵` |
| `Synthesis.lean`     | — | full forward chain bundle |

### Self-reference closure (why 213 doesn't explode)

| File                           | Statement |
|--------------------------------|-----------|
| `Lawvere.lean`                 | Lawvere fixed-point theorem (Russell / Curry / Girard / Cantor common mechanism); Cantor as corollary |
| `SelfReferenceClosure.lean`    | Raw admits universal Lens (safe self-reference) ∧ no Bool-surjection on Raw (paradoxical self-reference structurally blocked) |
| `Godel.lean`                   | Abstract Gödel-incompleteness via Lawvere: any (Pr, Repr, Repr_correct) is contradictory; Tarski's undefinability of truth; specialised to Raw |

### Completeness ledger

| Sense              | Holds in 213? | Witness |
|--------------------|---------------|---------|
| **Constructive**   | ✓             | ∅-axiom standard (every theorem `#print axioms` empty) |
| **Decidability**   | partial       | every `Decidable P` instance decides `P` |
| **Gödel**          | ✗             | `Godel.no_self_referential_decision` (abstract / via Lawvere) |

Each step imports only the previous step + the underlying
existing modules.

## ∅-axiom status

Every theorem in this sub-tree has `#print axioms` empty.

The currently *non-clean* fact `Theory.Atomicity.PairForcing.
pair_forcing` (depends on `propext`, `Quot.sound` via `omega`)
is **not** in this chain.  Step 3 uses only the clean
`Counts.partition_sum` (`NS + NT = d`); the full pair-uniqueness
statement is left as a separate marathon target (out of scope
for this chain).

## Why a separate directory?

The same theorems are scattered across:
  * `Theory/Atomicity/Five.lean`
  * `Theory/Atomicity/PairForcing.lean` (partly dirty)
  * `Lib/Physics/Simplex/Counts.lean`
  * `Lib/Math/Cohomology/Fractal/Level.lean`
  * `Lib/Physics/Foundations/NUniverseFromFractal.lean`
  * `Lib/Physics/Foundations/NUniverseFractalDepth.lean`
  * `Lib/Math/ResolutionLimit.lean`

This sub-tree makes the deductive flow Atomicity → 5 → (3, 2) →
recursion → 5²⁵ visible without hopping through unrelated
neighbours.
