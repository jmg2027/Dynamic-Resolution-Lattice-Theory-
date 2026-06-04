# UniverseChain — deductive chain from atomicity (∅-axiom)

This sub-tree consolidates in a single deductive chain the
∅-axiom theorems anchored at the **atomicity statement** and the
parametric vertex-count recursion `numV L = d^L`.

Atomic forcing (NS = 3, NT = 2, d = 5) and the residue are
foundational.  The vertex-count recursion is parametric: no
fractal level is privileged, the tower has no top.

## Reading order

| File              | Step | Statement |
|-------------------|------|-----------|
| `Residue.lean`       | 0 | distinction → residue (Raw inhabitant) → recursion automatic |
| `Atomicity.lean`     | 1 | `Atomic n ⟺ n = 5` |
| `Decomposition.lean` | 2 | `5 = 2·1 + 3·1`, unique alive decomp |
| `PairAxes.lean`      | 3 | `NS = 3, NT = 2, NS + NT = d` |
| `Recursion.lean`     | 4 | `numV L = 5^L` (parametric, no privileged level) |

Each step imports only the previous step + the underlying
existing modules.

## Möbius extension (algebraic-geometric realization)

Post-atomicity → algebraic-geometric realization
of (NS, NT, d) via Möbius P matrix `[[2, 1], [1, 1]]`.

| Step | Source | Statement |
|------|--------|-----------|
| 6 | G70 | Raw + Nat213 ctors → (NS=3, NT=2, d=5) |
| 7 | G74-75 | `1 = glue = NS-NT = det(P)` (axis-generator output) |
| 8 | G77 | Lucas seeds atomicity: L_0=NT, L_1=NS, L_2=7 |
| 9 | G78 | Pentagonal closure: P^10 ≡ I (mod 5) |
| 10 | G79 | SL(2,F_5) ≅ 2I (\|2I\|=120=24·5) |
| 11 | G80 | Δ⁴ ⊥ K_{3,2}^{(2)}: χ sum = -(NS·NT) |
| 12 | G81 | CRT (mod 5, mod 2) = pentagon × triangle |

Theorems are split across the current 4-ring layout:
`Lens/Number/Nat213/{Core,Lenses,AtomicityCorrespondence}.lean`,
`Lib/Math/Algebra/Mobius213OneAsGlue.lean`,
`Lib/Math/Geometry/Nat213{Rotation,AlgebraicGeometry}.lean`, and
`Lens/Number/Nat213/Tower/{NatPairToInt,NatTripleToZ2,NatPairToQPos}.lean`.
102 ∅-axiom theorems in the extension.

**Step 0 (Residue)** formalises Mingu's articulation
> "구분을 하면 항상 잔여물이 남는거 아냐?"

= G29 point 3 ("그 짝도 다시 가리킬 수 있다")
= the type signature `slash : (x y : Raw) → x ≠ y → Raw`.

The codomain `Raw` of `slash` makes the residue an inhabitant of
the same type as its inputs — so it can re-enter the constructor.
Recursion is *not* a separate Lens layer; it is the structure of
distinction itself.

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
  * `Lib/Math/ResolutionLimit.lean`

This sub-tree makes the deductive flow Atomicity → 5 → (3, 2) →
parametric recursion visible without hopping through unrelated
neighbours.
