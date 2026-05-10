# G82: Möbius extension chain summary (G65-G81 navigable index)

## Purpose

Single-page navigation entry for the post-atomicity Möbius
extension chain (G65 → G81).  Compresses 17 individual research
notes into a unified narrative + theorem index.

## The chain

```
Atomicity (NS=3, NT=2, d=5) [UniverseChain Steps 1-5]
        │
        ▼
Step 6: Raw + Nat213 ctor count = (NS, NT, d)        [G70]
        │
        ▼
Step 7: Möbius P encodes atomicity                    [G74-75]
        - top-left = NT, trace = NS, det = glue
        - 1 = glue = NS - NT = det(P)
        │
        ▼
Step 8: Lucas seq seeds atomicity                     [G77]
        - L_0 = NT, L_1 = NS
        - L_2 = 7 (= Mersenne M_3, = -χ(K_{3,2}^(2)))
        │
        ▼
Step 9: Pentagonal closure                            [G78]
        - P^5 ≡ -I (mod 5), P^10 ≡ I (mod 5)
        - Spiral starts at (NS, NT)
        │
        ▼
Step 10: SL(2, F_5) ≅ 2I                             [G79]
        - |2I| = 120 = 24 · 5
        - K_{3,2}^{(2)} cohomology: H^1 = ℤ^8
        │
        ▼
Step 11: Dual fillings (Δ⁴ ⊥ K_{3,2}^{(2)})          [G80]
        - χ(Δ⁴) + χ(K_{3,2}^{(2)}) = 1 + (-7) = -6
        - = -(NS · NT) = -(Type C ZOmega units)
        │
        ▼
Step 12: CRT (mod 5, mod 2) decomposition             [G81]
        - mod 5: order 10 = pentagonal D_5
        - mod 2: order 3 = triangular S_3
        - lcm = 30 = full closure
```

## Research notes index

| Note | Topic | Status |
|---|---|---|
| G65 | Nat213 type synthesis | active |
| G66 | Lens classification (Raw → Nat213) | active |
| G67 | Raw fractal via lenses | absorbed by G68 |
| G68 | Fractal atom = Nat213.one | active |
| G69 | Addition as slash-projection | active |
| G70 | Atomicity in lens fractal | **key** |
| G71 | Fold-direction duality | speculative |
| G72 | Division as axis-generator fold | **key** |
| G73 | Two fold families notation | active |
| G74 | 1 as glue / rotation axis | **key** |
| G75 | det = axis-generator fold output | **key** |
| G76 | 213-native rotation geometry | active |
| G77 | Lucas/Mersenne dual at 7 | **key** |
| G78 | Pentagonal closure P^10 ≡ I | ★ key |
| G79 | SL(2, F_5) ≅ 2I, cohomology | **key** |
| G80 | c=2 doubling, dual fillings | **key** |
| G81 | CRT (mod 5, mod 2) decomposition | **key** |

★ = session-defining discovery
**key** = essential to the chain narrative

## Lean ∅-axiom inventory

`Theory/Nat213/`:
- `Core.lean` — 12 theorems (Nat213 type, no_absorbing, add_comm, no_closed_sub)
- `Lenses.lean` — 19 theorems (lens framework, fractal atom, addition emergence)
- `AtomicityCorrespondence.lean` — 5 theorems (NS=3 ctors, NT=2 ctors)
- `OneAsGlue.lean` — 14 theorems (glue, det, P inverse)
- `RotationGeometry.lean` — 25 theorems (Pell-Fib, pentagonal closure, Lucas/Mersenne)
- `AlgebraicGeometry.lean` — 17 theorems (SL(2,F_5)≅2I, K_{3,2} cohomology, CRT, dual fillings)

`Theory/Tower/`:
- `NatPairToInt.lean` — 12 theorems (orthogonal-axis ℕ²→ℤ)
- `NatTripleToZ2.lean` — 6 theorems (3-axis Eisenstein)
- `NatPairToQPos.lean` — 4 theorems (multiplicative quotient)

`Lib/Math/UniverseChain/`:
- `MobiusChain.lean` — 1 sentinel + index of all above

**Total: ~115 ∅-axiom theorems** in the Möbius extension.

## How to read this chain

For the FIRST-TIME reader:
1. Start with G70 (atomicity in lens fractal) — the framework setup
2. G74-G75 (glue, det) — the structural insight
3. G78 (pentagonal closure) — the geometric meaning
4. G79 (SL(2,F_5) ≅ 2I) — the algebraic realization
5. G81 (CRT) — the deepest decomposition

For VERIFICATION:
- Open `Theory/Nat213/AlgebraicGeometry.lean`
- The headline theorems `algebraic_geometric_core`,
  `dual_fillings_sum_eq_neg_eisenstein`, `two_closure_structures`
  bundle the key results.

For PHYSICS interpretation:
- d = 5 = pentagon closure period (NS=3 spatial + NT=2 temporal)
- 1 = glue = Lorentz-style boost generator
- Pentagonal D_5 closure mod 5 = closed time-loop
- 2I shadow = full observer manifold (over ℤ[φ])

## See also

- `lean/E213/Lib/Math/UniverseChain/MobiusChain.lean` — chain capstone
- `lean/E213/Lib/Math/UniverseChain/INDEX.md` — chain reading order
- Individual research notes G65–G81 for detailed derivations
