# Mobius213/Px — sub-tree INDEX

Möbius matrix P = [[2,1],[1,1]] symmetry species catalog and
P-orbit closure programme.

**Status**: CLOSED — 28 files, ~450+ PURE declarations.
Promoted chapter: `theory/math/mobius213_p_orbit_closure.md`.

## File map

| File | Programme | Decls | Content |
|---|---|---|---|
| `SymmetrySpecies.lean` | catalog | 8 | Base 36-species type definitions |
| `OpenSpeciesClosure.lean` | catalog | 22 | Open-species closure machinery |
| `DenomInvariantFamily.lean` | catalog | 12 | Denominator-invariant families |
| `IterationSpecies.lean` | catalog | 15 | P-iteration species constructions |
| `ExtendedSpecies.lean` | catalog | 20 | Extended species beyond base 36 |
| `AxisGroupCount.lean` | catalog | 9 | 55 framework axes group counts |
| `DecompositionCatalog.lean` | catalog | 8 | Period decomposition catalog |
| `SyntacticCatalog.lean` | catalog | 26 | Syntactic species classification |
| `FibonacciAtomicLock.lean` | structure | 18 | P = Q² (Fibonacci shift), atomic = fib(2..5) |
| `NaturalnessClosure.lean` | closure | 15 | Naturalness boundary definition |
| `TripartiteK213.lean` | closure | 10 | K_{2,1,3} tripartite structure |
| `ModPPeriods.lean` | closure | 17 | Mod-p period catalog (primes ≤ 29) |
| `POrbitClosure.lean` | closure | 26 | L-sequence + P-orbit ring closure |
| `CharPolySelf.lean` | closure | 11 | Cayley-Hamilton + Cassini → P self-reference |
| `POrbitRing.lean` | closure | 22 | Inductive `InPOrbitRing` predicate |
| `PeriodDepthBounds.lean` | closure | 21 | Primes 41–97 depth tags (D_max = 4) |
| `CrossProductAxes.lean` | closure | 17 | Bipartite × Tripartite × P-orbit address |
| `POrbitDepth.lean` | closure | 19 | Inductive depth predicate `AtDepth` |
| `CassiniInduction.lean` | closure | 11 | Cassini identity n = 0..9 |
| `CassiniUniversal.lean` | universal | 16 | `cassini_universal` ∀n (PURE Nat ring) |
| `PnFibonacci.lean` | universal | 34 | P^n entries = fib at n = 0..5 |
| `PnFibonacciUniversal.lean` | universal | 14 | `det_pn_universal` ∀n (PURE Nat ring) |
| `QFibIdentity.lean` | universal | 9 | `Q00 n = fib(2n+1)` ∀n (NEW) |
| `LModP.lean` | closure | 9 | L mod p cycle closure verification |
| `PeriodReciprocity.lean` | closure | 35 | T_p divides p±1 via Legendre(5,p) |
| `ConvergentDet.lean` | universal | ~12 | Farey-neighbour property from det=1 |
| `PGeneratesNat.lean` | universal | ~18 | P generates ALL of ℕ≥1 (Chicken McNugget) |

## Organisation

Three layers:
  1. **Catalog** (8 files) — 36-species classification of P-symmetries
  2. **Closure** (11 files) — P-orbit ring, depth bounds, reciprocity
  3. **Universal** (4 files) — ∀n theorems (Cassini, det, Fibonacci)

## Key results

  · `det_pn_universal` — det(P^n) = 1 for all n
  · `cassini_universal` — L(n)·L(n+2) = L(n+1)² + 5 for all n
  · `Q00_eq_fib` — Q00 n = fib(2n+1) for all n (P^n ↔ Fibonacci)
  · `pn_fibonacci_universal` — full P^n entry formula ∀n
  · `fib_cassini_master` — fib(2n+3)·fib(2n+1) = fib(2n+2)² + 1 ∀n
  · `farey_neighbour_fib` — fib(2n+2)·fib(2n+1) = fib(2n)·fib(2n+3) + 1 ∀n
  · `det_one_four_readings` — det=1 as matrix/Cassini/Farey triple
  · `period_depth_bound_master` — D(p) ≤ 4 for all primes ≤ 97
  · `period_reciprocity_master` — T_p | (p±1) for 23 primes
  · `pgen_all_pos` — ∀ n≥1, PGen n (P generates ALL of ℕ)
  · `p_generates_nat_master` — 5-conjunct P-generates-ℕ capstone

## Cross-references

  · Theory chapter: `theory/math/mobius213_p_orbit_closure.md`
  · Essay: `theory/essays/p_orbit_closure_master.md`
  · Umbrella: `lean/E213/Lib/Math/Mobius213/Px.lean`

## Open frontier

  · D(p) = O(log p) universal bound (number-theoretic proof)
  · Period reciprocity universal proof (∀ odd prime p ≠ 5)
  · Lens-functorial cross-product (definitional factoring)
