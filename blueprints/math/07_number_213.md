# Number Theory 213 — Blueprint

**Priority**: ★★ (213's atomic structure → number theory natural)

---

## 1. Why This Field

ZFC number theory:
- ℤ, ℚ → ℝ → ℂ chain
- Primes, divisibility
- Diophantine equations
- Algebraic number theory (ℤ[i], ℤ[√d])

Natural emergence in 213:
- **Raw axiom itself is atomicity** — different meaning of primes
- **CayleyDickson** already formalized: ℤ[i], ℤ[√2], ℤ[ω] (29 files)
- **Padic** already formalized
- **dyadic prime 2** is 213 itself

Especially deeply connected to the *Critical line* track (RH/GRH).

## 2. 213-native Emergence

### 2.1 Atomic primes — 2 and 3

213 atom pair {2, 3} → two atomic primes.  d = 5 = 2 + 3.

Prime definition = atomic counting:
- 2 = base of dyadic
- 3 = NS (one side of atom)
- 5 = d (whole)
- other primes = *derived* from 213

### 2.2 Divisibility on dyadic tree

a | b in ZFC: ∃ k, b = a·k.
213-native: *periodicity* of bisection trajectory.

### 2.3 Modular arithmetic

ℤ/nℤ = atomic counting modulo n.  Pigeonhole (already formalized in OS)
directly applicable.

### 2.4 Continued fractions

Generalization of binary expansion in dyadic tree.  Already
the cut representation in Analysis 213.

### 2.5 Algebraic numbers

`Sqrt2Cut`, `Sqrt3IrrationalPure`, `Sqrt5IrrationalPure`,
`PellSeq`, `Padic` already formalized.  Generalization needed:
- ℤ[√d] for general d
- Galois extension (critical-line/ track already started)

### 2.6 Riemann zeta + RH

Critical-line track (193 files!) already in progress.  Analysis 213
+ Complex 213 (blueprint 04) combined → deeper tools.

## 3. Building Blocks

| Tool | Use |
|---|---|
| Raw axiom + atomicity | atomic primes 2, 3 |
| `OS/Pigeonhole.lean` | modular arithmetic |
| `OS/PrimitiveSizes.lean` | counting |
| CayleyDickson `ZSqrt*` | algebraic integers |
| `Padic` | p-adic numbers |
| `EulerSeq` | e (transcendental) |
| `WallisSeq` | π/2 (transcendental) |
| critical-line/ track | RH/GRH formalization in progress |

## 4. Phase Plan

### Phase NA — Atomic primes (3-5 commits)

1. `AtomicPrime := { 2, 3 }` (direct from Raw axiom)
2. `Prime n := atomic-counting derivable`
3. 5 = 2 + 3 (atomic decomposition propEq)
4. d^d = 5^5 = 3125 (natural occurrence)

### Phase NB — Divisibility + modular

1. `Divides a b` via dyadic
2. `ModN n` arithmetic (using Fin n)
3. Fermat little theorem skeleton
4. CRT (Chinese remainder) — using atomic

### Phase NC — Algebraic numbers

1. ℤ[i], ℤ[√d] generalization (over CayleyDickson)
2. Norm, trace propEq
3. Unit group structure

### Phase ND — p-adic + Continued fractions

1. p-adic valuation propEq
2. p-adic limit (Padic already in hand)
3. Continued fraction expansion (binary)

### Phase NE — Zeta + RH connection

1. Riemann zeta as Dirichlet series (Analysis + Complex 213)
2. RH skeleton
3. Integration with critical-line/ track

### Phase NF — Capstone

First year undergraduate number theory + introductory algebraic number theory.

## 5. Connections to Other Tracks

- **Critical Line / RH** (193 files!): direct integration
- **CayleyDickson** (29 files): already algebraic number ring
- **Atoms**: atomic counting
- **Standard Model**: prime distribution → mass spectrum

## 6. Open Problems

- **Infinite primes** — atomicity of 213 is *finite* aspect
- **Class field theory** — Galois extension 213-native?
- **Modular forms** — use Complex 213

## 7. Key Insights (★)

★ **Primes 2, 3 = atomic** — the *seeds* of 213 itself.  Remaining primes are
derived.

★ **Padic 213-native** — already formalized.

★ **Critical-line track = RH aspect of Number Theory 213** — integration possible.

## 8. First Marathon Command

```
"Start Phase NA.  Define AtomicPrime + 5 = 2 + 3 propEq + d^d propEq"
```

