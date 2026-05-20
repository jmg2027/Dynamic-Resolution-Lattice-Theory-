# Atomic Integers Catalog

Integers expressible via 213 atomic primitives (NS=3, NT=2, d=5, c=2).

## Small integers (1-30)

  1 = NS - NT, NT - 1
  2 = NT, c
  3 = NS, NT² - 1
  4 = d - 1, NS + 1, NT²
  5 = d, NS + NT, F_5
  6 = NS · NT, 3!, NS·(NS-1), d + 1
  7 = NS² - NT, prime
  8 = NS² - 1, F_6, NT³
  9 = NS²
  10 = C(d, 2), d·NT
  12 = 2·NS·NT, (d-1)·NS
  13 = NS² + NT², F_7, prime
  16 = NT⁴, NT·(NS²-1)
  17 = NS² + (NS²-1), prime
  18 = 2·NS²
  19 = NS³ - NT³
  20 = 4·d
  24 = d²-1, 4!, (d-1)(d+1), 12·NT
  25 = d²
  27 = NS³
  30 = NS·NT·d

## Medium integers (30-100)

  32 = NT^d   36 = (NS·NT)²   40 = (NS²-1)·d
  41 = α_GUT integer (prime)
  48 = NT⁴·NS   49 = (NS²-NT)²   50 = 2·d²
  54 = 2·NS³   60 = e-folds   64 = NT⁶
  72 = (d²-1)·NS   75 = NS·d²   80 = NT⁴·d
  81 = NS⁴   86 = Rn   100 = NT²·d²

## Large integers (100+)

  118 = Og   137 = 1/α_em (prime)
  168 = HO magic 7 (Z=168 prediction)
  192 = (NS²-1)(d²-1) (Muon lifetime)

## Atomic primes

  2, 3, 5, 7, 13, 41, 137

## Multi-output (same integer across unrelated frameworks)

  6 = NS·NT     [Pauli ε, Lorentz, AB pair, 3!]
  8 = NS²-1     [α_3, SU(3), b_1, Einstein, Hawking]
  12 = 2·NS·NT  [α_1, α_2, leptoquark]
  24 = d²-1     [SU(5), 4!, SM gauge]
  192 = 8·24    [Muon lifetime]

## N_resolution and φ — count-Lens readouts

  `N_resolution = d^(d²) = 5²⁵ = 298 023 223 876 953 125` —
    count-Lens readout at fractal level 2.  Consistent across four
    independent Lens applications (Lean formalisation,
    K₂₅ graph coloring, rank-2 tensor DOF, type-theoretic
    injective projection bound).  See `seed/RESOLUTION_LIMIT_SPEC
    .md` §2 + `lean/E213/Lib/Math/ResolutionLimit.lean` +
    `Lib/Physics/Foundations/NResolutionFromFractal.lean`
    (`n_resolution_atomic_decomposition`,
    `n_resolution_structural`).

  `φ = (1+√5)/2` — fixed point of Möbius P(x) = (2x+1)/(x+1),
    dominant eigenvalue of [[2,1],[1,1]] with characteristic
    polynomial λ² − 3λ + 1 (trace 3 = NS, det 1, disc 5 = NS+NT).
    Frozen + dynamic dual reading: P(φ) = φ (algebraic fixed
    point) and num_n/den_n → φ (Pell convergence) — same residue
    under two Lens readings.  Pell-unit invariant
    num_n · den_{n+1} − num_{n+1} · den_n = -1 across all
    convergent layers.  See `lean/E213/Lib/Math/Mobius213.lean`.
