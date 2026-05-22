# Atomic Integers Catalog

Integers expressible via 213 atomic primitives (NS=3, NT=2, d=5, c=2).

## Small integers (1-30)

  1 = NS - NT, NT - 1
  2 = NT, c
  3 = NS, NT² - 1
  4 = d - 1, NS + 1, NT²
  5 = d, NS + NT, F_5
  6 = NS · NT, 3!, NS·(NS-1), d + 1, |ZOmega^×| (Eisenstein units, G87 §5)
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
       · Modular fingerprint: configCountD 5 n ≡ 9 = NS² (mod 41)
         for all n ≥ 1.  The α_GUT residue is invariant under
         fractal level iteration.
         Lean: Lib/Math/Cohomology/Fractal/ConfigCountModular.lean
               §H.1 configCountD_5_succ_mod_41
  48 = NT⁴·NS   49 = (NS²-NT)²   50 = 2·d²
  54 = 2·NS³   60 = e-folds   64 = NT⁶
  72 = (d²-1)·NS   75 = NS·d²   80 = NT⁴·d
  81 = NS⁴   86 = Rn   100 = NT²·d²

## Large integers (100+)

  118 = Og   137 = 1/α_em (prime)
  168 = HO magic 7 (Z=168 prediction)
  192 = (NS²-1)(d²-1) (Muon lifetime)
  521 = Aurifeuillean handle on N_U + 1 = 5^(5^n) + 1 (n-uniform, prime)
       · 521 = (d² + NT²)² − d · (NT³)² = 29² − 5·8²
       · = N((d² + NT²) + NT³ · √d) in ℤ[√d]
       · = Φ_10(5), the unique Aurifeuillean cyclotomic factor of
         the count-Lens +1 family across all n ≥ 1
       · Three atomic readings of 29: NT^d − NS, d² + NT², d² + d − 1
       · Lean: Lib/Math/Cohomology/Fractal/ConfigCountAurifeuillean.lean
         + ConfigCountAurifeuilleanParam.lean (parametric ∀n)

## Atomic primes

  2, 3, 5, 7, 13, 41, 137, 521

## Multi-output (same integer across unrelated frameworks)

  6 = NS·NT     [Pauli ε, Lorentz, AB pair, 3!, |ZOmega^×|, χ-sum defect]
                  → 6-theorem master: Theory/SixTheorem.lean
  8 = NS²-1     [α_3, SU(3), b_1, Einstein, Hawking]
  12 = 2·NS·NT  [α_1, α_2, leptoquark]
  24 = d²-1     [SU(5), 4!, SM gauge]
  192 = 8·24    [Muon lifetime]

## N_resolution and φ — count-Lens readouts

  `configCountD : Nat → Nat → Nat`, `configCountD d n := d^(d^n)` —
    parametric count-Lens family in base `d` and level `n`.  The
    base `d = 5` is selected at the physics lens by
    `Theory.Atomicity.Five.atomic_iff_five` and the C2a / C2b
    corroborating constraints.  The level `n` is parametric.

    Slice `d = 5` (display-aliased `configCount`):
      · `configCount 0 = 5`
      · `configCount 1 = 3125`
      · `configCount 2 = 5²⁵ = 298 023 223 876 953 125`
        (display-aliased `N_U` per `Lib/Math/ResolutionLimit.N_U`)
      · `configCount 3 = 5^125 ≈ 2.35 × 10^87`

    Level-2 readout per base:
      · `configCountD 2 2 = 2^4 = 16`
      · `configCountD 3 2 = 3^9 = 19683`
      · `configCountD 5 2 = 5^25` (physics-selected)
      · `configCountD 7 2 = 7^49 ≈ 2.56 × 10^41`

    Clean recursion (∅-axiom PURE):
      `configCountD d (n+1) = (configCountD d n) ^ d`
    — canonical "level-up" identity.

    Two real Lean derivations of the level-2 value:
      (1) fractal iteration:
        `Physics/Foundations/NResolutionFromFractal.n_resolution_eq_hierarchy`
        + bridge `n_resolution_candidate_eq` to the parametric
        family.
      (2) K_{b²} graph b-colouring count:
        `Physics/Foundations/FractalLensCardinality.K_b_sq_coloring_count_eq`
        (parametric bridge), plus the d=5 instance
        `K25_coloring_count_eq_configCountD`.

    Both bridge into `configCountD` as the unifying object.
    Per CLAUDE.md "Universe-constant framing": no `def N_U`
    anywhere; the privileged status of the d=5 instance sits in
    `Theory.Atomicity.Five`, not in this family definition.
    See `seed/RESOLUTION_LIMIT_SPEC.md` §2.

  `φ = (1+√5)/2` — fixed point of Möbius P(x) = (2x+1)/(x+1),
    dominant eigenvalue of [[2,1],[1,1]] with characteristic
    polynomial λ² − 3λ + 1 (trace 3 = NS, det 1, disc 5 = NS+NT).
    Frozen + dynamic dual reading: P(φ) = φ (algebraic fixed
    point) and num_n/den_n → φ (Pell convergence) — same residue
    under two Lens readings.  Pell-unit invariant
    num_n · den_{n+1} − num_{n+1} · den_n = -1 across all
    convergent layers.  See `lean/E213/Lib/Math/Mobius213.lean`.
