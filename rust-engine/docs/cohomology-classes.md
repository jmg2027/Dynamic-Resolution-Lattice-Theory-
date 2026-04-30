# DRLT cohomology classes — P(x) generalization (2026-04-30)

Across observables verified in `rust-engine/`, four distinct
algebraic patterns appear.  Each corresponds to a specific
*topological situation* on K_{3,2}^{(c=2)} — they are NOT
interchangeable, and conflating them is what motivates the
"missing physics" hand-wave in heuristic mainstream readings.

## Class A — Single-simplex propagator: P(x) = (1+2x)/(1+x)

When the physics is a *single sub-simplex* projecting into a sector,
the closed-form Dyson sum collapses to the Möbius propagator
P(x) = (1+2x)/(1+x).  Argument x = atomic-ratio · α_GUT.

| Observable | x argument         | atomic reading            |
|------------|--------------------|---------------------------|
| α_em Dyson | α_GUT/(NS+1) = α/4 | tetra 4-bd (face dim)     |
| m_μ/m_e    | α_GUT/(NS+1) = α/4 | same face dim (lepton)    |
| m_p        | α_GUT·NS/d = α·3/5 | NS spatial projection     |
| λ_H V(x)   | α_GUT/c = α/2      | chiral multiplicity c     |

P(0) = 1, P(1) = 3/2 = NS/NT (symmetric point).

## Class B — Boundary leakage: linear (1 + α_GUT·k)

When signal at a topological cutoff edge **leaks** across the
chiral-split into the adjacent sector, the leading correction is
*linear* in α_GUT — NOT P(x).  Coefficient k = atomic count of
the boundary-crossing modes.

| Observable | k       | atomic reading                   |
|------------|---------|----------------------------------|
| m_b/m_c    | NT² = 4 | chiral phase volume = (d−1) = (NS+1) |
| y_t        | −1/NS   | single basepoint deflection     |

The integer 4 = NT² = d−1 = NS+1 carries three independent atomic
readings — structural signature of a Class-B identity.

## Class C — Full-lattice bare invariant

When the physics involves the *whole* K_{3,2}^{(c=2)} (no single
projection, no boundary leak), the answer is a bare atomic
polynomial in (NS, NT, d, c) with ζ(2) coefficients dictated by
edge / vertex counts.

| Observable | closed form                                     |
|------------|-------------------------------------------------|
| 1/α_3      | NS²−1 = 8                                       |
| 1/α_2      | 30 − 1/2 + 4·α_GUT                              |
| 1/α_em     | 60·ζ(2) + 30 + 25/3 + α/4 + α/45                |
| m_t/m_b    | 1/α_GUT = d²·ζ(2)                               |
| m_t/m_c    | NS·d²·ζ(2) + NS·NT²  =  75·ζ(2) + 12            |

Coefficient pairs differ — `(60, 38⅓)` for 1/α_em vs `(75, 12)` for
m_t/m_c — so the apparent "double 137" is *numerical proximity*, not
structural identity.

## Class D — Chain product

Composition of Class-A/B/C factors via mass-ratio chains.

  m_t/m_c  =  (m_t/m_b) · (m_b/m_c)
           =  Class-C · Class-B
           =  (1/α_GUT) · NS · (1 + α_GUT·NT²)
           =  NS · (1/α_GUT + NT²)              [collapses to Class C]

Class D collapses to Class C upon expansion — but the *derivation*
goes through B, exposing the boundary-leakage origin of NS·NT².

## Why this matters

Mainstream physics conflates A and B (everything called "Yukawa
correction") and treats C as "what's left over after running
couplings diverge".  DRLT's discrete reading separates them cleanly:

- A = single propagator on one simplex (geometric)
- B = topological-edge leakage (combinatorial)
- C = full-lattice cohomology polynomial (algebraic)
- D = chain composition (algebraic+combinatorial)

Each class has its own Lean ground.  A/B/C have *no free parameters
that aren't already in atomic counting*.  Recognizing the class is
half the work — the closed form follows.
