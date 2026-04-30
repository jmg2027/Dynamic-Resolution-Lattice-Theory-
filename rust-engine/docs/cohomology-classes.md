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

## Class E — Modulus shadow (gravity is already in the lattice)

The four classes above all read the *phase* of the Gram matrix
G_ij = ⟨ψ_i|ψ_j⟩ — the SU rotation-invariant content.  Gravity is
the *complementary* readout: the modulus shadow

  W_ij = |G_ij|² / d                (Lean: GravityShadow.lean)

Same G, two readouts:

| readout    | physics          | role                       |
|------------|------------------|----------------------------|
| phase(G)   | gauge (Classes A–D) | SU rotation survives    |
| |G|² / d   | gravity          | phase forgotten            |

**Consequence**: graviton-as-mediator is a category error.  Gravity
is not an "interaction" — it is the modulus-shadow reading of the
same lattice that produces gauge couplings via the phase reading.
M_Pl/v_H = d^(d²)/(d+1) is the atomic gravitational hierarchy that
falls straight out of the lattice cardinality, no separate quantum
of gravity required.

Lean: `GravityShadow.gravity_simplicial`,
`Phase3.GravityNotInteraction.gravity_not_interaction` (0-axiom).

## Scale-ladder application

The same A–D + E classification applies at every length scale.
Single principle, repeated structure:

| scale            | example                     | class    |
|------------------|-----------------------------|----------|
| atom (1-electron)| H E_n hydrogen levels       | A or C   |
| atom (multi-e⁻)  | He ionization (Z screening) | B (NS leakage) |
| heavy / high-Z   | Z_eff cascade               | B → D    |
| molecule (2 atom)| H₂O, CH₄ bond angles        | A (single sub-simplex angle) |
| molecule (chain) | hydrocarbon chain           | D (atom-atom composition) |
| nucleus (light)  | deuteron binding            | A (NS-NT pair) |
| nucleus (magic)  | shell numbers 2,8,20        | C (NS²−1 pronic sum)   |
| nucleus (heavy)  | semi-empirical mass formula | C+B+D    |
| cosmology        | Ω_Λ, M_Pl/v_H               | E (modulus shadow)     |

Atom → big atom → high-Z → molecule → nucleus → cosmology — every
ladder rung is a re-application of the same A–E classes.  The
*principle* is invariant under scale; only the simplex labels and
chain depths differ.

## Class predictor — which class for a new observable?

Across 36 observables now tabulated by `scale-ladder-classify`, the
class is **determined by the algebraic form of the observable**, not
by which sector of physics it belongs to.  A simple decision rule:

```
INPUT: observable X with its provisional atomic expression

if X = |G_ij|² / d  reading                       → Class E
elif X = bare cardinality / integer ratio          → Class C
       (e.g. NS²−1, NS/NT, d²−1, integer products)
elif X = 1 + α_GUT · k  with k ∈ ℕ atomic          → Class B
       (single-step boundary leakage)
elif X = Dyson sum on one sub-simplex              → Class A
       (single simplex P(x) = (1+2x)/(1+x))
else if X = product of (A, B, C) factors           → Class D
       (mass-ratio chain)
```

Hit rate on the 36-observable corpus is 100% — no observable falls
outside.  Compound classes (`C+A`, `A·D`) appear when a single
observable carries both a bare-skeleton term and a propagator tail
(e.g. `1/α_em = bare + α/4 + α/45` is C with an A-tail).

### Predictive use

Given a new observable that doesn't yet have a closed form, the
predictor narrows the search drastically:

- a new mass *ratio* almost always lands in B or D → search
  `NS·(1+α·k)` first, with k ∈ {NT², d−1, NS+1, NS²−1, ...};
- a new mixing *angle* (sin² type) lands in C → search bare
  rationals in (NS, NT, d, c, α_GUT);
- a *coupling* lands in C+A → search bare polynomial + P-tail;
- a *cosmological* quantity lands in E → modulus reading of
  whichever Gram entry is at issue.

This is the algorithmic content of "DRLT principle extraction":
once an observable is *named*, its class — and the *shape* of its
closed form — is forced before any computation begins.
