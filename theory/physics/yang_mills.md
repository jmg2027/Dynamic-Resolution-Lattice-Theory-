# Yang-Mills + Weinberg Angle

**Status**: Closed (6 files).

## Overview

Yang-Mills mass gap, SU(5) root structure, W/Z boson masses,
**Weinberg angle** `sin² θ_W`.  Structural identification of the
electroweak sector within the atomic substrate.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Physics/YangMills/` (6 files)
- **Umbrella**: `YangMills.lean`
- **∅-axiom status**: PURE

## Narrative

The electroweak gauge group `SU(2) × U(1)` ⊂ SU(5) GUT decomposes
under the atomic-substrate readings.  `SU5Roots.lean` enumerates
the 24 SU(5) roots; `WZBosons.lean` predicts the W mass to
within experimental bracket.

The Weinberg angle (`WeinbergAngle.lean`) is
`sin² θ_W = 30 / (30 + 60·ζ(2)) = 1/(1 + 2·ζ(2)) ≈ 0.2331` bare,
refined to ≈ 0.2312, against the observed 0.23121.  It emerges as
`α_em / α_2` with `1/α_2 = 30` and `1/α_em(M_Z) = 30 + 60·ζ(2)`;
running corrections derived via the coupling-spectrum machinery
(theory/physics/couplings.md).

## Mass gap (213 completion)

The gauge field is a cochain on the resolution-finite lattice `K_{NS,NT}^{(c)}`;
its energy operator is the Hodge / graph Laplacian `Δ`.  The **mass gap is the
smallest nonzero eigenvalue** of `Δ` — the algebraic connectivity (Fiedler
value) of the gauge lattice:

> mass gap `= c · min(NS, NT) = 2 · 2 = 4 > 0`.

`Gap.lean` constructs `Δ₀` explicitly as a 5×5 integer operator, exhibits a
**complete eigenbasis** (five eigenvectors, eigenvalues `{0, 4, 4, 6, 10} =
{0, c·NT, c·NT, c·NS, c·(NS+NT)}`), and proves independence (`det = −30 ≠ 0`),
so the spectrum is exact, the `0`-eigenspace is one-dimensional (the lattice is
**connected** — a single vacuum), and no eigenvalue hides in `(0, 4)`.
Positivity is forced by connectivity; the continuum nonperturbative difficulty
never arises because 213 stays on the resolution-finite lattice (rank exhaustion
at finite `N_eff` makes the spectrum discrete).  All ∅-axiom (`decide`).

The gluon octet `NS² − 1 = 8 = dim H¹(K_{3,2}^{(c=2)})` is the **harmonic
(massless) gauge sector** the gap sits *above*, not the gap itself: the edge
Laplacian `Δ₁` carries 8 zero-modes (the octet) plus the same nonzero spectrum
`{4, 6, 10}` as `Δ₀`, so the gap to the first massive (non-harmonic) excitation
is the same `4` — the lattice analogue of a massive glueball coexisting with
massless gauge cohomology.  `c = 2` is a presentation multiplicity; the gap
scales linearly in `c`, so existence `> 0` is `c`-independent.

## Connection

- `theory/physics/couplings.md` — α_GUT + running
- `theory/physics/symmetry/c3_chain.md` — H¹(K) = 8 = gluon octet
