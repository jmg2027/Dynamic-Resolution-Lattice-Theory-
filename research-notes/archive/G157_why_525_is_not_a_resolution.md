# G157 — Why 5²⁵ is not a resolution

**Tier-1.**  The *argument* behind the deletion of the
`5²⁵ = N_U = d^(d²) = configCount 2`-as-resolution chain.  The companion
registry `RERESEARCH_n_u_removal.md` records *what* was removed; this note
records *why* removal — not re-derivation — is the only coherent move.
Originator decision (Mingu Jeong).

## The claim that was deleted

> `1/α_em(IR)` (and three other observables) is evaluated at *the*
> finite resolution `N_U = 5²⁵`; at that resolution `ζ(2) = S(N_U)` is a
> finite rational and "π appears nowhere".

The number arose as `configCountD 5 2 = 5^(5²) = 5²⁵` — the count-Lens
readout at base `d = 5` (atomicity-forced), level `n = 2`.

## Three unjustified moves

**(1) The level is not selected — proven, not conjectured.**
`d = 5` is forced (`Theory.Atomicity.Five`).  The *level* `n = 2` is not.
G156 (`configCountD_injective` / `configCountD_strictMono`) makes the level
axis a strict order-embedding for `d ≥ 2`: no fixed point, no plateau,
nothing internal to the count that distinguishes one level.  The fractal
lift that "lands on" `5²⁵` chose its level so the vertex count would *equal*
`5²⁵` — fitting a target, not deriving it.  (The deleted recursion file even
carried two mutually inconsistent level labels, `L = 24` and `L = d² = 25`,
for the same landing.)

**(2) A configuration count is not a spectral-truncation index — category
error.**  In `S(N) = Σ_{k=1}^{N} 1/k²`, `N` is *how many terms you sum
before stopping*.  In `configCountD d n`, `5²⁵` is *how many distinguishable
states a level-`n` base-`d` lattice has*.  A count of states and a count of
series terms are different kinds of quantity; the identification
`N_resolution := #configurations` is a bare import of meaning with no
bridging arrow — exactly what the meta-principle forbids ("assume nothing,
give meaning to nothing").  The deleted capstone admitted as much: it noted
"Lean cannot compute `S` at `5²⁵`", i.e. the equation `ζ(2) = S(5²⁵)` was
*posited and never verified*.

**(3) "π is fake" is an artefact of (1)+(2).**  The "π appears nowhere"
reading holds only if `5²⁵` is granted as the resolution.  But what makes
`ζ(2)` equal to `ζ(2)` is the limit; truncating at `5²⁵` is an
approximation whose cutoff is arbitrary once (1) removes any privileged
level.  And the precision theorem that actually *works* —
`GramStructuralCapstone.invAlphaEm_precision_theorem`, 0.2 ppb — takes `π²`
as a **literal input** (`pi2_e12`).  The genuine content needed π all along;
the finitist substitute was doing no work.

## The foundational refutation: there is no "the resolution" slot

The only thing 213 actually delivers is finiteness *per level*: each act of
distinguishing is finite, so `configCountD d n` is finite at each `n` — a
**parametric family**, legitimate and kept.  The error was collapsing the
family into a single privileged total `N_U`.

That collapse contradicts the foundation it claimed to spring from:

  - **No privileged level** — G156 (`configCountD_injective`).
  - **No top** — the residue is outside *every* level's image:
    `Lens/FlatOntologyClosure.object1_not_surjective` +
    `self_covering_closure` (the pointing map is injective but not
    surjective), and `Cauchy/DepthCeilingResidue.diag_not_in_seq`
    (`diag f n = f n n + 1` escapes every level of any enumerated tower) =
    `Cantor.cantor_general`.

So "the resolution" was never a slot 213 opened.  Finitism dug the
slot — "the universe has a finite number of distinguishable states = its
resolution" — and `5^(d²)` was reverse-fitted into it because `5 = d` made
it look self-referential.  Both halves fail: the slot is foreign to 213,
and the filler (level 2) is arbitrary under G156.

## Why deletion, not re-derivation

Re-derivation presupposes the `count = resolution` identification is
salvageable.  It is not — it was never derived, only posited, and the
foundation forbids the privileged total it requires.  There is no theorem
to re-prove; there is a category error to remove.  Marking the chain "needs
re-derivation" (the prior registry framing) was already one concession too
many.

## What survives (the honest residue of the programme)

  - **Precision, with π as an input** — `GramStructural*` /
    `GradedFormulaPrecision`: given `π²` as a literal, the `K_{3,2}` cup-ring
    5-layer formula + the Newton-1 Gram cubic `25y³ + 1 = 25Xy²` reproduce
    `1/α_em` to 0.2 ppb.  No `5²⁵` anywhere.  This is the actual claim; it
    should be stated without "finitist / π-free / derivation" overclaim.
  - **Parametric combinatorics** — `configCountD`, `numV L = 5^L`,
    `configCount 2 = 5²⁵` (a *true arithmetic theorem*, kept as bare math),
    parametric Basel `S(N)` / Wallis `S_Wallis(N)`.
  - **Atomic forcing + residue** — `(NS,NT,d) = (3,2,5)`,
    `UniverseChain/{Atomicity,Decomposition,PairAxes,Residue}` — untouched.

## Pointers

  - Deleted (per `RERESEARCH_n_u_removal.md`, this session): the
    `N_resolution*` / `FiniteUniverse` / `FractalLensCardinality` modules,
    the finitist capstones (`FinitistObservableChain`,
    `ValidationStandardOne`), `AlphaEM/Capstone.MasterCapstone`,
    `UniverseChain/{Universe,Synthesis,MobiusChain}`,
    `Padic/DRLT.canonical_5adic_NU`.
  - No-privileged-level: `G156_configcount_level_injectivity.md`.
  - No-top / residue: `Lens/FlatOntologyClosure`,
    `Cauchy/DepthCeilingResidue`, `G152_residue_self_covering.md`.
