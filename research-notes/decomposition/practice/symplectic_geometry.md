# Decomposition: symplectic geometry / Hamiltonian mechanics (ω, Poisson bracket, Hamilton's equations, Liouville, moment map, Darboux)

*213-decomposition per `../README.md` (model v7.1). A **fresh** field, but a pure consolidation: it
**fuses** two already-built corners on one object (phase space). Tests one composite thesis: symplectic
geometry = the **q=±1 antisymmetric direction-bit** (`lie_theory.md`'s commutator/wedge) **+ the det=1
conservation** (`noether.md`'s Liouville/Noether), bound by ω. The symplectic form ω = the q=±1
antisymmetric reading; the Poisson bracket {f,g} = the Lie bracket; Hamilton's flow = the q=+1
conservation flow; Liouville's theorem = det=1 phase-volume preservation; dω=0 = de Rham's d²=0. The bar
is PREDICTION/REVELATION (collapse of two prior files onto one object), with the named symplectic-form /
phase-space / moment-map / Darboux objects honestly ABSENT.*

## The decomposition (C / Reading / Residue)

- **Construction `C` — the same `Mat2` ×-construction as `lie_theory.md`/`noether.md`/`curvature.md`,
  read on a phase *pair*.** Symplectic geometry introduces **no new construction**. Phase space is the
  paired distinguishing `(q, p)` — position-count and its conjugate directed-count — exactly the
  **directed count-pair of `integers.md`** doubled, and the linear symplectic group `Sp(2,ℝ) = SL₂` *is*
  the repo's unimodular `Mat2` with `det = 1` (the Stern–Brocot/modular generators `⟨L, R, S, U⟩`). So
  `C` = the `Mat2` family at `det = 1`, read on a 2-slot phase pair rather than along a tree
  (`noether.md`) or a loop (`curvature.md`).

- **Reading `L_ω` (the antisymmetric pairing reading)** — fold a pair of phase directions to their
  **oriented area**: `ω(u, v) = ` the antisymmetric bilinear pairing. This is `lie_theory.md`'s
  commutator reading and `homology.md`'s wedge read on phase vectors: the readout is **forced
  antisymmetric** by the same q=−1 pair-swap that signs `det`, flips the wedge `e_i∧e_j = −(e_j∧e_i)`,
  and builds ℤ's `−`. In the repo this reading is **already named the symplectic form**: `cup1` (the
  signed cup) is the imaginary, antisymmetric half of the Hermitian Gram `G = hPair + 𝐢·cup1`, and
  `SignedCup.lean` calls `Im(G) = cup1` *literally* "the **symplectic form** (the phase/gauge half)"
  (`gram_hermitian_gravity_gauge_split`). Non-degeneracy = the pairing is faithful (the q=±1 readout
  separates directions); closedness `dω = 0` = `de_rham.md`/`homology.md`'s `d²=0`
  (`dsq_zero_universal_delta4`).

- **The flow reading `L_H` (Hamilton's equations)** — the **q=+1 conservation flow**. Hamilton's
  equations `q̇ = ∂H/∂p, ṗ = −∂H/∂q` are exactly the antisymmetric pairing applied to `dH`: the flow is
  ω⁻¹ paired with the differential of `H`, so `Ḣ = {H, H} = 0` (H is conserved along its own flow — the
  bracket's `bracket_self = 0`). This is `noether.md`'s certified picture: a flow whose generator's
  invariant scalar is fixed (`noether_local`: ∂·j = 0 ⟺ the generator is Aut-invariant `det = 1`).

- **Residue** — `q = ±1`, the **escape/converge** tag of `ResidueTag.lean`. The symplectic flow at the
  `q = +1` (converge) pole is **volume-preserving** (Liouville): `det = 1` is the same `det_holonomy_eq_one`
  /`density_conserved_of_det_one` invariant of `noether.md`. The `q = −1` pole is the orientation-reversing
  / non-conserving sector. So ω fuses **both invariants** — its antisymmetry is the q=±1 *direction* bit
  and its preserved-volume flow is the q=+1 *det=1* bit, on one object.

## Re-seeing (⟨C | L⟩)

```
   phase space             =  ⟨ Mat2 family at det=1 (= Sp(2)=SL₂) | the antisymmetric pairing reading ω ⟩
   the symplectic form ω   =  the q=±1 antisymmetric reading  (cup1 = Im of the Hermitian Gram; SignedCup gram_..split)
   "ω antisymmetric"       =  the q=−1 pair-swap bit: swap operands ⇒ flip sign  (cup1_antisymmetric, bracket_antisymm)
   "ω non-degenerate"      =  the pairing is faithful (separates directions; the readout is injective on phase)
   "dω = 0 (ω closed)"     =  de_rham.md / homology.md two-step nilpotency  (dsq_zero_universal_delta4)
   the Poisson bracket {f,g} =  the Lie bracket [X,Y]=XY−YX  (bracket_antisymm, jacobi, tr_bracket_zero, bracket_leibniz)
   "{f,g} antisymmetric"   =  the SAME q=−1 antisymmetry as ω  (one direction bit, read on functions)
   "Jacobi for {·,·}"      =  Mat2Bracket.jacobi  (the graded-Leibniz q=−1 cyclic cancellation)
   Hamilton's equations    =  the q=+1 conservation flow: ω-pair dH, so Ḣ={H,H}=0  (noether_local; bracket_self)
   Liouville's theorem     =  det=1 ⇒ phase volume preserved  (density_conserved_of_det_one, det_holonomy_eq_one)
   conserved quantity      =  Aut-invariant character {Q,H}=0  (noether_local: ∂·j=0 ⟺ det g=1)
   moment map (absent)     =  the Aut-family's invariant readout valued in 𝔤* — engine present, named object NOT built
   Darboux's theorem (absent) = "all symplectic forms locally = standard ω" — a normal-form/local-triviality claim, NOT built
```

Set side by side, symplectic geometry is **the literal intersection of two earlier files**: `lie_theory.md`'s
bracket and `noether.md`'s det=1 conservation, *both* read on the same `Mat2`-at-det=1 object that is `Sp(2)=SL₂`.

| corner | reading on `C` | residue at the relevant pole | prior file |
|---|---|---|---|
| ω (the form) | antisymmetric pairing on phase vectors | q=−1 orientation sign (`cup1_antisymmetric`) | `lie_theory.md`/`homology.md` |
| {f,g} (Poisson) | commutator read as a difference | q=−1 antisymmetry, Jacobi (`bracket_antisymm`/`jacobi`) | `lie_theory.md` |
| Hamilton flow | ω-pair the differential of `H` | q=+1: `Ḣ={H,H}=0` (`bracket_self`/`noether_local`) | `noether.md` |
| Liouville | the det of the flow | q=+1 det=1 ⇒ volume preserved (`density_conserved_of_det_one`) | `noether.md` |
| dω=0 | the boundary read twice | nilpotent `d²=0` (`dsq_zero_universal_delta4`) | `de_rham.md`/`homology.md` |

## Revelation (collapse + forcing + spine: the Poisson bracket IS the Lie bracket, Liouville IS Noether's det=1, fused by ω)

**Collapse 1 — the Poisson bracket {f,g} = the Lie bracket [X,Y].** This is not an analogy; it is the
*same operation*. The Poisson bracket is antisymmetric, satisfies Jacobi, and is a derivation in each slot
(Leibniz) — the **exact three axioms** `Mat2Bracket.lean` proves for the matrix commutator:
`bracket_antisymm` (q=−1 pair-swap), `jacobi`, `bracket_leibniz`, with `bracket_self = 0` ({f,f}=0). The
classical fact "{·,·} makes C^∞(M) a Lie algebra" is therefore the calculus's *single* q=−1 antisymmetric
operation read on functions instead of on matrices — no new structure. The bracket's tracelessness
(`tr_bracket_zero`, the `sl` kernel) is the symplectic statement that the Hamiltonian vector fields are the
*divergence-free* (= volume-preserving) sector — exactly the additive twin that pairs with Liouville below.

**Collapse 2 — Liouville's theorem = Noether's det=1 (the same `density_conserved_of_det_one`).** Liouville
says the Hamiltonian flow preserves phase volume. A flow is volume-preserving iff its Jacobian has `det = 1`
(divergence-free generator). That is **verbatim** `noether.md`'s certified invariant:
`NoetherCurrent.density_conserved_of_det_one` (`det g = 1 ⇒ ∂_t ρ = 0`) and `noether_local` (`∂·j = 0 ⟺
det g = 1`), with the global charge `det_holonomy_eq_one` (det = 1 around any loop). So Liouville's theorem
is **not a separate phase-space miracle**: it is the det=1 conservation already proven for the unimodular
`Mat2` action, with "phase volume" the name for the conserved density `ρ`. The traceless bracket
(`tr_bracket_zero`) and the det=1 flow are the two sides of one fact: `tr X = 0` (algebra) exponentiates to
`det = 1` (group) — the `×↦+` arrow of `lie_theory.md`, here reading "divergence-free ⟹ volume-preserving."

**Forcing — ω's antisymmetry and closedness are forced, not posited.** ω antisymmetric falls out of the
q=−1 pair-swap (`cup1_antisymmetric`), exactly as the bracket's antisymmetry does — and the repo *already
names cup1 the symplectic form* (`SignedCup.gram_hermitian_gravity_gauge_split`: the Hermitian Gram splits
as `Re = metric` (symmetric, = I) ⊕ `Im = cup1 = symplectic form` (antisymmetric, zero diagonal)). The
"zero diagonal" half of that theorem (`GIm i i = 0`) is ω's `ω(u,u) = 0` — the wedge's `e_i∧e_i = 0`.
Closedness `dω = 0` is the same two-step nilpotency `d²=0` that `de_rham.md`/`homology.md` carry
(`dsq_zero_universal_delta4`): ω closed is *the same q=−1 sign-cancellation* that makes `∂²=0`, one degree
up. So **the three defining properties of ω — antisymmetric, non-degenerate, closed — decompose into
{q=−1 pair-swap (`cup1_antisymmetric`), faithful readout, `d²=0` (`dsq_zero_universal_delta4`)}**, all
already in the calculus.

**The q=±1 spine — ω carries BOTH poles, and that is the fusion.** This is the new datum past
`lie_theory.md` and `noether.md`: those two files each live on one residue pole (the bracket is the q=−1
antisymmetry; Noether's conservation is the q=+1 det=1). **Symplectic geometry is the field where they are
the same object.** ω's antisymmetry is the q=−1 direction bit (`bracket_antisymm`/`cup1_antisymmetric`); the
flow ω generates is the q=+1 conservation (`density_conserved_of_det_one`/`bracket_self`). The Gram-split
theorem makes the fusion literal in one Lean statement: the symmetric (metric, q=+1-ish, = I) half and the
antisymmetric (symplectic, q=−1) half are the real/imaginary parts of *one* Hermitian form. So Hamiltonian
mechanics = the calculus reading where the q=−1 antisymmetric pairing (which *defines* the geometry) and the
q=+1 det=1 conservation (which the flow *preserves*) are two readings of one `Mat2`-at-det=1 object — the
"symplectic = antisymmetry + conservation, fused" thesis, confirmed.

## LEVERAGE — verdict

**PREDICTION (consolidation), with the central legs BUILT ∅-axiom and the named symplectic objects honestly
ABSENT.** Symplectic geometry introduces no new construction and no new primitive: it is `lie_theory.md`'s
bracket and `noether.md`'s det=1 conservation read on one phase object, with ω the antisymmetric reading the
repo already names. Three of the five legs are fully built; the named field objects are the located gap.

- **Leg 1 — ω = the q=±1 antisymmetric reading. BUILT ∅-axiom.** `cup1_antisymmetric` (zero diagonal +
  full antisymmetry, the wedge sign) and `gram_hermitian_gravity_gauge_split` (the repo *names* `Im(G) =
  cup1` the symplectic form, antisymmetric with zero diagonal) — both PURE in `SignedCup.lean` (14/0). The
  antisymmetry is the *same* q=−1 pair-swap as `bracket_antisymm`/`det`/ℤ's sign. **The "symplectic form"
  object exists as `cup1` on `Δ⁴`'s H¹** — a finite, decidable instance, not a general `Ω²(M)`.

- **Leg 2 — {f,g} = the Lie bracket. BUILT ∅-axiom.** `Mat2Bracket.lean` (10/0 PURE): `bracket_antisymm`,
  `jacobi`, `bracket_leibniz`, `bracket_self` ({f,f}=0), `tr_bracket_zero` (the divergence-free/sl sector).
  These are *exactly* the Poisson bracket's defining axioms (antisymmetry + Jacobi + Leibniz/derivation).
  The collapse is real: the Poisson Lie-algebra structure on observables is the calculus's single q=−1
  antisymmetric operation, read on functions. No `PoissonBracket` object on a function ring is built; the
  *axioms* are, on `Mat2`.

- **Leg 3 — Liouville's theorem = det=1 conservation. BUILT ∅-axiom.** `NoetherCurrent.lean` (14/0 PURE):
  `density_conserved_of_det_one` (`det g = 1 ⇒ ∂_t ρ = 0` — phase volume preserved), `noether_local`
  (`∂·j = 0 ⟺ det g = 1`), `noether_global`; the global loop charge `det_holonomy_eq_one`
  (`HolonomyLattice.lean`, 26/0 PURE). Liouville is **the same theorem** as discrete Noether — phase volume
  is the conserved density. This is the sharpest collapse: a phase-space "miracle" is the unimodular det=1
  invariant already proven.

- **Leg 4 — Hamilton's equations = the q=+1 conservation flow. PREDICTION + PARTIAL.** Structurally,
  Hamilton's flow ω-pairs `dH`, giving `Ḣ = {H,H} = 0` — H conserved along its own flow, which is
  `noether_local`'s Aut-invariance + `bracket_self = 0`. The repo has a real discrete-flow corpus
  (`Foundations/MonovariantFlow` `flow_reaches`, `Optimization/GradientFlow` `d/dt F = −‖∇F‖² ≤ 0`,
  `Analysis/ODE/picardIterate`, per `differential_equations.md`), and the *conserved-along-flow* shape is
  exactly `noether_local`. **But a literal Hamiltonian vector field `X_H = ω⁻¹(dH)` with a continuous flow
  `φ_t` on phase space is NOT built** — the discrete `Mat2` setting hosts the det=1 generator and the
  bracket, not a `dH`/`X_H`/continuous `φ_t` object. PARTIAL: the conservation skeleton is certified, the
  variational/continuous Hamilton machine (same gap as `noether.md`'s missing `∂_μ j^μ` and
  `differential_equations.md`'s continuous integral operator) is the named open target.

- **Leg 5 — dω=0 (ω closed) = d²=0. BUILT ∅-axiom (cross-frame).** `dsq_zero_universal_delta4`
  (`V4Capstone.lean`, 5/0 PURE): the same q=−1 two-step sign-cancellation. Closedness of ω is the de Rham
  closedness `de_rham.md` carries — no new work.

**The located break (the genuinely missing legs).** Like `lie_theory.md`/`noether.md`, symplectic geometry
pins where the calculus stops:
  - **The `symplecticForm`/`PhaseSpace`/`PoissonBracket`-on-functions/`HamiltonianVectorField`/`Liouville`/
    `momentMap`/`Darboux` named objects are ABSENT** (grep-confirmed). The *engines* are PURE (ω = `cup1`,
    {·,·} = `Mat2Bracket`, Liouville = `NoetherCurrent` det=1), but no general `Ω²(M)`-bundle, no function
    ring `C^∞(M)` carrying the Poisson algebra, no manifold.
  - **The moment map** is the Aut-family's invariant readout valued in `𝔤*` (the `noether.md` conserved
    character one level up) — the engine is `noether_local` (Aut-invariant ⟹ conserved), but the `𝔤*`-valued
    `momentMap` object and the equivariance theorem are not built. Located at the same `d>1`/tangent gap
    `representation.md`/`lie_theory.md` named.
  - **Darboux's theorem** ("every symplectic form is locally the standard ω", a local-triviality / normal-form
    claim) is a *quotient-by-local-diffeomorphism* statement — it sits at the colimit/ambient-deformation
    corner (`knots.md`/README §5.1, Side B): no `Quot`-free normalize for the diffeomorphism action is built.
    Predicted-not-built; the calculus's honest boundary, not a 213 primitive miss.
  - **The infinitesimal/tangent `ε` (`T_e Sp`)** — inherited verbatim from `lie_theory.md`: the discrete
    `Mat2` hosts the finite det=1 generator and the bracket, not `T_e G` / `X_H` as a tangent field. Located
    at the resolution dial's `h→0` residue.

**Net verdict: PREDICTION (consolidation), no new primitive.** Symplectic geometry = `lie_theory.md`'s q=−1
antisymmetric bracket **fused with** `noether.md`'s q=+1 det=1 conservation **on one object** (the
`Mat2`-at-det=1 = `Sp(2)=SL₂` phase pair), bound by ω = the antisymmetric reading (`cup1`, which the repo
already names the symplectic form). The Poisson bracket **IS** the Lie bracket (`Mat2Bracket`, 10/0); Liouville's
theorem **IS** Noether's det=1 (`NoetherCurrent`, 14/0); dω=0 **IS** de Rham's d²=0 (`V4Capstone`, 5/0); ω
antisymmetric **IS** the q=−1 wedge (`SignedCup`, 14/0). The new datum past the two parent files: those two live
on *opposite* residue poles, and symplectic geometry is the field where they are **the same object's two
readings**. The genuine absences are the named symplectic-form/phase-space/moment-map objects, Darboux's
local-triviality (the colimit/diffeomorphism-quotient corner), and the continuous Hamiltonian flow `X_H`
(the variational/`h→0` gap). 38th decomposition; EXTENDS by consolidation, with the named field objects + Darboux
as the located breaks.

## Note for the technique — does symplectic geometry touch model v7.1?

**No new primitive; EXTEND + one consolidation note (the first explicit two-pole fusion on one object).**
The two invariants (character arrow, q=±1 residue) and four axes (direction, fold-height, resolution+base,
iteration-character) absorb symplectic geometry whole:

> **Symplectic geometry is the field where the q=−1 antisymmetric direction-bit and the q=+1 det=1
> conservation are two readings of one object.** Where `lie_theory.md` reads the q=−1 commutator (the
> bracket) and `noether.md` reads the q=+1 conserved character (det=1), symplectic geometry binds them by
> ω: ω = the antisymmetric pairing reading (`cup1`, the repo's own "symplectic form" =
> `Im(G)`), antisymmetric by the same q=−1 pair-swap as `bracket_antisymm`/`det`/the wedge; the Poisson
> bracket on observables IS that same Lie bracket (`Mat2Bracket.jacobi`/`bracket_antisymm`/`bracket_self`);
> Hamilton's flow ω-pairs `dH` so `Ḣ={H,H}=0` (q=+1 conservation, `noether_local`/`bracket_self`); and
> Liouville's volume-preservation IS the det=1 invariant (`density_conserved_of_det_one`/`det_holonomy_eq_one`),
> with the bracket's tracelessness (`tr_bracket_zero`) the divergence-free/volume-preserving twin. dω=0 is
> de Rham's `d²=0` (`dsq_zero_universal_delta4`). The located breaks: the named `symplecticForm`/`PhaseSpace`/
> `momentMap` objects (engines PURE, bundles absent), Darboux's local-triviality (the diffeomorphism-quotient
> /colimit corner, Side B), and the continuous Hamiltonian vector field `X_H` (the `h→0` tangent residue,
> the same cap `lie_theory.md`/`noether.md` hit).

So model v7.1's interior is unchanged; symplectic geometry is the **two-pole fusion corner** — ω the q=−1
antisymmetric reading whose flow preserves the q=+1 det=1 invariant — consolidating `lie_theory.md` +
`noether.md` + `de_rham.md` under the two standing invariants, with the named symplectic objects + Darboux as
the new located breaks.

## Verified Lean anchors (file:line — all grep + `scan_axioms.py`-verified this session; all PURE)

| Leg | Theorem (file:line) | Status |
|---|---|---|
| ★ ω = the q=±1 antisymmetric reading; the repo NAMES `cup1` the symplectic form (`Im` of the Hermitian Gram) | `Lib/Math/Cohomology/Cup/SignedCup.lean:57` `cup1`; `:62` `cup1_antisymmetric` (zero diag + full antisymmetry); `:118` `GIm`; `:127` `gram_hermitian_gravity_gauge_split` (Re=metric ⊕ Im=cup1=symplectic, antisymmetric, zero diagonal) | **PURE (14/0)** ✓ |
| ★ Poisson bracket = the Lie bracket: antisymmetry + Jacobi + Leibniz + {f,f}=0 + traceless (divergence-free) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean:66` `bracket`; `:76` `bracket_antisymm`; `:86` `bracket_self`; `:101` `tr_bracket_zero`; `:118` `jacobi`; `:135` `bracket_leibniz` | **PURE (10/0)** ✓ |
| ★ Liouville's theorem = det=1 conservation (phase volume preserved); Hamilton's-flow conservation | `Lib/Math/NumberSystems/Real213/ModularGeometry/NoetherCurrent.lean:97` `continuity_eq`; `:117` `density_conserved_of_det_one`; `:149` `noether_local`; `:178` `noether_global` | **PURE (14/0)** ✓ |
| ★ global conserved charge: det=1 around any loop (Liouville's invariant on a closed orbit) | `Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:93` `holonomy`; `:108` `holonomy_append`; `:136` `det_holonomy_eq_one`; `:292` `positive_loop_trivial`; `:313` `first_loop_is_the_fold` | **PURE (26/0)** ✓ |
| ★ dω = 0 (ω closed) = de Rham `d²=0` (the same q=−1 two-step nilpotency) | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41` `dsq_zero_universal_delta4`; `:62` `leibniz_universal_delta4` (Jacobi's graded-Leibniz twin) | **PURE (5/0)** ✓ |
| ω antisymmetry sign = `homology.md`'s wedge: `e_i∧e_j=−(e_j∧e_i)`, `e_i∧e_i=0` | `Lib/Math/Cohomology/Cup/SignedCup.lean:62` `cup1_antisymmetric` | **PURE** ✓ |
| q=±1 residue tag (ω antisymmetric q=−1 / det=1 flow q=+1, fused) | `Lib/Math/Foundations/ResidueTag.lean:73` `ResidueTag`; `:81` `multiplier`; `:86` `multiplier_unimodular`; `:228` `residue_tag_two_poles` | **PURE (55/0)** ✓ |
| cross-frame (the two parent files this fuses) | `lie_theory.md` (`Mat2Bracket.*`), `noether.md` (`NoetherCurrent.*`, `det_holonomy_eq_one`), `de_rham.md`/`homology.md` (`dsq_zero_universal_delta4`) | prior, ∅-axiom ✓ |

**Scan tallies (this session, `tools/scan_axioms.py` from repo root):** `Mat2Bracket` **10/0**; `NoetherCurrent`
**14/0**; `HolonomyLattice` **26/0**; `V4Capstone` **5/0**; `SignedCup` **14/0**; `ResidueTag` **55/0**. All PURE,
0 DIRTY.

## Dropped / flagged citations (honest)

- **`symplecticForm` / `PhaseSpace` / `PoissonBracket`-on-functions / `HamiltonianVectorField` /
  `Liouville`(volume theorem) / `momentMap` / `Darboux` — ABSENT.** Grep-confirmed
  (`grep -i "symplectic|Poisson|Hamiltonian|Liouville|momentMap|Darboux"` over `lean/E213`): no named
  symplectic-geometry object. The engines are built and PURE (ω = `cup1`, {·,·} = `Mat2Bracket`, Liouville =
  `NoetherCurrent` det=1), but no general `Ω²(M)`/manifold/function-ring bundle, no `momentMap`, no Darboux
  normal-form theorem. **Predicted-not-built, as expected.**
- **FALSE FRIENDS — flagged, NOT cited.**
  - **"Liouville" in-repo is the Liouville *function* λ(n) = (−1)^Ω(n) (number theory) and the Liouville
    *number*/valuation (transcendence), NOT Liouville's phase-volume theorem.** Hits:
    `NumberTheory/LiouvilleFunction.lean`, `NumberTheory/LiouvilleValuation.lean`,
    `Real213/Modulus/LiouvilleModulus.lean`, `Cauchy/DepthLiouvilleCoord.lean`. None is the volume theorem;
    the volume theorem's content is instead `NoetherCurrent.density_conserved_of_det_one` (cited above).
  - **"Hamiltonian" in-repo is the Hamiltonian *path/cycle* of graph theory** (`Combinatorics/
    TournamentHamiltonian.lean`, Redei's theorem), NOT Hamiltonian mechanics. Flagged, not cited.
- **No buildable witness proposed.** The thesis is fully grounded by existing PURE theorems
  (`cup1_antisymmetric` + `gram_hermitian_gravity_gauge_split` for ω; `Mat2Bracket.*` for the Poisson
  bracket; `density_conserved_of_det_one`/`det_holonomy_eq_one` for Liouville; `dsq_zero_universal_delta4`
  for dω=0). No new `decide`/inequality witness is needed or asserted; the genuine open targets (continuous
  `X_H`/`φ_t`, the `momentMap` object, Darboux's local-triviality) are continuous/quotient-corner gaps, not
  finite decidable facts.
- **Darboux flagged at the colimit/quotient corner.** Darboux's "all symplectic forms are locally standard"
  is a quotient-by-local-diffeomorphism (normal-form) claim — README §5.1's ambient-deformation / Side-B
  corner — so it is a *located* break (the diffeomorphism-action normalize is not built), not a missing 213
  primitive.
