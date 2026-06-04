import E213.Lens.Cardinality
import E213.Lens.FlatOntologyClosure
import E213.Lens.ProofISA
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FLTPrimary
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FreshmanDream
import E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov

/-!
# The lift catalog — three solved finite→uniform lift archetypes on the proof-ISA

`Lens.ProofISA` names the instruction set; this file is the **compilation catalog** — three
*already-solved*, `∅`-axiom, infinite-abstract theorems whose **finite→uniform lifts** are structurally
distinct.  Each `abbrev` pins a solved theorem; the surrounding text records *how* its lift is achieved —
a template library for the one open lift, the Markov uniqueness kernel `H`.

The point (`seed/PROOF_ISA.md`): an open problem's difficulty is a *missing finite→uniform lift* on the
shared instruction set.  Cataloguing *solved* lifts makes the framework a cumulative instrument — a solved
problem missing the *same* lift as `H` gives transfer; a solved problem's lift mechanism gives a template
for `H`'s.  Nothing here closes `H`; it records *which* archetype `H` is closest to.

## Archetype 1 — DIAGONAL / direct (`lift_diagonal`)
The `DIAGONALIZE` instruction self-supplies the uniform witness: the anti-diagonal is built uniformly as
a function of the enumeration, so the local disagreement-at-index *is* the uniform non-surjectivity.
**Lift cost: zero** — the instruction's content *is* the lift.  This is "the residue is the most primitive
proof technique for the infinite" made operational.

## Archetype 2 — INDUCTIVE / LOOP (`lift_loop`)
`flt_primary`: `∀ a, a^p ≡ a (mod p)`.  The lift is `COMPILE-DOWN` (binomial reduced mod `p`, middle
coefficients vanish, leaving the per-step **freshman's dream** `(a+1)^p ≡ a^p + 1`, `lift_loop_step`)
then `LOOP` (induction on `a`).  **Lift cost: one induction** — available because the per-step relation
closes a recurrence.

## Archetype 3 — ORBIT / free-action (`lift_orbit`) — in `H`'s own family
`markov_max_unique_of_orbit`: composite Markov uniqueness from one realizability check per phantom orbit.
The lift is a **free unit-root action** (`lift_orbit_freeaction`, `root_orbit_inj`: `e·u ≡ u ⟹ e ≡ 1`)
collapsing the finite root-window onto orbit representatives; the `u₁ = u₂` coincidence closes
*structurally*, not by enumeration.  Discharged at `1325 = 25·53` and `985 = 5·197`.  **Lift cost:
free-action collapse + one realizability residue** — and that residue, uniform in `c`, is `H`.

## `H` localized
`H` is the uniform cross-word continuant-trace `SEPARATE` (`markovNum` injective on all tree paths;
`ContinuantMarkov.markovNum_injective_pathsUpTo_4` is its finite instance).  It matches **A1 no** (paths
do not anti-construct a Markov number — there is no Cantor diagonal), **A2 no** (trace-injectivity is
global cross-word, not a single-step recurrence), **A3 closest** (the orbit lift already lifts a finite
Markov sample to uniform composite uniqueness, and its open residue is a per-`c` realizability — the same
family as `H`).  So `H` sits in **two ISA-compiled forms of one residue**: the trace-`SEPARATE` form and
the orbit-realizability form.  A3 is the coordinate carrying a realized same-family lift precedent — the
direction is to probe the orbit / µ-ν lift of the trace-`SEPARATE`.
-/

namespace E213.Lib.Math.Foundations.ProofISALifts

/-- **A1 DIAGONAL** — the solved uniform lift whose cost is zero: Cantor non-surjectivity, the diagonal
    self-supplying the uniform witness (`= isa_diagonalize`). -/
abbrev lift_diagonal := @E213.Lens.Cardinality.cantor_general

/-- **A1 (concrete)** — the same lift as the residue's non-surjectivity onto `Raw → Bool`. -/
abbrev lift_diagonal_concrete := @E213.Lens.FlatOntologyClosure.object1_not_surjective

/-- **A2 LOOP** — the solved inductive lift: Fermat `∀ a, a^p ≡ a (mod p)`, the finite step lifted by
    induction on `a`. -/
abbrev lift_loop := @E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FLTPrimary.flt_primary

/-- **A2 step** — the finite per-step identity the induction lifts: the freshman's dream. -/
abbrev lift_loop_step := @E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FreshmanDream.freshman_dream

/-- **A3 ORBIT** — the solved free-action lift, *in `H`'s own family*: composite Markov uniqueness from
    one realizability check per phantom orbit. -/
abbrev lift_orbit := @E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov.markov_max_unique_of_orbit

/-- **A3 free action** — the cancellation that collapses the orbit: `e·u ≡ u (mod c) ⟹ e ≡ 1`. -/
abbrev lift_orbit_freeaction := @E213.Lib.Math.NumberSystems.Real213.SternBrocotMarkov.root_orbit_inj

end E213.Lib.Math.Foundations.ProofISALifts
