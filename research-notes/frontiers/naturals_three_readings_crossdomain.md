# Cross-domain — ℕ generated three ways, and forcing at a third scale (2026-06-24)

Insights surfaced fusing this branch's spine/FTA/rival work with the main corpus
(`arithmetic_generation.md`, `forced_by_the_distinguishing.md`, the genesis-seam).

## 1. ℕ is generated three ways — three count-readings of one distinguishing

- **Multiplicity** (count-shadow): `count : List Unit → Nat` over append — `+` first.
  `theory/math/numbersystems/arithmetic_generation.md` (main).
- **Depth** (successor-spine): `toNat = depth` over the `slash`-successor `rawSucc` —
  `succ` first. `theory/math/numbersystems/naturals_from_the_spine.md` (this branch).
- **Population** (level-cardinality): `census = rawCount ∘ toNat`, the `2,3,5,12,68`
  recurrence — the count of distinct `Raw`s at each level. `RawNatCensus` (this branch).

The same spine `rawTower` carries readings 2 and 3 (`two_readings`); reading 1 is the
unit-list shadow. One object, three Lens readouts — none privileged. The seed insight:
*"how many units" (multiplicity), "how deep" (depth), and "how many distinct things at
this depth" (population) are three count-Lenses on the one distinguishing, agreeing on
`0,1,2` and diverging by what they count.*

## 2. "Forced by the distinguishing" now has a THIRD scale — the primitive itself

`forced_by_the_distinguishing.md` (essay 103) fused two forcings: forced **axis**
(additive count-Lens, atoms a,b) and forced **atoms** (×-count-Lens, primes, via
`vp_separation`). This branch's `RivalArity.arity_distinctness_forcing` adds a third,
*below* both: the forced **primitive** — binary-distinct is the unique generative arity
(unary too weak, ternary sterile on the 2-seed, non-distinct over-generates,
relation-first `Bool`-codomain non-generative). So the forcing principle reads at three
resolutions: which primitive (arity-2-distinct) → which axis (count-Lens) → which atoms
(vp_separation). The rival-forcing is the ground floor the two count-Lens forcings stand on.

## 3. The genesis-seam's "un-generatable boundary" was dissolved

`arithmetic_generation.md` named the multiplicative-atom/FTA layer as the boundary where
generation stops — "uniqueness completes on a *non-structural* descent" (the borrowed
`Nat.strongRecOn`/`Nat.div`). This branch closed it: `FTAUniquenessGrounded` completes FTA
uniqueness on a **structural** descent (`subMod` fuel + `isPart_wf`), no borrowed division.
So the stated boundary was not generated-vs-ungeneratable but generated-vs-borrowed-engine:
once the engine is regrounded, the "boundary" moves. (The genuine remaining boundary is the
kernel `inductive` itself + the `Nat` readout — strictly smaller.)

## Status
Recorded to seed an essay. Insight 1 is the strongest standalone essay (three readings of
ℕ); 2 extends an existing essay; 3 is a correction already applied to the stale line in
`distinguishability_is_the_one_dial.md`.
