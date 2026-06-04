# Odometer / residue-unit closure — synthesis (patterns + next seeds)

**Anchor.**  The residue unit `+1` is now a complete ∅-axiom dynamical theory: the binary
odometer (`Theory/Raw/Odometer`, 41 PURE), the profinite value + `ℤ`-action freeness
(`Theory/Raw/OdometerValue`, 18 PURE), the golden/Zeckendorf carry
(`Real213/ZeckendorfCarry`, 7 PURE), narrated in
`theory/essays/foundations/{the_residue_unit_odometer,the_unit}.md`.  This note records what the
closure made visible.

## Patterns

- **A single 213 primitive, formalized as a full dynamical system.**  The unit `+1` is not a
  scattered numeric coincidence but one object with a complete structure: injective (no-cycle),
  invertible (`±1` = a `ℤ`-action via the borrow `dec`), reversible where the descent forgets,
  continuous (a `ℤ₂`-homeomorphism), `+1 mod 2ᵏ` on every truncation, and the same `+1` in the
  golden base.  Template: take a residue primitive, build its dynamics end-to-end, land on a
  homeomorphism/group-action theorem.  Candidate re-applications: the `swap` automorphism (already
  a `ℤ/2`), the shift (a one-sided sub-dynamics) — is there a comparable full theory for each?

- **The ∅-purity pure-`Nat` trap catalog (methodology lesson).**  Repeatedly, the obvious core
  lemma carries `propext` / `Quot.sound`: `omega`, `Nat.add_mul`, `Nat.mul_assoc`,
  `Nat.add_left_cancel`, `simp only [<def>]` (equation-lemma compilation), and `rw [iff_lemma]`
  into a `Prop` goal (e.g. `Bool.and_eq_true`).  The pure replacements are: `Meta.Nat.PureNat.add_mul`,
  a hand-proved `add_left_cancel_pure` (induction + `Nat.succ.inj`), `rfl` equation lemmas instead
  of `simp only [def]`, and `cases`-based Bool splits + `decide` instead of iff-`rw`.  This is a
  reusable checklist for any pure-`Nat`/`Bool` arithmetic proof.

- **Carry-explicit over modular (the value technique).**  `bval_odo` states `+1 mod 2ᵏ` as
  `bval k (odo f) + carryOut·2ᵏ = bval k f + 1` — no division, so all-`Nat`, dodging the mod/omega
  traps.  General lesson: state "mod" facts carry-explicitly to stay ∅-pure.

## New questions / seeds

- **Pure-`Nat` toolkit — done.**  `lt_two_pow` (n < 2ⁿ) and the canonical left-cancellation
  `add_left_cancel` now live in `Meta/Nat/PureNat`; the three former duplicate proofs
  (`Beq213.nat_add_left_cancel_pure`, `NatHelper.add_left_cancel_pure`,
  `GoldenFormMarkov.add_left_cancel_pure`) are now thin one-line delegations to it (signatures
  preserved, so all consumers — `OdometerValue`, `MarkovTree`, `Padic/SetoidAssoc`, the cohomology
  essays — are unchanged).  One proof, three re-export wrappers; all PURE.

- **Odometer `ℤ`-action ↔ Markov / Stern-Brocot — first bridge done.**
  `Real213/OdometerSternBrocotUnit.odometer_sternbrocot_shared_unit`: both the odometer (dyadic
  `ℤ₂`) and the Stern-Brocot mediant tree (`SternBrocotMarkov.mInterval`) are **`List Bool`-path-
  indexed** residue descents sharing the **unimodular unit** — the Stern-Brocot `det = 1` IS the
  glue `NS − NT` (`genL_det_is_glue`, `genL = P`), the same unit the odometer carry begins at.
  Honest scope: the shared *value* + shared *index*, not a forced common map (the dyadic↔CF
  conjugacy is the Minkowski `?` function, residual).  Next: build `?` as a residue-internal
  order-isomorphism of the two `List Bool` trees (harder).

- **Carry-depth: a decidable sub-classification.**  The full µF/νF classification from a stream is
  constructively obstructed (`¬∀↔∃`); but the *eventually-periodic* streams (decidable run
  structure) may admit a decidable carry-depth class — the holonomic/finite-state end
  (`non_holonomicity_as_finite_state_escape.md`).  Is there a clean decidable sub-coordinate?

## Cross-references

`theory/essays/foundations/{the_residue_unit_odometer,the_unit,the_frontier_has_a_form}.md`,
`theory/math/algebra/phi_self_similarity.md` §3.7, `Lens/Number/SharedUnitAcrossReadings`,
`Meta/Nat/PureNat`, `frontiers/markov_lagrange/`.
