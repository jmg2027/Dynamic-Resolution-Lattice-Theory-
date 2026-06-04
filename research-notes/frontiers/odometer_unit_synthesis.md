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

- **Pure-`Nat` toolkit — partially done; dedup remains.**  `lt_two_pow` (n < 2ⁿ) is now in
  `Meta/Nat/PureNat`; `OdometerValue` reuses the existing `Beq213.nat_add_left_cancel_pure`
  instead of a local copy.  *Discovery*: the pure left-cancellation is **duplicated** across
  `Meta/Nat/Beq213` (`nat_add_left_cancel_pure`), `Meta/Tactic/NatHelper` (`add_left_cancel_pure`),
  and `Real213/GoldenFormMarkov` (`add_left_cancel_pure`).  Remaining task: consolidate the three
  to one canonical home (`Meta/Nat/PureNat`) + re-export, updating the consumers
  (`Padic/SetoidAssoc`, `MarkovTree`, the cohomology essays that cite it).  A real dedup pass
  (rippley — own commit chain).

- **Odometer `ℤ`-action ↔ Markov / Stern-Brocot.**  Both the odometer (`ℤ₂` successor) and the
  Markov/Stern-Brocot tree (`frontiers/markov_lagrange/`) are `SL(2,ℤ)`/numeration structures on
  the residue.  Does the odometer's `+1` relate to the mediant descent (`ModularGeodesicLens`)?
  A shared `det = 1` unit runs through both — is there a single dynamical statement?

- **Carry-depth: a decidable sub-classification.**  The full µF/νF classification from a stream is
  constructively obstructed (`¬∀↔∃`); but the *eventually-periodic* streams (decidable run
  structure) may admit a decidable carry-depth class — the holonomic/finite-state end
  (`non_holonomicity_as_finite_state_escape.md`).  Is there a clean decidable sub-coordinate?

## Cross-references

`theory/essays/foundations/{the_residue_unit_odometer,the_unit,the_frontier_has_a_form}.md`,
`theory/math/algebra/phi_self_similarity.md` §3.7, `Lens/Number/SharedUnitAcrossReadings`,
`Meta/Nat/PureNat`, `frontiers/markov_lagrange/`.
