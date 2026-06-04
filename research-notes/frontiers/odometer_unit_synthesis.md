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
  Honest scope: the shared *value* + shared *index*, not a forced common map.  The **Minkowski `?`
  is being compiled in layers** (`Real213/OdometerSternBrocotUnit`):
    - **L1 skeleton** (`minkowski_skeleton`) — the Stern-Brocot tree (`sbInterval`, Farey `det=1`)
      and the dyadic tree (`dyInterval`, children `2·lo`/`2·lo+1`) are one `List Bool` binary tree
      under two unimodular labellings; the path-identity is the order-iso between the CF and dyadic
      addresses.
    - **L2 value** (`minkowski_compile`) — the dyadic side IS the binary numeration
      (`dyInterval_value`: `(dyInterval path).1 = binVal path`, the odometer's world); the
      Stern-Brocot side is the mediant fraction `sbMediant`; `?` is the path-indexed map between
      them.
    - **L3 order** (partial, `dyadic_local_order`) — the dyadic side is order-preserving:
      `binVal (true::t) < binVal (false::t)` (`2k < 2k+1`).  The Stern-Brocot side is the same local
      order on the mediant fraction, reducing to the det-1 invariant (cross-mult gap
      `3·(bc−ae) = 3 > 0`); that `ℤ` cross-multiplication + the global monotonicity over all
      path-pairs is the remaining bounded step (the SternBrocotMarkov §7–§8 slope engine).
    - **L4 analytic** — the singular `?` (order-completion / limit) is residual, reached by no
      finite path (`object1_not_surjective` pattern).

- **Carry-depth: a decidable sub-classification.**  The full µF/νF classification from a stream is
  constructively obstructed (`¬∀↔∃`); but the *eventually-periodic* streams (decidable run
  structure) may admit a decidable carry-depth class — the holonomic/finite-state end
  (`non_holonomicity_as_finite_state_escape.md`).  Is there a clean decidable sub-coordinate?

## Cross-references

`theory/essays/foundations/{the_residue_unit_odometer,the_unit,the_frontier_has_a_form}.md`,
`theory/math/algebra/phi_self_similarity.md` §3.7, `Lens/Number/SharedUnitAcrossReadings`,
`Meta/Nat/PureNat`, `frontiers/markov_lagrange/`.
