# Group Theory 213 — Module Index

Blueprint: `blueprints/math/11_group_213.md` (retired).

## Modules

| File | Topic | Status |
|---|---|---|
| `Cyclic.lean` | ℤ/nℤ as `Nat` modular addition; n=2/n=5 explicit | ∅-axiom |
| `Symmetric.lean` | `Perm = Nat → Nat`; identity / compose / `swap01` involutive | ∅-axiom |
| `GroupAction.lean` | cyclic shift action; ℤ/5ℤ orbit witnesses | ∅-axiom |
| `SU5Channels.lean` | SU(5) GUT integration: 5⊗5 = 25, 24 generators, d^(d²) link | ∅-axiom |
| `Capstone.lean` | 5 cluster witnesses + `total_witness` | ∅-axiom |
| `Group.lean` | umbrella | — |

## 213-native paradigm

  * **Finite group = `Nat`-modular**: ℤ/nℤ is the modular sum
    operator on `Nat`; no abstract `Group` typeclass infrastructure.
  * **Symmetric group = `Nat → Nat`**: function composition is
    associative by `rfl`; `swap01` involution by case-on-Nat.
  * **Group action = pointwise computation**: orbits witnessed at
    individual elements via `rfl`.
  * **SU(5) GUT** is *channel counting*: 5 ⊗ 5 = 25 with 24
    traceless generators.  Bridges to `N_U = d^(d²) = 5²⁵` system
    invariant (see `seed/RESOLUTION_LIMIT_SPEC.md`).

## Honest scope

  * Lagrange's theorem at the abstract-quotient level not built —
    13's already-formalized DHA `S5*.lean` work is the structural
    extension for the symmetric-group / representation side.
  * Lie-algebra brackets: skeleton via `composePerm` algebra; full
    24-generator structure of SU(5) is in `Lib/Physics/Symmetry/`.
  * Galois extension (number-theory bridge) is a follow-up
    marathon.

## Connection to physics

  * `SU5Channels.su5_total_channels = 25` aligns with DRLT's d²= 25
    K_{3,2}^{(c=2)} channel count.
  * `su5_generators = 24` is the input to the `α_em ~ 1/137`
    derivation (gauge boson count).
  * `d_pow_d_sq_consistency : 5^25` agrees with the N_U count-Lens readout (definitional identity).
