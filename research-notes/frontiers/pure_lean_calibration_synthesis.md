# Cross-campaign synthesis — the propext-trap workaround + "hand-wave → explicit object"

**Anchor.**  Two independent campaigns landed in `main` together: the determinant /
permutation-sign stack (`Lib/Math/Algebra/Linalg213/`, `DetMul`/`DetTranspose`/`PermSign`)
and the Reverse Mathematics 213 marathon (`Lib/Math/Logic/`, field 17).  Read side by side
they share two structural patterns worth recording.

## Patterns

- **The core-`Decidable`/core-lemma propext leak, and its hand-rolled-pure workaround,
  recurs independently.**  The determinant proof avoids the default `Decidable (a ∈ l)`
  (which carries `propext`/`Quot.sound`) by a constructive `cnt`-decision pigeonhole
  (`permutation_sign_as_homomorphism.md`); field 17 avoids `omega`, `Nat.succ_ne_zero`,
  `List.append_nil`/`append_assoc`, `if`/`split`, and `decide`-on-a-`Prop` by
  `Bool.noConfusion`/`Nat.noConfusion`/`Nat.succ.inj`/`cases` + hand-rolled pure lemmas
  (`append_nil_pure`, `parity`, `the_omniscience_ledger.md`).  Same trap, same fix shape,
  two campaigns that never touched each other — the methodology essays
  `pure_funext_avoidance`, `pure_nat_ring_methodology`, `bool_assoc_failure_meaning` are
  describing one growing discipline, and a *consolidated propext-trap catalog* (which core
  constructs leak, which `*_pure`/`*213` replacement to use) is now earned.

- **Each campaign makes a classically hand-waved step an explicit 213 object.**  The
  permutation sign's "well-defined parity" becomes a *sorting invariant*
  (`PermSign.psign_mul`, `Q_swap`); reverse math's "set-existence axiom" becomes an
  *omniscience hypothesis* on the residue carrier (`the_omniscience_ledger.md`:
  cost on the hypothesis line, not the axiom line).  Both relocate a classical
  hand-wave from rhetoric to a pointable object — the residue read under a Lens
  (`seed/AXIOM/07_primacy.md` §7.1), not an assumed primitive.

## New questions

- **A single `Meta/` propext-trap reference** (the catalog above) co-located with the
  `*_pure`/`*213` replacements, so each future campaign reaches for the workaround instead
  of rediscovering the trap.  Does it want to be a `Meta/` doc + a checked lemma bundle?
- **Is "classical hand-wave → explicit object" a general promotion signal?**  Both essays
  arose exactly when a hand-waved step (parity / set-existence) became a theorem; this may
  be a pattern-able essay trigger (cf. `promotion_essay_log.md`).

## Cross-references
`theory/essays/algebra/permutation_sign_as_homomorphism.md`,
`theory/essays/methodology/{the_omniscience_ledger,pure_funext_avoidance,pure_nat_ring_methodology,bool_assoc_failure_meaning}.md`,
`books/math/reverse-math-213.md` (Pure-Lean notes), `STRICT_ZERO_AXIOM.md`.
