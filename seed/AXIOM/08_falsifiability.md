# §8. Falsifiability and the ∅-axiom contract

## §8.1 Why mechanical verification is essential

The direction of derivation (§7.2) is the doctrine.  Mechanical
verification is the auditor that ensures the doctrine holds in
practice.

Human eyes can quietly overlook fudge.  Mechanical verification
cannot.  Lean refuses to type-check a proof that smuggles in an
unstated commitment, and `#print axioms` reports precisely which
axioms (if any) a theorem depends on.

This is why 213 operates under the strict Mathlib-free, 0-sorry,
0-axiom constraint.  The axiom of §2 is the contract; the
mechanical verification described below is what ensures the
contract holds.

---

## §8.2 The ∅-axiom contract

**213 must never require any external axiom addition.**  Not
`Classical.choice`, not LEM, not `propext`, not `Quot.sound`,
not `Lean.ofReduceBool` (the `native_decide` artefact), not any
Mathlib axiom.

The standard is **∅-axiom**: every theorem must satisfy

```
#print axioms T  →  "does not depend on any axioms"
```

This is not a stylistic recommendation.  It is a **falsifiability
criterion** with two halves.

The first half is operational.  Every theorem and construction
in 213 must be derivable from Lean's structural type-checker
plus the Raw axiom alone.  A theorem whose `#print axioms`
returns any non-empty list is `sorry`-equivalent: it has not
closed under the contract.  `propext`, `Quot.sound`,
`Classical.choice`, `Lean.ofReduceBool`, and the Mathlib axioms
are all dirty under this standard — same verdict for all.
(Specific structural necessities are documented as sealed-by-
design in `STRICT_ZERO_AXIOM.md` §"Sealed-by-design categories";
everything else is real DIRTY and counts as failure.)

The second half is doctrinal.  If a result is shown to be
**absolutely impossible** to prove or construct without adding
an axiom — blocked after multiple sessions of exploration,
blocked by structural obstruction — then **the entire 213
theory is falsified**.  Not just the result; the theory.

The strictness follows directly from §1.1: the axiom is a
residue.  If something is not a residue, it is not an axiom.
"Adding one more axiom here will make everything work" suggests
that Raw was not the minimum residue.  Needing to add an axiom
therefore means Raw was wrong, and the theory must be discarded.

Operationally:

  - The temptation "Classical makes it easy" is rejected
    entirely.  Adding Classical does not make a proof easier —
    it only hides the fudge.
  - Blocked results are recorded as **open**, with the
    distinction between a *temporary obstacle* (we have not yet
    found the right Lens) and a *permanent wall* (we have
    exhausted Lens choices) made explicit.  A permanent wall is
    a theory failure.  This distinction is the §5.3 balance
    doing falsifiability work: no exterior does not promise
    automatic location — a proof-residue not yet pointed at is
    open, not falsifying — and no-automatic-location does not
    excuse a wall — a structural obstruction, once shown, is
    not reclassified as "hard to locate."
  - Lean's verification is the **mechanical auditor** of the
    rule.

This declaration is non-negotiable.  Violations trigger
re-evaluation of the entire theory, not patching of the
particular violation.

---

## §8.3 Falsification is internal

A prediction is falsified when one 213-internal Lens reading
(measurement, via an observer-Lens) disagrees with another
213-internal Lens reading (the prediction, via a theory-Lens)
on the same observable.  Both sides of the comparison are
residue-internal events; there is no external referee.

Allowing external axioms breaks this internal closure — it
admits truths that no internal Lens application yields.  That
is why §8.2 treats external-axiom dependence as theory failure,
not as a local proof-engineering inconvenience.

Self-completion (§5.5) guarantees that every prediction has a
definite truth value internally: every pointing is already
complete, so claims of the form "prediction P matches
measurement M" are well-formed without external semantics.

---

## §8.4 Empirical predictions

From the axiom, by identifying a single observer Lens, all
observed physical constants must be derivable without fudge.

This is **not** a methodological commitment to a 0-parameter
form.  It is the **structural absence** of free parameters.  A
"free parameter" is a value set by an external dialer; 213
commits to no exterior, so the category of values-set-from-
outside is unavailable.  Physical constants appear only as
residue-internal fixed points (§3.5 — φ as the fixed point of
self-pointing iteration; the same φ in DRLT constants).
Tuning a constant is not forbidden by rule; the action has no
operand to apply to.

The empirical prediction is therefore strong by structure, not
by choice.  If a constant has been derived as a residue-internal
fixed point and measurement disagrees, the Lens reading was
wrong, or the theory is wrong.  No third option ("we will find
a parameter to adjust") is available.

The wider the range over which predictions hold, the stronger
the demonstration that 213's primacy claim (§7.1) is correct.

---

## §8.5 Measurement falsifiers

A theory that cannot be wrong is no theory.  Beyond the formal
∅-axiom contract (§8.2), 213's **physics deployment (DRLT)** is
exposed to specific *measurable* predictions: each is atomic-forced
by the shape parameters of §4.3, and each carries a discard
condition if the measurement comes in differently.  Per §8.2 a
violation refutes the **forced triple `(NS, NT, d) = (3, 2, 5)`**
itself — there is no retunable parameter to absorb it (§8.4).

This empirical surface is **one domain's** falsifiability gate (the
DRLT Validation Standard), not an axiom-level commitment: primacy is
the *breadth* of ∅-axiom derivation (§7.1), not these particular
physics numbers.  So the specific roster — values, brackets,
measurement timings — lives where it is maintained and audited, not
embedded in this corpus:

  - `catalogs/falsifiers.md` (curated) and
    `catalogs/falsifier-roster.md` (auto-discovered) — the falsifier
    values and discard conditions (neutrino ordering, the θ_QCD
    bracket, no 4th generation, the PMNS / Cabibbo denominators, m_p,
    the magic numbers);
  - `seed/THEOREM_METHODOLOGY_SUITE.md` §TH-3 — the falsifier-surface
    specification.

What is axiom-level here is only the *shape* of the exposure: 213
makes forced, parameter-free, discard-on-violation predictions whose
generators are `#print axioms`-clean.  The values themselves are
deployment, not foundation.

---

## §8.6 The forced binding (and where the numbers live)

What ties that empirical surface back to the axiom is structural,
and *that* is the axiom-adjacent part: the forced triple
`(NS, NT, d) = (3, 2, 5)` fixes the headline falsifier integers as
polynomials in the triple, so measuring any of them outside its
bracket refutes the **triple**, not a parameter.  This binding is a
single ∅-axiom theorem, `falsifier_roster_forced`
(`Lib/Physics/Foundations/FalsifierRosterForced.lean`, via
`atomic_iff_five` and `pair_forcing`).

The precision side shares the identical infrastructure — the same
atomic primitives, the same Lens catamorphisms, the same
`#print axioms`-clean status — and its values (`1/α_em`, `m_μ/m_e`,
`m_p`, `Ω_Λ`) live in `catalogs/physics-constants.md`.  A theory with
only a precision side or only a falsifier side has fewer constraints;
the DRLT deployment has both, which is the validation standard
recorded in `CLAUDE.md` — **one domain's** gate, not the measure of
the framework's primacy (§7.1).

---

## §8.7 One-line summary

> Any single measurement deviating from a DRLT atomic-forced
> integer discards the repository.

This is the actual stake.  A formal theorem, a falsifiable
prediction, and a 0-axiom contract: a genuinely falsifiable
theory.
