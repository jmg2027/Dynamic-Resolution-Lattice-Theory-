# §5. Direction of derivation and Falsifiability

## §5.1 Derive, not reconcile

**Everything other than this axiom** must be either derived from the
axiom or the result of a specific Lens choice.

- Substituting external constants, fitting to experimental values,
  importing structure from other theories — all are **fudge**.
- When fudge is found, the **Lens is corrected**, not the formula.
- If that too fails, **the theory is abandoned**.  The
  infinite-extension defense of "more Lenses will be found" is not
  permitted.

## §5.2 Why mechanical verification is essential

Mechanical verification (Lean) does not permit fudge.  Therefore the
point of derivation failure is **revealed automatically**.  The
human eye can quietly overlook fudge; the machine cannot.

This is why 213 operates under the Mathlib-free + 0 sorry + 0 axiom
constraint.  The axiom is the contract; mechanical verification is
the auditor.

## §5.2.1 Adding external axioms is a theory-wide discard condition

**213 must never require any external axiom addition** — no
Classical.choice, LEM, no `propext`, no `Quot.sound`, no
`Lean.ofReduceBool` from native_decide, no Mathlib axioms.

The standard is **∅-axiom**: every theorem must satisfy
`#print axioms T → "does not depend on any axioms"`.

This is not merely a recommendation; it is a **falsifiability
criterion**:

- Every theorem and construction in 213 must be derivable from
  Lean's structural type-checker + the Raw axiom alone.
- A theorem with *any* non-empty `#print axioms` output is
  **`sorry`-equivalent**: it has not closed under the falsifiability
  contract.  `propext` and `Quot.sound` were tolerated in earlier
  sessions but are now treated identically to `Classical.choice` —
  same dirty bit, same falsified-at-this-tier verdict.
- If any result is shown to be **absolutely impossible** to prove /
  construct without an additional axiom (e.g., still blocked after
  multiple sessions of exploration), this means **the entirety of
  213 theory is falsified**.  Not just the result alone — the theory
  itself is discarded.

This strictness is a direct consequence of §1 ("the axiom is a
residue"):

- If it is not a residue, it is not an axiom.
- "Adding just one more axiom here will make everything work"
  suggests Raw is not the "minimum residue."
- Therefore, needing to add an axiom = the Raw axiom is wrong =
  theory discard.

**Operational side**:

- Entirely reject the temptation "Classical makes it easy."  It does
  not become easier — fudge is merely hidden.
- Results that are blocked are simply left as "open," but "open" is
  distinguished as either a **permanent wall** or a **temporary
  obstacle**.  A permanent wall means theory failure.
- Lean verification is the **mechanical auditor** of this
  falsifiability.

This rule is Mingu's confirmed declaration (2026-04-24).  It is
never relaxed; violations trigger re-evaluation of the entire
theory.

## §5.3 Empirical predictions

From this axiom, by identifying a single Lens (the physical
observer Lens), all observed physical constants must be derivable
without fudge.

This is not a *methodological commitment* to 0-parameter form — it
is the *structural absence* of free parameters.  "Free parameter"
means "value set by an external dialer"; 213 commits to no exterior
(`07_self_reference.md` §8.1), so the category of
values-set-from-outside is unavailable.  Physical constants appear
only as residue-internal fixed points (cf. `02_statement.md` §3.4 —
φ as the fixed point of self-pointing iteration; same φ in DRLT
constants).  *Tuning* a constant is not forbidden — the action has
no operand to apply to.

The empirical prediction is therefore strong by structure, not by
choice: if a constant has been derived as a residue-internal fixed
point and measurement disagrees, the Lens reading was wrong, or the
theory is wrong.  No third option ("we'll find a parameter to
adjust") is available.

The wider the range over which predictions hold, the stronger the
claim of the axiom's primacy.

---

## §5.4 Measurement falsifiers (CLAUDE.md verification criterion 2)

213 must simultaneously provide *formalized new physics that no one
can contest*.  Each *measurable* integer is *atomic-forced*:

| Measurement | Timing | DRLT prediction | If violated |
|---|---|---|---|
| Neutrino ordering | JUNO ~2030 | normal | discard |
| θ_QCD | nEDM ~2027-30 | [2.5,3.0]×10⁻¹¹ | discard |
| 4th gen particles | LHC ongoing | absent | discard |
| PMNS angles | DUNE/HK ~2030 | leading denom {NS,NT,d²-1} | discard |
| Cabibbo λ | LHCb/Belle II | 5/22 ± 1% | discard |
| m_p | Lattice QCD next | 938.27 atomic | discard |
| Magic numbers | verified | {2,8,20,...} | (already verified) |

## §5.5 Formal guarantees

  Phase 3 Falsifier:
    `phase3_falsifiers : 19-conjunct, 0 axioms`

  Phase 1 precision quantities:
    1/α_em = 137.036 ppm
    m_μ/m_e = 0.48 ppb
    m_p exact (lattice precision)
    Ω_Λ = 0.0008%

## §5.6 One-line summary

> "Any single measurement deviating from the DRLT forced integer →
> repo deleted"

This is the *true stake* of 213.  Formal theorem + falsifiable + 0
axioms = a genuinely falsifiable theory.
