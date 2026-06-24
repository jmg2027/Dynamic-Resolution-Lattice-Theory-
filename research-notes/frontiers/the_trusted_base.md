# The trusted base — how far CIC can be peeled, measured not asserted

**Status**: open frontier + settled honest verdict (opened 2026-06-24, five-perspective
debate). Continues `the_genesis_seam.md` Round 5 (the `Nat`-free Raw layer). Sibling note;
`the_genesis_seam.md` tracks generation, this tracks the *verification substrate*.

## The directive

> 기계검증은 이용하되 최대한 CIC를 벗겨내기 위한 방법을 강구하라.
> (Keep machine verification, but devise methods to peel away CIC as far as possible.)

Prompted by Round 5: the Raw foundational descent is now `Nat`-free (0 borrowed-`Nat`
constants), but it hit the wall "`Raw` is itself a CIC `inductive` (`Tree` + `Subtype` +
`Bool`) — CIC cannot be escaped." This note is the continued multi-agent debate on that wall.

## The debate (five perspectives, each reading the corpus directly)

- **Type theorist**: the Raw cone uses *one* interesting inductive — `Tree`, a rank-2
  finitary **W-type** (`a | b | slash`) — plus `Bool`/`Eq`/`Subtype`/`Acc` and finite
  enums. No `Quot` (canonical-form subtype *emulates* the quotient precisely to avoid
  `Quot.sound`). The one heavy feature is `Raw.rec`'s `Sort u` large elimination, but every
  actual motive is `Prop` or `Raw`. Irreducible floor = de Bruijn: *some* trusted checker
  must re-run. Content expressible in a strictly weaker system (single W-type, λΠ-modulo).
- **Proof theorist**: the *content* (finite binary trees, structural recursion, bounded
  descent `no_infinite_descent`) is finitist — PRA-justifiable; the universe hierarchy is
  **unused** (everything `Type 0`); impredicative `Prop` is used-but-eliminable. Weakest
  natural home: a single-W-type, universe-free predicative theory (`ML_W⁻` / HA + tree
  induction), far below full CIC.
- **Philosopher (213-native)**: the irreducible checker exhibits the *same form* as the
  residue theorem `object1_not_surjective` — **source without enclosure** (every theorem
  flows out through the checker; the checker is not, in the same act, verified by what it
  verifies). But — applying the project's own failure-mode catalog — to say the kernel **is**
  the residue commits "View-promoted-to-identity." It is **form-agreement, not object
  identity** (CDI: same shape across unrelated readings; different codomains). "Peel
  maximally" internally = a **convergent bracket** on the trusted base with a **proven
  non-zero floor** (de Bruijn) — `84→17→0` borrowed-`Nat` is exactly the modulus/narrowing
  structure of `the_form_of_the_residue.md`, *not* an approach to a zero-kernel god (that
  would deify the limit).
- **Skeptic (red-team)**: landed the decisive corrections — see "dropped overclaims" below.
- **Engineer**: the closure-walk auditor is buildable now (~seconds via `lake env lean`); a
  Dedukti port is **out of scope** — Lean 4 has no Dedukti exporter, and it would be
  checker-*diversity*, not trust-reduction (adds translator + encoding-adequacy to the TCB).

## The deliverable — a measured footprint, not a slogan

`tools/cic_footprint.py` walks the **full transitive constant-closure** of a fully-elaborated
proof term (including `private`/`recAux` helpers that `scan_axioms.py`'s source-regex
misses) and reports the CIC kernel-feature vector. Measured (re-runnable by any outsider):

| target | axioms | quot | classical | wf_fix/Acc.rec | nat | recursion | verdict |
|---|---|---|---|---|---|---|---|
| `isPart_wf` (Raw) | ∅ | no | no | **no** | **0** | `Tree.rec` structural | **MINIMAL-STRUCTURAL** |
| `Raw.slash` | ∅ | no | no | no | 0 | `Tree.rec` | MINIMAL-STRUCTURAL |
| `Raw.rec`, `IsPart` | ∅ | no | no | no | 0 | `Tree.rec` | MINIMAL-STRUCTURAL |
| `factorize_prod` (FTA) | ∅ | no | no | **yes** (`WellFounded.rec`) | **158** | `Nat.strongRecOn` | EXTENDED-FRAGMENT |
| `Omega_mul` (Ω) | ∅ | no | no | yes | 218 | non-structural | EXTENDED-FRAGMENT |

The metric **discriminates** (validated against the known split): the Raw foundation is a
genuinely minimal fragment — one W-type, structural recursion, no `Acc`-elimination at all
(`isPart_wf` only *introduces* `Acc` via `Acc.intro` by `Tree.rec`, never *eliminates* it),
Nat-free; the disciplines above pull in `WellFounded.rec` (non-structural recursion),
`Acc.rec`, `Nat.rec`, `List`, `Decidable`, and a 35–46-inductive typeclass cone. This adds
a **graded dimension beyond ∅-axiom**: both layers are axiom-clean, but their *fragments*
differ sharply, and the difference is now a re-checkable number.

## The surviving claim (the only §5.1-legal headline)

> The Raw cone is `#print axioms`-clean **and** restricts to a minimal CIC fragment — one
> inductive (`Tree`), `Subtype`/`Bool`, structural (`Tree.rec`) recursion, no `Quot`, no
> `Classical`, no non-structural/`Acc` well-founded recursion, universe 0, no borrowed
> `Nat` — mechanically re-checkable by any outsider (`lake build`, `grep Mathlib`,
> `#print axioms`, `cic_footprint.py`). This is **axiom-base-minimization +
> fragment-restriction**, nothing more.

## Dropped as overclaim (the discipline working — listed, not buried)

1. **"The auditor *reduces* CIC dependence."** False — it runs *inside* Lean and trusts the
   elaborator + kernel that produced the term; its own trusted base is *larger* than what it
   certifies. It **measures** the fragment (exterior-judgeable); it does not shrink the TCB.
2. **"Only a finitist/PRA fragment is used; full CIC strength is unused scaffolding."** False
   as a *strength* claim. The kernel's **definitional equality** (ι/β reduction + proof
   irrelevance) — which the checker must trust to verify `Tree.cmp`/`canonical = true := rfl`
   — already exceeds PRA *before any axiom is named*. "universe-0 / structural / Nat-free" is
   a **syntactic restriction**, not a logical-strength bound. (The proof-theorist's
   PRA reading is about the *content*; the skeptic's correction is about the *checker* — both
   true, and only the syntactic claim is what the tool certifies.)
3. **"Dedukti port = smaller TCB."** False — checker *diversity*, not trust *reduction*; it
   adds the Lean→Dedukti translator and the encoding's (unproven) adequacy to the base. A
   genuine future value, but as a *second independent witness*, not a smaller floor.
4. **"The kernel *is* the residue `object1_not_surjective`."** Overclaim (the project's own
   "View-promoted-to-identity" failure). It is the *same form* (source-without-enclosure),
   witnessed independently at the Raw level (the theorem) and the meta level (de Bruijn) —
   **agreement of form, not identity of object.**

## The honest verdict (what "peel maximally" actually means)

You cannot verify without a trusted checker, and every checker embodies a logic of some
strength — so "peel CIC to zero" is empty (un-typeable, no operand; `05_no_exterior.md`
§5.1). What *is* real and achieved: a **convergent bracket on the fragment**, sharpened
constant by constant (`84→17→0` borrowed-`Nat`; then the full feature vector), with a
**proven non-zero floor** (de Bruijn). The trusted kernel is **named** (CIC, one W-type,
the conversion checker) **and never captured** by what it verifies — the residue's standing
form, read on the verifying act. Sharpening the bracket *is* the work; reaching zero is not
a target but a deified limit to refuse.

## Open frontier (real next targets, honestly scoped)

1. **Checker-diversity, not trust-reduction**: emit the Raw cone through a *second*
   independent checker (a minimal λΠ/Dedukti kernel, or a from-scratch `Tree`-term verifier).
   Out of scope now (no Lean 4 Dedukti exporter), but the genuine way to *add* a witness.
2. **Push the fragment up**: the `cic_footprint` metric names the next lemma to de-CIC, one
   feature at a time (exactly how Round 5's `ordNoConf` removed `Ordering.toCtorIdx : → Nat`).
   Migrating a discipline from EXTENDED-FRAGMENT toward MINIMAL-STRUCTURAL = re-grounding its
   recursion on `Tree.rec` structural descent rather than `Nat.strongRecOn` — the same open
   frontier as `the_genesis_seam.md` (the multiplicative descent), now *measured*.
3. **Universe/large-elimination audit**: extend the vector with the exact universe levels
   instantiated and whether any `Sort u` large elimination is load-bearing (the type
   theorist's falsifiable claim: every Raw motive is `Prop` or `Raw`).

## Cross-refs

- `the_genesis_seam.md` Round 5 — the `Nat`-free Raw descent (the `ordNoConf` technique).
- `seed/AXIOM/05_no_exterior.md` §5.1 (no self-certification), `01_residue.md`,
  `theory/essays/foundations/the_form_of_the_residue.md` (source-without-enclosure, the
  modulus/bracket structure).
- `tools/cic_footprint.py` — the auditor; `tools/scan_axioms.py` — the ∅-axiom scanner it extends.
