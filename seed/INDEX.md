# seed/ — DRLT 213 foundational corpus

If you read one file in `seed/`, read **this one**.  It contains
the axiom, the key concepts, and the falsifiability rule.
Everything else is detail.

---

## The axiom in 4 clauses (`AXIOM/02_statement.md`)

1. **Something exists.**  At least two: `a`, `b`.  They stand in
   a *primitive distinction* relation — no relation other than
   "not equal" is presupposed.
2. **Pairing of two somethings is yet another something.**
   Recorded `a / b`.  Closed: paired again with other elements.
3. **Pairing is symmetric.**  `a / b = b / a`.  No absolute
   order.
4. **No pairing with oneself.**  `x / x` is undefined.  Self is
   not distinguished from self.

That is the entire commitment.  Every result of 213 is either
derived from these 4 clauses, or it is a specific Lens choice on
top.  No third option.

---

## Key concepts (what makes this corpus what it is)

**Residue, not declaration.**  The axiom is not a claim about
"the foundation of the world."  It is the minimum residue that
inevitably remains the moment one tries to point at something.
Notation, the moment it begins, endlessly produces new
somethings; the axiom is the minimum expression of that
recursion.

**Primitive distinction.**  Not "relation" (which presupposes
existing somethings + ZFC properties), not "difference" (which
presupposes "sameness").  Primitive distinction operates *first*;
"primitive" = a pledge of no further reducibility.

**No exterior.**  Every act of describing the axiom **already
occurs inside 213**.  "Lens", "derivation", "observer" — each is
a something among somethings.  The dichotomy "is the Lens inside
or outside the axiom?" does not hold.  See
`AXIOM/07_self_reference.md` §8.4 for Claude's mandatory
dichotomy-avoidance guide.

**Derive, not reconcile.**  All results must come from the
axiom + explicit Lens choices.  Substituting external constants,
fitting to experimental values, importing structure from other
theories — all are *fudge*.  When fudge is found, the Lens is
corrected, not the formula.  If that fails too, the theory is
abandoned.

**Three-direction uniqueness.**  Raw is uniquely determined from
all three sides:

- *below* — removing any clause collapses to trivial / static /
  void (`Meta/AxiomMinimality`).
- *sideways* — any distinguishability framework factors through
  Raw (`Meta/UniversalLens`).
- *above* — Raw's shape is forced to (NS, NT, d) = (3, 2, 5)
  (`Theory/Atomicity/{Five, PairForcing, …}`, pure-ℕ, no Raw
  import).

**Resolution limit (a fourth invariant).**  N_U = d^(d²) = 5²⁵
arises independently in 4 mathematical domains (Lean fractal
lens cardinality / K_25 graph coloring / rank-2 tensor dof at
d=5 / max injective projection space).  This is the system
invariant — see `RESOLUTION_LIMIT_SPEC.md` (it is canonical;
when it diverges from any AXIOM/ chapter on resolution-limit,
that spec wins).

---

## The falsifiability rule (`AXIOM/04_falsifiability.md` §5.2.1)

> 213 must never require any external axiom addition (no
> Classical, LEM, native_decide, …).
>
> If any result is shown to be **absolutely impossible** without
> adding an axiom, **the entirety of 213 is discarded**.  Not
> the result alone — the theory itself.

This is a direct consequence of "the axiom is a residue": if
adding an axiom is genuinely necessary, Raw was not the minimum.

The mechanical auditor of this rule is Lean's `#print axioms`
command + the project's Mathlib-free + 0 sorry + 0 external
axiom constraint.

**Measurement falsifiers** (each violation = repo discarded):

| Measurement | DRLT prediction |
|---|---|
| Neutrino ordering | normal |
| θ_QCD | [2.5,3.0]×10⁻¹¹ |
| 4th gen particles | absent |
| Cabibbo λ | 5/22 ± 1% |
| m_p | 938.27 atomic |
| Magic numbers | {2,8,20,...} ✓ already verified |

---

## Naming policy: 213 / DRLT / E213

| Name | Meaning | Where used |
|---|---|---|
| **213** | the formal axiom framework — Raw + 4-clause axiom + Lens framework + ∅-axiom commitment.  The mathematical / type-theoretic side. | Throughout AXIOM corpus; metatheorems and Lean tree are about 213. |
| **DRLT** | "Dynamic Resolution Lattice Theory" — the physics deployment of 213 (Zeno → pixels intuition per `ORIGIN.md`). | Physics constants (CLAUDE.md), `Lib/Physics/` Lean tree, papers, "DRLT zero-parameters" capstones. |
| **E213** | the Lean namespace.  Mechanical artifact (`namespace E213.Theory`, `namespace E213.Lens`, …). | Lean source only. |

**Disambiguation rule.**  Use **213** for axiom / mathematical
framework statements.  Use **DRLT** for physics (constants,
observables, predictions).  Use **E213** only inside Lean code
or when citing specific Lean modules.  When in doubt about a
math/physics-boundary claim, prefer **213** (it is the broader
name; DRLT is a physics specialization).

---

## Directory layout

```
seed/
├── INDEX.md                   ← this file (standalone entry)
├── ORIGIN.md                  ← DRLT origin narrative
├── PAPER1.md                  ← archival, cited by ~25 Lean files
├── RESOLUTION_LIMIT_SPEC.md   ← N_U structural-invariant authority
├── NOTATION.md                ← symbol conventions
└── AXIOM/                     ← the axiom corpus, 12 chapters
    ├── INDEX.md               ← chapter TOC
    ├── 00_nature.md           ← residue, distinction, 3-dir uniqueness
    ├── 01_notation_recursion.md
    ├── 02_statement.md        ← the 4-clause axiom
    ├── 03_form.md             ← why this form
    ├── 04_falsifiability.md   ← discard rule + measurement falsifiers
    ├── 05_primacy.md
    ├── 06_formalization.md    ← Lean correspondence
    ├── 07_self_reference.md   ← §8.4 dichotomy guide (Claude refresh)
    ├── 08_implementation.md   ← Raw + Theory faithful-emulator analysis
    ├── 09_audit.md            ← Lean ↔ axiom cross-check
    └── 99_history.md          ← deprecated R-frame + change log
```

## What seed/ is NOT

- **NOT the source of truth.**  `lean/E213/` is.  When seed/
  and Lean disagree, Lean wins.
- **NOT a reading order for the mathematics.**  See
  `guide/INDEX.md` (deductively-ordered narrative).
- **NOT a paper draft.**  `papers/` was deleted (commit
  a02b751); only `papers/README.md` retained as historical
  marker.

## Quick cross-references

- `lean/E213/Theory/Raw*.lean` — formal counterpart of the
  4-clause axiom.
- `lean/E213/Theory/Atomicity/{Five, PairForcing}.lean` —
  formal counterpart of "atomicity forces (NS=3, NT=2, d=5)".
- `lean/E213/Lib/Physics/Foundations/FiniteUniverse.lean` —
  formal counterpart of `RESOLUTION_LIMIT_SPEC.md` (1/α_em
  rational at every finite N_U; π² is limit-label, not a 213
  primitive).
- `LESSONS_LEARNED.md` (root) — guardrails extending the axiom
  corpus.
- `lean/E213/ARCHITECTURE.md` — canonical layer architecture.
- `CLAUDE.md` boot sequence — read
  `AXIOM/07_self_reference.md` §8.4 every session start.
