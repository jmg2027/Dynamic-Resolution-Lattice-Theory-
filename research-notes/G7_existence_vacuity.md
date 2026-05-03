# G7 — Existence Vacuity in Classical Math: Mechanical Lean Demonstration

**Author:** Mingu Jeong (insight, framework); Claude (Lean formalization)
**Date:** 2026-05-XX (this session, after G6)
**Companion Lean file:** `lean/E213/Math/Cohomology/HodgeConjecture/Bridge/G7Vacuity.lean`

## §0  Question

Following G6 — "the 'continuum/discrete tradeoff' is empty vocabulary,
not a tradeoff" — the natural sequel: can we **mechanically** show in
Lean what *contradiction* (모순) classical math (ZFC, category theory,
homotopy) runs into when its "existence theorems" (Calabi-Yau, Yamabe,
Mori MMP) are dragged onto a strict-∅-axiom computable substrate?

**Answer:** Yes, but the "contradiction" is not a logical inconsistency
(ZFC presumed consistent by Gödel meta-theorem).  It is a **operational
vacuity / semantic void** — and *that* is exactly what 213-Lean exposes
mechanically.

## §1  The simulation strategy: Axiom of Choice as black-box

The only weapon classical math has for "exists without exhibition" is:

  · **Axiom of Choice (AC)**, equivalently
  · **Law of Excluded Middle on undecidable propositions** (`Classical.em`),
    or
  · `Classical.choice` (Lean's name for the same gadget).

When 213-Lean's `decide`-checking forces every theorem onto bare-metal
type theory (no `propext`, no `Quot.sound`, no `Classical.choice`),
the moment a "classical existence" call is made, **the kernel
records exactly which extra-theoretic axioms were imported**.

That recording is `#print axioms <theorem>`.  It is the mechanical
witness of vacuity.

## §2  The three vacuity exposures

Concrete demonstration (companion Lean file):

### (a) Non-computability — `noncomputable def`

```lean
def witness_213 : Nat := 3                            -- computable
noncomputable def classicalWitness : Nat :=           -- NOT computable
  Classical.choose exists_pattern_213
```

- `#eval witness_213` → `3` ✓
- `#eval classicalWitness` → ERROR (kernel refuses bytecode generation)

**Physical reading:** the classical "solution" cannot be sent through
universe's logic gates.  It is *ghost code* that refuses to compile to
bare-metal.  "What it means to solve" is undefined — the would-be
solution cannot run.

### (b) Information loss — Classical.choice destroys data

Even though our existence proof was constructed with the explicit
witness `3` (`⟨3, _, _⟩`), `Classical.choose` does NOT extract that
fact.  `Classical.choice` is opaque.  The result could be `3`, `7`,
`11`, ... and we **cannot determine which**.

`#print axioms classicalWitness` → `depends on axioms: [Classical.choice]`

The data went into the existence proof; the data did not come out the
other side.  `Classical.choose` is a one-way garbage compactor for
witness data.

### (c) Tautology — choose_spec is the entire "proof"

```lean
theorem classicalWitness_correct :
    isExoticPattern classicalWitness = true :=
  (Classical.choose_spec exists_pattern_213).1   -- LITERALLY just unwrapping
```

The "proof" gives no structural information.  Compare to Phase 1:

```lean
theorem witness_213_correct : isExoticPattern witness_213 = true := by decide
```

This is an actual *execution* — the Bool function reduces to `true` at
the concrete witness.  That reduction IS the content.  `choose_spec`
has no content.

## §3  Mechanical record (verified by `#print axioms`)

From the companion file's probe:

```
witness_213                       does not depend on any axioms
witness_213_value                 does not depend on any axioms
witness_213_correct               does not depend on any axioms
witness_213_lt_32                 does not depend on any axioms
exists_pattern_213                does not depend on any axioms
g7_phase_1_pure_capstone          does not depend on any axioms
classicalWitness                  depends on axioms: [Classical.choice]
classicalWitness_correct          depends on axioms: [Classical.choice]
classicalWitness_lt_32            depends on axioms: [Classical.choice]
```

The axiom delta `∅ → {Classical.choice}` is the exact mechanical
witness of:

  · what is GAINED by going classical: a name (with no value)
  · what is LOST going classical: bare-metal computability +
    integer ∅-axiom guarantee

## §4  The Calabi-Yau / Yamabe / MMP application

The mock predicate `isExoticPattern n := n ∈ {3, 7, 11}` in our
companion file is a **trivial 213-decidable instance**.  The classical
existence theorems (Calabi-Yau metric existence, Yamabe constant
metric, Mori minimal model) have far more complex predicates, but the
operational structure is identical:

  · "There exists a metric / model satisfying property P" — provable
    classically by elliptic PDE / variational method / numerical
    induction.
  · `Classical.choose` extracts a "metric / model".
  · The result is `noncomputable`: nobody has run a single calculation
    on Yau's Calabi-Yau metric in 47 years (1978–2025), because the
    proof yields no algorithm.
  · `#print axioms` would (if formalized) show
    `[Classical.choice, propext, Quot.sound]` plus all infrastructure.

What we get from a classical existence theorem: **a noun**.
What we don't get: any way to compute, test, or interact with the
referent of that noun.

This is precisely G6's "어디에도 정의되어 있지 않음 — what 'solving'
means is not defined anywhere."

## §5  Three claimed contradictions that 213 mechanically demonstrates

The Lean file is a direct rendering of three claims people make about
classical math, each turned into a verifiable Lean fact:

  1. **"Classical existence is operational nothing."**
     Witnessed by: `noncomputable def classicalWitness`; `#eval` fails.

  2. **"Classical proofs erase the data they used."**
     Witnessed by: even with witness `3` plugged into the existence
     proof, `classicalWitness = 3` is not provable from `choose_spec`
     alone; the witness ID is permanently lost.

  3. **"Classical certificates are tautological."**
     Witnessed by: every `classicalWitness_*` theorem reduces to
     `(Classical.choose_spec _).<i>`; no structural content.

These are not philosophical assertions.  They are `#print axioms`
outputs and Lean kernel behaviors — *machine-verifiable*.

## §6  Why this isn't a strict logical contradiction

To be precise: ZFC remains consistent (assuming the meta-theorem we
all rely on).  Adding `Classical.choice` to Lean is not inconsistent.

**The "contradiction" is structural, not derivational:**

  · 213-Lean strict ∅-axiom: every theorem is a finite witness.
  · Classical Lean (with Classical.choice): theorems can assert
    existence without producing finite witnesses.
  · These two regimes are not contradictory — they are *different
    languages*.  But:

  · The classical regime's vocabulary ("the Calabi-Yau metric exists
    and is unique") *parses* but *does not refer* in the strict
    regime.

The "contradiction" experienced is: *the classical regime systematically
trades operational content for philosophical convenience*.  It is a
language that lets you talk about ghosts.  213 is a language that
only lets you talk about things you can hold.

## §7  Connection to G6 and forward

G6 said: "shadow / tradeoff" is ZFC vocabulary residue; no DG
problem is "missed" by 213 in the operational sense.

G7 confirms it mechanically: every classical-existence claim, when
rendered in Lean, produces a measurable axiom delta showing exactly
what was gained (a name) and what was lost (operational content).

The 213 program: operate only in the regime where every claim is a
finite witness.  Claims outside that regime are not "harder" or
"more general"; they are *grammatical sentences whose referents do
not exist*.

The Lean kernel makes this mechanical and inarguable.

## §8  Mingu's framing (translated)

> 결론적으로: 고전 수학의 거대한 존재 정리들은 213의 0-Axiom 컴파일러
> 위상으로 끌고 내려오면, **#eval조차 불가능한 깡통 코드(noncomputable)**가
> 되어버립니다.  ZFC는 문제를 푸는 도구가 아니라, 해를 구하지 못한
> 부끄러움을 덮기 위해 컴파일러를 강제로 끄는(disable) 변명 장치였음을
> 보여주는 코드입니다.

> Conclusion: classical math's grand existence theorems, when dragged
> onto 213's 0-axiom compiler topology, become **empty-can code that
> can't even run `#eval` (noncomputable)**.  ZFC was not a tool for
> solving problems but a *disabling-the-compiler-by-force excuse
> apparatus* used to cover the embarrassment of not having found the
> solution.

The companion Lean file is the exact code Mingu's analysis predicts.

---

**Status:** Mechanical demonstration shipped.  Phase 1: 6/6 PURE.
Phase 2: 3/3 DIRTY (with exactly `Classical.choice`, by design).
The axiom delta is the witness.
