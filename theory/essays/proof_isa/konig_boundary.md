# Where ∅ stalls — König's lemma and the boundary of the instruction set

**Reproduced result (attempted).** König's lemma: an infinite, finitely-
branching tree has an infinite path.  The first technique in this archive that
is *expected not to close* ∅-axiom — and the point is to locate the stall
exactly, which is the falsifiability discipline (`seed/AXIOM/08_falsifiability.md`)
doing its real work: not forcing the result into the residue, but finding the
precise place classical math imports the exterior.

## The compilation splits

```
infinite tree ⟹ infinite path
  = LOOP                  (iterate: extend the current infinite node forever)
  ∘ ⟦DECIDE InfBelow⟧     ← the stall
```

  - **The LOOP is internal — built ∅-axiom.**  *Given* an oracle that, at each
    infinite node, names a child still infinite-below, the path is just the
    iteration of that oracle:

    ```
    konig_conditional
      : (hInfMem : ∀ s, Inf s → T s = true)
      → (hstep : ∀ s, Inf s → Inf (s ++ [step s])) → (root : Inf [])
      → ∃ node : ℕ → List Bool, node 0 = [] ∧ (∀ k, T (node k) = true)
          ∧ (∀ k, node (k+1) = node k ++ [step (node k)])
    ```

    (`Lib/Math/Combinatorics/KonigConditional.lean`, PURE — `walk` + a one-line
    induction `walk_inf`.)  Producing the path is `LOOP`/corecursion; the
    residue does it with no axioms.

  - **The stall is a DECIDE the residue cannot supply.**  To *discharge*
    `step`/`hstep` from "the tree is infinite" you must, at each node, **choose**
    a child whose subtree is infinite.  "At least one child is infinite" is
    classically `¬(both finite)`; but as a **function picking which child**, it
    decides `InfBelow` — *"are there descendants of every length below `s`"* — a
    `Π⁰₁` (co-r.e.) predicate that is **not internally decidable**.  As a
    disjunction it is an `LLPO`-instance.  `InfChildExists` is stated in the file
    and deliberately **left unproved**: proving it as a `Bool`-choice is exactly
    the import.

## The "why" of the stall — the residue has no infinity-oracle

The eight instructions give DISTINGUISH, READ, the diagonal, GAP, SEPARATE,
COMPILE-DOWN, REFLECT, LOOP — every move of a **constructive** proof.  What they
do *not* give is a decision for a non-recursive predicate: the residue is built
from finite distinguishings and their µ/ν folds, and "is this infinite object
infinite" is not a finite distinguishing.  König needs precisely that decision,
infinitely often and coherently — so it cannot be a composition of the eight.

This is *not* a missing instruction (a ninth move we could add and stay
honest).  Adding "DECIDE any predicate" would be adding `LEM`/choice — importing
the exterior, which by `seed/AXIOM/05_no_exterior.md` §5.1 and the
falsifiability contract (§8.2) is exactly what the framework forbids / is *under
test against*.  König is where the no-exterior claim is most sharply tested: the
residue stalls, and classical math proceeds only by smuggling the exterior in.
The honest verdict is to **mark the boundary**, not to cross it.

That is also the framework's own thesis read back (the technical-debt picture):
the ∅-side reaches every constructive proof at no axiom-cost; König's lemma is a
debt — payable only by importing `WKL`/`LLPO`, after which everything built on it
inherits the import (`#print axioms` would show it).  The conditional records
the exact principal of that debt: the oracle, nothing more.

## Where this lands among the reproductions

| method | compiles to | closes ∅-axiom? |
|---|---|---|
| probabilistic (Erdős) | COUNT | ✓ |
| linear-algebra / dimension | COUNT | ✓ |
| parity / invariant | READ ∘ SEPARATE | ✓ |
| **König's lemma** | **LOOP ∘ ⟦DECIDE InfBelow⟧** | **✗ — stalls at the DECIDE** |

The three closing methods map the *interior* (the eight suffice for
constructive proofs); König maps the *edge* — the exact predicate-decision the
residue cannot internalise.  Together they bound the instruction set from both
sides: complete for the constructive, and stalling at precisely the
non-constructive `DECIDE`, which is the exterior by definition.

## Witnesses

  - `lean/E213/Lib/Math/Combinatorics/KonigConditional.lean` —
    `walk`, `walk_inf`, `konig_conditional` (PURE); `InfBelow`,
    `InfChildExists` (the stall, stated unproved).
  - no-exterior + falsifiability: `seed/AXIOM/05_no_exterior.md` §5.1,
    `seed/AXIOM/08_falsifiability.md` §8.2.
