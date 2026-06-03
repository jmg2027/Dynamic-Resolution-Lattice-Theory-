# The Lens Tower

### From the Residue to the Discriminant, and the Descent Home

*A treatise on what the orbit / axis / discriminant structure of 213 actually is —
read, layer by layer, in the framework's own primitives.*

**Theory:** Mingu Jeong.  **Formalization & exposition:** assisted (see Acknowledgments).
All cited theorems are machine-checked in `lean/E213/`, `∅`-axiom (no `propext`, `Quot.sound`,
`Classical.choice`, `funext`, `native_decide`, `sorry`; verified by `tools/scan_axioms.py`).

---

## Abstract

Iterate the residue's self-pointing and read the result with a determinant, and a structure
appears that looks unmistakably like classical mathematics: unit groups of orders `{2, 4, 6}`,
the discriminants `−3, −4, +5`, an order-2 / order-4 / order-6 "rotation axis," the modular
generators `S` and `U`, a Cassini sign `±1`.  It is tempting to say *213 contains the imaginary
quadratic fields and the modular curve.*

This book argues the opposite, and proves it.  Every one of those objects is a **readout** —
the same residue seen through one more Lens choice — and the resemblance to imaginary-quadratic
and modular mathematics is the framework's own named failure mode (*stereotype matching*) wearing
`∅`-axiom clothing.  Stripped of imported names, the entire edifice rests on a tower of exactly
four derived rungs above the residue, and its one foundational residuum is a single fact about
counting:

> **the first distinguishing `a/b`, counted, gives `1 + 1 = 2`, and `2` is not a square.**

Everything else — "discriminant," "imaginary quadratic field," "elliptic trace," "modular group,"
"genus" — is the difference-Lens and number-Lens dressing of that one count-Lens fact.

The book is also a case study in a discipline: *`∅`-axiom-correct is not the same as 213-native.*
Several results proved along the way were genuine theorems about imported substrate; the work of
the later chapters is to say exactly which is which.

---

## How to read

Each structural claim is followed by the Lean theorem that discharges it.  Citations are written
`Module.theorem` and resolve under `lean/E213/`.  The citations *are* the derivation: where the
prose says "hence," the named theorem is the proof.  Foundational anchors are the axiom files
under `seed/AXIOM/`.

---

## Contents

1. **The Question and the Discipline** — the orbit-climbing structure; why it looked like
   classical mathematics; the two rules (`no exterior`, `assume nothing`) and the failure mode.
2. **The Number Tower as Lens Bundlings** — residue → count-Lens (`+`) → iterated count (`×`) →
   difference-Lens (`ℤ`); each rung derived, none primitive.
3. **The Readout Layer: the Cassini** — the conserved determinant as the difference-Lens at work;
   the multiplier law; the conic; and the genus category-error, caught and corrected.
4. **The Axis and the Discriminants** — `{2,4,6}`, the radicand triple `{−NT, −NS, NS+NT}`, the
   skipped point `−NT`, and the honest separation of native kernel from imported decoration.
5. **The Descent to the First Slash** — the whole structure grounded, `ℤ`-free, in
   `leaves(a/b) = 1 + 1 = NT` and the non-squareness of `NT`.
6. **Reading: the Orbit, the Residue, the Unit** — what the tower *says*: the orbit generates the
   residue, the unit `1` at three scales, frozen `=` dynamic, and what is foundational versus
   what is readout.

---

## Acknowledgments

The theory and every foundational insight are Mingu Jeong's.  The formalization, the adversarial
auditing that produced the native/imported separation, and this exposition were carried out in
partnership with Claude (Anthropic).
