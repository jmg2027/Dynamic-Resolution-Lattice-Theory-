# The omniscience ledger — a theorem's reverse-math cost, in 213

A theorem's cost is the omniscience principle it carries **as an explicit hypothesis** —
none, `LPO`, `LLPO`, a selection oracle (dependent choice), or the fan theorem — and that
hypothesis is exactly what keeps the theorem ∅-axiom.  The cost lives on the *hypothesis
line*, not the axiom line.

## 213-native answer

The residue's decision carrier is `Nat → Bool` (a test, a predicate, a row of the
self-cover `Object1`).  An **omniscience principle** is a `Prop` claiming to decide
something infinitary about such a stream — `LPO`, `WLPO`, `MP`, `LLPO`
(`Lib/Math/Logic/Omniscience.lean`).  213 never *proves* these; it states them and
calibrates each theorem by which one it consumes.  `Lib/Math/Logic/Capstone.lean`'s
`reverse_math_ledger` bundles the spine into one ∅-axiom witness: a free interior, the
`LPO`-decisions, the `LLPO`-selection.

## Derivation

The grades, each `#print axioms`-empty:

- **none** — the diagonal / non-surjection family: `DiagonalBase.cantor_stream_not_enumerable`
  (the `Nat → Bool` carrier is not enumerable), the residue's own `object1_not_surjective`.
- **LPO** — `Pi01Decision.lpo_decides_pi01` / `lpo_decides_sigma01` (deciding `Π⁰₁` / `Σ⁰₁`);
  instance `lpo_decides_infiniteBelow` (König's "infinite-below", via the native `existsLevel`).
- **LLPO** — `LLPO.lpo_imp_llpo` and `LLPOSelection.llpo_infChildExistsN`: König child
  selection, tightened from `LPO` to the weaker `LLPO` (the monotone turn-off encoding).
- **selection oracle / dependent choice** — `WKLHeineBorel.wkl_of_oracle`: WKL proper
  (unbounded ⟹ an infinite path) given the per-node `step` oracle.
- **fan theorem** — `WKLHeineBorel.FanTheorem`: HB proper, the Brouwerian dual, named.

Each closes ∅-axiom because the cost is a *parameter*, not a kernel import.

## Dual function

This is classical **reverse mathematics** with its packaging stripped: where the standard
program calibrates a theorem by the set-existence axiom it needs over a base system `RCA₀`,
213 calibrates by the omniscience principle it consumes over the residue's own carriers (the
binary tree, the decision stream).  The refinement is the **two-ledger identity**: the
meta-level ledger `STRICT_ZERO_AXIOM.md` records which *kernel* axioms (`propext`,
`Quot.sound`, `Classical.choice`) a theorem pulls; the omniscience ledger is its
*object-level* twin.  Carrying an omniscience principle as a hypothesis is precisely what
keeps a theorem ∅ at the meta level — trying instead to *prove* the decision inside Lean
(`Classical` / `decide` / `omega`) is what pulls the kernel axiom.  One cost, written on the
hypothesis line here and the axiom line there.

## Cross-frame connections

The obstruction every grade pays for is **one**: the freeze-decision — capture an unending
transition as a finished verdict — i.e. `object1_not_surjective` (`the_one_diagonal.md`).
The proof-ISA's König stall (`theory/essays/proof_isa/konig_boundary.md`) is that same
boundary read on the instruction set; the local compactness identity
`KonigConditional.infChildExists_iff_finiteSubcover` and the global
`WKLHeineBorel.wkl_heineBorel_calibration` pin `LPO` / `LLPO` / choice / fan on one carrier
at once.  One obstruction, graded none → `LPO` → `LLPO` → choice / fan — every grade a
hypothesis you can point at.

## Open frontier

The two genuinely external grades — the bare dependent choice that assembles per-node
selections into a *global* path (WKL beyond `LLPO`) and the fan theorem (HB proper) — are
*named and isolated* (`wkl_of_oracle`, `FanTheorem`), by design not internal.  That
isolation **is** the calibration: there is nothing to internalize, only to hypothesize.
Extending the ledger past binary trees (a `p`-ary spine; the general `WKL ⟺ Heine–Borel`
global direction) is open.

## Self-check note

The "two ledgers" is not a substrate / superstructure split — both are one cost read at two
scales (`seed/AXIOM/05_no_exterior.md` §5.1).  Naming the omniscience family does not
promote it above the residue: each principle is a `Prop` on the `Raw`-derived carrier
`Nat → Bool`, a Lens reading, not a layer over Raw.
