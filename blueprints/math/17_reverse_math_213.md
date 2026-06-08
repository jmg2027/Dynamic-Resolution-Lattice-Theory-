# 17 — Reverse Mathematics 213 (the omniscience / axiom-cost ledger)

**Marathon field 17.  Track: math.  Phase G.**  Status: STARTED (Phase GA below).

## Why this field

The repo already proves *which theorems are ∅-axiom* (`STRICT_ZERO_AXIOM.md`) and *where
the residue stalls* (König's `InfChildExists`).  That is reverse mathematics in disguise:
calibrating each theorem by the non-constructive decision it costs.  Standard reverse math
calibrates over `RCA₀`; 213 calibrates over the **residue's own carriers** (`Nat → Bool`
decision streams, the binary/p-ary digit trees, the self-cover `Object1`), ∅-axiom.
Making the ledger explicit is the **legibility bridge to recognized mathematical logic** —
the field that lives on exactly this kind of calibration (Simpson SOSOA; the omniscience
hierarchy LPO/LLPO/WLPO/MP; WKL ⟺ Heine–Borel).

## 213-native emergence

The residue's decision carrier is `Nat → Bool` (a test, a predicate, the `Object1`
codomain rows).  An **omniscience principle** is a claim to *decide* something infinitary
about such a stream — exactly the "freeze a transition into a verdict" move
(`the_one_diagonal.md`).  213 refuses these as theorems; it states them as Props and
calibrates everything else against them.  The diagonal family (Cantor, `object1_not_surjective`)
is the **free interior** (no omniscience needed); König/compactness sit at the LLPO rung;
the ledger records the rest.

## Building blocks already in place

- **Free interior (no omniscience):** `Lens/FlatOntologyClosure.object1_not_surjective`,
  `Lens/Cardinality/Cantor.cantor_general` — the diagonal/non-surjection family, all PURE.
- **The first calibration:** `Lib/Math/Combinatorics/KonigConditional.lean` —
  `InfChildExists` (the selection stall) ↔ `FiniteSubcoverOracle` (compactness) modulo the
  child-disjunction decision (`infChildExists_iff_finiteSubcover`); `WKL ⟺ Heine–Borel`
  local form on the residue carrier.
- **Escapes (reached-by-none):** `Padic/NuEscape` (2-adic νF escape; general-`p`
  `zpSeq_not_enumerable`), `reached_by_none.md`.
- **Essays:** `theory/essays/foundations/the_one_diagonal.md` (the one obstruction /
  Lawvere), `the_reference_claim.md`; `theory/essays/methodology/why_the_reframing_recurs.md`.
- **Topology 213** already has `Heine-Borel = rfl` (`Math/Topology/`) — the dyadic-cover
  side to connect.

## Phase plan

- **Phase GA — Omniscience principles + implications.**  DONE.  `LPO/WLPO/MP/LLPO`
  (`Omniscience.lean`) + `lpo_imp_wlpo`, `lpo_imp_mp`, `lpo_iff_wlpo_and_mp` (LPO ⟺ WLPO ∧
  MP); `lpo_imp_llpo` (LPO ⟹ LLPO, via native `parity`, `LLPO.lean`); `lpo_decides_sigma01`.
- **Phase GB — König / compactness ↔ omniscience.**  *Predicate-decision half DONE*
  (`Lib/Math/Logic/Pi01Decision.lean`): `lpo_decides_pi01` (LPO decides every `Π⁰₁`) +
  `existsLevel` + `lpo_decides_infiniteBelow` — *deciding* infinite-below costs **LPO**.
  *GB-cont DONE* (`Lib/Math/Logic/ChildSelection.lean`): `lpo_infChildExistsN` — LPO +
  tree-monotonicity (`LevelAntitone`) ⟹ child selection; `levelAntitone_of_downwardClosed`
  (+`existsLevel_pred`) discharges monotonicity from a downward-closed tree, giving
  `lpo_infChildExists_downwardClosed` (selection for an actual Bool tree).  *GB-cont3 DONE*
  (`KonigBridge.lean`): `infB_iff_infBelow` — native `InfB` = the ∃-form
  `KonigConditional.InfBelow`, so the calibration speaks König's own predicate.
- **Phase GC — the free interior as the base.**  Catalogue the diagonal/non-surjection
  family (`object1_not_surjective`, Cantor) as the no-omniscience base (the `RCA₀`-analogue),
  and the reached-by-none escapes as its companions.
- **Phase GD — the ledger capstone.**  A table (theorem → omniscience cost) over the
  residue carriers; reconcile with `STRICT_ZERO_AXIOM.md` (the axiom-cost ledger made
  explicit and principled).

## Connections to other tracks

- **Topology 213** (Heine–Borel, dyadic covers) — Phase GB's compactness side.
- **Logic / Proof Theory 213** (field 14, intuitionistic predicate calculus) — the
  proof-side companion; omniscience principles are the semantic-decision side.
- **`the_one_diagonal` / `why_the_reframing_recurs`** — the Lawvere universality the ledger
  instantiates.

## Unsolved problems

- **Tighten the König-selection cost LPO → LLPO** (headline): a fresh selection-from-LLPO
  proof via the monotone turn-off encoding (NOT via `lpo_imp_llpo`, wrong direction); sketch
  in `books/math/reverse-math-213.md` Open section.
- Global `WKL ⟺ Heine–Borel` (the local step is done; the global finite-subcover argument
  over the residue's compactness carrier is open).
- The fan theorem and bar induction as residue-native principles.
- A one-carrier (p-ary spine in `CoResidue`) unification of the escapes.

*Resolved this campaign:* the external Lawvere placement (diagonal family = Lawvere;
omniscience family = a separate Brouwerian hierarchy, not a Lawvere instance) and the
two-ledger reconciliation with `STRICT_ZERO_AXIOM.md` (object-level omniscience cost =
hypothesis form of meta-level kernel-axiom cost) — both written up in the book.
