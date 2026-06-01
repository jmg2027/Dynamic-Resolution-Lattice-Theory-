# Classical-correspondence surface (the propext / Quot.sound catalog)

Every `propext` / `Quot.sound` theorem in `lean/E213/` lives at one
boundary: where 213's distinguishing structure — which is **PURE** in
the `Raw → Bool` / pointwise-`↔` / decidable layer — is *read into* the
classical `Prop` / function-`=` world.  `propext` / `Quot.sound` (=
`funext`) is exactly the toll for that crossing
(`seed/AXIOM/06_lens_readings.md` §6.3: the strict reading is
`Raw → Bool`; stating something as `Raw → Prop` function-`=` is the
classical exit).

So the DIRTY catalog ≈ the framework's **classical-correspondence
surface**.  The PURE ∅-axiom core does **not** depend on category (A)
below — those theorems exist to say "this 213 object, read classically,
**is** the standard object (∧ / ∨ / ↔ / cup / instance)".

Current state (`tools/scan_all_axioms.py` for the live count): the 213-math core
is ∅-axiom; the non-sealed `propext`/`Quot.sound` that remain are the `Prop`-atom
thesis surface (category B) + the CayleyDickson open items (category D,
`Trig.conj_mul_anti` / `SedenionHeavy.flexible`).  The Lens ring is 0 real DIRTY.
Tag in source: `grep -rn "classical-correspondence surface" lean/`.

## (A) Correspondence / translation — "= the standard object"

DIRTY because they assert a 213 object **equals / matches** a classical
`Prop` or function object.  Each has a PURE 213-native twin (a `Bool`
lens or pointwise statement) carrying the actual content; the DIRTY form
is the outward bridge.  Removable from the ∅-axiom core without losing
213 content.

| Theorem(s) | Standard object asserted | PURE 213-native twin |
|---|---|---|
| `Lens.Properties.Morphism.BoolProp.boolToProp{,_true,_false,_and,_or,_xor,_iff}`, `universalMorphism_commute{,_xor,_or,_iff}` (10) | Bool→Prop morphism: `Bool.{and,or,xor}` ↔ `Prop.{And,Or,Iff}` | the `Bool` connectives themselves (PURE) |
| `Lens.SemanticAtom.canonical{Truth,Iff,And,Or}Map{,_a,_b,_slash}` (12) | the Prop semantic-atom maps | `aCountParityLens` / `iffBoolLens` etc. (`Lens Bool`, PURE) |
| `Lib.Math.Choice.CanonicalTruthChar.{canonicalTruthMap_iff_aCountOdd, canonicalTruthMap_ne_canonicalIffMap, canonicalTruthMap_ne_canonicalIffMap_witness, canonicalIffMap_iff_iffBoolLens, canonicalAndMap_iff_eq_a, canonicalOrMap_iff_ne_b}` (6) | "the Prop map = (a-count parity / iff-fold) of Raw" | the witness / Bool-lens `view` equalities (PURE) |
| `Lib.Math.Cohomology.Surfaces.T2Minimal.CupPairing.cup_symm` (1) | cup graded-commutativity `α ⌣ β = β ⌣ α` (standard cohomology), stated as cochain function-`=` (`funext`) | `cup α β s = cup β α s` pointwise (PURE; Int part already `Int213.{mul,add}_comm`) |
| `Lib.Math.Hyper.Hyper213Tower.lensTowerHasDistinguishing` (1) | the tower carries the standard `HasDistinguishing` instance | the recursive `lensHasDistinguishing` data (PURE structure) |

## (B) Thesis adoption — `propext` IS the claim

Not a bridge to a standard object: the 213 commitment that **`Prop`
itself** occupies the distinguishing slot (`propXor` = the Prop-parallel
of `Raw.slash`).  Removing the seal removes the thesis.

`Lens.SemanticAtom.{propAsDistinguishing, propAsDistinguishingAnd,
propAsDistinguishingOr, propAsDistinguishingIff, propXor_comm,
iff_comm_eq, exists_non_lens_expressible}` (7).

## (C) Lens `equiv` / `refines` `=`-surface — `equivR`-rebuilt (RETIRED)

Internal, load-bearing (not correspondence): the refinement lattice.  The
codomain-polymorphic Reading-equivalence API (`ReadingEq` / `equivG` /
`refinesG` in `Lens/ReadingEquiv.lean`, reducing to `equivR` at `Raw → Prop`
and `equiv` at the default instance) now carries the **whole universalLens
refinement surface ∅-axiom**, with the hub `universalLens_kernel_eq_E_R` + the
closure companions `universalLens_{recovers_R, idempotent_R}` PURE.  The
`=`-of-view forms are gone; the lone `=`-cost is the isolated bridge
`equivR_to_equiv`.  See `theory/lens/dirty_recovery_patterns.md` Pattern P5,
`STRICT_ZERO_AXIOM.md`.

PURE now: `Universal.QuotLens`, `Instances.Cauchy`, `Lattice.{Join,
IndexedJoin, FamilyMeet, FamilyJoin}`, `Algebra.Corresp`,
`Properties.CanonicalForm`, `Lib.Math.Choice.Resolved`,
`Instances.Leaves.DepthJoin` (the leaves⊔depth tier classification — the
`omega`/`simp` arithmetic was replaced by explicit PURE Nat reasoning +
`if_pos`/`if_neg`).

PURE now (the Lens-of-Lens funext surface — retired by the equivalence-unification
arc, `research-notes/RFC_reading_equivalence_primitive.md`): `Compose.{OnLens,
OnLensImage, OnLensImageGeneric, OnLensImageLevel2}`, `Properties.TowerLevel3`,
`Lib.Math.Cauchy.GenericFamily`.  `HasDistinguishing` is now stated over its
reading-sameness `same` (`= ` realization at concrete codomains, `eqPW`/`sameLens`
at `Lens β`); the recursive Lens tower uses `universalMorphism_unique` +
`sameLens`-transitivity.

Remaining `propext` here is **category (B)**, not (C): `propAsDistinguishing*` /
`canonical*Map` / `BoolProp.universalMorphism_commute_*` — `propext` IS the
"Prop is an atom of meaning" thesis, kept by design.

## (D) Genuine results via classical representation — purifiable backlog

Real theorems whose DIRTY is inherited from `propext`-carrying Nat/Int
core lemmas or structure-`ext`, not from correspondence.  Purifiable by
the swap playbook (cf. `KerSizeUniversal`, 2026-06-01: `Nat.{mul_assoc,
mul_div_cancel_left, add_mul_div_left, add_mul_mod_self_left,
add_sub_cancel'}` → PURE infra; `CayleyHeavy`, 2026-06-01: `omega` /
`Int.mul_eq_zero` → `Int213.{add_nonneg, add_eq_zero_of_nonneg,
mul_eq_zero}`).

PURE now: `Levels.CayleyHeavy` (`normSq_eq_zero_iff`, `no_zero_div`),
`Tower.CDTower` (`CD_tower_full` — cascaded from `CayleyHeavy.no_zero_div`).

Still DIRTY — **not** a playbook swap (genuine theorem development):
  · `Levels.TrigintaduoionionHeavy.conj_mul_anti` (`hurwitz_ring`, 128
    Int-var): needs `NonAssocStarRing213 Sedenion` (the
    Sedenion→`CDDouble Cayley` algebra bridge, replicating
    `CayleyAlgebra213`) so the proof can go structural like
    `SedenionHeavy.conj_mul_anti`.
  · `Levels.SedenionHeavy.flexible` (`hurwitz_ring`, 32 Int-var): the
    **CDDoubleFlexible cross-pair open item** — Sedenion's base (Cayley)
    is non-associative, so `cd_flexible` (which needs base alternativity
    via `cd_alt_left`) does not apply; flexibility of the double of a
    merely-flexible base needs the cross-pair lemma (`CDDoubleFlexible`,
    long-standing CD open).

## (E) Intentional axiom exhibits / plumbing / tests

By construction, not backlog:
  · `Lens.AxiomLenses.Bridges.{Funext, QuotSound}` (2) — deliberately
    exhibit `funext` / `Quot.sound`.
  · `Meta.Tactic.NativeGuard` (2) — guard test module.
  · `Tactic.{elabQuadExtension, elabDeriveConjugation,
    elabVerifyConjugation}` (3) — `Classical.choice` via the
    `Lean.Elab.Command` monad (metaprogramming plumbing, not math).

## Reading

The split is the point: (A) is a removable outward surface, (B) is a
single thesis commitment, (C) is recoverable internal machinery, (D) is
ordinary purity backlog, (E) is intentional.  None of (A)–(E) is a
`Classical.choice` / `native_decide` in 213-mathematical content — the
falsifiability-forbidden axioms remain absent
(`seed/AXIOM/08_falsifiability.md` §8.2).
