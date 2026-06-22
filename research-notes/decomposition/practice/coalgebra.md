# Decomposition: coalgebra / corecursion

*213-decomposition of "coalgebra / corecursion" — F-coalgebras, the final coalgebra, the
anamorphism (unfold), coinduction / bisimulation, streams / infinite data, the duality with
initial algebras / catamorphisms (fold), Lambek's lemma — per `../README.md` (model v7.1) and
`../SYNTHESIS.md` (the two invariants + the q=±1 spine + `Lens.view = Raw.fold` the catamorphism).
A field the thesis predicted would be **the calculus's `Raw.fold` catamorphism DUALIZED** (the ν to
the fold's µ). The grep found the repo did not leave this as prose: it **built the dual ∅-axiom** —
`Theory/Raw/{MuNuMirror, CoResidue, StateMachine}.lean` are the µF/νF mirror, the final coalgebra
`SlashNu`, the anamorphism `lAna`, and a positive (non-coinductive) bisimulation.*

The thesis under test: coalgebra is the calculus's **`Lens.view = Raw.fold` read in the dual
direction** — the unfold/anamorphism, the co-construction. The calculus's core arrow out of `Raw`
is the catamorphism `Raw.fold` (`raw_initial`/`dhom_unique_pointwise`): fold a construction *down*
to a readout, `Raw = µF`. The dual is the final coalgebra / anamorphism: unfold a seed *up* into a
(possibly infinite) self-pointing tree, the νF. Streams / infinite data = the modulus / approximant
sequence (the never-closing pointing, the residue's shape as a coinductive object). Bisimulation =
the co-version of equality = `Lens.refines`/`proj_val_eq_iff` read coinductively. Lambek's lemma =
the µ/ν structure-iso the repo names `MuNuMirror`. Coinduction = the greatest-fixed-point dual of
induction (`KnasterTarski.gfp`). No new primitive: the ν to the fold's µ.

## The decomposition (C / Reading / Residue)

- **Construction `C` — the distinguishing, with its co-operation made explicit (same `C`, two
  directions).** Nothing is added. The slash `x/y` is one distinguishing step; the catamorphism
  `Raw.fold` *folds it down* (`Raw.fold_slash : fold (x/y) = c (fold x) (fold y)`), `Raw = µF` (the
  least fixed point, finite, well-founded — `Lambek.no_infinite_descent`/`isPart_wf`). The **dual**
  is to *unfold a seed up*: an `F`-coalgebra is a seed type `X` with a transition
  `c : X → Bool × X × X` (root-shape + two child-seeds), and the **anamorphism** `ana c` walks the
  observation path, branching by the seed's children. `C` is unchanged; the co-direction reads the
  *same* slash as "what does this node unfold into", not "what does this node fold down to".

- **Reading `L` — read the distinguishing in the dual (co-) direction, to a co-tree of observations.**
  Where the catamorphism `L = Raw.fold` reads each node *inward* to a scalar/number, the
  **co-reading** `L = ana / lAna` reads each seed *outward* to a `CoShape := List Bool → Bool`
  (a path-function: `s p = true` ⟺ the node at observation path `p` is a branch). The co-reading is
  the unique arrow *into* the final coalgebra exactly as the catamorphism is the unique arrow *out
  of* the initial algebra — `ana_unique`/`lAna_unique` is the literal dual of `dhom_unique_pointwise`.
  - **anamorphism (unfold)** `ana c` / leaf-absorbing `lAna c` — exists for every coalgebra and
    commutes with the projections *by definition* (`ana_isBranch/coLeft/coRight` are `rfl`).
  - **finality** — `final_coalgebra` / `slashNu_final`: any co-hom equals `ana`/`lAna` (pointwise,
    by induction on the *finite* path — no coinduction primitive). `CoShape` (the M-type, presented
    as path-functions) is *a* final coalgebra of `F X = Bool × X × X`; the exact slash functor's νF
    is the consistent + anti-reflexive subtype `SlashNu`, which is *itself* final (`slashNu_final`).
  - **bisimulation** = the co-version of equality, but **positive**: `Distinct s t := ∃ q, s q ≠ t q`
    (one differing observation) and `TraceEq s t := ∀ q, s q = t q`, with
    `traceEq_iff_not_distinct : TraceEq s t ↔ ¬ Distinct s t`. This is `Lens.refines`/
    `proj_val_eq_iff` read coinductively (agree at every observation stage) — but inequality is a
    *single witness path*, so co-data equality never needs a coinductive bisimulation relation.

- **Residue, q-tagged — the escaping stream (q=−1), reached by no finite construction.** The
  co-reading's surplus is the **infinite self-pointing the finite `Raw` never reaches**: a named
  inhabitant of the νF carrier outside the µF image. `allBranch := fun _ => true` (branch
  everywhere, no leaf) is its own left subtree — genuine infinite `coOut`-descent — and
  `raw_ne_allBranch : ∀ r, toShapeRaw r ≠ allBranch`. The *exact*-slash inhabitant is the
  left-spine `spineL` (`a/(a/(a/…))` — the `rawTower` limit, anti-reflexive), with
  `spineL_escapes : ∀ t, spineL ≠ lToShape t`. **This is `cardinality.md`'s q=−1 escape diagonal in
  co-data clothing** — the stream that oscillates outside every finite reading, the same
  `object1_not_surjective` pole. The stream = the modulus / approximant sequence
  (`continued_fractions`/`nonstandard`'s `Nat→Raw`): a coinductive object whose finite signature is
  every finite truncation, the limit being reached by none (`MuNuMirror.ascent_unbounded`).

## Re-seeing

```
   a coalgebra / corecursion =  ⟨ C (distinguishing, read in the co-direction) | L = ana/lAna (the unfold) ⟩ ⊕ Residue(the escaping stream, q=−1)

   catamorphism (fold)        =  Raw.fold = Lens.view              (raw_initial/dhom_unique_pointwise — the unique arrow OUT of µF=Raw)
   anamorphism (unfold)       =  ana / lAna                         (the unique arrow INTO νF; ana_unique/lAna_unique — the literal DUAL)
   F-coalgebra (X, c:X→FX)    =  a seed + transition c:X→Bool×X×X   (CoResidue §5/§12 — coOut the canonical one on CoShape)
   the final coalgebra (νF)   =  CoShape (M-type) / SlashNu         (final_coalgebra; slashNu_final — finality by FINITE-path induction)
   Lambek's lemma (str.map iso) =  the µ/ν mirror, MuNuMirror       (ascent_total_descent_partial: µF descent WF, νF ascent unbounded)
   coinduction (gfp dual of induction) =  KnasterTarski.gfp         (gfp_fixed/gfp_greatest — the greatest fixed point)
   bisimulation               =  TraceEq = ¬ Distinct               (traceEq_iff_not_distinct — Lens.refines coinductively, POSITIVE)
   a stream / infinite data    =  the escaping co-tree = the modulus  (allBranch/spineL: reached by no finite Raw, raw_ne_allBranch/spineL_escapes)
   determinacy (behaviour fixed by transition) =  finality          (StateMachine.transition_determines_behaviour — finality read as FSM determinacy)
   the residue's escape, structurally  =  spineL escaping the minimised machine  (StateMachine.residue_escapes_minimal_machine)
   comultiplication Δ (the co-fold)  =  natSplits/splits           (hopf_algebras.md: CoAppend213.mem_splits_iff — the slash read CO-, on COUNT)
```

## Revelation

**Collapse + forcing + the q=±1 spine — and the central datum is that the dual is BUILT, not prose.**

**Collapse (the spine — the deepest in this note):** *coalgebra is `Lens.view = Raw.fold` read in the
dual direction, and the repo names the µ/ν mirror it is the ν-half of.* The calculus's one arrow out
of `Raw` is the catamorphism `Raw.fold` = `Lens.view` (`raw_initial`, `dhom_unique_pointwise`); the
final coalgebra is the unique arrow *into* `SlashNu`/`CoShape` (`ana_unique`/`lAna_unique`/
`final_coalgebra`/`slashNu_final`) — **the literal categorical dual, proved by the same finite-path
induction reversed.** `MuNuMirror` *names* the duality: `ascent_total_descent_partial` is one theorem
holding both poles — `Raw = µF` (descent well-founded, `no_infinite_descent`) and the νF escape
(ascent unbounded, an explicit total upward `IsPart`-stream `rawTower`). So the four "coalgebra"
notions collapse onto the calculus's existing catamorphism by direction-reversal:
fold↔unfold, induction↔coinduction (`KnasterTarski.lfp`↔`gfp`), least-fixed-point↔greatest-fixed-point,
µF↔νF — the **same `C` and the same self-pointing read at its two cofinal ends**.

**Forcing:** the anamorphism is *forced* as the only co-direction reading — `ana c` commutes with
`coOut` by `rfl`, and finality (`ana_unique`/`lAna_unique`) is forced by finite-path induction, the
*dual* of `dhom_unique_pointwise`'s "the only arrow out of `Raw`". Lambek's lemma — the structure map
of µF/νF is an iso — is *forced* by the mirror: `Raw` is the least fixed point (the slash decode
`Lambek.decompose` is the inverse of `slash`, `StateMachine.transition_deterministic` makes it
single-valued) and `SlashNu` is the greatest (`slashNu_final`); the two are the same self-pointing's
two fixed points. Bisimulation is *forced positive*: equality of co-data is the plain decidable
complement of one differing observation (`traceEq_iff_not_distinct`) — the feared coinductive
bisimulation is unnecessary, because anti-reflexivity / inequality is `∃`-shaped
(`slash_children_distinct`, a *constructed* witness path via `treeDiffPath`).

**The q=±1 spine:** the catamorphism residue and the coalgebra residue are one object at the two
poles. The **finite, well-founded** µF side is `q=+1`-converging (every descent reaches an atom,
`no_infinite_descent`; the finite machine is reachable + reduced, `mu_carrier_reachable_reduced_machine`).
The **escaping stream** side is `q=−1`: `allBranch`/`spineL` are reached by no finite `Raw`
(`raw_ne_allBranch`/`spineL_escapes`) — `cardinality.md`'s fixed-point-free diagonal made a co-tree,
the same `object1_not_surjective`/`OneDiagonal` escape. `StateMachine.residue_escapes_minimal_machine`
displays it: the minimised finite automaton is complete on finite behaviours, yet a genuine
non-degenerate behaviour (`spineL`) escapes it — `the_form_of_the_residue.md`'s **source-without-
enclosure** at the FSM scale. The stream IS the residue's coinductive shape (the never-closing modulus),
not a god above the finite.

## VALIDATE verdict — **EXTEND (the dual is BUILT ∅-axiom; the calculus is upgraded, not predicted-absent)**

No new primitive. Coalgebra is `Raw.fold`/`Lens.view` dualized — the ν to the fold's µ — and the
crucial datum (revising the predicted-not-built prior) is that the repo **built the dual ∅-axiom**:
the final coalgebra `SlashNu` (`slashNu_final`, with its own finality), the anamorphism `lAna`/`ana`
(`ana_unique`/`lAna_unique`, the dual of `dhom_unique_pointwise`), the µ/ν mirror `MuNuMirror`
(`ascent_total_descent_partial`), and a *positive* (non-coinductive) bisimulation `TraceEq = ¬Distinct`
(`traceEq_iff_not_distinct`). Re-seeing rows this note pins beyond `category_theory.md`'s
"`fold` = catamorphism" remark:
1. **the anamorphism / final coalgebra is BUILT** — `final_coalgebra`/`slashNu_final` is the exact
   dual of `raw_initial`/`dhom_unique_pointwise`, both ∅-axiom by finite-path induction. **EXTEND.**
2. **coinduction = `gfp`** — `KnasterTarski.gfp_fixed`/`gfp_greatest` is the greatest-fixed-point dual
   of the `lfp` induction in the same file. **EXTEND.**
3. **bisimulation is POSITIVE** — co-data equality `TraceEq` is the decidable complement of one
   differing observation `Distinct`; no coinductive bisimulation relation is needed
   (`traceEq_iff_not_distinct`, `treeDiffPath` constructs the separating path). **EXTEND.**
4. **the stream = the q=−1 escape residue** — `allBranch`/`spineL` reached by no finite `Raw` is
   `cardinality.md`'s diagonal as a co-tree, consolidated onto the `q=±1` spine. **EXTEND.**

This UPGRADES two SYNTHESIS claims that were recorded as honest open legs: README's
"a native final `F`-coalgebra (νF) is an open piece, blocked by Mathlib-free coinduction"
(`MuNuMirror`'s own docstring) is now **closed** by `CoResidue.slashNu_final` — the M-type
path-function presentation makes finality provable by finite-path induction, no coinduction primitive.
The clean EXTEND has one honest scope note (below), not a break.

## Verified Lean anchors (file:line:theorem — all grep-confirmed + `tools/scan_axioms.py`-scanned this session)

| Coalgebra datum | Theorem / def (file:line) | Purity (module tally) |
|---|---|---|
| catamorphism = the unique arrow OUT of µF=Raw | `Lens/Foundations/SemanticAtom.lean:412` `raw_initial` | **PURE** (in mixed module 11 PURE / 23 DIRTY; `raw_initial` itself PURE) ✓ |
| catamorphism uniqueness (the fold) | `Lens/Foundations/UniversalDistinguishing.lean:103` `dhom_unique_pointwise` | **PURE** ✓ |
| catamorphism recursion law | `Theory/Raw/Fold.lean:37` `Raw.fold_slash` | (Fold module) ✓ |
| µ/ν mirror: descent WF, ascent unbounded | `Theory/Raw/MuNuMirror.lean:105` `ascent_total_descent_partial`, `:50` `ascent_unbounded`, `:92` `tower_ascent_isPart` | **8 PURE / 0 DIRTY** ✓ |
| µF floor: descent terminates | `Theory/Raw/Lambek.lean:273` `no_infinite_descent`, `:199` `isPart_wf`, `:308` `terminal_iff_atom` | **PURE** ✓ |
| ★ anamorphism (unfold), exists + commutes | `Theory/Raw/CoResidue.lean:155` `ana` (def), `:216` `unfold_existence_and_escape` | **140 PURE / 0 DIRTY** ✓ |
| ★ anamorphism uniqueness (dual of dhom) | `Theory/Raw/CoResidue.lean:315` `ana_unique`, `:621` `lAna_unique` | PURE (in the 140) ✓ |
| ★★ final coalgebra (νF), up to pointwise eq | `Theory/Raw/CoResidue.lean:338` `final_coalgebra` | PURE (in the 140) ✓ |
| ★★ exact slash-νF carrier + finality | `Theory/Raw/CoResidue.lean:542` `SlashNu` (def), `:565` `slashNu_carrier`, `:726` `slashNu_final` | PURE (in the 140) ✓ |
| νF faithful embedding of µF | `Theory/Raw/CoResidue.lean:553` `rawToSlashNu_faithful`, `:254` `lToShape_faithful` | PURE (in the 140) ✓ |
| ★★ the escaping stream (q=−1 residue) | `Theory/Raw/CoResidue.lean:119` `raw_ne_allBranch`, `:128` `structural_escape`, `:462` `spineL_escapes` | PURE (in the 140) ✓ |
| both faces are unfolds | `Theory/Raw/CoResidue.lean:194` `toShape_eq_ana`, `:179` `allBranch_eq_ana` | PURE (in the 140) ✓ |
| bisimulation = positive trace eq | `Theory/Raw/StateMachine.lean:262` `traceEq_iff_not_distinct`, `:242` `TraceEq` (def), CoResidue`:368` `Distinct` | **21 PURE / 0 DIRTY** ✓ |
| finality read as FSM determinacy | `Theory/Raw/StateMachine.lean:76` `transition_determines_behaviour`, `:289` `behaviours_traceEq` | PURE (in the 21) ✓ |
| residue escapes the minimised machine | `Theory/Raw/StateMachine.lean:380` `residue_escapes_minimal_machine`, `:358` `mu_carrier_reachable_reduced_machine` | PURE (in the 21) ✓ |
| coinduction = greatest fixed point (gfp) | `Lib/Math/Order/KnasterTarski.lean:114` `gfp` (def), `:132` `gfp_fixed`, `:148` `gfp_greatest` | **19 PURE / 0 DIRTY** ✓ |
| comultiplication Δ = co-fold (the slash read CO-, on count) | `Meta/Nat/CoAppend213.lean:89` `mem_splits_iff`; `Meta/Nat/Convolution213.lean:49` `natSplits`, `:156` `conv_comm`, `:257` `conv_assoc` | **8 PURE / 0 DIRTY** (CoAppend); **49 PURE / 0 DIRTY** (Convolution) ✓ |

## Dropped / flagged (honest)

- **Named `Coalgebra` / `FCoalgebra` / `Bisimulation` / `HopfAlgebra` *structure* bundles — ABSENT
  (grep-confirmed).** `grep -E "structure (Coalgebra|FCoalgebra|Bisimulation|HopfAlgebra)|inductive
  (Coalgebra|Bisimulation)"` over `lean/E213/` finds nothing. The coalgebra apparatus is present as
  **path-function emulation**, not a bundled `F`-algebra/`Coalgebra` typeclass: the coalgebra is the
  bare transition `c : X → Bool × X × X` / `X → Option Bool × X × X`, νF is the subtype `SlashNu`,
  and finality is a theorem, not a universal-property record. So the *structure* is fully built and
  PURE; only the *named generic bundle* is absent (the same honest shape as `category_theory.md` —
  the engine is the most-built thing, the named object open).
- **Bisimulation is NOT a coinductive relation — flagged as the calculus's reading, not a re-skin of
  classical bisimulation.** `TraceEq`/`Distinct` are deliberately the *positive* (finite-witness)
  forms; the file states co-data equality "never needs a bisimulation here". Classical bisimulation
  (a coinductive relation with a bisimulation-up-to principle) is *not* built and is, by the
  construction's design, not needed for this functor — flagged so the "bisimulation" labelling is
  read as the decomposition (the co-version of `Lens.refines` made positive), not a claim that the
  coinductive bisimulation relation exists in Lean.
- **Honest scope of finality (from the source docstrings, not hidden).** `final_coalgebra` is
  finality *up to pointwise/extensional equality* of path-functions (the `h = ana c` form needs
  `funext`, deliberately avoided — the propext/funext 1-categorical ceiling, README break #4).
  `final_coalgebra` proper is for the full-binary-tree functor `F X = Bool × X × X` (the
  over-approximation); the *exact* slash-νF finality is `slashNu_final` among anti-reflexive
  coalgebras. The "stream = modulus" tie to `continued_fractions`/`nonstandard` is the *interpretive*
  gloss (the escaping co-tree as a never-closing approximant), grounded by the escape theorems, not by
  a built `Stream`/corecursive-sequence object — flagged.
- **`conv_assoc`/`conv_comm`/`mem_splits_iff` as "comultiplication / co-fold" is `hopf_algebras.md`'s
  reading** (the slash read CO- on the *count*, a Δ-comultiplication), cited here only as the
  count-shadow companion to the structural co-fold (`ana`/`lAna`): comultiplication is the co-fold on
  number-readouts, the anamorphism is the co-fold on the construction itself. Not re-derived here.

### Buildable witness (named)

The natural ∅-axiom closure of this note is a **`gfp`-presented bisimulation as νF-equality**: state
and prove that `TraceEq` (the positive trace-equality) is the **greatest fixed point** of the
co-step functor `Φ(R) s t := (coIsBranch s = coIsBranch t) ∧ R (coLeft s) (coLeft t) ∧ R (coRight s)
(coRight t)` via `KnasterTarski.gfp_greatest` — exhibiting *one* theorem that bisimulation
(`StateMachine.traceEq_iff_not_distinct`) and coinduction (`KnasterTarski.gfp`) are the same object,
the literal coinductive dual of the inductive `lfp` equality on `Raw`. The carriers
(`CoShape`/`SlashNu`) and both fixed-point engines (`gfp`, finite-path finality) are already PURE;
only the welding `TraceEq = gfp Φ` is unwritten — and it needs no coinduction primitive, since the
gfp is the order-dual lub already built.
