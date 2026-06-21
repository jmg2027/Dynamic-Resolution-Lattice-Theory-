# COUNT-duality — the union bound and LYM are one incidence double-count

**Reproduced result.** Two named bounds from two different chapters of combinatorics,
each long-closed and ∅-axiom in the corpus:

  - the **union bound** of Erdős' probabilistic method —
    `BoolEnum.bcount (anyBad preds) L ≤ totalCount preds L`
    (`CountExistence.union_bound`), the heart of `R(k,k) > 2^{k/2}`;
  - the **LYM inequality** of Sperner theory —
    `Σ_{A∈F} #{chains through A} ≤ #chains` (`Sperner.lym_double_count`), the heart
    of the antichain bound `C(n,⌊n/2⌋)`.

The new content is not either bound — it is the **proof that they are one move**:
both descend from a single Bool incidence-matrix double-count
(`CountDuality.incidence_balance` = `Sperner.sumOver_swap`), differing only in
which marginal is bounded. `CountDuality.count_duality` is the one proof object
carrying both. All seven declarations `#print axioms`-empty
(`lean/E213/Lib/Math/Combinatorics/CountDuality.lean`).

## Why we picked it — narrated unity is not proven unity

`seed/PROOF_ISA.md`, the `Sperner.lean` §7 docstring, and `lym_inequality.md` all
say the same sentence: the union bound and LYM are *"one move — Fubini on a 0/1
incidence matrix, read once by rows and once by columns."* But the **proofs** do
not share that move. The union bound is discharged by per-element subadditivity
(`CountExistence.bcount_or_le`, `cond_or_le`), while LYM is discharged by the
double-count swap (`Sperner.sumOver_swap`). Two structurally different proofs with a
prose claim of identity stretched across them.

A claim that two domains are "the same" is, in 213, a claim about a shared kernel
(`Lens.refines`, `lensIso_iff_kernel_eq`), and it is licensed *only when the shared
structure is exhibited as a theorem* — never by a value-coincidence and never by a
sentence. A vacuous `... : True` headline carries no map and so is not a
unification; only a proven map is
(`research-notes/frontiers/rebuild_roadmaps/cross_domain_unification_rebuild.md`).
The narrated union-bound/LYM unity sits in exactly that unproven status until a
shared engine is exhibited. This essay exhibits it.

## Derivation — one engine, two marginals

The engine is the finite Fubini swap on a `Bool` incidence matrix `g : α → γ → Bool`
(rows `α`, columns `γ`), summed as `Σ⟦g A c⟧`:

> `incidence_balance` : `Σ_A Σ_c ⟦g A c⟧ = Σ_c Σ_A ⟦g A c⟧`  (`= Sperner.sumOver_swap`).

The two count primitives the two chapters used — `BoolEnum.bcount` (Erdős side) and
`Sperner.lcount` (Sperner side) — are the *same* 0/1 count, each equal to
`Sperner.sumOver` of the indicator (`CountDuality.bcount_eq_sumOver`,
`Sperner.lcount_eq_sumOver`). That identification is what lets one swap serve both.

**Row read → union bound** (`union_bound_via_balance`). Take rows = bad events
`preds`, columns = colourings `L`, `g p l = p l`. The only ingredient beyond the
bare balance is the per-row `||`-collapse — the indicator of a disjunction is at
most the row-sum of the individual indicators (`ind_anyBad_le`):

  `bcount (anyBad preds) L = Σ_l ⟦anyBad preds l⟧ ≤ Σ_l Σ_p ⟦p l⟧`
   `= Σ_p Σ_l ⟦p l⟧ = Σ_p bcount p L = totalCount preds L`,

the middle equality being `incidence_balance`. This re-derives the union bound
*through* the swap, where the subadditivity proof never touches it.

**Column read → LYM** (`lym_via_balance`). Take rows = antichain `F`, columns =
chains, `g A c = inc A c`. Here the bounded marginal is the *column*: each chain
meets the antichain at most once (`hcap`: `Σ_A ⟦inc A c⟧ ≤ 1`), so

  `Σ_A #{chains through A} = Σ_A Σ_c ⟦inc A c⟧ = Σ_c Σ_A ⟦inc A c⟧ ≤ Σ_c 1 = #chains`,

again with `incidence_balance` the middle step. Same engine; the cap replaces the
collapse.

So the two bounds are not analogous — they are **literally the two marginals of one
`sumOver_swap`**. The union bound bounds the *row* indicator (an OR) and reads off
the column total; LYM bounds the *column* total (≤ 1) and reads off the row sum.

## Dual function — what the unification buys

Reading classically, this is the standard observation that the probabilistic
first-moment/union bound and the LYM double-count are both first-moment arguments on
an incidence relation. Reading 213-native, it is a small but genuine instance of the
operational content of *no exterior* (`seed/AXIOM/05_no_exterior.md` §5.1): two
combinatorial domains built independently — Erdős/Ramsey over `allBoolLists`, Sperner
over `perms` — are one residue read under two Lenses, and the unity is a
**checkable theorem**, not a resemblance. It is also the point where the `COUNT`
instruction's advertised "two faces" (`seed/PROOF_ISA.md`, the `GAP`-sub-mode note)
becomes *proven* to be two faces rather than asserted to be.

Honest scope (`§8` falsifiability discipline). This does **not** make the Proof-ISA
an engine that solves hard problems — it solves nothing new; both bounds are already
closed. What it does is convert one narrated cross-domain identity into a proof,
closing the gap between the repo's prose and its proof-state. That is the modest,
correct unit of progress for the breadth/primacy claim: a unification earns the word
only when it carries a map.

## Cross-frame connections

  - **Sperner/LYM** (`lym_inequality.md`, `sperner_double_counting.md`): the column
    read in full; this essay shows its engine is shared.
  - **Probabilistic method** (`probabilistic_method.md`): the row read; the deficit
    `Σ|badᵢ| < |codomain|` that forces a good colouring is the same column-total
    bound seen here.
  - **Chain/antichain duality** (`chain_antichain_duality.md`): a *different*
    duality — Mirsky/Dilworth swap comparability for partitions; COUNT-duality swaps
    *which marginal of one matrix* is bounded. Two distinct dualities on the same
    Boolean lattice.
  - **LensIso / unified equivalence** (`theory/lens/unified_equivalence.md`): the
    template for "two structures are one" as kernel coincidence; COUNT-duality is the
    shared-engine instance at the level of a counting identity rather than a Lens.

## Constructive accessibility

Point at it. The shared engine: `CountDuality.incidence_balance`. The two faces:
`union_bound_via_balance` (Erdős) and `lym_via_balance` (Sperner). The capstone
pairing both: `count_duality`. The count-primitive bridges:
`bcount_eq_sumOver`, `totalCount_eq_sumOver`, and the `||`-collapse `ind_anyBad_le`.
All ∅-axiom (`#print axioms` empty), 7 PURE / 0 DIRTY by `tools/scan_axioms.py`.
