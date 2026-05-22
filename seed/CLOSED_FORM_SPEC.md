# CLOSED_FORM_SPEC — closed-form spec for 213 (Tier 5)

The substantial mathematics of 213 can be expressed without external
axioms (`propext`, `funext`, `Quot.sound`, `Classical`, Mathlib).
The mechanism is **vertical-internal projection** + **pointwise eq**:
points where a naïve formulation would call `funext` / `propext` /
`Quot.sound` are recast as projections to canonical-form-image
relations stated pointwise.

See also:
  - `research-notes/archive/universe_chain/G84_closed_form_pattern_unification.md`
    (探索 note)
  - `lean/E213/Lens/Number/Nat213/*` and
    `lean/E213/Lens/Bool213/*` (Lean implementation, post-Option-C
    layout)
  - `lean/E213/Lib/Math/Real213/ChainToCut.lean` (bridge)

## 3-domain meta-pattern (post-Option-C, 2026-05-18)

Each domain carries a projection of the same shape:

  - **closure**: projection `r`'s image is in canonical form.
  - **idempotence**: `projection² = projection` (or pointwise).
  - **boundary commutativity**: vertical-external projection is
    compatible.
  - **fixed-point ↔ image**: `projection r = r ↔ predicate r`.

| domain | object | projection | base / combine | image predicate |
|---|---|---|---|---|
| Bool213 | Raw | `booleanProj` | T, and | `IsBool213` |
| RawCut | Raw²→Raw | `cutBooleanProj` | pointwise | `IsBoolValued` |
| CauchyCutSeq | struct | `cauchyProj` | `constCauchyCutSeq ∘ limit` | `IsConstAtLimit` |

Lean locations:
  - `lean/E213/Lens/Bool213/Raw.lean`
  - `lean/E213/Lens/Number/Nat213/RawCut.lean`
  - `lean/E213/Lib/Math/Analysis/CauchyProj.lean`

**Note on the former Nat213 row** (`leavesCountRaw` / `IsChain`):
The Option C refactor (commit `9efd8263`, 2026-05-18) removed the
Raw-side projection `leavesCountRaw` together with all Raw-side
arithmetic on `Nat213`.  ℕ₊ is now the *image* of
`Lens.leaves.view : Raw → Nat`, a *projection to Nat*, not a
Raw-internal projection.  Conceptually this is the same
`projection r ∈ image` shape, but the codomain has moved from Raw
to Nat — the Raw side carries only the chart representative
(`Raw.numeral`).  See
`research-notes/2026-05-18_lens_emergence_path.md` for the full
reasoning.

## ChainToCut bridge — ℕ₊ chain ↔ Real213 cut

The Method A Raw chain embeds into Real213's cut universe.  Core
cut operations commute through the bridge.  Post-Option-C the
homomorphism is expressed at the **value level** via Peano
arithmetic (the previous Raw-level `Raw.add` / `Raw.mul` are
deleted).

| Real213 operation | Bridge theorem |
|---|---|
| `cutSum` (add) | `cutSum_chainToCut` |
| `cutMul` (mul) | `cutMul_chainToCut` |
| `cutLe` (≤) | `cutLe_chainToCut_iff` |
| `cutMax` (LUB) | `cutLe_cutMax_chainToCut_iff` |
| `cutMin` (GLB) | `cutLe_cutMin_chainToCut_iff` |

Lean: `lean/E213/Lib/Math/Real213/Cauchy/ChainToCut.lean`.

## Bridge composition

ChainToCut + CauchyProj compose naturally:
`chainCauchyCutSeq r := constCauchyCutSeq (chainToCut r)`.

Lean: `lean/E213/Lib/Math/Analysis/ChainCauchy.lean`.

## Propext-avoidance trick set

Patterns to keep theorems PURE (reusable).  When a future session
hits a propext leak, apply these in order:

  1. **`rw [Iff_lemma]`** → `Iff.trans (lemma) ?_`.  Iff rewrite
     carries propext.
  2. **`rw [Iff_lemma] at hyp`** → `(Iff_lemma _ _).mp hyp`
     directly.
  3. **`rw [Eq_lemma] at hyp`** → `Eq_lemma ▸ hyp` (term-mode).
  4. **`▸` motive ambiguity** → split with `calc`.
  5. **`Bool.and_eq_true` / `Bool.or_eq_true`** Iff avoidance —
     direct match-mode helpers:
     ```
     and_left  : (a && b) = true → a = true
     and_right : (a && b) = true → b = true
     and_intro : a = true → b = true → (a && b) = true
     or_cases  : (a || b) = true → a = true ∨ b = true
     or_left, or_right : a/b = true → (a || b) = true
     ```
  6. **Nat-core leak** → `E213.Tactic.Nat213.*` helpers:
     `mul_assoc`, `add_mul`, `add_sub_of_le`, `le_sub_of_add_le`,
     `mul_mul_mul_comm_213`, `le_of_mul_le_mul_right`,
     `sub_le_sub_left`.
  7. **`decide_eq_true_iff`** → direct two-direction `Iff.intro`:
     `· intro h; exact decide_eq_true (..mp h)`
     `· intro h; exact ...mpr (of_decide_eq_true h)`.
  8. **`by_cases` / `omega` / `simp`** → `cases` / `match` /
     manual Nat lemmas.
  9. **`rw [decide_eq_true_eq]` / `rw [decide_eq_false_iff_not]`**
     → direct `decide_eq_true (proof)` /
     `decide_eq_false (fun h => ...)`.  Decide-Iff carries propext.
  10. **`Nat.sub_add_cancel`** (carries `propext`) →
      `Nat.succ_pred_eq_of_pos` (PURE).
  11. **`Nat.le_max_left` / `Nat.le_max_right`** (carry `propext`)
      → switch from depth-based to leaves-based reasoning, or use
      `Nat.le_add_left` / `Nat.le_add_right`.
  12. **`List.append_nil` / `List.append_assoc` / `List.length_append`**
      (carry `propext`) → `E213.Tactic.List213.{append_nil,
      append_assoc, length_append}` — manually proved
      `congrArg`-based replacements.

## Active limitations (deeper propext chains)

These modules are partially resolved with the surface trick set;
deeper Lean-core dependencies remain:

  - `Real213.CutSumGeneral` — 4 DIRTY, Quot.sound removed but
    propext remains.
  - `Real213.CutMidMono.cutLe_a_cutMid_at` — same.
  - `Cauchy.GenericFamily.*` — funext-by-design (Lens combine).
  - `Cauchy.WallisSharper.wallis_sharper_lower` — omega + by_cases
    + decide chain.

These need either deeper trick development or Lens-equality refactor-style staged
refactor via `eqPW`.

## Future work

  - Lens-level vertical-internal projection (eqPW generalisation)
    — a candidate 4th domain.
  - Cauchy sequence-level `cutSum` / `cutMul` bridge.
  - DRLT physics theorems → ∅-axiom (currently 19 sealed → 0).
  - ~~L3 syntactic internalisation~~ — **closed 2026-05-18** in
    `Lens.SyntacticInternalization`.  Polish-prefix parser/printer
    with full bijection: forward (`parseTree_printTree`), reverse
    (`printTree_parseTree`), and injectivity (`printTree_injective`).

## Bishop subsumption

The Lens-output function space of 213 contains the reals as a named
subspace — no Bishop-style piecewise construction needed.  Companion
to the Real213-Analysis deep-dive reading and
`Lib/Math/Real213/Core/AsLensOutput.lean` (formal carrier).

### The doctrinal claim

Classical analytic constructions of ℝ each build the real line from
some substrate with careful definitions of equality, ordering,
arithmetic, completeness:

  · Cauchy sequences (Bishop's choice for constructive analysis)
  · Dedekind cuts (set-theoretic)
  · Decimal / signed-digit expansions
  · …

Bishop's program is the most delicate of these because it must
hand-rebuild every operation with explicit ε-N moduli.

213's approach: the Lens-output function space `Raw → Bool` (or
`Nat → Nat → Bool` after a count-Lens application) is
**structurally present** the moment the axiom + Lens framework is
committed.  ℝ is a **choice of subspace**: pick
`Cut := Nat → Nat → Bool` with a specific interpretation
(`c m k = true ⟺ x ≤ m/k`).  Operations like `cutSum`, `cutMul`,
`cutMid` are **chosen functions** that happen to satisfy rational
arithmetic under that interpretation.

The key insight: **the function space `Nat → Nat → Bool` is not a
construction of ℝ; it is a space large enough to contain ℝ for
free**.  Operations are then named, not invented.

### Operational realisation

`lean/E213/Lib/Math/Real213/Core/AsLensOutput.lean`:

```lean
/-- Reals as cuts.  Lens-output realisation — no construction needed,
    only a named subspace of the universal `Nat → Nat → Bool`. -/
abbrev RealAsLensOutput := Nat → Nat → Bool
```

Subsequent files (`CutSum.lean`, `CutMul.lean`, `CutMid.lean`, …)
each pick a function in this space and prove the interpretation
identity.

### What's formalised vs. what's a bridge

Formalised:

  · `RealAsLensOutput := Nat → Nat → Bool` (the abbreviation).
  · `Real213` struct (Layer 2) ↔ `chainToCut` bridge ↔
    `RealAsLensOutput` (Layer 3).
  · Per-operation correctness (cutSum, cutMul, cutMid, …): each
    operation's identity at concrete rational pairs proven via
    `decide` or pointwise reduction (e.g. `cutSum_int_int`,
    `cutMul_one_const_at`).
  · Algebraic structure (CutPoset, lattice, dyadic completeness).

Bridge work (multi-session):

  · Bishop ↔ DRLT formal equivalence — Bishop's `CauchyReal` ≃
    `Real213` modulo equivalence; Bishop's operations ↔ DRLT's cut
    operations; the framing-level extensions DRLT introduces.
  · Universal characterisation: prove `RealAsLensOutput` satisfies
    the Bishop axioms (Cauchy completeness, Archimedean,
    decidable order at rationals).

### Why the bridge is principled, not a gap

The Bishop comparison is a **translation layer into another
framework**, not a DRLT-internal closure.  213's falsifiability
rule (`seed/AXIOM/04_falsifiability.md` §5.2.1) demands that DRLT
predictions hold without external axioms.

The PURE proof status of `RealAsLensOutput`, the cut operations,
and the algebraic structure (verified by `#print axioms`) is the
DRLT-internal closure.  Bishop subsumption is the *outer claim*
that DRLT's space is bigger — to formalise it Lean-level requires
an external Bishop API to compare against, which is outside the
∅-axiom contract.

### Companion pointers

  · `lean/E213/Lib/Math/Real213/Core/AsLensOutput.lean` — formal
    carrier.
  · `seed/RESOLUTION_LIMIT_SPEC.md` — relates `RealAsLensOutput` to
    the finite-N_U bound (cuts evaluated at `m, k ≤ N_U`).
  · `LESSONS_LEARNED.md` Pattern #17 — framework-internal
    subsumption.
  · `catalogs/cross-domain-identifications.md` — math ↔ physics
    bridges sit on top of `RealAsLensOutput`.

The full Bishop ↔ DRLT comparison (5-7 sessions): implement a
minimal Bishop API in the 213 namespace; prove `RealAsLensOutput`
↔ Bishop carrier (via `chainToCut` + dyadic bisection); prove the
operations match; characterise the extensions (graded structure,
Lens-output realisation, resolution-limit ceiling).  This is
**doctrinal closure**, not predictive enhancement.  DRLT's
falsifier surface (`THEOREM_METHODOLOGY_SUITE.md` §TH-3) is
independent of the Bishop comparison.

---

## Conclusion

The 3-domain projection catalog (Bool213 / RawCut / CauchyCutSeq) +
bridges (`ChainToCut`, `CauchyProj`) form a **compression tool
catalog**:

  - New domain → follow the 3-domain template to define
    projection.
  - propext leak → apply the trick set (1–11) immediately.
  - Real213 / Cauchy connections → use `ChainToCut` /
    `CauchyProj` patterns.

This is the formal realisation of 213's ∅-axiom thesis —
composable, mechanically audited (`#print axioms` verified),
reusable.

## Change log

  - **2026-05-18 (Option C refactor)**: Nat213 row removed from the
    4-domain pattern table.  Path references updated from
    `Theory/Closed/*` to `Lens/Number/Nat213/*` and `Lens/Bool213/*`
    (post-2026-05-14 migration).  Document language uniformised
    to English.  Trick set extended with #10–#11.
  - **2026-05-18 (L3 + L4 syntactic internalisation closure)**:
    `Lens.SyntacticInternalization` reached full bijection:
    `parseTree_printTree` (forward, 21 PURE symbols) extended with
    `parseHelper_sound` + `printTree_parseTree` + `printTree_injective`
    + `printRaw_parseTree` (4 PURE symbols, +138 lines).
    `chartChain_value_injective` + `chartChain_injective` added to
    `ChartGeneral` (uses 213-native `add_left_cancel` +
    `mul_left_cancel_pos` to dodge propext-tainted core).
