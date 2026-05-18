# CLOSED_FORM_SPEC — closed-form spec for 213 (Tier 5)

The substantial mathematics of 213 can be expressed without external
axioms (`propext`, `funext`, `Quot.sound`, `Classical`, Mathlib).
Where `funext` / `propext` / `Quot.sound` previously entered, we
substitute **vertical-internal projection** + **pointwise eq**.

See also:
  - `research-notes/G84_closed_form_pattern_unification.md` (探索 note)
  - `lean/E213/Lens/Number/Nat213/*` and
    `lean/E213/Lens/Bool213/*` (Lean implementation, post-Option-C
    layout)
  - `lean/E213/Lib/Math/Real213/Cauchy/ChainToCut.lean` (bridge)

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

## Active limitations (deeper propext chains)

These modules are partially resolved with the surface trick set;
deeper Lean-core dependencies remain:

  - `Real213.CutSumGeneral` — 4 DIRTY, Quot.sound removed but
    propext remains.
  - `Real213.CutMidMono.cutLe_a_cutMid_at` — same.
  - `Cauchy.GenericFamily.*` — funext-by-design (Lens combine).
  - `Cauchy.WallisSharper.wallis_sharper_lower` — omega + by_cases
    + decide chain.

These need either deeper trick development or G83-style staged
refactor via `eqPW`.

## Future work

  - Lens-level vertical-internal projection (eqPW generalisation)
    — a candidate 4th domain.
  - Cauchy sequence-level `cutSum` / `cutMul` bridge.
  - DRLT physics theorems → ∅-axiom (currently 19 sealed → 0).
  - L3 syntactic internalisation (extending
    `Lens.SyntacticInternalization` to constructive
    parser/printer round-trip).

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
