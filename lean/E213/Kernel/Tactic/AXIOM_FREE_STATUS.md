# 213-native ∅-axiom migration — status

Tracking the systematic elimination of `propext` and `Quot.sound`
from `lean/E213/`.  Companion to `OMEGA213_MIGRATION.md`.

The DRLT-allowed Lean kernel base is `{propext, Quot.sound}`.  The
*strict* ∅-axiom standard ("does not depend on any axioms") is
stronger.  This file records the catalog of standard-Lean constructs
that block strict ∅-axiom, and the 213-native replacements for each.

## Migrated files (∅-axiom verified)

| File | Theorems | Notes |
|---|---|---|
| `Math/Pigeonhole.lean` | `no_inj_succ`, `no_inj_lt` | 20 omega + 2 simp + Fin.elim0 + literal `(0 : Fin 1)` all replaced |

## Catalog of axiom leaks discovered

Each Lean-core construct in this table was empirically observed to
inject `propext` (and/or `Quot.sound`) into theorems.  Replace with
the 213-native form on the right.

| Lean-core construct | Brings | 213-native replacement |
|---|---|---|
| `by omega` | propext, Quot.sound | `by omega213` |
| `by simp` | propext | targeted `rw` chains, explicit `Nat.*` lemmas |
| `by simpa` | propext | `have ... ; exact ...` |
| `Nat.sub_add_cancel` | propext | inline cases proof: `n - 1 + 1 = n` from `n ≠ 0` |
| `Fin.elim0` | propext | `fun h => absurd h.isLt (Nat.not_lt_zero _)` |
| `(0 : Fin (n+1))` literal | propext | explicit `⟨0, Nat.zero_lt_succ _⟩` |
| `funext` (general) | Quot.sound | structural pointwise lemmas (per-construct) |

## Lean-core lemmas verified ∅-axiom

These are safe to use directly:

  - `Nat.le_refl`, `Nat.zero_le`, `Nat.zero_lt_succ`, `Nat.lt_succ_self`
  - `Nat.le_succ_of_le`, `Nat.lt_succ_of_le`, `Nat.lt_succ_of_lt`
  - `Nat.succ_lt_succ`, `Nat.succ_le_succ`, `Nat.succ_le_of_lt`
  - `Nat.le_of_lt`, `Nat.le_of_lt_succ`, `Nat.le_of_not_lt`
  - `Nat.lt_of_lt_of_le`, `Nat.lt_of_le_of_lt`, `Nat.lt_of_le_of_ne`
  - `Nat.le_trans`, `Nat.lt_irrefl`, `Nat.not_lt_of_le`
  - `Nat.le_pred_of_lt`, `Nat.sub_one_lt`, `Nat.pos_of_ne_zero`
  - `Nat.not_lt_zero`, `Nat.add_sub_of_le`
  - `Nat.mul_le_mul_left`, `Nat.mul_le_mul_right`
  - `Fin.ext`, `Fin.isLt` (field accessor)
  - `congrArg` (with explicit `α := ...` when arg type ambiguous)
  - `dif_pos`, `dif_neg`, `if_pos`, `if_neg`
  - `by_cases h : P` (when P is `Decidable`)
  - `induction n` on `Nat`
  - `unfold`, `rw [...]` (with ∅-axiom equations)

## Methodology

### Probe procedure

To detect axiom leaks in a candidate file F:

  1. Create `lean/E213/_AxiomProbe.lean`:
     ```lean
     import E213.<F's module path>
     #print axioms E213.<F's namespace>.<theorem₁>
     ```
  2. `lake build E213._AxiomProbe`
  3. Read `info: ... depends on axioms: [...]` lines.
  4. If any non-empty axiom set, find leaks via binary-split of
     suspected sub-proofs (see "Bisection" below).
  5. Delete `_AxiomProbe.lean` after diagnosis.

### Bisection

For each suspected lemma `L` used in F:

  1. Write `theorem probe_L (...) : ... := L ...` in `_AxiomProbe.lean`.
  2. Build, `#print axioms probe_L`.
  3. If propext/Quot.sound appear → `L` is the leak; provide a
     213-native replacement.

### Common leak surfaces

  - **OfNat instance for `Fin (n+1)`**: `(0 : Fin (n+1))` literal goes
    through `Fin.instOfNat` which depends on propext.  Always use
    explicit `⟨0, Nat.zero_lt_succ _⟩`.
  - **Lean-core lemmas with `simp` proofs**: any `theorem` whose
    body is `by simp ...` will carry propext to all callers.  Probe
    before relying.
  - **`Fin.elim0`**: replace with `fin0_absurd` style helper.

## Migration order recommendation

Bottom-up by dependency:

  1. **Leaf utility files** (no E213 imports beyond `Kernel/Tactic/`):
     - `Math/Pigeonhole.lean` ✓
     - `Math/Cauchy/PellSeq.lean` (12 omega)
     - `Math/Cauchy/Archimedean.lean` (12 omega)
     - `Math/ModArith/JoinEquivGCD.lean` (11 omega)
  2. **Mid-layer Math** (depending on above)
  3. **Hypervisor/Lens** sub-clusters
  4. **Physics** chain
  5. **Capstones** — already strict via `does not depend on any axioms`
     in their final step; internal lemma cleanup extends chain cleanliness.

## omega213 coverage extensions (this session)

Added patterns to `omega213` macro:
  - `Nat.lt_succ_self _`
  - `Nat.lt_succ_of_lt`
  - `Nat.succ_lt_succ`, `Nat.succ_le_succ`
  - `Nat.le_of_lt_succ`
  - `Nat.lt_of_lt_of_le` (had only the dual form before)
