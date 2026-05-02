# 213-native ∅-axiom migration — status

Tracking the systematic elimination of `propext` and `Quot.sound`
from `lean/E213/`.  Companion to `OMEGA213_MIGRATION.md`.

The DRLT-allowed Lean kernel base is `{propext, Quot.sound}`.  The
*strict* ∅-axiom standard ("does not depend on any axioms") is
stronger.  This file records the catalog of standard-Lean constructs
that block strict ∅-axiom, and the 213-native replacements for each.

## 213-native helper modules (`Kernel/Tactic/`)

Modular by topic — each file has *one* coherent concern:

  - `Omega213.lean` — `omega213` tactic (linear ℕ arithmetic).
  - `Nat213.lean`   — pure ℕ-arithmetic helpers (cancellation,
                       sub/add, mul, distributivity).  13 theorems.
  - **`Mod213.lean`**   — *cohomological-trajectory primitives*:
                       parity (mod 2), mod3, mod6, CRT pairing
                       (mod6 ↔ (parity, mod3) = Eisenstein-6th-roots
                       phase walk).  **11 theorems**.
                       See `research-notes/G2_trajectory_principle.md`,
                       `G3_raw_as_universal_trajectory.md`.
  - `Fin213.lean`   — `Fin` helpers (`absurd0`).

All theorems in these modules are individually verified ∅-axiom.

### Nat213 catalog (pure arithmetic)

  - `sub_one_add_one`     `n ≠ 0 → n - 1 + 1 = n`
  - `sub_add_cancel`      `m ≤ n → n - m + m = n`         (general)
  - `add_sub_of_le`       `m ≤ n → m + (n - m) = n`
  - `add_sub_cancel_right` `a + b - b = a`
  - `le_sub_of_add_le`    `a + b ≤ c → a ≤ c - b`
  - `cases_lt_two`        `n < 2 → n = 0 ∨ n = 1`
  - `cases_lt_three`      `n < 3 → n = 0 ∨ n = 1 ∨ n = 2`
  - `add_right_cancel`    `a + c = b + c → a = b`
  - `add_left_cancel`     `a + b = a + c → b = c`
  - `mul_assoc`           `a * b * c = a * (b * c)`
  - `mul_sub_distrib`     `b ≤ a → c * (a - b) = c*a - c*b`
  - `ne_zero_of_le_ne`    `b ≤ a → a ≠ b → a ≠ 0`
  - `sub_one_lt_of_lt_succ_ne`  `b ≤ a → a ≠ b → a < n+1 → a-1 < n`

### Mod213 catalog (trajectory primitives)

  - `parity`              `Nat → Bool`              (step-2 walk)
  - `parity_step` / `_zero` / `_one`                (rfl)
  - `parity_succ`         `parity (n+1) = !parity n`
  - `parity_double`       `parity (2*n) = false`
  - `parity_double_succ`  `parity (2*n+1) = true`
  - `mod3`                `Nat → Nat`               (step-3 walk)
  - `mod3_step` / `_zero` / `_one` / `_two`         (rfl)
  - `mod3_lt_three`       `mod3 n < 3`
  - `mod3_succ`           `mod3 (n+1) = (mod3 n + 1) % 3`
  - `mod6`                `Nat → Nat`               (step-6 walk)
  - `mod6_step`, `mod6_lt_six`
  - **`mod6_parity`**     `parity (mod6 n) = parity n`  (CRT half 1)
  - **`mod6_mod3`**       `mod3   (mod6 n) = mod3 n`    (CRT half 2)

## Migrated files (∅-axiom verified)

| File | Theorems | Notes |
|---|---|---|
| `Math/Pigeonhole.lean` | 2 | 20 omega + 2 simp + Fin.elim0 + literal `(0 : Fin 1)` |
| `Firmware/Atomicity/NonDecomposable.lean` | 3 | omega + rcases + match-on-value pattern |
| `Firmware/Atomicity/ArityForcing.lean` | 2 | omega-pigeonhole on Fin 2 → 6-case `cases_lt_two` |
| `Math/Infinity/Pair.lean` | 5 | 5 omega + Nat.add_left/right_cancel + Prod.mk.injEq |

## Catalog of axiom leaks discovered

Each Lean-core construct in this table was empirically observed to
inject `propext` (and/or `Quot.sound`) into theorems.  Replace with
the 213-native form on the right.

| Lean-core construct | Brings | 213-native replacement |
|---|---|---|
| `by omega` | propext, Quot.sound | `by omega213` |
| `by simp` | propext | targeted `rw` chains, explicit `Nat.*` lemmas |
| `by simpa` | propext | `have ... ; exact ...` |
| `Nat.sub_add_cancel` | propext | `Nat213.sub_add_cancel` |
| `Nat.le_sub_of_add_le` | propext | `Nat213.le_sub_of_add_le` |
| `Nat.add_left_cancel` | propext | `Nat213.add_left_cancel` |
| `Nat.add_right_cancel` | propext | `Nat213.add_right_cancel` |
| `Nat.div_lt_iff_lt_mul.mpr` | propext | (TODO Nat213 — iff destructor brings propext) |
| `Nat.le_div_iff_mul_le.mpr` | propext | (TODO Nat213) |
| `Fin.elim0` | propext | `Fin213.absurd0` |
| `(0 : Fin (n+1))` literal | propext | explicit `⟨0, Nat.zero_lt_succ _⟩` |
| `Prod.mk.injEq.mpr` | propext | `congr (congrArg Prod.mk hx) hy` |
| `match n, h2, h4 with \| 2,_,_ \| 3,_,_` (small-case match) | propext, Quot.sound | `match Nat.lt_or_ge n k with` cascade + `Nat.le_antisymm` |
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
