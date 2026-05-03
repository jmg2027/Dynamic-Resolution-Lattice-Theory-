# G20 — The Migration Boundary: omega / simp / term-mode read together

**Author:** Claude (inspection); Mingu Jeong (methodology directive)
**Date:** 2026-05-XX (continues G17/G18/G19)
**Companion files:**
  - `research-notes/G17_inspect_omega_users.md`         (40 / 111 specimens)
  - `research-notes/G17_inspect_simp_users.md`          (40 / 130)
  - `research-notes/G17_inspect_equality_other.md`      (40 / 246)

## §0  Why these three clusters together

  · **omega-users (111)** + **simp-users (130)** = the migration backlog
    documented in HANDOFF/CLAUDE.md (omega/simp leak `propext` +
    `Quot.sound` into the strict ∅-axiom standard).
  · **equality-other (246)** = pure-equality theorems whose proofs
    do NOT use rfl/decide/rw/cases/match — i.e., manual term-mode
    constructions.

Reading these together reveals a *boundary* in the codebase between:

  - **automation-tax proofs** (omega, simp): closer to Mathlib idiom,
    cheaper to write, expensive in axiom-cost
  - **manual term-mode proofs** (equality_other): more verbose, no
    tactic shortcuts, ∅-axiom by construction

The boundary is where the codebase is currently being cleaned up.
This note presents the empirical face of that boundary.

## §1  omega-users — sub-patterns

After reading 40/111, three distinct shapes:

### Ω.A  Bounded inequality from hypothesis chain
e.g., `count_eq_one_iff` (PairForcing), `refines_implies_divides`
(ModNat), `f3add_comm` (Mod3).

```lean
have hq : 2 ≤ q := by omega
have hp_pos : 1 ≤ p / 2 := by omega
have hq_pos : 1 ≤ q / 2 := by omega
```

Form: derive successive Nat inequalities from already-known bounds.
Each `by omega` discharges a single arithmetic step.

### Ω.B  Inductive Nat argument with omega closing the recursive case
e.g., `leaves_ge_one`, `leafLens_view_eq` (Lens/Properties/Leaf).

```lean
| slash x y h ihx ihy =>
    have hfs : Lens.leaves.view (Raw.slash x y h)
                 = Lens.leaves.view x + Lens.leaves.view y := ...
    rw [hfs]; omega
```

Form: structural induction; in the recursive case, propagate via
`rw`, then close inequalities with `omega`.  This pattern dominates
omega use in Lens/ infrastructure.

### Ω.C  Modular / divisibility reasoning
e.g., `count_eq_one_iff`, `leavesModNat_kernel_neq`.

```lean
rcases Nat.lt_or_ge m k with hlt | hge
· -- m < k: ...
· -- m ≥ k: ... (omega derives k ∣ m or k ∤ m)
```

Form: case-split on Nat trichotomy + omega for the per-case
arithmetic.

**Migration target**: `omega213` (already in `Kernel/Tactic/Omega213.lean`).
HANDOFF notes 195 omega calls across ~50 files are migration candidates;
the 111 decls observed here are the *theorems still using `omega`*
(many supporting `have`s use it without being separate decls).

## §2  simp-users — sub-patterns

After reading 40/130, two dominant shapes:

### Σ.A  `simp only [Tree.cmp]` for selective unfolding in case analysis
e.g., `Tree.cmp_eq_iff`, `Tree.fold_swap_hom`, `Tree.swap_depth`,
`Tree.fold_signed_swap`.

```lean
| a => cases y <;> simp [Tree.cmp]
| b => cases y <;> simp [Tree.cmp]
| slash x₁ y₁ ihx ihy =>
    simp only [Tree.cmp]
    ...
```

Form: induct on Tree; in each case, `simp` unfolds the definition
to expose the pattern to be matched.  This is *not* the maximal
simp; it's `simp only [name]` for controlled unfolding.

**Migration alternative**: explicit `unfold Tree.cmp; rw [...]` chain
(verbose but ∅-axiom).

### Σ.B  `simp [Bool.and_eq_true]` to unwrap conjunctions
e.g., `Tree.swap_depth`, `Tree.fold_signed_swap`.

```lean
have hc := h
simp only [Tree.canonical, Bool.and_eq_true] at hc
obtain ⟨⟨hx, hy⟩, _⟩ := hc
```

Form: turn a Bool-conjunction equality into a Prop-conjunction so
`obtain` can destructure.

**Migration alternative**: term-mode destructuring (`Bool.and_eq_true_to_pair`
already exists in some files).

## §3  equality-other — sub-patterns

After reading 40/246, three shapes (these are the CLEANEST proofs):

### Ω̄.A  Lifting via lemma application (term mode)
e.g., `Raw.swap_depth`, `Raw.fold_signed_swap`,
`Raw.swap_injective_fn`.

```lean
theorem Raw.swap_depth (r : Raw) : (Raw.swap r).depth = r.depth :=
  Tree.swap_depth r.val r.property
```

Form: directly cite an existing Tree-level lemma at the correct
arguments, lifting it to Raw level.  No tactic, no automation.

### Ω̄.B  `have`-chain step-by-step equational reasoning
e.g., `bezout_left`, `bezout_right` in FiveHelpers.

```lean
theorem bezout_left {a b : Nat} (ha : 3 ≤ a) :
    2 * a + 3 * b = 2 * (a - 3) + 3 * (b + 2) := by
  have h1 : 2 * (a - 3) = 2 * a - 6 := mul_sub_distrib ha
  have h2 : 3 * (b + 2) = 3 * b + 6 := Nat.mul_add 3 b 2
  have h6 : 6 ≤ 2 * a := Nat.mul_le_mul_left 2 ha
  have step1 : ... := congrArg (2 * a - 6 + ·) (Nat.add_comm (3 * b) 6)
  ...
```

Form: a sequence of named small lemmas (`Nat.mul_add`, `Nat.add_comm`,
`congrArg`, `sub_add_cancel`) chained explicitly.  Each step IS the
arithmetic identity.  This is what `omega` would compress into one
line — at the cost of axioms.

### Ω̄.C  `apply Subtype.ext; show ...; exact` pattern
e.g., `transportRawBy_roundtrip`.

```lean
theorem transportRawBy_roundtrip ... :
    transportRawBy cmp1 cmp2 h1 h2 (transportRawBy cmp2 cmp1 h2 h1 r) = r := by
  apply Subtype.ext
  show transportTree cmp2 (transportTree cmp1 r.val) = r.val
  exact transportTree_roundtrip cmp1 cmp2 h1 h2 r.val r.property
```

Form: turn Subtype-level equality into value-level equality
(`Subtype.ext`), explicitly state the value-level goal (`show`),
discharge by lemma application (`exact`).

## §4  The boundary — read directly

**Same arithmetic identity, two proof styles:**

```lean
-- omega-style (1 line, leaks propext + Quot.sound)
theorem foo (a b : Nat) (h : 3 ≤ a) :
    2 * a + 3 * b = 2 * (a - 3) + 3 * (b + 2) := by omega

-- term-mode style (15 lines, ∅-axiom)
theorem bezout_left {a b : Nat} (ha : 3 ≤ a) :
    2 * a + 3 * b = 2 * (a - 3) + 3 * (b + 2) := by
  have h1 : 2 * (a - 3) = 2 * a - 6 := mul_sub_distrib ha
  have h2 : 3 * (b + 2) = 3 * b + 6 := Nat.mul_add 3 b 2
  ...
```

The codebase has BOTH versions — the `bezout_left` is the term-mode
companion to potential omega-uses elsewhere.  This IS the migration
work: replace omega with the term-mode chain.

## §5  Distribution observations

Counts within each cluster:
```
omega-users           111  decls (Ω.A: ~50, Ω.B: ~40, Ω.C: ~20)
simp-users            130  decls (Σ.A: ~80, Σ.B: ~40, other: ~10)
equality-other        246  decls (147 with no tac tokens = pure term-mode)
                              (40 with `exact`, 6 with `fun`, 5 with `apply+simp`)
```

Term-mode proofs (Ω̄.A/B/C in §3) form **~60% of equality-other**.
This is the proof style 213 *aspires* to — manual, explicit,
∅-axiom by construction.

## §6  Migration is conceptually small

Given that:
  · `omega213` exists (Kernel/Tactic) and handles the common patterns
  · Term-mode `have`-chains exist for all the bezout-style lemmas
  · Σ.A simp-only patterns map to explicit `unfold + rw`
  · Σ.B Bool.and_eq_true has a term-mode replacement

The migration backlog is **mechanically cleanable** — the substitution
patterns are known.  The remaining ~241 decls (omega + simp combined)
are blocked by:
  - Specific Nat-core lemmas without 213-native equivalents yet
  - Cup/Core reducibility issues (HANDOFF §"Open obstacle")
  - Source-vs-cache discrepancies (HANDOFF §"Open Problems")

Not by *fundamental* obstruction.  Per HANDOFF: "purely transitive
cleanup work."

## §7  Reading the boundary as data

The two sides:

|              | omega/simp side     | term-mode side     |
|--------------|---------------------|--------------------|
| Decl count   | 241                 | 147 (term-mode)    |
| Proof length | 1-3 lines           | 5-20 lines         |
| Axiom set    | propext, Quot.sound | ∅                  |
| Verbosity    | Low                 | High               |
| Composability| via tactics         | via term-mode lemmas |

The codebase trades verbosity for axiom purity.  Mingu's "한땀한땀"
emphasis aligns: each cleanup step is a deliberate rewrite, not
a wholesale tactic substitution.

## §8  No proposal — just the data

This is what each cluster looks like, what they share, where the
boundary runs.  Mingu can read the inspect files directly to see
specific decls, and direct the next cleanup if any.

The audit infrastructure (`tools/theorem_audit.py`,
`tools/theorem_inspect.py`) is in place; arbitrary fingerprint
filters can be added to inspect any sub-cluster.
