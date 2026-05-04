# G24 — Six Functional Families: Classification After Exhaustive View

**Author:** Claude (synthesis); Mingu Jeong (methodology directive)
**Date:** 2026-05-XX (continues G17–G23)
**Companion files:**
  - `research-notes/G17_combo_full_distribution.md` (566 combos full table)
  - `research-notes/G17_inspect_combos_11_50.md` (specimens for ranks 11-50)
  - All G17_inspect_*.md (cumulative ~5500 specimens read)

## §0  Now-permitted classification

Mingu (this session): **"완전히 다 버고나서 분류해보면될듯"** —
"after looking at everything, then we can classify."  G17–G23
recorded raw fingerprints + inspections without imposing structure.
This note attempts a classification *now that the data has been seen*.

The classification below is **descriptive** (read off frequency
patterns + proof-shape recurrence) rather than prescriptive.  Each
family is grounded in inspected specimens.

## §1  Combo complexity profile (foundation)

```
slots/combo  unique combos   theorems   % of all
    0              1           229       5.0
    1             16         2,018      43.6
    2             62           986      21.3
    3            100           438       9.5
    4            103           519      11.2
    5             95           159       3.4
    6             75           121       2.6
    7             48            64       1.4
    8+           104            90       1.9
```

**90% of theorems use ≤4 slots.**  Beyond 4 slots, complexity is rare.

## §2  The six families (descriptive)

After reading specimens across all 566 combos, theorem proofs
cluster into six functional families.  Each family is identified by
*which kind of mathematical content* the theorem expresses, not just
by combo identity.

### F1 — Atomic Computational Check (~52% of theorems)
Statement: a single equality or inequality.
Proof: kernel evaluates and verifies.

```lean
-- F1a: decide
theorem leaves_equates : Lens.leaves.view rAAB = Lens.leaves.view rABB := by decide

-- F1b: rfl
theorem boolToConstLens_true : boolToConstLens true = constTrueLens := rfl

-- F1c: rfl + light rewrite
theorem boundary_at_k0 : energy allDown = isoperimetricProfile 0 := by decide
```

Combos in F1: `decide`, `rfl`, `rfl, rw`, `decide, exact`, `decide, simp`, ...

Cumulative: ~2,400 theorems (52% of all).

### F2 — Bundled Atomic Checks (~16%)
Statement: a conjunction of atomic claims (∧).
Proof: bundle via `decide` directly OR via `refine ⟨...⟩ <;> decide`
OR via term-mode anon constructor.

```lean
-- F2a: AND closed by single decide
theorem phase_CE_capstone :
    kerSizeDelta0 = 2 ∧ 2^5 = 32 ∧ 2^12 = 4096 := by decide

-- F2b: refine + decide capstone
theorem mul_generators_ne_zero :
    I' * J ≠ 0 ∧ J * I' ≠ 0 ∧ I' * I' ≠ 0 ∧ J * J ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- F2c: anon constructor (term-mode bundle)
theorem cohabit_peano_depth (h : Raw.a ≠ Raw.b) :
    peanoLens.view (r h) = 2 ∧ Lens.depth.view (r h) = 1 :=
  ⟨peano_view h, depth_view h⟩

-- F2d: anon with rfl proofs
theorem mpi_sq_bracket :
    Nat.ble 18001 18934 = true ∧ Nat.ble 18935 19500 = true := ⟨rfl, rfl⟩
```

Combos in F2: `AND, decide`, `AND, anon, decide, refine`, `AND, anon`,
`AND, anon, rfl`, ...

Cumulative: ~750 theorems (16%).

### F3 — Universal Dispatch (~14%)
Statement: ∀ x, P x.
Proof: term-mode pattern match on x's constructors, OR `intro` +
structural recursion (induction).

```lean
-- F3a: term-mode pattern match
theorem getBase_eq {N k : Nat} :
    ∀ (x : RawNk N k) (h : isBase x = true), x = .object (getBase x h)
  | .object _, _ => rfl
  | .rel _,    h => by cases h

-- F3b: intro + induction + decide on bases + rw on recursive case
theorem pellFSMmod11_run_period_5 :
    ∀ k, pellFSMmod11.run (k + 5) = pellFSMmod11.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show pellFSMmod11.step (pellFSMmod11.run (k' + 5))
        = pellFSMmod11.step (pellFSMmod11.run k')
    rw [ih]

-- F3c: ∀ closed by intro + rw (no induction)
theorem zmod6Lens_combine_comm :
    ∀ u v : Nat, zmod6Lens.combine u v = zmod6Lens.combine v u := by
  intro u v
  show (u * v) % 6 = (v * u) % 6
  rw [Nat.mul_comm]
```

Combos in F3: `FORALL, decide`, `FORALL, decide, intro, rw`,
`FORALL, intro, rw`, `FORALL`, `FORALL, intro, rfl, rw`, ...

Cumulative: ~650 theorems (14%).

### F4 — Implication Chain (~10%)
Statement: H₁ → H₂ → ... → C.
Proof: `intro` + structural unpack + propagation + conclude.
OR pure term-mode lift (the most common subform).

```lean
-- F4a: pure term-mode lift
theorem Raw.swap_depth (r : Raw) : (Raw.swap r).depth = r.depth :=
  Tree.swap_depth r.val r.property

-- F4b: intro + rw chain
theorem swapLens_view_involutive :
    ∀ r : Raw, swapLens.view (swapLens.view r) = r := by
  intro r
  rw [swapLens_view_eq_swap, swapLens_view_eq_swap, Raw.swap_swap]

-- F4c: intro + structural unpack
theorem block_constant_implies_aut_invariant ... : ... := by
  obtain ⟨f, hf⟩ := h
  intro σ hσ hinj i j
  rw [hf (σ i) (σ j), hf i j]
  ...
```

Combos in F4: `(empty)`, `IMPLIES`, `IMPLIES, rfl`, `exact, rw`,
`IMPLIES, rw`, `exact`, `intro, rw`, ...

Cumulative: ~470 theorems (10%).

### F5 — Existential Witness (~5%)
Statement: ∃ x, P x.
Proof: provide explicit witness via `⟨witness, proof⟩` OR
via `refine ⟨?_, ...⟩` then close goals.

```lean
-- F5a: term-mode anon
theorem image_contains_a (α : Type) [d : HasDistinguishing α] :
    ∃ r : Raw, universalMorphism α r = d.a :=
  ⟨Raw.a, universalMorphism_a α⟩

-- F5b: refine with witness + decide
theorem fin3_image_strict :
    ∃ x : Fin 3, ¬ ∃ r : Raw, universalMorphism (Fin 3) r = x := by
  refine ⟨2, ?_⟩
  intro ⟨r, hr⟩
  rcases fin3_image_in_01 r with h | h
  · rw [h] at hr; exact absurd hr (by decide)

-- F5c: refine with witness + universal proof
theorem orderCauchy_from_true_forever (xs : Nat → Raw) (m k : Nat)
    (h : ∀ n, orderProj m k (abLens.view (xs n)) = true) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → ... := by
  refine ⟨0, ?_⟩
  intro i j _ _; rw [h i, h j]
```

Combos in F5: `EXISTS, anon`, `EXISTS, anon, exact`, `EXISTS, refine`, ...

Cumulative: ~170 theorems (3.7%, the smallest family by count).

### F6 — Negative Existence / Failure (~3%)
Statement: ¬ ∃ x, P x  (or `∃ x, ¬ ...`).
Proof: assume the hypothetical, derive contradiction by exhibiting
two finite witnesses with disagreeing required values.

```lean
-- F6a: ¬ ∃ via two-witness contradiction
theorem maxLens_R4_fails :
    ¬ ∃ conj : Nat → Nat, SwapMatching maxLens conj := by
  rintro ⟨conj, hmatch⟩
  -- derive conj 1 = 0 from one Raw, conj 1 = 1 from another → contradict.
  ...

-- F6b: ∃ x ¬∃ ... (image gap)
theorem int_image_strict :
    ∃ x : Int, ¬ ∃ r : Raw, universalMorphism Int r = x := by
  refine ⟨-1, ?_⟩
  intro ⟨r, hr⟩
  have h_nonneg : 0 ≤ universalMorphism Int r := int_image_nonneg r
  rw [hr] at h_nonneg
  exact absurd h_nonneg (by decide)
```

Combos in F6: `NEG, decide`, `NEG, exact, intro`,
`EXISTS, NEG, ...`, ...

Cumulative: ~140 theorems (3%).

## §3  Family share summary

```
F1  Atomic computational check    52%  (decide, rfl, light variants)
F2  Bundled atomic checks         16%  (∧, anon, refine + decide)
F3  Universal dispatch            14%  (∀ + intro + induction/rw/decide)
F4  Implication chain             10%  (term lift, intro+rw, destruct)
F5  Existential witness            4%  (∃ + anon witness)
F6  Negative existence             3%  (¬∃ + finite contradiction)
─────────────────────────────────────
                                 ~99%  of 4,624 theorems
```

The remaining ~1% covers exotic combinations (omega+simp+cases mixed,
hybrid cross-family blends) and the 9 Classical.* demos.

## §4  Cross-family hybrids

About 5% of theorems span two families simultaneously:

  · F2 + F3:  `AND, FORALL, anon` (33 decls) — bundled per-prime
              FSM-period statements (Pisano marathon Type B).
  · F3 + F4:  `FORALL, IMPLIES` (30) — `∀ x, P x → Q x`.
  · F4 + F1:  `IMPLIES, rfl` (60) — `H → C` where C is by rfl.
  · F2 + F5:  `EXISTS, AND, anon` — bundle multiple existentials.

These are NOT new families; they are *combined applications* of
the six basic families.

## §5  What the family classification expresses

Each family corresponds to a distinct *operational mode* of 213:

  · **F1**: **trajectory-endpoint verification** — kernel runs a
    bounded computation to completion.
  · **F2**: **trajectory-bundle verification** — multiple endpoints
    verified together; consolidation is the point.
  · **F3**: **trajectory enumeration over indices** — same shape at
    every constructor / Nat-step.
  · **F4**: **trajectory propagation** — given trajectory invariant,
    push it through definitions.
  · **F5**: **trajectory production** — exhibit the explicit
    trajectory whose endpoint matches a goal.
  · **F6**: **trajectory-impossibility witness** — show two finite
    trajectories rule out any single-trajectory existence.

Together: 213's six core operations on trajectories.  No seventh.

## §6  Comparison with prior framings

  · vs **G6 axiom-cost spectrum** (rejected, too top-down): 6
    families is *empirical*, not derived from external axiom-cost.
    But correlates strongly: F1/F2/F3/F4/F5/F6 are all ∅-axiom by
    construction; the non-classified ~1% holds the omega/simp/Classical
    leak.

  · vs **G10 MTD spectrum** (rejected, too speculative): 6 families
    is *what the kernel verifies*, not "Kolmogorov complexity".  But
    correlates: F1 ≈ MTD-zero (bounded compute), F3/F4 ≈ MTD-grows-
    with-N (induction), F5/F6 ≈ MTD-bounded (named witness).

  · vs **G22 5 dominant shapes** (Shapes 1-5): G22 was per-combo
    grouping; G24 is cross-combo *functional* grouping.  The 5
    Shapes from G22 are precisely "F1 with proof-method variation"
    + "F2 with proof-method variation" — i.e., F1 splits into
    Shapes 1/3 (decide/rfl), F2 splits into Shapes 2/5 (decide/refine),
    F4 = Shape 4 (term-mode lift).

So G24 unifies the previous descriptions under one functional axis.

## §7  Where this leaves the question

The user's earlier critique of axiom-cost / MTD was: *both axes
were external, neither emerged from the data.*  G24's 6 families
emerged from inspecting ~5500 specimens across 566 combos.  Each
family is anchored to specimen patterns that recur.

This IS the empirical classification.  Whether to LABEL it as
"the" classification, or whether to keep refining (e.g., split F4
into "intro+rw" vs "term-mode lift" sub-families), depends on the
purpose:

  · For *understanding what 213 reasoning is*: 6 families suffices.
  · For *guiding cleanup work* (omega/simp migration): the
    proof-method axis is more useful (G19 strata).
  · For *catalog-building* (which marathon does what): the marathon-
    archetype lens (G23) is more useful.

Each lens reveals a different aspect of the same data.

## §8  Anchor specimen per family

For Mingu's intuition, one anchor per family:

```lean
-- F1
theorem K_squared : (I' * J) * (I' * J) = ⟨⟨-1, 0⟩, 0⟩ := by decide

-- F2
theorem chi_N_pattern : chi_delta4 = 1 ∧ chi_two_glued = 2 ∧ ... := by decide

-- F3
theorem getBase_eq {N k : Nat} :
    ∀ (x : RawNk N k) (h : isBase x = true), x = .object (getBase x h)
  | .object _, _ => rfl
  | .rel _,    h => by cases h

-- F4
theorem Raw.swap_depth (r : Raw) : (Raw.swap r).depth = r.depth :=
  Tree.swap_depth r.val r.property

-- F5
theorem image_contains_a {α} [d : HasDistinguishing α] :
    ∃ r : Raw, universalMorphism α r = d.a :=
  ⟨Raw.a, universalMorphism_a α⟩

-- F6
theorem int_image_strict :
    ∃ x : Int, ¬ ∃ r : Raw, universalMorphism Int r = x := by
  refine ⟨-1, ?_⟩
  intro ⟨r, hr⟩
  exact absurd (hr ▸ int_image_nonneg r) (by decide)
```

Six theorem-shapes.  Six trajectory-operations.  213's reasoning
condensed into six concrete examples.
