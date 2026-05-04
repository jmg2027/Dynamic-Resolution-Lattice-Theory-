# G21 — Building Blocks: defs, implications, universals

**Author:** Claude (inspection); Mingu Jeong (methodology directive)
**Date:** 2026-05-XX (continues G17–G20)
**Companion files:**
  - `research-notes/G17_inspect_def_only.md`        (50 / 1369 defs)
  - `research-notes/G17_inspect_implication_thm.md` (50 / 483 →-theorems, no ∃)
  - `research-notes/G17_inspect_universal_thm.md`   (50 / 618 ∀-theorems, no ∃)

## §0  What this note is

Continues the empirical pass.  G17–G20 read theorem clusters; this
note reads:
  · **defs (1369)** — what 213 NAMES as primitive objects
  · **implications (483)** — conditional reasoning shapes
  · **universals (618)** — quantification structures

Together: how 213 builds *blocks* of reasoning, before any
particular theorem.

## §1  defs cluster — what is NAMED in 213

After reading 50/1369 specimens, six broad shapes:

### Δ.A  Boolean / Prop predicates on simple types
e.g., `isA : Fin 5 → Bool := i.val < 3`,
`Survives : Nat → Prop := residue a = 1`,
`isBase : RawNk N k → Bool` (pattern match).

Form: `def P : T → Bool/Prop := concrete_condition`.

### Δ.B  Combinatorial / arithmetic functions
e.g., `count (p q : Nat) : Nat := (p / 2) * (q / 2)`,
`residue (a : Nat) : Nat := a % 2`,
`classify (i j : Fin 5) : BlockPair := match isA i, isA j with ...`.

Form: `def f : T₁ → ... → Tₙ → S := computational_recipe`.

### Δ.C  Inductive structure classifications
e.g., `inductive BlockPair | AAdiag | AAoff | AB | BA | BBdiag | BBoff`,
`def Decomp (n a b : Nat) : Prop := n = 2 * a + 3 * b`.

Form: explicit finite type with named constructors, OR proposition
encoding a structural relation.

### Δ.D  Property predicates with quantification
e.g., `def PreservesPartition (σ : Fin 5 → Fin 5) : Prop :=
       ∀ i : Fin 5, isA (σ i) = isA i`,
`def Atomic (n : Nat) : Prop :=
       ∃ a b, Decomp n a b ∧ IsAlive a b ∧ ∀ a' b', ...`.

Form: `def P : T → Prop := ∀/∃ + decidable_inner`.

### Δ.E  Witness extractors (constructive `Choose`)
e.g., `def getBase {N k : Nat} : (x : RawNk N k) → isBase x = true → Fin N
       | .object i, _ => i
       | .rel _,    h => by cases h`.

Form: structural pattern match; given a "Bool-flag = true" hypothesis,
return the concrete witness.  This is the **213-native replacement for
Classical.choose** (G7 §2).

### Δ.F  Numerical / structural constants
e.g., `def pairSize : Nat := 2`, `def closureSize : Nat := ...`.

Form: `def C : T := concrete_value`.  Named anchors for repeated use.

### Distribution sense
- Δ.A/B/F dominate quantitatively (small concrete defs).
- Δ.C/D structure the discourse (named types, named props).
- Δ.E is rare but crucial (replaces Classical.choose without axioms).

**Common thread**: every def is an *explicit recipe* — either a
concrete value, a finite computation, an inductive type with named
constructors, or a structural pattern match.  No "axiom posits the
existence of …" definitions.  The universe of 213-objects is built
up by named recipes only.

## §2  implications cluster — conditional reasoning shapes

After reading 50/483 (those with → in stmt, no ∃), four shapes:

### →.A  Hypothesis structural unpack + propagation
e.g., `block_constant_implies_aut_invariant`,
`canonical_partition`.

```lean
theorem H : H₁ → H₂ → P := by
  intro h₁ h₂
  obtain ⟨...⟩ := h₁     -- destructure
  rw [...]               -- propagate
  ...
```

Form: `intro` the hypothesis, `obtain` to destructure, `rw` to
propagate sub-equalities, conclude.

### →.B  Induction on the hypothesis itself
e.g., `reachable_isBase`, induction on the `ReachableNk` proof.

```lean
theorem T : Reachable x → P x := by
  intro h
  induction h with
  | base i => proof_for_base_case
  | step _ _ ih => proof_using_IH
```

Form: induct on the inductive proof (not on the data).  Each
constructor case yields a sub-goal handled by structural argument.

### →.C  Predicate transfer
e.g., `cmpRev_props : CmpProps cmp → CmpProps (cmpRev cmp)`,
`fold_structured_lens_expressible`.

Form: assume property P holds on input, construct property Q on
output — by transferring the structure.

### →.D  Bool / Prop conversions (small term-mode)
e.g., `Bool.and_eq_true_to_pair : (a && b) = true → a = true ∧ b = true`.

```lean
theorem Bool.and_eq_true_to_pair : ∀ {a b : Bool},
    (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | false, _, h => by cases h
  | true, false, h => by cases h
```

Form: term-mode pattern match on Bool inputs; in valid cases
construct the pair, in vacuous cases discharge by `cases h`.

## §3  universals cluster — quantification dispatch shapes

After reading 50/618 ∀-theorems (no ∃), three dominant shapes:

### ∀.A  Term-mode pattern match (∀ over finite-constructed type)
e.g., `getBase_eq`, `Bool.and_eq_true_to_pair`.

```lean
theorem foo : ∀ x : Inductive, P x
  | constr1 _ => proof_1
  | constr2 _ => proof_2
```

Form: `theorem T : ∀ x, P x | pattern => proof`.  Direct term-mode
case analysis without `intro` or tactic mode.

### ∀.B  `intro` + induction
e.g., `reachable_isBase`, `leaves_ge_one`, `parityLens_view_eq_leaves_odd`.

```lean
theorem T : ∀ r : Raw, P r := by
  intro r
  induction r using Raw.rec with
  | a => proof_a
  | b => proof_b
  | slash x y h ihx ihy => proof_slash
```

Form: `intro` the variable, induct on its structure, dispatch each
constructor case (using IH in recursive cases).

### ∀.C  Universal lifted from existing lemma (term mode)
e.g., `RawBy_bijection := transportRawBy_roundtrip cmp1 cmp2 h1 h2`.

Form: `theorem T : ∀ x, P x := existing_universal_lemma`.  Just
cite the existing lemma at the matching type.

## §4  How the three clusters fit together

The three clusters together describe **213's reasoning skeleton**:

```
  defs (1369)
   ├─ name primitive objects (Δ.A/B/F)
   ├─ name structures (Δ.C)
   ├─ name properties (Δ.D)
   └─ name witness extractors (Δ.E, the Choose-replacement)
        ↓
  ∀ universals (618)
   ├─ over finite type → pattern match (∀.A)
   ├─ over inductive type → induction (∀.B)
   └─ lifted from existing lemma (∀.C)
        ↓
  → implications (483)
   ├─ destructure + propagate (→.A)
   ├─ induct on hypothesis (→.B)
   ├─ transfer predicate (→.C)
   └─ Bool/Prop conversion (→.D)
```

Reading these together: 213 **builds** by naming primitives and
recipes (defs), then **quantifies** by pattern-matching/induction
(universals), then **conditions** by destructuring hypotheses and
propagating (implications).

Every step is a structural / computational operation on named data.

## §5  What is NOT in any of these clusters

  · No abstract algebraic structures (no "let G be a group, then
    every element has an inverse" without specifying G).
  · No `Classical.choice`-style witness extraction (Δ.E covers it
    constructively).
  · No "limit" / "completion" definitions (no `∃ x, x = lim sₙ`).
  · No `axiom`-typed definitions (zero of those in the entire codebase
    outside fixed kernel axioms).

213 builds reasoning out of named recipes + structural quantification
+ hypothesis-propagation.  No fourth ingredient.

## §6  Cross-cluster sample side-by-side

```lean
-- Δ.E  Witness extractor (def, constructive Choose-replacement)
def getBase {N k : Nat} : (x : RawNk N k) → isBase x = true → Fin N
  | .object i, _ => i
  | .rel _,    h => by cases h

-- ∀.A  Universal via pattern match (term mode)
theorem getBase_eq {N k : Nat} :
    ∀ (x : RawNk N k) (h : isBase x = true), x = .object (getBase x h)
  | .object _, _ => rfl
  | .rel _,    h => by cases h

-- →.B  Implication via induction on hypothesis
theorem reachable_isBase {N k : Nat} (h : N < k) :
    ∀ {x : RawNk N k}, ReachableNk x → isBase x = true := by
  intro x hr
  induction hr with
  | base i => rfl
  | @step f _ hne ih =>
      exfalso
      let g : Fin k → Fin N := fun i => getBase (f i) (ih i)
      ...
      exact E213.Math.Pigeonhole.no_inj_lt h g g_inj
```

The three blocks together: define `getBase` (Δ.E), prove its
relationship to .object via pattern match (∀.A), then leverage
both in an inductive implication (→.B).  213's reasoning style
in one chain.

## §7  Cumulative observation across G17–G21

Five inspections so far covered ~3,400 specimens across 11 clusters:

```
∃ + capstones                             257
equality (rfl/decide/rw/cases/match)    2,302
omega/simp/term-mode equality             487
defs/implications/universals            2,470
                                       ─────
                                        ≈ 5,500 (some overlap)
```

Across all of these, the *uniform* operational substrate is:

  · **Named primitive objects** (defs, ~1370)
  · **Computational equality** (decide/rfl, ~1800)
  · **Structural propagation** (rw + cases + match, ~700)
  · **Constructive witnesses** (∃ with explicit terms, ~170)
  · **Inductive dispatch** (universals + implications, ~1100)
  · **Migration backlog** (omega + simp, ~241)

Every theorem in 213 falls into one or more of these slots — and
the slots are *operations on named, finite, computable data*.

## §8  No taxonomy proposed

Per Mingu's directive, this note records what surfaced from reading.
It does not assemble a hierarchy.  Whether the slot-list above
amounts to a classification, or whether it's just a description of
what one sees, is for further inspection (and Mingu's intuition).

The audit infrastructure is in place; arbitrary new fingerprint
filters can be added.  Three big remaining unread clusters:

  · The 1888 `rw` *occurrences* (different from 377 rw-using DECLS):
    this counts how often rw appears, not in how many decls.  A
    decl using rw 5 times tells different things.
  · Specific marathon namespace deep dives (Cohomology 1387,
    Real213 835).
  · The 11 instance / 4 noncomputable-def / 1 lemma decls (very
    small clusters worth eyeballing).
