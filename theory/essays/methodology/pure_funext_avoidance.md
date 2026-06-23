# Five patterns for closing funext-blocked theorems in PURE Lean

Making `Eq : (Nat → α) → (Nat → α) → Prop` mean "all outputs of the two functions agree"
requires `funext`, and that axiom drags `propext` along with it.  213 has *no observer who
inspects functions from outside* (`seed/AXIOM/05_no_exterior.md` §5.1), so it cannot assert
funext-style function identity directly.  Instead it gathers the pointwise facts **that they
agree at each distinguishing event** and expresses, at the structural level, *how those facts
are bundled*.  The five patterns are that bundling method.

## 213-native definition

In 213, function identity is **agreement of trajectory endpoints**.  If two trajectories
start from the same input and arrive at the same distinguishing output, those two
trajectories are *recognized as equal* — with no separate claim that the functions
themselves are equal.  The four patterns are four forms that **structurally encode** this
trajectory-endpoint agreement.

## Derivation

**State Accumulator** (`lean/E213/Lib/Math/NumberSystems/Padic/NegInvolutionFull.lean` + `NegInvolutionPreserve.lean`).  The carry-chain of `Zp.neg ∘ Zp.neg = id` looked like it would blow up polynomially.  Compressing it to a single Bool `all_zero_below x k` fixed the branching at 2 per step.  `neg_carry_eq_state` reduces the carry to a state, `neg_preserves_state` shows that `Zp.neg` preserves the state, and `zp_neg_neg_digit_at` proves `((Zp.neg(Zp.neg x)).digits k).val = (x.digits k).val` at every k.  The discovery that the *part of the trajectory that must be remembered* is always 1 bit — this is the 213-native core of the carry chain.

**Bundled Subtype** (`lean/E213/Lib/Math/NumberSystems/Real213/ValidCut/IntValidCut.lean`).  The precision-doubling artifact of `cutSum_assoc` (`cutSum (cutSum cx cy) cz` reads cx at `4k`, while `cutSum cx (cutSum cy cz)` reads it at `2k`) is blocked for a general cut.  If one bundles into the cut, via `IntValidCut := { cut, represents, is_integer }`, a cutEq proof that "it represents an integer", then both associations reduce to `constCut ((a+b)+c) 1` and `Nat.add_assoc` finishes.  The invariant is bundled *into the structure* rather than carried as a hypothesis — closing the identity trajectory at the type level.

**Setoid Category** (`lean/E213/Lib/Math/NumberSystems/Padic/SetoidFramework.lean` + `SetoidAlgebra.lean` + `ZpSqrtDSetoid.lean`).  `ZpSeqEquiv x y := ∀ k, x.digits k = y.digits k` is the decision to call pointwise agreement *equivalence of functions*.  The `Setoid (ZpSeq p)` instance makes this decision explicit at the type level, and `LensMap` bundles *equivalence-preserving* morphisms.  `zp_neg_neg_equiv_id` states that `Zp.neg ∘ Zp.neg` and `id` are *equivalent as functions* without funext.  Function identity is reduced not to `Eq` but to an *explicit equivalence relation*.

**Residual Induction** (`lean/E213/Lib/Math/NumberSystems/Padic/HenselResidual.lean`, surfacing the existing `Padic/Hensel.lean`).  An attempt to show the correctness of the Hensel-lifted inverse `Y_n` via a carry chain is blocked, but the *residual-term recurrence* of the truncation `(X_n · Y_n).trunc (n+1) = 1` bypasses the carry.  `Zp.mul_invSeq_correct` proves the truncation agreement at every level n, and `Zp.invSeq_succ_trunc_extend` expresses the level n→n+1 lift in general Nat/Int arithmetic alone.  An *algebraic* recurrence in truncation units, instead of the infinite loop of a carry chain.

**Inductive cong constructor**.  In an inductive predicate `P` with a function-typed argument, when some candidate function `candidate` is *pointwise equal to* the target `v` *but a different function literal* (a generator XOR-add construction like `candidate v = ⊕ᵢ bᵢ·gᵢ`), it appears one cannot reach `P v` without `funext`.  Solution: add to the `P` inductive type a new constructor that propagates pointwise equivalence
```
| cong (v w : EnrichedFaceVal c) (h : ∀ s t m, v s t m = w s t m) :
    P w → P v
```
— bundling pointwise equivalence *into the inductive structure itself* so that the witness propagates across the entire pointwise-eq equivalence class.  Whereas the Setoid Category reduces function identity via an *external* equivalence relation, the cong constructor embeds the equivalence *inside the inductive type* — a pointwise fact confers membership eligibility *on the spot* (the *shape* makes explicit that the predicate is defined on equivalence classes).

## Dual function

These four patterns are funext-bypass tricks of classical Lean while *at the same time* being concretizations of 213's trajectory-witness principle — 213's identity is *the distinguishing endpoints of trajectories agree*, not *the functions are equal*.  Once you strip away the packaging that funext enforces ("if two functions agree at every point they are equal"), what remains is exactly G2's trajectory-as-witness, namely the stance that *identity is the agreement of the distinguishing reached*.

## Cross-frame connections

Five expressions of the same structural fact:
  - **State Accumulator** = §5 self-pointing affects the next step *only through the current state* (no external history reference).
  - **Bundled Subtype** = type-level realization of §8.4 dichotomy avoidance (bundling the assumption into the structure rather than leaving it as an external hypothesis).
  - **Setoid Category** = defining identity as an *internal relation* with no separate external adjudicator.
  - **Residual Induction** = G2 trajectory-as-witness operating on truncation instead of the carry chain.
  - **Inductive cong constructor** = embedding the equivalence class *inside* the inductive structure — whereas the Setoid pulls an external relation up to the type level, cong makes the equivalence itself one case of the inductive type (the *shape* makes explicit that the predicate is defined on equivalence classes).

All five patterns derive from the same 213-native stance that *identity is inferred from internal consistency*.  The absence of funext is not a *defect* but the direct result of the *stance* that 213 does not cede function identity to an external observer.

## Closed follow-ups

Both follow-ups from the time the original essay was written are now closed:

- **Abstracting Zp.add associativity into a LensMap composition law** — `Lib/Math/NumberSystems/Padic/SetoidAssoc.lean` (8 PURE).  Reduces associativity to truncation units via `Zp.add_trunc` (Residual Induction), extracts digit-equality via `digits_eq_of_trunc_eq`, and `zp_add_setoid_monoid_capstone` bundles the entire monoid structure (assoc + comm + zero) at the Setoid level (`zp_add_setoid_group_capstone` adds `x+(−x)≈0` to complete the additive abelian group).  Core: trunc-level associativity is the `Nat.add_assoc + add_mod_gen` chain.

  - **Up to a commutative ring — the multiplicative Setoid identities** (`SetoidMul.lean`, 7 PURE).  Applying the same `of_trunc_all` lift to the multiplication ring-quotient theorems (`Zp.mul_trunc_comm`/`mul_trunc_assoc`/`mul_add_trunc`/`add_mul_trunc`, and `mul_trunc_one_left`) closes `zp_mul_comm_equiv`/`zp_mul_assoc_equiv`/`zp_mul_one_left_equiv` (multiplicative commutative monoid) + left/right distributivity (`zp_mul_add_distrib_equiv`/`zp_add_mul_distrib_equiv`) at the Setoid level.  `zp_setoid_commRing_capstone` bundles the additive abelian group + multiplicative monoid + distributivity into one theorem, stating that **`(ZpSeq p, ZpSeqEquiv)` is a commutative ring** without funext/propext.  Combined with `SetoidAlgebra.mul_respects` (that multiplication itself preserves `ZpSeqEquiv`), this is the full ring structure on the quotient.

- **Pushing `cutSum_assoc` beyond integer-extended** — `Lib/Math/NumberSystems/Real213/ValidCut/HalfValidCut.lean` (11 PURE).  Extends IntValidCut(b=1) to HalfValidCut(b=2).  Since `cutSum_half_general` provides bidirectional cutEq at b=2 too, the same pattern (bundled subtype + Nat.add_assoc) gives closure.

## b ≥ 3 cutSum_assoc — progress of the diagnosis

The backward direction at `b ≥ 3`, originally classified as "write a new theorem", is a *hardcode artifact of the cutSum implementation*.  `Lib/Math/NumberSystems/Real213/Sum/CutSumAssocB3.lean` (7 PURE) documents the phenomenon:

  · **Forward universal**: `cutSum_same_denom_forward` holds at any `b ≥ 1`.
  · **Backward counterexample** at `b ∈ {3, 4, 5}`: for example, at `a = 2, c = 1, b = 3, m = 1, k = 1`, `constCut 3 3 1 1 = true` but `cutSum (constCut 2 3) (constCut 1 3) 1 1 = false` (decide-verified).
  · **Eventual agreement**: at sufficient precision such as `m ≥ 10`, both sides agree.
  · **Meta capstone** `b_ge_3_assoc_meta`: bundles the above 4 into one theorem.

Detailed analysis in `essays/bool_assoc_failure_meaning.md`.  Core: `cutSum`'s factor-2 hardcode reflects only NT of the (NS, NT) = (3, 2) atom and drops NS.  Not a problem "outside" the framework but the cutSum implementation *under-realizing 213's (3, 2) commitment* — `Physics/Foundations/AtomicConstantsParametricFullIff.lean` `c2b_full_iff` + `Theory/Atomicity/Five.lean` `atomic_iff_five` already prove the (3, 2) → every real decision chain.

**Closure progress**: `Lib/Math/NumberSystems/Real213/Sum/CutSumN.lean` (6 PURE) defines the parametric `cutSumN N` (factor-N search granularity) + proves `cutSumN_same_denom` bidirectional at any N > 0.  `Lib/Math/NumberSystems/Real213/ValidCut/ThirdValidCut.lean` (15 PURE) closes b = 3 associativity via the IntValidCut/HalfValidCut pattern — `cutSumN_assoc_thirdValidCut` (full assoc), `cutSumN_comm_thirdValidCut`, `thirdvalidcut_full_assoc_capstone`.  `cutSumN_3_2_1_at_1_1` decide-verifies that the CutSumAssocB3 counterexample (a=2, c=1, m=1, k=1) is true under `cutSumN 3`.

Open: the `is_native` wrapper (the `b ∈ ⟨2, 3⟩` multiplicative monoid gate) — the closure for each of b ∈ {1, 2, 3} is closed, but a unified wrapper for general multiplicative composites (b = 6, 9, 12, ...) is a follow-up.

## Provenance

These four patterns were proposed as *architectural-level prescriptions* in a consultation with an external LLM (Gemini Pro), and were implemented as-is in PURE Lean.  The consultation prompt specified 5 blockers together with concrete Lean files / theorems / tried-and-failed paths; the response was 4 patterns + 1 long-term item (higher cohomology).  46-chapter closure / 550 PURE / 0 DIRTY was the result of this single consultation cycle.

| Pattern | Lean realization | Blocker |
|---|---|---|
| State Accumulator | `NegInvolutionFull` + `NegInvolutionPreserve` | Zp.neg involution |
| Bundled Subtype | `ValidCutFramework` + `IntValidCut` | cutSum_assoc |
| Setoid Category | `SetoidFramework` + `SetoidAlgebra` + `ZpSqrtDSetoid` | funext-free function eq |
| Residual Induction | `HenselResidual` (surfacing `Padic/Hensel`) | Hensel correctness |
| Inductive cong constructor | add a pointwise-eq `cong` case to the inductive predicate | function-typed argument candidate-to-target bridge |

A case where, even without the external LLM explicitly knowing 213's stance, an architectural insight into the same structural problem of *how to handle extensionality inside MLTT* translated straight into a 213-native realization.

## The sister chapter on the Lens-arrow side — Pattern P1 ↔ Inductive cong constructor

`theory/lens/dirty_recovery_patterns.md` presents five patterns (P1-P5) that reduce DIRTY (propext / Quot.sound) to a PURE Lens-arrow statement.  They are at **a different layer but the same structure** as this essay's five patterns:

  · **P1 (Lens-Eq → LensIso via eqPW)** ↔ this essay's **Inductive cong constructor**.  P1 reduces the funext-requiring claim `L = M : Lens α` to `LensIso L M` (= `∀ x y, L.equiv x y ↔ M.equiv x y`), and the bridge `lensIso_of_eqPW` closes it using only a pointwise eq proof + a symmetric-combine assumption.  The Inductive cong constructor generalizes the same *pointwise-equality-as-bridge* principle to an arbitrary inductive predicate (when the predicate has a function-typed argument) — `InPrimaryCupSpanPlusBoundary` is its example.
  · P2 (mutual morphism → LensIso): sister of the Setoid Category — applies where a *mutual morphism pair* is natural instead of *making the equivalence explicit as an external relation*.
  · P3 (Quot → LensImage): a Lens-level variant of the Bundled Subtype — a Σ-type representation avoids `Quot.sound`.
  · P4 (slash-cong claim → kernel inheritance): separates out the `=`-form of the universalLens reverse direction — distinguishing the recoverable region from the sealed `=`-shim.
  · P5 (Prop-codomain Lens-`equiv` → `equivR` / `refinesR`): the 213-native meaning of "identical under L" is pointwise `↔` (distinguishing-equivalence) and is PURE.  `view x = view y` (Lean `=`) imports Prop/function identity additionally — showing that the universalLens reverse direction is not a structural but a statement-shape cost (`universalLens_kernel_eq_E_R` PURE).

The two directions (Padic / Real213 vs Lens-algebra) derive from the same *pointwise-distinguishing-as-equivalence* principle.  Just as the Lens-arrow is the single concept of unified_equivalence.md (the 213-native unified object of equivalence / equivalence class / isomorphism / homomorphism), **the cong constructor is the form in which that same single concept manifests at the inductive predicate level** — the *internal structure* expressing equivalence-class closure without external axioms.
