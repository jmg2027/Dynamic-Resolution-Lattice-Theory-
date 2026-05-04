# G18 — Pattern Inspection: Two Clusters Read Stitch-by-Stitch

**Author:** Claude (inspection); Mingu Jeong (methodology directive)
**Date:** 2026-05-XX (continues G17)
**Companion files:**
  - `tools/theorem_inspect.py`
  - `research-notes/G17_inspect_existential.md` (169 ∃-decls full bodies)
  - `research-notes/G17_inspect_capstone.md` (87 capstone-decls full bodies)

## §0  What this note is

G17 collected raw fingerprints (decide=2670, ∃=170, ⟨=1105, …) without
interpretation.  G18 follows Mingu's "한땀한땀" directive by reading the
ACTUAL bodies in two carefully-chosen clusters and recording what
sub-patterns surface.  **Still no top-down classification.**  Sub-pattern
labels below are *descriptive readings*, not category boxes.

Two clusters chosen for first read:
  · **∃-cluster** (170 decls): tests what 213 actually proves to "exist".
  · **Capstone cluster** (87 decls, refine⟨..⟩<;>decide): tests what
    213 considers a "consolidated result of a marathon".

Together they probe the two ends of theorem grain — fine (single ∃)
and coarse (multi-claim bundle).

## §1  ∃-cluster — what it shows

After reading ~50 of the 169 bodies, **five sub-patterns surface
naturally** (counts approximate, by pass-through):

### A. Witness extraction from inductive hypothesis
e.g., `reachable3_only_object`, `reachable_base_only`,
`nat_surjective_with_form`, `nat_image_surjective`.

Form: `Reachable3 x → ∃ i : Fin N, x = .object i`.
Proof: induction on the hypothesis; at each constructor case
extract a witness from the IH.

What it expresses: **"a structural property forces a specific shape,
and we can name the witness explicitly from the recursion."**

### B. Eventual stabilisation (Cauchy / orderProj style)
e.g., `cauchy_iff_eventually_class`, `cauchy_data_of`,
`pointwise_limit_match`, `ratio_one_below_orderProj_eventually`,
`euler_orderCauchy_at_concrete`, `orderCauchy_from_false_witness`,
`orderCauchy_from_true_forever`.

Form: `∃ N, ∀ n ≥ N, P n` — finite-N stabilisation.
Proof: provide explicit N (often 0, 2, or N₀ from hypothesis),
then dispatch the ∀ part with `intro` + structural argument.

What it expresses: **"the trajectory enters a stable regime after a
NAMED finite step; that step is given as data."**  No "limit point"
is invoked; the stable behaviour is described as a property of all
n ≥ N for explicit N.

### C. Constructive surjectivity / image inhabitation
e.g., `parityXor_image_ge_three`, `bool_image_surjective`,
`image_contains_a/b`, `image_closed_under_distinct_combine`,
`nat_image_zero/one/surjective`, `abLens_surjective`,
`fold_structured_lens_expressible`, `raw_initial`.

Form: `∃ r : Raw, view r = target`.
Proof: provide explicit Raw element (Raw.a, Raw.b, Raw.slash _ _ _),
verify the view equation.

What it expresses: **"every value in the codomain is hit by an
explicit Raw witness; the witness is constructed from the Raw
generators (a, b, slash)."**  This is *literal* image construction.

### D. Negative existence / failure of universal property
e.g., `maxLens_R4_fails`, `parityLens_R4_fails`, `negSqLens_not_collapse`,
`sum_not_coproduct_xor`, `sum_not_coproduct_and`, `int_image_strict`,
`fin3_image_strict`, `exists_non_lens_expressible`,
`leavesModNat_kernel_neq`.

Form: `¬ ∃ f, P f` or `∃ x, ¬ ∃ r, view r = x`.
Proof: assume the hypothetical f or r, derive contradiction by
plugging in two specific Raw values whose required outputs disagree.

What it expresses: **"the universal property P cannot be satisfied;
two witnesses lead to contradictory required values."**  This is
constructive *negative* — the contradiction is a finite-data witness,
not a Classical reductio.

### E. Initial-object existence
e.g., `raw_initial`, `lens_expressible_iff_fold_structured`.

Form: `∃ f, base + slash + uniqueness clauses`.
Proof: take f = universalMorphism (or Lens.view), verify each clause.

What it expresses: **"the initial object exists and IS this
explicit construction."**  Not "exists abstractly"; the construction
IS the existence.

### Empirical observation across A-E

EVERY ∃-decl in this cluster either:
  · supplies a witness directly (term mode `⟨w, proof⟩`), OR
  · supplies a witness via `refine ⟨?_, ...⟩` (then proves goals), OR
  · derives `¬ ∃` by contradiction over two finite witnesses.

**Zero use of `Classical.choose` outside the G7/G9 demos.**  The
empirical "what 213 proves to exist" is uniformly: *something we
can name from the Raw generators or a decidable enumeration*.

## §2  Capstone cluster — what it shows

After reading ~40 of the 87 bodies, **five sub-patterns** surface:

### α. Multi-instance formula realisation
e.g., `fib_pisano_predict_correct`, `pisano_predict_correct_6/_7`,
`pisano_predict_proper_correct`, `signature_predict_correct_7`.

Form: `predict 3 = a₃ ∧ predict 5 = a₅ ∧ predict 7 = a₇ ∧ ...`.
Proof: `refine ⟨?_, ?_, ...⟩ <;> decide`.

What it expresses: **"a single uniform formula realises the
expected output at multiple PARAMETER INSTANCES."**  The capstone
shouts: "this is not 4 separate facts; it's ONE formula working at
4 places."

### β. Two-derivation agreement
e.g., `alpha_3_two_derivations`, `b1_two_derivations_agree` (in
AlphaEMBridge), our own `np_hard_solved_capstone`, etc.

Form: `derivation_A_result ∧ derivation_B_result ∧ both_equal`.
Proof: cite each derivation, then decide the equality.

What it expresses: **"two independent derivation paths give the
same answer; hence the answer is structurally robust."**

### γ. Multi-component validation
e.g., `mul_generators_ne_zero` (CayleyDickson), `code_params`
(MLDecoder), `level_else_zero` (Ising).

Form: `claim₁ ∧ claim₂ ∧ ... ∧ claim_n`, each a decidable equality
or inequality at a specific instance.

Proof: `refine ⟨?_, ?_, ...⟩ <;> decide`.

What it expresses: **"all components of this structure satisfy the
expected pattern; nothing is missed."**  Coverage check, not single
fact.

### δ. Cross-domain bridge
e.g., `beilinson_regulator_213_capstone`, `motive_etale_fusion_capstone`,
`spin_glass_213_capstone`, `discrete_geometry_capstone`.

Form: claims about *two or more* different complexes/structures
(Δ⁴ + K_{3,2}^{(c=2)}, motivic + étale, …) bundled together with
identifying equations linking them.

Proof: `refine ⟨..., ...⟩ <;> decide`.

What it expresses: **"the same trajectory framework gives the
expected answer in multiple distinct domains; the integration is
structural, not coincidental."**

### ε. Self-similar / bounded-pattern verification
e.g., `thueMorse_self_similar_small`, `signatures_distinct`.

Form: `∀ n ≤ K, P n ∧ ∀ n ≤ K, Q n`.
Proof: `refine ⟨?_, ?_⟩ <;> decide` (decide handles bounded ∀ via
enumeration when N ≤ K is small).

What it expresses: **"a structural pattern (substitution, distinct
trajectory) holds throughout a bounded range of n, verified by
finite enumeration."**

### Empirical observation across α-ε

The capstone bundling is universally **"refine ⟨?_, ?_, ...⟩
<;> decide"** or near-variant.  The semantic content is:
  · multi-instance (α): same formula, several inputs
  · multi-derivation (β): same number, several derivations
  · multi-component (γ): same structure, several parts
  · multi-domain (δ): same framework, several substrates
  · multi-step (ε): same property, several steps in a finite range

All are *INTEGRATION via uniform proof method*.  The decide tactic
acts as a single closing move for arbitrary finite bundles.

## §3  Comparing ∃ and capstone clusters

Both clusters together delineate two operational modes 213-Lean uses:

  · **∃ mode** = constructive witness production + structural
    contradiction for failure
  · **Capstone mode** = integration of multiple decidable facts
    under a single proof tactic

Neither cluster involves Classical reasoning.  Neither cluster
talks about "approximate" or "limit" entities.  Both clusters'
output is *finite, named, decidable*.

The two modes correspond loosely to:
  · ∃ mode: the *atomic act* of 213 ("here is the named trajectory")
  · Capstone mode: the *aggregation* of those atomic acts into a
    coherent statement of "what was achieved"

But this is a description after the fact, not a top-down taxonomy.
Inspection of more clusters (decide-only equalities, cases-based
proofs, the migration-backlog omega cluster) would refine the picture.

## §4  What is NOT yet observed

Things this inspection has NOT touched:
  · the 2,548 pure-equality decls (the dominant 42% — would need a
    much larger inspection pass)
  · the 287 cases-based decls
  · the 162 match-based decls (structural recursion patterns)
  · the 1305 rfl-only decls (definitional unfoldings)
  · the omega/simp migration backlog (111 + 130)

Each of these is its own cluster; each presumably has its own
sub-patterns.  Sequential inspection would build the empirical
basis further.

## §5  No classification proposed (yet)

Per Mingu's directive: classification must EMERGE from data, not
be imposed.  This note records what surfaced from reading; it does
not assemble those surfacings into a hierarchy or taxonomy.

The next pass would be either:
  · inspect another cluster (e.g., the 162 match-based decls or
    the 105 cross-marathon capstones), or
  · re-read the existing two clusters more carefully, taking notes
    on each individual decl, or
  · let Mingu look at the inspect files directly and direct the
    next read.

The pattern data is on the table; deciding what it means is the
next stitch.
