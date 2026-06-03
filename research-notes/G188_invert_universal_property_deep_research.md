# G188 — Deep research on the invert move: the universal property and what it forces

**Date**: 2026-06-03.  **Method**: 4-agent adversarial deep research (world-class-algebraist
framing) on this session's number-tower founding, each agent pushing one facet + flagging
PROVABLE / NARRATIVE / STEREOTYPE.  Result: **4 new ∅-axiom theorems**, two rejections.

## The four facets and their verdicts

### 1. Universal property of the invert move → PROVABLE (the deepest result)
`PairCompletion.invert_is_one_move` was a conjunction of properties; it did not *characterize*
the construction.  The universal property does: the pair-completion is **the** group receiving
the semigroup, through which every map to an abelian group factors.  Built ∅-axiom, Quot-free,
on representatives respecting `pairEquiv` (the repo's native factor-through style,
`Lens/Initiality.view_unique`, not an imported `Functor`/`Adjunction`):

- **`PairCompletionUniversal.lean` (15 PURE)** — `AbTarget` (abelian-group target, laws as
  ∀-equalities, no Mathlib/funext); `lift M H f (a,b) = f a − f b`.  **Existence**:
  `lift_respects_pairEquiv` (well-defined on the completion), `lift_combine` (homomorphism),
  `lift_eta` (factors `f` through `η m = (m∘a, a)`); `invert_factors_through_any_group`.
  **Uniqueness** (now closed, choice-free): `lift_unique` — any `g` respecting `pairEquiv` +
  `combine` + `η` equals `lift`, via `pair_equiv_eta_combine` (every pair `~ η(a) ∘ inv(η(b))`).
  Capstone `invert_is_the_universal_group_completion` = existence ∧ uniqueness.  Toolkit
  `ab_neg_add`, `ab_add_add_add_comm` (middle-four interchange), `ab_add_{left,right}_cancel`,
  `ab_neg_unique`.
- **STEREOTYPE flagged**: "left adjoint to the forgetful functor `AbGroup → CommCancelSemigroup`"
  imports a 2-categorical frame the residue does not supply — keep in narrative only.  The
  *content* (initiality = concrete factoring map + uniqueness) is native, matching
  `Theory/Raw/Lambek` (initiality as `decompose`/`build` round-trip, not a functor category).
- **Uniqueness**: holds for any `g` that respects `pairEquiv`/`combine`; unconditional uniqueness
  needs choice on the fiber (`Lens/Compose/Factoring.lean:17` "converse requires AC") — left as
  the hypothesized companion, not attempted.

### 2. Tower as a diagram of universal constructions → NARRATIVE (real, but not a Lean object)
All three moves *are* universal constructions: count = initial algebra (`Lambek.two_closures`,
`Lens/Initiality.view_unique`), invert = group completion (above), complete = idempotent Cauchy
fixpoint (`CompletionTower.completion_idempotent`).  The honest SHAPE is a **diagram with a
`ℤ ⊥ ℚ_+` branch**, not a chain.  Pinned in Lean:

- **`PairCompletion.invert_branch_two_distinct_instances`** — `addCCS` and `mulCCS` differ
  (`add 1 1 = 2 ≠ 1 = mul 1 1`) yet share the emergent diagonal identity; the two inverse-axes
  are orthogonal instances of one move, joined at the diagonal, not serialized.

- **STEREOTYPE flagged**: "lattice of adjoints" does NOT unify the three axis-vocabularies
  (refines-breadth / depth `(h,d)` / CD-grade) — it is a *fourth* vocabulary; forcing them under
  "adjoints" is the External-classification failure.  It also does not contradict the shared-unit
  resolution: **adjoints relate the OBJECTS (rung to rung); the unit relates the READINGS (axis
  to axis)** — orthogonal claims; the unit is the answer to "how many axes?".

### 3. `(unit, period) = (1, 2)` → mostly NUMEROLOGY, one genuine factorization
The decomposition `NS = (NS−NT) + NT` is just `ns_is_succ_nt` (`NS = NT+1`) re-read; `1·2`,
`1+2`, `2²−1=3=N_gen` are numerology (no structural Lean theorem); the physics routing is
overreach.  The ONE genuine result, salvaged and proven:

- **`CassiniUnimodular.multiplier_unit_magnitude_sign_order_NT` + `qpow_one` (13 PURE)** — the
  unimodular multiplier `q = ±1` factors as (unit magnitude, order-`NT` sign): the golden
  `q = +1` conserves the determinant (`qpow 1 n = 1`); the swap `q = −1` has order **exactly**
  `NT = 2` (`qpow (−1) NT = 1`, `qpow (−1) 1 ≠ 1`).  The two shared invariants (unit `1`, residue
  size `NT`) are the magnitude and sign-order of the *one* multiplier.

### 4. Unit-free emergence = no-exterior → UNIFICATION REAL (at the principle level)
The group identity emerges as the diagonal with NO base unit (`Nat213` has no additive `0`,
`Peano.no_additive_identity_at_one`) — the no-exterior principle (`05_no_exterior §5.1`) realized
inside a Lens-readout.  Completed the law:

- **`PairCompletion.diagonal_is_combine_identity`** — the diagonal *is* the `combine`-identity
  (`combine (k,k) p ~ p`), the missing half of `combine_swap_equiv_diagonal`.  Together:
  **identity = swap-fixed diagonal = combine-identity, emergent, unit-free**, generic over
  `CommCancelSemigroup`.
- Connection to Lambek = analogy of KIND (fixed-locus-of-the-closure-map, internally generated),
  NOT the same object (µF-of-endofunctor ≠ Fix-of-involution).  **Boundary held**: the emergent
  unit is a READOUT (inside a view's image), NOT the residue (outside every view's image,
  `FlatOntologyClosure.object1_not_surjective`).  Calling it "the residue" would be the
  view-promoted-to-identity failure.

## Cross-marathon convergence (emergent, not designed)

The concurrent non-holonomicity session independently bridged its discriminant dial to this
founding work (`FoundingDynamicBridge`: the founding swap = the dial's elliptic floor `S`).
Deepened here to the whole dial (`FoundingDialUnification.founding_unit_floors_dial_trace_runs_tiers`,
1 PURE): the two marathons split the order-2 companion `comp p q` along its coordinates — the
**founding fixes the determinant** (`= q`, the unit `NS − NT`), the **dial varies the trace**
(`disc = p² − 4q`); and the forced atomic counts are the tier boundaries (`p = 0` elliptic swap,
`p = NT` parabolic, `p = NS` hyperbolic golden with `disc = d`).  Parametric: det-floor +
trace-dial.  Atomic (pins `NS = 3`): `p = NT`/`p = NS` landing on the tiers.

Deepened further (`parabolic_at_NT_is_difference_lens_depth1`): the **parabolic tier (trace `NT`)
is the difference-Lens rung** — `liftKZ 1 s n = s(n+1) − s n` is the `ℤ`-difference, and parabolic
⟺ that output is constant (`polyDepthZ 1`, depth-1).  Full tier↔rung correspondence, **complete in Lean**:
`ℤ`-sign = elliptic (period-2 swap), `ℤ`-difference (depth-1) = parabolic
(`parabolic_at_NT_is_difference_lens_depth1`), `ℚ`/`ℝ` ratio/Cauchy = hyperbolic
(`hyperbolic_at_NS_is_ratio_cauchy_rung`: det = unit `NS−NT`, convergents' cross-det = same unit,
completing to `φ`).  `ℕ` (count) is the base they are read from.  The founding number-rungs *are*
the discriminant tiers — two marathons, one structure.

## Net new theorems (all ∅-axiom, 0 dirty)
| Theorem | Module | What it forces |
|---|---|---|
| `invert_is_the_universal_group_completion` (+ `lift*`, `lift_unique`, 15 PURE) | `PairCompletionUniversal` | invert = THE universal group completion (existence ∧ uniqueness, choice-free) |
| `diagonal_is_combine_identity` | `PairCompletion` | emergent unit = swap-fixed diagonal = combine-identity |
| `invert_branch_two_distinct_instances` | `PairCompletion` | `ℤ ⊥ ℚ_+`: two instances, one move, joined at the diagonal |
| `multiplier_unit_magnitude_sign_order_NT` | `CassiniUnimodular` | det multiplier `±1` = (unit magnitude, order-`NT` sign) |

## Carryover / open
- **Uniqueness — CLOSED** (`lift_unique`, choice-free) via the representative-canonicalization
  `pair_equiv_eta_combine` (every pair `~ η(a) ∘ inv(η(b))`).  The full universal property
  (existence ∧ uniqueness) is `invert_is_the_universal_group_completion`.  The only AC issue was
  for `g`'s that do *not* respect `pairEquiv` — but those are not maps on the completion at all,
  so the hypothesis is not a restriction, it is the definition of "map on the completion".
- **Int instantiation — DONE** (`intTarget`, `natToInt_hom`, `liftZ`, `addCCS_completion_is_Int`):
  the additive completion of `(Nat213, +)` is `ℤ` — `liftZ` is the integer-difference map,
  `(2,1) ↦ +1`, `(1,2) ↦ −1`, and by the capstone it is the unique factoring hom.  The universal
  property is non-vacuous.  (A `mulCCS → QPos` instance would need a concrete `ℚ_+` group type,
  which the repo does not have — the pair model `NatPairToQPos` is itself that type.)
- The "diagram of universal constructions" is narrative; if ever formalized it must NOT be a
  "lattice of adjoints" (4th vocabulary) — stay with the shared-unit (downward) unification.
