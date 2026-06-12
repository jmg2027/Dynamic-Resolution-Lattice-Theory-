# STRICT ∅-AXIOM — the 213 axiom standard

> **Canonical definitions (single source of truth):** see "Terms"
> section below.  When other documents (HANDOFF.md, CLAUDE.md,
> scan_all_axioms.py comments) drift from these definitions, this
> file wins.  Falsifiability anchor: `seed/AXIOM/08_falsifiability.md` §8.2.

## Terms (canonical)

| Term | Definition |
|---|---|
| **PURE** | `#print axioms <thm>` returns "does not depend on any axioms".  Identical to "strict ∅-axiom".  This is the standard target. |
| **DIRTY** | `#print axioms` returns "depends on axioms: [...]" with a non-empty list.  Any of `propext`, `Quot.sound`, `Classical.choice`, `Lean.ofReduceBool` (from `native_decide`), `sorryAx`. |
| **sealed-DIRTY-by-design** | A DIRTY theorem accepted because (a) Lean-core boundary (well-founded recursion, Lean.Elab metaprogramming inheriting Classical.choice via the Lean.Elab.Command monad), or (b) Lens funext-by-design (higher-order Lens equality requires funext on the combine field, refactoring would redefine what "Lens equality" means).  Listed in `tools/scan_all_axioms.py` `SEALED_DIRTY_PREFIXES`. |
| **real DIRTY** | DIRTY ∧ NOT sealed-by-design.  This is the regression budget. |

**The 213 axiom set is ∅** — a theorem meets the standard iff PURE.

**Forbidden absolutely** (per `seed/AXIOM/08_falsifiability.md` §8.2, falsifiability
trigger): `Classical.choice` and `Lean.ofReduceBool` in **213
mathematical content** (theorems about Raw, Lens, observables).
Tactic files (`E213.Meta.Tactic.*`) that inherit Classical.choice
purely via the Lean.Elab.Command monad are *plumbing*, not 213-math
content; sealed under (a) above with explicit justification.

**Always allowed but not target**: `propext` and `Quot.sound` are
part of the Lean 4 core kernel base.  213 aims to avoid them where
possible (PURE target) but does not falsify if a result requires
them via Lean-core well-founded recursion proofs.

---

## Sealed-by-design categories

The seal list in `tools/scan_all_axioms.py` waives modules whose
DIRTY status is *structural* — refactoring would redefine what the
module is, not improve its derivation.  Any DIRTY outside this list
is a real regression.

### (a) Prop-as-distinguishing thesis — `propext`

`HasDistinguishing` is the typeclass for "framework instance: a
type with a/b/combine such that True ≠ False analogue holds and
combine is symmetric."  When the type is `Prop`, the field
`combine_sym : combine P Q = combine Q P` is a propositional
equality between Props — provable in Lean 4 only via the kernel
axiom `propext`.

Sealed modules:

  · `E213.Lens.SemanticAtom`
      `propAsDistinguishing` + `propAsDistinguishing{And, Or, Iff}`
      use `combine = propXor / And / Or / Iff`; `combine_sym` is
      `(P * Q) = (Q * P)` at type `Prop`.  Carries `iff_comm_eq`
      and `propXor_comm` for the symmetry lemmas.
      `canonical{Truth, And, Or, Iff}Map_*` are derived via
      `universalMorphism_*` and inherit the propext use.

  · `E213.Lens.Properties.Morphism.BoolProp`
      `boolToProp : Bool → Prop` is `b ↦ (b = true)`.  Theorems
      `boolToProp_true / false / and / or / xor / iff` and
      `universalMorphism_commute*` equate Props (e.g. `boolToProp
      (and x y) = (boolToProp x ∧ boolToProp y)`) — propext.

The thesis "Prop is an atom of meaning" *is* what `propext`
expresses.  Removing the seal would require removing Prop as a
HasDistinguishing instance, which removes the thesis.

### (b) Lens kernel as function-`=` of views — `Quot.sound` (= `funext`) + `propext`

`Lens.combine : α → α → α` for the universal / indexed / Cauchy
Lens family is function-valued — `α = Raw → β` or `α = (i : ι) →
...`.  Then `Lens.combine_sym : combine x y = combine y x` becomes
a function equality, which in the Lean 4 kernel is `funext`,
derived from `Quot.sound`.  `Lens.equiv` on Raw is the same
pattern at one level up: it states `L.view r = L.view r'` at type
`Prop` (Iff↔Eq via propext) and `Lens.refines` says
`L.equiv r r' → M.view r = M.view r'` (function equality on
view).  Both patterns inherit propext + Quot.sound from the kernel.

This category is a **statement-shape** cost, not a redefinition cost,
and the universalLens refinement surface is **retired from it**.  The
213-native meaning of "the same under `L`" is the
distinguishing-equivalence — pointwise `↔` — carried by the
codomain-polymorphic Reading-equivalence API in `Lens/ReadingEquiv.lean`:

  · `ReadingEq α` — per-codomain reading-sameness (`=` at the default
    instance, pointwise `↔` at `Raw → Prop`), an equivalence relation,
    laws PURE;
  · `Lens.equivG` / `Lens.refinesG` — codomain-polymorphic equivalence /
    refinement, reducing **definitionally** to `equiv` (default) and
    `equivR` (`Raw → Prop`);
  · `Lens.equivG_slash_congruence` — the slash-congruence, generic over
    the codomain.

The load-bearing hub `universalLens_kernel_eq_E_R` (`equivR r r' ↔ E r r'`)
plus the closure companions `universalLens_recovers_R` /
`universalLens_idempotent_R` (built on `universalLens_equivR_slash_congruence`
/ `combine_cong_pw` / `fold_pw`) are PURE, and **every consumer is stated on
this API** — the refinement lattice (`Join`, `IndexedJoin`, `FamilyMeet`,
`FamilyJoin`), the Cauchy limit Lens, the kernel↔slash-congruence bijection
(`Corresp`), the choice-as-Lens-spec, and the canonical-form / idempotence
theorems (`CanonicalForm`) are all ∅-axiom.  The `=`-of-view-functions forms
are gone; the only `=`-cost is the single isolated bridge
`Lens.equivR_to_equiv` (the `↔ ⟹ =` direction, kept by design).  Only
`propAsDistinguishing` (category a) remains irreducible by thesis.  See
`theory/lens/dirty_recovery_patterns.md` Pattern P5 and
`theory/lens/unified_equivalence.md`.

Remaining sealed module in this category:

  · `E213.Lens.Instances.Leaves.DepthJoin`
      Three-tier classification of `Raw` via `JoinEquiv
      Lens.leaves Lens.depth` (a `Nat`-valued lens family).  The 10
      tier invariants (`small_invariant`, `tier_invariant`,
      `class_of_a_iff_small`, `three_classes_distinct`, `tierLens_*`,
      `depth_refines_tierLens`, `leaves_refines_tierLens`,
      `joinEquiv_subset_tierLens`, `leaves_depth_join_not_universal`)
      carry `propext` / `Quot.sound` from the `omega` / `simp`-closed
      arithmetic helpers, **not** from the refinement API — this is the
      `omega`/`simp`→explicit purification playbook (cf. `Mobius213.Px`),
      a separate backlog from the Reading-equivalence rebuild.

### Net effect

Scope note: until the build gate was made comprehensive, only the
umbrella-reachable subset was ever scanned, and that subset was fully PURE
(non-sealed).  The comprehensive gate now scans **all 1532 modules**, which
exposes the purity status of the previously-ungated clusters.  Current
`tools/scan_all_axioms.py`:

  · The 213-mathematical core is ∅-axiom.  The only non-sealed `propext`/`Quot.sound`
    that remains is the **`Prop`-atom thesis surface**
    (`propAsDistinguishing*` / `canonical*Map` / `BoolProp.universalMorphism_commute_*`,
    category (a) — `propext` IS "`Prop` is an atom of meaning").  The **CayleyDickson
    category-D backlog is closed** (2026-06-01): `Trig.conj_mul_anti` via the
    `NonAssocStarRing213 Sedenion` bridge (`SedenionAlgebra213`), and
    `SedenionHeavy.flexible` via the `CDDoubleFlexible` cross-pair +
    `FlexAlt213 Cayley` — both verified PURE (`#print axioms`).  The Lens ring is
    **0 real DIRTY** (`scan_all_axioms.py --filter Lens`): its equivalence surface is
    stated on reading-equivalence (`ReadingEq.same` / `equivR` / `sameLens`), not `=` of
    views.  Run `tools/scan_all_axioms.py` for the live count.
  · **No `Classical.choice` and no `Lean.ofReduceBool` (`native_decide`) in any
    213-mathematical content** — the falsifiability-forbidden axioms are absent.
    The only `Classical.choice` carriers are three `CommandElab` elaborators
    (`Lib.Math.Tactic.QuadExtension`, `Meta.Tactic.{DeriveConjugationCodomain,
    VerifyConjugation}`), inherited via the `Lean.Elab.Command` monad — sealed
    plumbing per category (a), not math content.
  · The remaining real DIRTY are **`propext` / `Quot.sound` only** (the
    "allowed-but-not-target" core-kernel axioms) — the `Prop`-atom thesis surface
    (category B).  The CayleyDickson category-D items (`Trig.conj_mul_anti`,
    `SedenionHeavy.flexible`) are now both closed.  The category-D backlog uses the `Mobius213.Px` playbook
    (`omega` → `rfl`/`Nat.two_mul`/`Nat.add_right_comm`; `Nat.mul_assoc`/`Nat.add_mul`
    → `NatRing.nat_*`; `simp` → explicit `rw`; `Nat.mul_lt_mul_left`/`mul_lt_mul_right`
    (the `Iff`) pull `Classical.choice` → constructive `c*m+1 ≤ c*m+c ≤ c*n` helper,
    cf. `KerSizeUniversal.mul_lt_mul_left_pure`) + the Int/`same` playbooks
    (`Meta/Int213`, `ReadingEq`/`sameLens`).
  · **Gate vindication**: closing the build-gate hole exposed a genuine
    falsifiability violation that had been invisible — `KerSizeUniversal`'s
    `Classical.choice` (via `Nat.mul_lt_mul_left`) in an orphaned cluster, now
    fixed.  A gate that only follows umbrella imports cannot guarantee the
    ∅-axiom standard; the comprehensive build is required.
  · **Sealed-by-design** per categories (a) + (b): the Prop-as-distinguishing
    family + the three CommandElab plumbing modules.  **213-native re-reading
    (not just ∅-axiom)**: only the **3 CommandElab** + `propAsDistinguishing` are
    *irreducible*.  The 3 CommandElab inherit `Classical.choice` via the
    `Lean.Elab.Command` monad (no `↔`-form alternative); `propAsDistinguishing` is
    `propext` expressing the thesis "Prop is an atom of meaning".
  · **The universalLens refinement surface is PURE** (the headline (a)
    pointwise-API rebuild, done).  The 213-native notion of "the same under `L`"
    is the pointwise **Reading-equivalence** (`equivR`, `∀ s, view x s ↔ view y
    s`); `Lens/ReadingEquiv.lean` lifts it to the codomain-polymorphic
    `ReadingEq` / `equivG` / `refinesG` (reducing definitionally to `equiv` at
    the default instance and `equivR` at `Raw → Prop`).  The kernel hub
    (`universalLens_kernel_eq_E_R`), the slash-congruence
    (`universalLens_equivR_slash_congruence`), and the closure companions
    (`universalLens_recovers_R` / `universalLens_idempotent_R`) are all PURE, and
    **every consumer is stated on this API**: the refinement lattice (`Join`,
    `IndexedJoin`, `FamilyMeet`, `FamilyJoin`), the Cauchy `limitLens`, the
    kernel↔slash-congruence bijection (`Corresp`), `Choice.choice_as_lens_spec`,
    and `CanonicalForm.{refinesEquiv, lens_canonical_universal,
    lens_canonical_idempotent}`.  The `=`-of-view-function forms are gone; the
    lone `=`-cost is the isolated bridge `equivR_to_equiv` (the `↔ ⟹ =`
    direction).  Only `propAsDistinguishing` stays irreducible.  Anchors:
    `theory/lens/dirty_recovery_patterns.md` Pattern P5,
    `theory/lens/unified_equivalence.md`.

---

## PURE-bounded on Lean 4 core (2026-05-22)

**Verification**: the dependency-purity audit (transitive Lean-core
axiom scan) + the N5 + N6 centralisations below.

Beyond avoiding `Classical.*`/`native_decide`/`sorryAx`, the DRLT
corpus has been audited for *Lean-core* axiom dependencies (those
inherited transitively via Lean's standard-library lemmas that
themselves bring `propext`/`Quot.sound`).

Net status: **DRLT is PURE-bounded on Lean 4 core** — no non-test
DIRTY citation chain reaches outside the kernel.  Two centralisations
made this possible during the cycle:

  · **N5**: `Nat.max_comm` → `NatHelper.max_comm` (5 sites).
  · **N6**: `Int.mul_sub` / `Int.sub_mul` → `Meta.Int213.{mul_sub, sub_mul}`
    (12 sites).
  · **N8/N9** (this branch): `NatHelper.mul_left_comm` + `Nat.add_right_comm`
    adoption (25 sites, Pattern #10).

Future Lean-core upgrades that change axiom dependencies of
standard-library lemmas are caught by re-running the
dependency-purity audit (`tools/scan_all_axioms.py`).

---

## Latest scan

(Numbers vary by run due to scanner timeouts on slow modules; refer
to HANDOFF.md "current state" for the freshest reading.  1232 total
`.lean` files; scanner enumerates ~500-1000 ★-marked theorems
depending on timeout state.)

**2026-05-22 (audit branch `claude/document-file-audit-FeGcU`)**:
Full repo scan reports **1145 PURE / 0 real DIRTY + 56 sealed-DIRTY-
by-design (1201 total)**.

The 56 DIRTY theorems are all waived under the sealed-by-design
categories above:

  · 23  E213.Lens.SemanticAtom                  — category (a) propext
  · 10  E213.Lens.Properties.Morphism.BoolProp  — category (a) propext
  · 10  E213.Lens.Instances.Leaves.DepthJoin    — category (c) Classical.choice (5) + category (b) Quot.sound (5)
  ·  5  E213.Lens.Universal.QuotLens            — category (b) Quot.sound
  ·  4  E213.Lens.Lattice.IndexedJoin           — category (b) Quot.sound
  ·  3  E213.Lens.Instances.Cauchy              — category (b) Quot.sound
  ·  1  E213.Lens.Instances.FunctionSpace       — category (b) Quot.sound

DRLT mathematical content (`E213.Lib.Math.*`, `E213.Lib.Physics.*`,
`E213.Theory.*`, all capstones) is **fully PURE**.  Zero unsealed
DIRTY: every Lean-core axiom use is structurally justified per
§"Sealed-by-design categories".

### The Lambert weld closed — `LowerBase` proven, `coth(1/q)` series ≡ CF (2026-06-11)

Eight modules, **297 PURE / 0 DIRTY** (`tools/scan_axioms.py`), under
`Lib/Math/NumberSystems/Real213/ExpLog/`:

  · `LambertWeld` 47 · `LambertMinor` 20 · `LambertOrder` 40
  · `LambertMasterId` 37 · `LambertPoly` 34 · **`LambertBridge` 77**
  · `CothSeriesCut` 22 · `ExpMoebius` 20

Headlines (all strict ∅-axiom, hypothesis-free):

  · **`LambertBridge.lowerBase (q) (hq : 1 ≤ q) : LowerBase q`** — the
    base inequality `devA_i·s_{2i+1} ≤ (4i+3)·devB_i·c_{2i+1}` for every
    `i`, via the convolution–master bridge (master identity over ℕ with
    weight-threading accumulators; division-free budget; diagonal
    `(4i+2)!!` Padé flip absorbing all sub-diagonal slack).
  · **`weld_closed`** — the series and CF limit cuts of `coth(1/q)`
    agree on every probe; **`cothSeriesCauchySep`** — total modulus `k+2`.
  · **`expTwoOverQCFCauchySeq`** (`ExpMoebius`) — `exp(2/q)`
    unconditional, modulus `k+2`; `e² ∈ (22/3, 37/5]`.

Promoted: `theory/math/analysis/lambert_weld.md`.

### Discrete Perelman core — four wall items + kernel pinch + entropy (2026-06-10)

Five modules / sections, **69 PURE / 0 DIRTY**:

  · `GeometrizationConjecture/WeightedGreen` 11 — weighted Green identity
    + `dirichlet_gradient_identity` (the weighted heat flow IS the
    gradient flow of `𝓕_w`; wall item (i)).
  · `GeometrizationConjecture/DiscreteGaussian` 11 —
    `gaussian_normalization` `Σ C(t,x) = 2^t` (the `(4πτ)^{−n/2}`
    content), `gaussian_li_yau`, `harnack_forward`,
    `no_local_collapsing` + `kernel_density_pinch` (wall items (ii)–(iii)
    + cigar exclusion).
  · `Combinatorics/Binomial` 15 — `binom_absorption`,
    `binom_log_concave`, `binom_le_central` (division-free Li–Yau +
    unimodality engines).
  · `GeometrizationConjecture/DiscreteSurgery` 15 — general
    Gauss–Bonnet, cut-a-neck ledger (`χ+1`, curvature `+2`),
    round-XOR-neck dichotomy, termination in exactly `b₁` steps
    (wall item (iv)).
  · `GeometrizationConjecture/RicciFlowDiscrete` 17 — incl. §7
    `ricci_chi_entropy_monotone` (`V(K') ≤ 16·V(K)`, the discrete
    Perelman entropy descent).

Promoted: `theory/math/geometry/discrete_perelman_core.md`.

### Async growth ladder + Raw census structure — strict ∅-axiom (2026-06-10)

Eight closures + Slash additions, 74 PURE, 0 DIRTY
(`tools/scan_axioms.py`); the async point–line frontier's full
ranked agenda, items 1–8:

  · **`...UniverseChain.RawEnumeration`** (+8 PURE) — the honest
    counting theorem `honest_count`: `enumTreeDepth n` lists exactly
    the canonical Trees of depth ≤ n (`enum_members` soundness,
    `enum_complete` completeness), Nodup, length `rawCount n`.  The
    anticipated `Tree.cmp`-transitivity gate dissolved — the strict
    `Pairwise (cmp = lt)` invariant needs only the lex head
    structure + `cmp_self_eq` + swap conversions.

  · **`E213.Theory.Async` (AsyncReach.lean)** (12 PURE) — O1:
    `reach_closed` (reachable snapshots are subterm-closed, via the
    new `Raw.slash_inj`), `reach_extend`/`reach_joinable`
    (conflict-freeness in finite form, no fairness),
    `every_raw_reached` (totality by `Raw.rec` + joinability),
    `list_reached`.  `memDec` hand-rolled (core list-`∈` instance
    leaks propext).
  · **`E213.Theory.Raw` (Slash.lean)** (+3 PURE) — `slash_val_lt`,
    `slash_val_gt`, `slash_inj` (pair injectivity: equal slashes
    have equal unordered input pairs).

  · **`E213.Theory.Async`** (14 PURE) — the fused asynchronous growth
    system (states = point lists, one `fire` event): `step1_forced`,
    `level2_canonical` (exact swap-conjugate disjunction),
    `level3_diverges` (depth-2 completion vs depth-3 fork disagree
    beyond a global swap).  List-membership decidability instance
    avoided (propext leak); explicit `Mem` constructors.
  · **`...UniverseChain.RawPastCompleteness`** (6 PURE) — depth-≤2 terms
    are past-complete over the previous downset; at depth 3 the filter
    keeps exactly the full join (`depth3_boundary`).
  · **`...UniverseChain.AtomicityCensusBridge`** (8 PURE) — the two 5s
    mediated: `choose2_fixed` (`choose2 n = n ↔ n = 3` for `n ≥ 1`),
    `two_fives` (census `5` = `pairSize + choose2 closureSize`, level-2
    additions one swap orbit).
  · **`...UniverseChain.RawCountQuadratic`** (9 PURE) — `choose2_add`
    (Vandermonde), `choose2_double` (`2C(n,2)+n = n²`),
    `rawCount_normal_form` (`2T(n+1)+T(n) = T(n)²+4`),
    `rawCount_mod5_cycle`/`_table` (pure period 3, cycle `(2,3,0)`;
    generic self-restart, no privileged level).
  · **`...UniverseChain.RawCountBounds`** (6 PURE) — strict base-2
    sandwich `2^(2^(n+1)) < rawCount (n+3) < 2^(2^(n+2))` (base = NT
    = 2, not d = 5), lower bound sharp at `n = 0` (both sides 5).
  · **`...UniverseChain.RawDagSize`** (8 PURE) — `dagSize` event-cost
    fold; census sandwich `depth ≤ dagSize ≤ leaves − 1` over depth ≤ 3;
    `sharing_starts_at_depth3` filters exactly the three `a/b`-reusing
    terms.

The async point–line arc is closed ∅-axiom and promoted to
`theory/math/foundations/async_growth.md`; the residual open direction
is the exact-membership converse of reachability (recorded under the
async-growth frontier topic).

### Fibonacci 5-adic valuation `ν₅(F_n) = ν₅(n)` — FULLY CLOSED, strict ∅-axiom (2026-06-08)

`E213.Lib.Math.NumberTheory.FibZValuation` (PURE), `.FibZIdentities`
(13/13 PURE), `.DyadicFSM.FibApparitionMod5` (20/20 PURE) — all 0 DIRTY
(`tools/scan_axioms.py`).  The full 5-adic arithmetic of Fibonacci at the
ramified golden prime `5`:

  · `five_dvd_fib_iff` — rank of apparition `α(5) = 5` (`5 ∣ F_n ⟺ 5 ∣ n`).
  · `lucasMod5_never_zero` — Lucas never `0 mod 5` (regular Binet branch).
  · `twentyfive_dvd_fib_iff` — `25 ∣ F_n ⟺ 25 ∣ n` (the `ν₅ ≥ 2` rung).
  · `fibZ_quintuple` — `F_{5m} = F_m·(25F_m⁴ + 25(−1)ᵐF_m² + 5)`.
  · **`fibN_val_law`** — `∀ n k, 5ᵏ ∣ F_n ⟺ 5ᵏ ∣ n`, i.e. `ν₅(F_n) =
    ν₅(n)` (lifting-the-exponent, all orders, via Euclid for prime 5).

Chapter: `theory/math/numbertheory/fibonacci_5adic_valuation.md`.

### General rank law `α(p) ∣ p − (5/p)` + shared `ℚ(√5)` morphism — strict ∅-axiom (2026-06-08)

`E213.Lib.Math.NumberTheory.DyadicFSM.RankApparition` (10/10 PURE) and
`.GoldenFieldBridge` (10/10 PURE) — 0 DIRTY (`tools/scan_axioms.py`).  Two
named open bridges of `fibonacci_golden_prime_crossdomain` closed:

  · **`rank_law_dispatch`** — the Fibonacci rank of apparition `α(p) ∣ p − (5/p)`
    in entry-point form `p ∣ F_{p−(5/p)}`, the index dispatched on the
    FSM-walking Legendre character `legendre213 5 p` (split `p−1`, inert `p+1`,
    ramified `p`).  Each branch via the universal Fibonacci-mod-`p` machinery
    (`binet_F_p_minus_1_zero`, `fpp1_eq_zero_of_frob_phi`, `rank_apparition_five`);
    mirrors `UniversalDispatch.universal_dispatch_pellCoeff`.
  · **`shared_golden_field_morphism`** — the Binet polynomial `x²−x−1`
    (Fibonacci) and the Gaussian-period polynomial `x²+x−1` (`ℚ(ζ₅)⁺`/cp_phase)
    are one `ℚ(√5)` object under `x ↦ −x` (`bPoly_neg_eq_gPoly`), sharing
    discriminant `5` and the single ramified prime `5` (both perfect squares
    mod `5`, double roots `3`, `2`, negatives).

Chapters: `theory/math/numbertheory/fibonacci_5adic_valuation.md`,
`theory/essays/synthesis/the_golden_prime.md`.

### Sperner's theorem compiled to COUNT's double-counting face (2026-06-05)

`E213.Lib.Math.Combinatorics.Sperner` — **39/39 PURE / 0 DIRTY** (`tools/scan_axioms.py`).
Sperner (1928): the largest antichain in the Boolean lattice `2^[n]` has size `C(n,⌊n/2⌋)`, compiled down
the proof-ISA to the **double-counting / dual-union-bound** face of `COUNT` (the mirror of the Ramsey
union bound).  General `∅`-axiom closures: `layer_size` (the `k`-layer has `binom n k` subsets — the READ,
count recursion = Pascal), `eq_of_subseteq_card_eq` (equal-size distinct sets incomparable — SEPARATE),
`lower_bound` (the middle layer is an antichain of size `binom n ⌊n/2⌋` — tight), the binomial-unimodality
chain (`absorb` the absorption identity `(k+1)C(n,k+1)=(n−k)C(n,k)`, `binom_mono_up/down`, `binom_climb_*`,
`binom_le_binom_mid`), `uniform_antichain_le` (single-layer Sperner, general), and the LYM engine
(`sumOver_swap` = Fubini on a 0/1 incidence matrix, `lym_double_count` = per-column cap ⟹ row-sum bound).
Structural `half` (= ⌊n/2⌋) avoids the propext-tainted `Nat.div` lemmas; `add_mul_pure` / NatHelper
sub-lemmas keep `absorb` clean.  Open rung (honest, mirrors Ramsey's named bound): the permutation
chain-counts `n!` and `k!(n−k)!`.  Essay: `theory/essays/proof_isa/sperner_double_counting.md`.

`E213.Lib.Math.Combinatorics.Permutations` — **21/21 PURE** — the permutation
enumeration the repo previously lacked (it had only `LPerm` equivalence):
`perms` (via `insertEverywhere` + a propext-free `flatMap213`), `perms_length :
(perms l).length = fact l.length` (the `n!` chain count), `perms_sound` +
`perms_complete` + `mem_perms_iff` (`p ∈ perms l ↔ LPerm p l` — exactly the
permutations, via `insert_comm`), `self_mem_perms`, and `perms_append_mem`
(orderings concatenate).  Reusable for the Leibniz determinant sum.

The LYM→Sperner reduction is then **complete and ∅-axiom** (`Sperner` 47/47 PURE):
`binom_mul_fact` (`C(n,k)·k!·(n−k)! = n!`, from `absorb`), `fact_mul_ge_mid`
(`k!·(n−k)!` minimised at the middle), and `sperner_upper_bound` (any chain model
with `|chains| = n!`, ≤ 1 member per chain, ≥ `k!·(n−k)!` chains per size-`k`
member ⟹ `|F| ≤ C(n,⌊n/2⌋)`).

★★★ **The named bound is CLOSED unconditionally** —
`E213.Lib.Math.Combinatorics.SpernerChains` (**49/49 PURE**): the geometric chain
model (chains = `perms (idxList n)`, `inc A c` = the size-`|A|` prefix-set of `c`
equals `A`) discharges both hypotheses — `chain_cap` (`hcap`: prefix-sets nest, so
≤ 1 member per chain) and `chain_low` (`hlow`: the duplicate-free family
`{σ++τ}` of `k!·(n−k)!` chains through `A`, via `perms_append_mem` + `inc_concat`).
`sperner` / `sperner_theorem`: **Sperner's theorem (1928) fully proven ∅-axiom** —
largest antichain of `2^[n]` has size exactly `C(n,⌊n/2⌋)` (upper bound + tight
`Sperner.lower_bound`).  Essay: `theory/essays/proof_isa/sperner_double_counting.md`.

★★ **The named Ramsey bound is CLOSED** — `E213.Lib.Math.Combinatorics.RamseyNamedBound`
(**13/13 PURE**): the `K_N` edge model instantiating `erdos_schema`.  `pairsCount_eq`
(#edges inside `S` = `C(cardB S, 2)`, via the Pascal step `binom_succ_2`),
`monoEvent_count` (each monochromatic event holds on `≤ 2·2^{C(N,2)−C(k,2)}` colourings,
via `matchesC_count`), and `ramsey_lower`: `2·C(N,k) < 2^{C(k,2)}` ⟹ a 2-colouring of
`K_N` with no monochromatic `k`-clique (`R(k,k) > N`), with `t = C(N,k)` the subset count
`Sperner.kLayer_card`.  **Both named proof-ISA COUNT bounds — Sperner and Ramsey — are now
closed**, completing the series (`theory/essays/proof_isa/`).

★ **The LYM inequality — the per-term refinement Sperner discards** —
`E213.Lib.Math.Combinatorics.LymInequality` (**5/5 PURE**): `lym_inequality`
(engine form over any chain model), ★★ `lym_antichain` (named, unconditional:
`Σ_{A∈F} |A|!·(n−|A|)! ≤ n!`, the division-free form of the Bollobás–LYM
inequality `Σ 1/C(n,|A|) ≤ 1` via `binom_mul_fact`), `lym_tight_layer`
(sharpness — a full layer saturates at `= n!`, so the layers are exactly the
extremal antichains), and `sperner_via_lym` (LYM ⟹ Sperner: apply the discarded
`min` `fact_mul_ge_mid`, then cancel).  Reuses `Sperner.lym_double_count` +
`SpernerChains.{chains_length,chain_cap,chain_low}` — the named inequality is the
existing engine stopped one line before Sperner's collapse, strictly stronger
than the number it implies.  Essay: `theory/essays/proof_isa/lym_inequality.md`.

★ **Bollobás' set-pair inequality — the same engine, a new incidence** —
`E213.Lib.Math.Combinatorics.BollobasSetPair` (**21/21 PURE**): the COUNT
double-count on the *favour*-incidence (pairs × orderings).  New content:
`before` + `before_antisymm` (ordering antisymmetry, no `Nodup`),
`favours`/`favours_before`, and ★ `bollobas_cap` — cross-intersection
(`A_i∩B_j ≠ ∅`) + per-pair disjointness (`A_i∩B_i = ∅`) ⟹ each ordering favours
≤ 1 pair (the column cap, *the content of Bollobás*).  ★ `bollobas_sum` (the
engine = `lym_double_count` on favours, unconditional) and ★★ `bollobas` (the
named bound `|F| ≤ C(a+b,a)`, `n`-independent, modulo the favour-count
`V·(a+b)! = n!·a!·b!`).  The rung's **arithmetic is discharged**:
`favourCountTarget = C(n,a+b)·a!·b!·(n−a−b)!`, `favourCount_mul` (the identity
`favourCountTarget·(a+b)! = n!·a!·b!` from `binom_mul_fact`), and
`bollobas_of_count` — `|F| ≤ C(a+b,a)` from the *single* clean geometric
inequality `favourCountTarget ≤ #{favouring}`.  That rung is now **CLOSED** —
`E213.Lib.Math.Combinatorics.BollobasCount` (**36/36 PURE**): the favour-count
injection.  `weave` (mask-guided interleave) + order preservation
(`weave_favours`), the position partition (`partition_perm`,
`restPos`/`disjointVec`), `weave` filter/map recovery
(`map_q_weave`/`filter_q_weave`/`filter_nq_weave`), `wovenFam` with
`wovenFam_length = favourCountTarget`, `wovenFam_nodup`, `wovenFam_subset`,
`favourCount_lower` (the rung), and ★★★ `bollobas_uniform` — `|F| ≤ C(a+b,a)`,
`n`-independent, **unconditional ∅-axiom**.  **Bollobás' set-pair inequality is
fully proven.**

★ **Mirsky's theorem on the Boolean lattice — the dual of Sperner** —
`E213.Lib.Math.Combinatorics.ChainAntichain` (**81/81 PURE**): **Mirsky + Dilworth
on `2^[n]`, both fully closed.**  *Mirsky*: `chain_card_inj` (the chain SEPARATE),
`chain_length_le` (height ≤ `n+1`), `canonChain` + `canonChain_max` (achieved), and
★★ `mirsky_boolean` — longest chain = `n+1` = #layers = minimum antichain partition.
*Dilworth*: `dilworth_lower` (any chain cover ≥ `C(n,⌊n/2⌋)`, via the choice-free
`memBL`/`findChain` assignment); the de Bruijn–Tengbergen–Kruyswijk SCD (`scd`,
`extendC`/`raiseC`) with chain + cover (`scd_isChain`, `scd_chain_cover`); the
symmetric-level invariant (★★ `scd_sym`: `cardB` run `[k,…,n−k]`, `2k+|C|=n+1`),
`sym_span` + `scd_has_middle`/`scd_middle_unique` (each chain meets `⌊n/2⌋` once);
the SCD partition (★★ `scd_same`/`scd_disjoint`/`scd_nodup`, via tail-membership
`mem_extendC`/`mem_raiseC` + `extendC_raiseC_disjoint`; no constructor injectivity
needed); and the count (★★★ `scd_card`: `|scd n| = C(n,⌊n/2⌋)` via the nodup
middle-layer trace) ⟹ ★★★ `dilworth_boolean` — **min chain cover `= C(n,⌊n/2⌋) =`
max antichain** (Sperner), the chain-cover dual of Mirsky.

Bollobás reuses `lym_double_count`, `binom_mul_fact`,
`SpernerChains.{truePos,idxList,perms,lcount_le_one_of}` — Bollobás is LYM's
compilation with the incidence swapped (subsets×chains → pairs×orderings) and
the antichain cap swapped for the cross-intersection cap.  Essay:
`theory/essays/proof_isa/lym_inequality.md` (Bollobás section).

### Markov composite uniqueness: prime-power-neighbour families addition (2026-06-04)

`E213.Lib.Math.NumberSystems.Real213.MarkovUniqueness` + `…SternBrocotMarkov` +
`E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor` — **all PURE / 0 DIRTY**.  Composite Markov
uniqueness (`MarkovMaxUnique c`) closed unconditionally for two further infinite families beyond Button's
odd prime powers: the **even `2·pᵏ`** family (`markov_two_prime_pow_unique`, via CRT recombination
`two_roots_of_two_prime_pow`) and **Zhang's `3c±2` criterion** (`markov_max_unique_via_3c_pm2`: if `3c−2`
or `3c+2` is an odd prime power, unique — the discriminant `9c²−4 = (3c−2)(3c+2)` read mod the prime-power
factor, `sq_eq_collapse_pp`), with `markovMaxUnique_985` a concrete composite (`5·197`, `3c−2 = 2953`
prime).  Supporting `∅`-axiom chain: `zhang_linear_core`, `zhang_quadratic(_sum)`, `zhang_gap_dvd` /
`zhang_sum_dvd`, `zhang_gap_determines_pair` / `markov_sum_determines_pair`, `markov_sum_le_max`,
`sq_collapse_pow_ordered`, `prime_of_no_small_factor`.  The proof-method (read the same residue mod a
prime-power factor where `SEPARATE` fires) is the `REFRAME` lift archetype (`Foundations.ProofISALifts`,
`lift_reframe`).  `#print axioms` clean on all.

### Euler's criterion — full iff (`aᵐ ≡ 1 ⟺ QR`), strict ∅-axiom (2026-06-05)

`E213.Lib.Math.NumberTheory.ModArith.EulerCriterion` (**2 PURE**) + `…ModArith.EulerConverse`
(**14 PURE**).  For a prime `p` with `2m = p−1` (odd-prime witness, carried as a hypothesis so no
division enters) and a unit `1 ≤ a < p`:
- `euler_dichotomy` — `p ∣ (aᵐ − 1) ∨ p ∣ (aᵐ + 1)` (`aᵐ ≡ ±1`): `Y = aᵐ`, `Y² = a^(p−1) ≡ 1`
  (FLT), factor `(Y−1)(Y+1)`, disjunctive Euclid `nat_prime_dvd_mul`.
- `euler_qr_pow_one` — `a ≡ x²` ⟹ `p ∣ (aᵐ − 1)` (residue lands on `+1`), `pow_mod_base` +
  `pow_mul_loc` + FLT.
- `euler_converse` — `p ∣ (aᵐ − 1)` ⟹ `∃ x, x² ≡ a`: **squares-list saturation** of
  `RootBound.eval_zero` (the `m` squares `[1²..m²]` are `m` distinct roots of `Xᵐ−1`; a non-square
  root would give `m+1` distinct roots of a length-`(m+1)` polynomial, forcing const `−1 ≡ 0`).
  Supporting: `sqFrom` window (+ `_length`/`mem_`), `sq_diff_not_dvd` (Euclid-on-two-factors
  distinctness), `sqFrom_pairwise`, `sqFrom_roots`, `firstSqrt` search, and the cast bridges
  `natCast_sub` / `mod_eq_of_dvd_sub` / `dvd_int_sub_to_mod_eq`.
- ★ `euler_criterion` — the **full iff** `aᵐ ≡ 1 (mod p) ⟺ a` is a quadratic residue.

`#print axioms` clean on all 16.

### First supplement to quadratic reciprocity (`−1` QR ⟺ `p ≡ 1 mod 4`), strict ∅-axiom (2026-06-05)

`E213.Lib.Math.NumberTheory.ModArith.EulerFirstSupplement` (**4 PURE**).  `neg_one_qr_iff`:
`(∃ x, x² ≡ p−1 (mod p)) ⟺ p ≡ 1 (mod 4)`, for prime `p`, `2m = p−1`.  Corollary of `euler_criterion`
(`a = p−1`): `−1` a QR ⟺ `(p−1)ᵐ ≡ 1`, and `(p−1)ᵐ ≡ (−1)ᵐ` is `1` iff `m` even
(`neg_one_sq_mod`/`neg_one_odd_pow_mod`), and `2m = p−1` makes `m` even ⟺ `p ≡ 1 mod 4`
(`neg_one_pow_dvd_iff_even`, `even_iff_pmod4`, pure `mod_two_cases`).  The full iff (`QRNegOne` had only
the `p≡1mod4 ⟹ QR` direction).

### Legendre character multiplicativity (`(ab/p) = (a/p)(b/p)`), strict ∅-axiom (2026-06-05)

`E213.Lib.Math.NumberTheory.ModArith.LegendreMultiplicative` (**5 PURE**).  `legendre_mul`:
for prime `p`, `2m = p−1`, units `a, b < p`, `a·b` is a QR ⟺ (`a` is a QR ⟺ `b` is a QR) — the
Legendre character is a homomorphism, no symbol definition needed.  Via `qr_iff_pow_one`
(`QR(c) ⟺ cᵐ ≡ 1`) + `pow_m_mod_cases` (`cᵐ % p ∈ {1, p−1}`) + `(ab)ᵐ ≡ aᵐ·bᵐ` (`mul_pow_loc`),
a 2×2 case split (`iff_of_true`/`iff_of_false`, `negone_sq_mod_p`).

### Gauss's lemma (`QR(a) ⟺ ∏signs = 1`), strict ∅-axiom (2026-06-05)

`E213.Lib.Math.Algebra.Linalg213.ProdCongr` (**3 PURE**) + `E213.Lib.Math.NumberTheory.ModArith.GaussLemma`
(**15 PURE**).  For a prime `p`, `2m = p−1`, unit `1 ≤ a < p`: `a` is a quadratic residue **iff** the
least-residue sign product `∏ₓ sgFn(a·x) = 1` (= `(−1)^μ`).  Built across three layers:
- **Layer 1** (`ProdCongr`): `prodZ_congr_map`, `prodZ_map_mul`, `prodZ_map_const_mul`.
- **Layer 2** (`GaussLemma` §1-5): the half-system `seg m = [1..m]`, the `List.Nodup→cnt-Nodup` bridge
  (`cntNodup_of_listNodup`), the pigeonhole (`mem_of_card_le`), the `fold`, `fold_mem`, `fold_inj`,
  and ★ `fold_perm` (`LPerm ((seg m).map (fold a p m)) (seg m)`) — the combinatorial core.
- **Layer 3** (`GaussLemma` §6-7): `int_dvd_cast_sub_mod`, `not_dvd_prodZ` (prime ∤ product of units),
  `prodZ_pm` (∏ of ±1 is ±1); ★ `gauss_core` (`↑aᵐ ≡ ∏signs`, the product-congruence assembly +
  `int_euclid` cancellation of the coprime `M = m!`); ★ `gauss_qr` (with Euler `qr_iff_pow_one` + `p∤2`).

`#print axioms` clean on all.  The gateway to the second supplement and quadratic reciprocity.

### Second supplement (`2` QR ⟺ `p ≡ ±1 mod 8`), strict ∅-axiom (2026-06-05)

`E213.Lib.Math.NumberTheory.ModArith.SecondSupplement` (**7 PURE**).  `second_supplement`: `2` is a QR
mod a prime `p` iff `p ≡ ±1 (mod 8)`.  Via `gauss_qr` at `a = 2` — `2x ≤ 2m = p−1 < p` (no wraparound),
so the sign product is `m`-only (`two_qr_iff`); `prodZ_seg_sign` evaluates it as `(−1)^(cnt2 m k)`
(`k`-induction, threshold decoupled); `cnt2_at_m` (`cnt2 m m = m − m/2`); `neg_one_pow_iff`; then the
`m = 4q+r` bridge (`(m−m/2)%2` and `p%8 = 1+2(m%4)` both functions of `m%4`, `decide`).  Both
supplements to quadratic reciprocity are now ∅-axiom.

### ★★★★★ Quadratic reciprocity — FULLY CLOSED, strict ∅-axiom (2026-06-05)

`E213.Lib.Math.NumberTheory.ModArith.QuadraticReciprocity` (**11 PURE**) +
`Linalg213/SumLinear` (`sumZ_map_zero`, `sumZ_swap` finite Fubini) + `AddMod213.le_div_iff_mul_le`.
★ `quadratic_reciprocity`: for distinct odd primes `p, q` (`m=(p−1)/2, n=(q−1)/2`),
`(q QR mod p ↔ p QR mod q) ↔ (m·n) even` (Eisenstein form — the two residue conditions agree unless
both `p ≡ q ≡ 3 mod 4`).  The complete elementary route is ∅-axiom:

- **Eisenstein's lemma** `floor_qr` — for an odd `a` coprime to the odd prime `p`, `a` is a QR mod `p`
  (`z² ≡ a mod p`) ⟺ the floor sum `Σₓ∈[1,m] ⌊a·x/p⌋` is even.  Chain: `floor_mod_split`
  (`Σ↑(a·x) = ↑p·Σ↑⌊a·x/p⌋ + Σ↑(a·x%p)`) + `Sa_eq` + `fold_sum` (`Σ↑(fold x) = Σ↑x`, `fold_perm`) +
  `residue_fold_even` (per-element `2·(…)`) ⟹ `floor_mu_even` (`2 ∣ (Sfloor + Imu)`, `a` odd +
  `int_euclid`); `imu_eq_countNeg` (`Imu = ↑μ`, μ = `countNeg ((seg m).map (sgFn a p m))`); `gauss_mu_gen`
  (QR ⟺ μ even, the Gauss stack generalized `a<p → p∤a` by reducing to `gauss_mu` at `a%p`).
- **Rectangle double-count** `floor_sum_rectangle` — for `p=2m+1, q=2n+1`, `p∤q·x`, `q∤p·y`:
  `Σ⌊q·x/p⌋ + Σ⌊p·y/q⌋ = m·n` (the lattice-point count of `[1,m]×[1,n]` either side of the diagonal
  `q·x=p·y`, none ON it since `p∤q·x`).  Per-column count `colCount_eq_floor`
  (`#{y : p·y<q·x} = ⌊q·x/p⌋`, via `le_div_iff_mul_le` + `count_le_eq`); cross term swapped by
  `sumZ_swap` (Fubini); `elem_tri` trichotomy `[py<qx]+[qx<py]=1` collapses the grid to `m·n`.
  `floor_bound` (`⌊q·x/p⌋ ≤ n` for `x ≤ m`) keeps each column in range.
- **Assembly** — `floor_qr` at residues `q` and `p` + `floor_sum_rectangle` via `parity_sum_iff`
  (parity of `S+T=↑(mn)` decides whether `2∣S ↔ 2∣T`); Int parity from
  `int_even_or_odd`/`two_mul_ne_one`.

Propext-avoidance throughout: `two_prime` pure (no `decide`-on-`∣`), `Iff.trans` not `rw`-on-iff,
`map_congr` not `funext`, `le_of_dvd_pos` not `Nat.le_of_dvd`.  Narrative: `theory/math/numbertheory/quadratic_reciprocity.md`.

### A6 FLOW — monovariant normal-form lift archetype (2026-06-05)

`E213.Lib.Math.Foundations.MonovariantFlow` — **12 PURE / 0 DIRTY**.  The sixth proof-ISA lift
archetype, the well-founded sibling of A2 LOOP: a self-map `f` with a `Nat`-monovariant that strictly
descends off fixed points converges to a normal form (`flow_reaches`; the descent disjunction is
`Prop`-data so the split is constructive — no decidable equality, no `Classical`).  Canonical instance:
the **Euclidean GCD flow** `(a,b) ↦ (b%a,a)` converging to `(0, gcd a b)` (`euclid_flow_normal_form`),
the gcd the invariant the descent preserves (`gcd213_rec`).  The discrete realization of the Ricci-flow
shape `GeometrizationConjecture/Ricci.lean` recorded as open (monovariant in place of Perelman's
entropy).  Pinned in `Foundations.ProofISALifts` as `lift_flow` / `lift_flow_gcd`; registered in
`seed/PROOF_ISA.md`.  `#print axioms` clean on all 12.

### A6 FLOW drives the Geometrization Ricci pillar to a complete proof (2026-06-05)

`E213.Lib.Math.Geometry.GeometrizationConjecture.RicciFlow` — **8 PURE / 0 DIRTY**.  The proof-ISA
methodology end-to-end: the Ricci-flow conquest *compiled down to* A6 FLOW and the archetype *driving the
complete proof*.  The K_{3,2}^{(c=2)} cell-filling coherentization (`Filled.lean`: `b_1 = 8 - k`, 3
fillable 4-cycles) is exhibited as a convergent monovariant flow — `coherentization_flow_converges`
(∀ C, via `flow_reaches`), `coherentization_normal_form` (reaches `k = C` in `C` steps),
`ricci_pillar_K32_flow_close` (canonical normal form: all 3 cells filled, `b_1 = 5`).  Upgrades the
Geometrization Ricci pillar from OPEN (`Poincare.lean` capstone table) to **CLOSED via A6 FLOW** in the
repo's 213-native chart-Lens model.  Pinned in `ProofISALifts` as `lift_flow_geometrization`.

### A6 FLOW drives smooth-metric round-sphere Ricci flow → finite extinction (2026-06-05)

`E213.Lib.Math.Geometry.GeometrizationConjecture.RicciSphereFlow` — **9 PURE / 0 DIRTY**.  The genuinely
*smooth-metric* simplest case: on the round `n`-sphere the Ricci-flow PDE collapses to the linear ODE
`dρ/dt = −2(n−1)` on the squared radius (`Ric(round Sⁿ)=(n−1)g` + scale-invariance), so the discrete Euler
step `ρ ↦ ρ − 2(n−1)` is *exact* and compiles onto A6 FLOW.  `round_S3_ricci_extinction` (`n=3`,
rate `4`): the 3-sphere shrinks to a round point in finite time — the seed of Perelman's finite-extinction
theorem.  `sphere_flow_converges` / `sphere_reaches_extinction` (general rate), `round_sphere_extinction`
(`n≥2`).  Pinned as `lift_flow_sphere`.  **Honest scope**: the homogeneous/ODE case, *not* the core; the
general-metric `𝓕/𝓦`-monotonicity (Riemannian-geometry + PDE, Mathlib-forbidden) stays OPEN.

### Gradient-flow monotonicity compiled to the ISA (2026-06-05)

`E213.Lib.Math.Analysis.Optimization.GradientFlow` — **9 PURE / 0 DIRTY**.  The structural reason
Perelman's `𝓕/𝓦` is a monovariant, standard proof translated to `0`-axiom.  On an abstract `ℤ`-inner-
product space (`IPSpace`), gradient descent `x ↦ x − τ∇F` on `F(x)=⟪x,x⟫` (∇F=2x) satisfies the
**descent identity** `gradient_descent_identity`: `F(x−τ∇F) = F(x) − τ(1−τ)·‖∇F‖²` — from *only*
`ip_comm` + `ip_smul_left` + `ring_intZ` (∅-axiom ℤ ring tactic).  Hence `gradient_descent_monotone`
(`0 ≤ τ ≤ 1`, via `mul_nonneg` + `ip_nonneg`).  The discrete `0`-axiom form of `d/dt F = −‖∇F‖²`: the
monovariant's descent is *forced by* the gradient structure (the A6 `descent` hypothesis **derived**, not
assumed).  **ISA insight**: gradient flow is *not* A6 — its `F` decreases geometrically (`(1−2τ)²`),
converging asymptotically, so it compiles to **monotone + bounded-below ⟹ convergent** (completeness),
not well-founded `ℕ`-descent.  Frontier sub-step 1 closed (the Ricci-flow smooth-core frontier, `research-notes/frontiers/`).

### Completeness-LOOP: asymptotic convergence of the gradient value (2026-06-05)

`E213.Lib.Math.Analysis.Optimization.CompletenessLoop` — **6 PURE / 0 DIRTY**.  The *second* instruction
gradient-flow monotonicity compiles to (the first being the descent identity).  The geometric value
`vₖ = F(xₖ) = N₀/2ᵏ` (contraction `r ≤ 1/2`) is monotone decreasing (`value_decreasing`), **strictly
positive at every finite step** (`value_pos` — never finitely reaches the infimum `0`, the non-A6
feature), yet **converges to `0` with explicit modulus** `K(n)=N₀·2ⁿ` (`value_below`: `k ≥ N₀·2ⁿ ⟹
N₀·2ⁿ < 2ᵏ`, via the hand-rolled `lt_two_pow_self`).  Bundled in `completeness_loop`.  The **monotone +
bounded-below ⟹ convergent** instruction (repo `Nat→Nat` modulus idiom) — distinct from A6's finite
well-founded descent.  So `𝓕/𝓦`-monotonicity = [descent-identity (`GradientFlow`)] + [completeness-LOOP
(here)], two instructions, neither A6.  Frontier sub-step 3 closed.

### Full Real213 Cauchy object for the gradient value (2026-06-05)

`E213.Lib.Math.Analysis.Optimization.RealCauchyWitness` — **4 PURE / 0 DIRTY**.  The completeness-LOOP
realized as an actual element of the Real213 completion: the value cut sequence `vᵢ = constCut 1 (2ⁱ) =
1/2ⁱ` is a genuine `CauchyCutSeq` (`Analysis/CauchyComplete`) with explicit **proven modulus** `N m k = k`
(`gradientValueCauchy`) — the `cauchy` field discharged by stability past index `k` (`csConst`/`cs_true`,
using `lt_two_pow_self`).  Limit is `0` on the interior `m ≥ 1` (`gradientValueCauchy_limit_interior`).
Honest boundary: `cutEq` is *pointwise* and the diagonal limit differs from `constCut 0 1` only at `m = 0`
(the open/closed Dedekind artifact — the limit is the *open* `0`); a full `cutEq` is **not** claimed.
Instead the limit is pinned at the real `0` by **order-squeeze** — `limit_nonneg` (`0 ≤ limit`) +
`limit_below_dyadic` (`limit ≤ 1/2ⁿ`, ∀ n), bundled `gradient_value_converges_to_zero`; Archimedeanness
forces the unique such real to be `0`.  This completes ② (completeness-LOOP) from modulus-level
(`CompletenessLoop`) to a bona-fide Real213 Cauchy real reaching its infimum `0`.

### Homogeneous Ricci flow — the Einstein trichotomy (2026-06-05)

`E213.Lib.Math.Geometry.GeometrizationConjecture.RicciHomogeneous` — **6 PURE / 0 DIRTY**.  The sign of the
Einstein constant `λ` (`Ric = λg`) sets the homogeneous flow on the size `ρ` (`dρ/dt = −2λ`):
`λ>0` (sphere) **finite extinction** = A6 (`sphere_reaches_extinction`); `λ=0` (Ricci-flat / flat torus /
Calabi–Yau) **stationary**, every state its normal form (`flat_torus_stationary`, A6 cost 0); `λ<0`
(hyperbolic) **diverges**, no fixed point (`expand_iter`/`hyperbolic_diverges`/`expand_no_fixed`), **not
A6**.  Bundled `einstein_trichotomy`.  Sub-steps 2 + 4 of the Ricci frontier; Einstein metrics are the
homogeneous fixed points, sign of `λ` = shrink/steady/expand.  Anisotropic Berger-sphere pinching (2-var
ODE) remains open.

### A7 POSITIVITY archetype + Cauchy–Schwarz (2026-06-05)

`E213.Lib.Math.Foundations.Positivity` — **11 PURE / 0 DIRTY**.  The seventh proof-ISA lift archetype, the
square/norm twin of A5 COUNT: a bound forced because its **gap is a square** (`positivity_of_sq`:
`gap = s² ⟹ 0 ≤ gap`, via `int_sq_nonneg`).  Drives **Cauchy–Schwarz** (2-D, ℤ) — `cauchy_schwarz_2d`:
`⟨u,v⟩² ≤ ⟨u,u⟩⟨v,v⟩` because the gap `= (u₀v₁−u₁v₀)²` (the Lagrange identity `lagrange_2d`, discharged by
`ring_intZ`), no analysis.  Pinned in `ProofISALifts` as `lift_positivity` / `lift_positivity_cs`;
registered in `seed/PROOF_ISA.md` (catalog now seven archetypes).  Classical shadow: Weil RH weights,
Kazhdan–Lusztig positivity, Mordell heights.  Reach: same archetype drives **AM–GM** (`amgm_2`:
`4ab ≤ (a+b)²`, gap `(a−b)²`) and **3-D Cauchy–Schwarz** (`cauchy_schwarz_3d` via `lagrange_3d` +
`positivity_of_sq3`, gap a sum of three squares).  Rigidity face = positive-definiteness:
`positive_definite_2`/`positive_definite_3` (`Σ vᵢ² = 0 ⟹ v = 0`, via `add_eq_zero_of_nonneg` +
`mul_eq_zero`) and `dist_sq_zero_imp_eq` (the squared distance separates points — POSITIVITY drives
`SEPARATE`).

### Marathon T1 — exp Taylor convergence modulus (ratio-test core) (2026-06-05)

`E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpModulus` — **4 PURE / 0 DIRTY**.  Closes the
convergence-modulus follow-up `CutExpSeries` deferred (the geometric majorant `Mⁿ/n!`, "ratio-test
argument not yet done").  Worked at the term-magnitude level `Mᵏ/k!` (numerator `Mᵏ`, denominator `k!`,
`M` bounds `|x|`), no cut comparison: `pow_half_step` (`2·M^{k+1} ≤ Mᵏ·(k+1)` once `2M ≤ k+1`) →
`expTerm_ratio_half` (cross-multiplied `2·M^{k+1}·k! ≤ Mᵏ·(k+1)!` — the `(k+1)`-th Taylor term is ≤ half
the `k`-th) → `expTerm_geom_majorant` (`2ʲ·M^{N+j}·N! ≤ Mᴺ·(N+j)!` for `2M ≤ N+1`, the geometric tail
ratio `1/2`) → `expTail_geom_decay` (base `N = 2M`: the tail decays as `term(2M)·2^{−j}` with explicit
dyadic modulus `j ↦ 2ʲ`).  Plus `expTerm_antitone` (terms non-increasing past `2M` — the
alternating-series-test input for the `sin`/`cos` series, T2).  Rung **T1** of the transcendentals marathon;
next: package the rate into a `CauchyCutSeq` over `expPartialSum` (T1→T2 bridge) then `sin`/`cos` series (T2).

### Marathon T1 (algebraic route) — exp(m) convergents + cross-determinant; e's clean modulus is m=1-special (2026-06-05)

`E213.Lib.Math.NumberSystems.Real213.ExpLog.CutExpConvergents` — **5 PURE / 0 DIRTY**.  Generalizes the
`EulerModulus` convergent arithmetic from e (= exp 1) to **exp(m) for every integer argument**: `expNum m`
(`A_{n+1} = (n+1)A_n + m^{n+1}` over `eulerDen = n!`), `expNum_one` (`expNum 1 = eulerNum`, exp(1)=e),
`exp_cross_det` (`expNum m (n+1)·D_n = expNum m n·D_{n+1} + m^{n+1}·D_n` — cross-determinant `m^{n+1}·n!`,
generalizing `euler_cross_det`'s `n!`), `exp_convergents_mono` (strictly increasing for `m ≥ 1`).
**Honest finding**: feeding this into `RateModulus.Htel_of_crossdet` reduces the rate certificate to
`i(i+1)m^{i+1}+i ≤ (i+1)²`, which holds for all `i ≥ 1` only at `m = 1` (why **e** gets the clean
`N(m,k)=k+2`) and **fails for m≥2 already at i=1** (`exp_two_rate_fails_at_one`: `9 > 4`; contrast
`exp_one_rate_holds_at_one`: `3 ≤ 4`).  So the clean `RateModulus` modulus is e-special; general exp(m)'s
modulus comes from the **analytic** geometric majorant (`CutExpModulus`, threshold `2m`).  The algebraic
and analytic routes to exp's convergence are complementary.  **Routes unified** (same file): the convergent
increment IS the Taylor term — `eulerDen_eq_factorial` (`eulerDen n = n!`), `exp_increment_eq_taylor`
(`e_{i+1}−e_i = m^{i+1}/(i+1)!`, the partial-sum step adds exactly the next Taylor term), and
`exp_increment_geom_decay` (the convergent gaps decay geometrically past `2m` via
`CutExpModulus.expTail_geom_decay`, over the convergent denominators) — so the convergents are Cauchy with
the analytic `2m`-threshold modulus, the route that actually delivers exp(m).  (Note: the RateModulus margin
`1/(i·d_i)` is structurally e-tied — it bounds e's tail `~1/(i·i!)` but not exp(m)'s `~m^{i+1}/(i+1)!` at
*any* threshold; the analytic route is the only one for `m ≥ 2`.)  Also `HeatEqDiscrete.lazy_eq_nonlazy_plus_self`
(`lazyHeatStepNum = heatStepNum + 2u_x` — the self-weight that moves the stencil symbol `cos θ → 1+cos θ`,
removing the `−1` checkerboard eigenmode; the structural reason for the spectral gap).

### Marathon P3 infra — finite-grid sum + discrete mass conservation (2026-06-05)

`E213.Lib.Math.Analysis.ODE.HeatEq.Conservation` — **8 PURE / 0 DIRTY**.  Builds the reusable finite-grid
sum `gridSum n f = Σ_{x<n} f x` (`gridSum_congr`, `gridSum_add`, `gridSum_two_mul`) with **cyclic-shift
invariance**: `gridSum_rightNbr` / `gridSum_leftNbr` — the neighbour maps `leftNbr`/`rightNbr` are the two
full-cycle rotations of `{0,…,n−1}`, so re-summing along them returns the same total (via
`gridSum_head_shift` moving the wrapped head term, + `leftNbr_rightNbr`: `leftNbr ∘ rightNbr = id` on the
grid).  First consumer: **mass conservation** — `heatStep_mass_conservation` (`Σ heatStepNum = 2·Σu`),
`lazyHeatStep_mass_conservation` (`Σ lazyHeatStepNum = 4·Σu`): the heat step redistributes mass without
creating/destroying it (averaged total invariant), the discrete conservation law companion to the maximum
principle.  Purity note: required NatHelper's pure `add_sub_cancel_right` / `add_self_mod_pure` (Lean-core
`Nat.add_sub_cancel` and `Nat.add_mod_right` leak `propext`) and a `gridSum_congr`-based scalar lemma
(avoiding `funext`/`Quot.sound`).  `gridSum` now unblocks the Dirichlet energy (P3 proper).

**Discrete summation by parts** (same file §4, 3 more PURE): `gridSum_mul_shift_symm` (the edge
correlation `Σ u(x)·u(rightNbr x)` is shift-symmetric — reindex by the rotation via `leftNbr ∘ rightNbr =
id`), and the **Dirichlet pairing** `heatStep_dirichlet_pairing` (`⟨u, heatStep u⟩ = 2·Σ u(x)·u(rightNbr x)`)
/ `lazyHeatStep_dirichlet_pairing` (`⟨u, lazy u⟩ = 2Σu² + 2·corr`, i.e. `4Σu² − E(u)` in `Nat`-clean
additive form).  The discrete integration-by-parts / Green identity underlying energy estimates, with pure
products (no `Nat`-subtraction).

**Signed Dirichlet energy + Green identity** (same file §5, 2 more PURE): `sqDistNat a b = |a−b|²`
(sign-correct: `(a−b)²+(b−a)²`, one term truncated to 0 in `Nat`), `dirichletEnergy n u =
Σ_x |u(rightNbr x)−u(x)|²`, and `dirichletEnergy_green` (`E(u)+2·corr = 2·Σu²` — over ℤ, `E(u) = ⟨u,−Δu⟩`,
the Dirichlet form *is* the energy).  Note (correcting an earlier over-pessimistic "ring normalizer blocked"
claim): `ring_nat` closes the asymmetric binomial fine — its *only* failure was an un-pruned
zero-coefficient monomial (a literal `0*0` from the truncated `(b−a)²`); removing it with
`Nat.zero_mul`/`Nat.add_zero` first lets the normalizer succeed.

### Marathon P3 — pointwise L²-Jensen (convexity) bounds via POSITIVITY (2026-06-05)

`E213.Lib.Math.Analysis.ODE.HeatEq.EnergyL2` — **2 PURE / 0 DIRTY**.  The heat step is a convex average, so
by convexity of the square it cannot increase the L² norm pointwise: `heatStep_l2_jensen`
(`(a+b)² ≤ 2(a²+b²)`, gap the single square `(a−b)²`) and `lazyHeatStep_l2_jensen`
(`(a+2b+c)² ≤ 4(a²+2b²+c²)`, gap `(a−2b+c)²+2(a−c)²`).  Worked over ℤ via the **POSITIVITY archetype**
(`Foundations/Positivity`): `ring_intZ` for the SOS gap identity + `positivity_of_sq`/`positivity_of_sq3` —
the `amgm_2` pattern reused.  The pointwise L²-dissipation seed, energy-method companion of the L∞ maximum
principle.  (The *summed* signed Green identity it complements is now also done — see `HeatEqConservation`
§5 above; the only `ring_nat` subtlety was un-pruned `0*0` zero-coefficient terms.)  **Energy-decay heart**
(same file, +1 PURE): `lazy_energy_pointwise` — the local energy dissipation `(s+r−q−p)² ≤
4·((q−p)²+2(r−q)²+(s−r)²)` over ℤ, from `grad(lazy u) = lazy(grad u)` (the lazy-step edge difference is the
lazy stencil on the three edge gradients) + Jensen.  Its grid-sum (`gridSum_le` added to `HeatEqConservation`)
gives `E(lazy u) ≤ 16·E(u)`.

### Marathon P3 CAPSTONE — Dirichlet energy decay `E(lazy u) ≤ 16·E(u)` (2026-06-05)

`E213.Lib.Math.Analysis.ODE.HeatEq.EnergyDecay` — **3 PURE / 0 DIRTY**.  The lazy heat step does **not increase
the (averaged) Dirichlet energy** — the L²-method conclusion, the analytic engine behind discrete smoothing /
convergence to equilibrium.  `lazy_energy_decay`: `E(lazyHeatStepNum u) ≤ 16·E(u)` (the `16 = 4²` is the
stencil normalization).  Assembled from: `sqDistNat_cast` (the `Nat`↔ℤ square bridge `↑(sqDistNat a b) =
(↑a−↑b)²`), `lazy_energy_pointwise_nat` (the ℤ pointwise dissipation `(s+r−q−p)² ≤ 4(…)` cast to `Nat` via
`Int213.Order.le_of_ofNat_le`), `gridSum_le`/`gridSum_mul_left`/`gridSum_add`, and cyclic-shift invariance
(`gridSum_rightNbr` turns each shifted edge-gradient energy back into `E(u)`).  All ∅-axiom — the `propext`
leaks of core `Int.ofNat_*` / `Nat.add_sub_cancel_left` / `sub_eq_zero` were sidestepped with term-mode casts
(explicit `Int.ofNat` typing dodges the `Nat.cast` `rw`-mismatch) + NatHelper pure sub-lemmas + `Nat.zero_sub`.
**Marathon PDE rungs P1–P3 now complete.**  Companion **L² norm contraction** (same file §4, 2 more PURE):
`lazy_l2_norm_bound` — `Σ_x (lazyStep u)² ≤ 16·Σ_x u²` (the lazy step does not increase the averaged L²
norm of the *field*), via the pure-`Nat` `lazy_l2_pointwise_nat` (`(a+2b+c)² ≤ 4(a²+2b²+c²)`, cast of
`lazyHeatStep_l2_jensen`) + shift invariance.  No gradient/`Nat`-subtraction, so it is the simpler
field-L² companion of the energy (gradient-L²) decay.

### Marathon P3 — pointwise L²-Jensen (convexity) bounds via POSITIVITY (2026-06-05)

### A6 CORE rung 5 — Ollivier–Ricci: Kantorovich weak duality + concrete triangle κ=½ (2026-06-05)

`E213.Lib.Math.Geometry.GeometrizationConjecture.OllivierRicci` — **60 PURE / 0 DIRTY** (§§2–6; the
parametric `K_m` §7 is catalogued under "discrete curvature parametric closure" below).  The last discrete
curvature rung: Ollivier–Ricci `κ(x,y)=1−W₁(m_x,m_y)/d(x,y)`, whose heart is optimal transport.  Built the
integer grid sum `gridSumZ` (+ `_add`/`_sub`/`_mul_left`/`_le`/`_congr`/**`_fubini`** sum-swap) and proved
**`kantorovich_weak_duality`**: for any transport plan `π ≥ 0` and `1`-Lipschitz potential `f`,
`Σ_x f·μ − Σ_y f·ν ≤ Σ_x Σ_y d·π` (the `W₁`-dual ≤ `W₁`-primal direction) — proof: marginals + Fubini reduce
both sides to `Σ_x Σ_y (f x − f y)·π x y ≤ Σ_x Σ_y d x y·π x y` (termwise via `mul_le_mul_right_nonneg`).
`ollivier_bracket`: `1−transportCost ≤ 1−dualValue`, the curvature bracket that pins `κ` when a plan and a
potential meet.  **Concrete `κ` now exhibited** — the triangle `C₃` worked example (`triD`/`triPi`/`triMu0`/
`triMu1`/`triF`): `triangle_coupling` (plan marginals match), `triF_lipschitz` (`triF` is `1`-Lipschitz, all
branches by `decide` + `Order.sub_self_zero` on the diagonal), `triangle_ollivier_optimal`
(`dualValue = transportCost = 1`, plan meets potential) ⟹ scaled `W₁ = 1`, Ollivier `κ = 1 − ½ = ½ > 0`:
the triangle is positively curved (a concrete value, not just the bracket).  **`ollivier_plan_optimal`**
(general optimality certificate: `dualValue` depends only on marginals, so a plan meeting a `1`-Lipschitz
dual is cost-optimal among all plans sharing its marginals) + **`triangle_plan_optimal`** (`triPi`'s cost
`1 ≤` cost of *every* valid coupling) make `W₁ = 1` a genuine optimum, not just a matched pair.  **Sign
contrast**: the square `C₄` worked example (`c4D`/`c4Pi`/`c4F` + `c4_coupling`/`c4_ollivier_flat`/
`c4_plan_optimal`, with helpers `c4F_le_one`/`c4F_nonneg`/`c4F_lipschitz`/`sub_le_of_le_of_nonneg`) gives
Ollivier `κ = 0` (flat, no triangles) against the triangle's `κ = ½ > 0` (clustered) — Ollivier curvature
tracks local clustering, the transport analogue of the Forman / Gauss–Bonnet sign↔topology results.  **Full
sign trichotomy**: the double-star (`dsD`/`dsPi`/`dsF` + `ds_coupling`/`ds_ollivier_negative`/`ds_plan_optimal`,
helpers `dsF_le_one`/`dsF_ge_negtwo`/`dsF_lipschitz`/`sub_le_sub_bounds`) gives Ollivier `κ = 1 − 5/3 = −2/3 < 0`
(a tree, like hyperbolic space).  So `+` (triangle) / `0` (square) / `−` (double-star) are all ∅-axiom theorems
— the complete Ollivier mirror of the Forman / Gauss–Bonnet sign↔topology trichotomy.  Purity:
Int213 `Order`/`OrderMul`
pure inequalities (core `Int.add_le_add`/`mul_le_mul_of_nonneg_right`/`sub_le_sub_left`/`Int.sub_self` all leak
`propext`).

### A6 CORE rung 6 — Bakry–Émery curvature-dimension `CD(K,N)` + discrete Bochner (2026-06-08)

`E213.Lib.Math.Geometry.GeometrizationConjecture.BakryEmery` — **42 PURE / 0 DIRTY** (§§1–2 here; the
parametric §§3–5 are catalogued under "discrete curvature parametric closure" below).  The **fourth** curvature
frame: Bakry–Émery curvature via the carré-du-champ iteration `Γ₂ = ½LΓ − Γ(f,Lf)` of the graph Laplacian,
scaled to `ℤ` (`gammaL`/`gamma2L`, `gammaTri`/`gamma2Tri`).  **Discrete Bochner identity** — `bochner_line`:
`4Γ₂(f)(x) = (Lf(x−1))² + 2(Lf(x))² + (Lf(x+1))²` (the flat `Ric = 0` Bochner `½Δ|∇f|² = |Hess f|² + Ric(∇f,∇f)`,
only squares) ⟹ `cd_0_2_line` (the line/large cycle is `CD(0,2)`, curvature `0`) + `gamma2_line_nonneg`.
`bochner_triangle`: `4Γ₂ = 5·(2Γ) + 2(f₁−f₂)²` (i.e. `Γ₂ = (5/2)Γ + ½(f₁−f₂)²`) ⟹ `cd_triangle` (the triangle
`C₃ = K₃` is `CD(5/2,∞)`, the complete-graph value `(n+2)/2`) + `gammaTri_nonneg`.  `CD(K,N)` is the synthetic
(Lott–Sturm–Villani) meaning of `Ric ≥ K, dim ≤ N` — so this is the dimension-independent handle for the
general-`n` Ricci **lower bound** even while the smooth `n`-tensor flow stays walled.  Sign agreement: flat line
`K=0` / triangle `K=5/2>0` — same as Forman/Gauss–Bonnet/Ollivier.  Proofs `ring_intZ` (Bochner identities) +
`int_sq_nonneg`/`add_nonneg`/`Order` (the SOS bounds), stencil-parametrised à la `ConformalCurvature` (no index
arithmetic).

### A6 CORE — discrete curvature parametric closure + Lichnerowicz spectrum + tensor calculus (2026-06-10)

The Ricci-flow marathon closed the discrete-curvature ladder **parametrically across graph families**
(strict ∅-axiom throughout; `tools/scan_axioms.py` 60/42/16/11/23/14 PURE, 0 DIRTY):

- `…GeometrizationConjecture.OllivierRicci` §7 — the complete graph `K_m` for **general `m`**:
  Ollivier `κ = (m−2)/(m−1) > 0` (`kmPi` coupling + optimality), the parametric form of the
  triangle/square/double-star trichotomy.
- `…GeometrizationConjecture.BakryEmery` §§3–5 — `K_m` is `CD((m+2)/2, ∞)` **sharp**
  (`cd_complete_graph`, `cd_complete_graph_sharp`, `complete_graph_gammaC_witness`); the star
  `K_{1,b}` centre is `CD((3−b)/2, ∞)` (`cd_star`, negative for `b ≥ 4`) and a leaf is
  `CD((5−b)/2, ∞)` (`cd_star_leaf`) — curvature now a *function of the family parameter*.
- `…GeometrizationConjecture.BakryEmeryBipartite` — **16 PURE / 0 DIRTY**, general bipartite
  `K_{a,b}` at an `A`-vertex: `CD(min(3a−b, b−a+4)/2, ∞)`, split into the wide regime
  `b ≥ 2a−2` (`kab_cd_wide`, SOS only) and the narrow regime (`kab_cd_narrow`, via the discrete
  Cauchy–Schwarz `cauchy_schwarz_gridZ`).  DRLT core: `K_{3,2}` is `CD(3/2, ∞)` (`kab_K32_pos`)
  — **positive** Bakry–Émery against Forman `−1`, an honest cross-frame sign divergence
  (`theory/essays/synthesis/curvature_as_lens_readout.md`).
- `…GeometrizationConjecture.DiscreteLichnerowicz` — **11 PURE / 0 DIRTY**, curvature → spectrum:
  the integration-by-parts trio `km_green`/`km_rayleigh` (`Σ(Lf)² = m·E`), `km_eigenvalue` +
  eigenspaces (`km_const_eigen`, `km_meanzero_eigen`) ⟹ the `K_m` Laplacian spectrum is
  `{0¹, m^{m−1}}`; `lichnerowicz_abstract` (`CD(K) ⟹ K ≤ λ`, Int positive cancellation).
- `…Geometry.TensorCalculus` — **23 PURE / 0 DIRTY**, dimension-free general-metric algebraic
  tensor calculus: Christoffel (1st/2nd kind, symmetry, metric compatibility) → Riemann tensor
  with **all four symmetries** (via the metric 2-jet `riemLow`) → Ricci + first Bianchi → scalar
  `R = g^{ij}Ric` + Einstein `R = λn`; `perelman_rate_nonneg` (`0 ≤ Σ(Ric_{ij}+∇_i∇_j f)²`, the
  algebraic Perelman `d/dt 𝓕 ≥ 0` rate).  Chapter: `theory/math/geometry/riemannian_curvature_tensor.md`.
- `…Combinatorics.IntGridSum` — **14 PURE / 0 DIRTY**, the `gridSumZ` finite-Int-sum toolkit
  (add/sub/mul_left/le/congr/fubini + nonneg), domain-agnostic infra relocated out of the
  curvature leaf; 5 consumers.

Chapter: `theory/math/geometry/discrete_curvature.md` (the parametric discrete-curvature closure).

### A6 CORE rung 7 — time-evolution: all-time fixed-point stability (2026-06-08)

`E213.Lib.Math.Geometry.GeometrizationConjecture.RicciFlowDiscrete` (§6, +1 PURE).  `lazyRicciFlow` (the
smoothing `(¼,½,¼)` step iterated) + **`ricci_flow_fixed_point_stable`**: `lazyRicciFlow n t (constInit c) x =
4ᵗ·c` for *every* `t` — constant curvature is a genuine all-time fixed point (averaged curvature `= c`,
unchanged across all time), the discrete "round/Einstein metric stays round under Ricci flow for all time",
complementing rung 3's `flow_reaches` *to* the fixed point.  Induction on `t` via `lazyHeatStep_const` at the
three stencil sites + `Nat.pow_succ`/`ring_nat`.

### A6 CORE — smooth 2D-conformal Gauss curvature (the smooth route) (2026-06-05)

`E213.Lib.Math.Geometry.GeometrizationConjecture.ConformalCurvature` — **4 PURE / 0 DIRTY**.  Opens A6's
**smooth** route (distinct from the closed discrete Forman route) via the 2D-conformal sidestep
(the Ricci-flow smooth-core frontier, `research-notes/frontiers/`): for `ds²=λ(dx²+dy²)` with polynomial `λ`, the Liouville Gauss curvature
`K=(|∇λ|²−λΔλ)/(2λ³)` is rational — no transcendentals.  `confKNum = |∇λ|²−λΔλ` (curvature numerator over
ℤ); `confK_flat` (constant `λ` ⟹ `K=0`, S3), `confK_paraboloid` (`λ=x²+y²+1` ⟹ numerator `−4`, negative
curvature), `confK_dome` (`λ=C−x²−y²` ⟹ numerator `4C`, positive curvature), `conformal_curvature_trichotomy`
(flat/neg/pos, S4) — genuine smooth 2D-conformal Ricci curvature, `ring_intZ`.  The smooth wall (general-`n`
+ transcendental metrics) stays; 2D-conformal polynomial `λ` is this side of it.  **S5 ✅** (same file, 2 more PURE): the flow `∂_tλ=−2Kλ` cleared to `λ²·∂_tλ=confFlowRate=−confKNum`; `conf_flow_flat_stationary` (flat = fixed point) + `conf_flow_stationary_imp_flat` (fixed point ⟺ flat `K=0`) — the smooth 2D-conformal route S3–S5 closed.

### A6 CORE rung 4 — discrete Gauss–Bonnet: curvature sign ↔ topology as a theorem (2026-06-05)

`E213.Lib.Math.Geometry.GeometrizationConjecture.DiscreteGaussBonnet` — **4 PURE / 0 DIRTY**.  Makes rung
1's curvature↔`b₁` table a **theorem**: vertex curvature `κ(v)=2−deg(v)`, `gauss_bonnet_Kmn`
(**`Σ_v κ(v)=2·χ`**, `χ=V−E` for `K_{m,n}`), `euler_eq_one_sub_b1` (`χ=1−b₁`, cyclomatic `b₁=E−V+1`),
`totalCurv_eq` (**total curvature `=2−2·b₁`** — positive ⟺ tree `b₁=0`, negative ⟺ cyclic `b₁≥1`), and
`curvature_sign_topology` (`K_{1,1}` `+2`/`b₁=0` vs `K_{3,2}` `−2`/`b₁=2`).  Derived by `ring_intZ`, not
tabulated.  A6 discrete core rung 4 (the A6 Ricci-core ladder, `research-notes/frontiers/`).

### A6 CORE TOUCHED — discrete Ricci flow as heat flow on curvature (2026-06-05)

`E213.Lib.Math.Geometry.GeometrizationConjecture.RicciFlowDiscrete` — **5 PURE / 0 DIRTY**.  The
transcendentals + PDE-estimates marathon was split off precisely to unblock the A6 Ricci-flow core; this
file spends the PDE estimates on it.  **Bridge**: smooth Ricci flow linearizes to the heat equation on
curvature (`∂_t R = ΔR + 2|Ric|²`, Hamilton), so the discrete Ricci flow's edge-curvature field evolves by
the **discrete heat step** — and the heat estimates ARE the discrete Ricci-flow a-priori estimates.
`ricciFlowStep = lazyHeatStepNum`; `ricci_curvature_bounded` (no blow-up, `heatIter_range`),
`ricci_energy_monotone` (**curvature Dirichlet energy decays `E(flow K) ≤ 16·E(K)`** — `lazy_energy_decay`,
the discrete Perelman 𝓦-/entropy-monotonicity), `ricci_uniform_stationary` (uniform `K_{NS,NT}` curvature
`4−NS−NT` is the normalized fixed point, `lazyHeatStep_const`), `ricci_total_curvature_conserved` (Σ curvature conserved, `4·Σ` — the normalised flow's volume/total-scalar preservation, from mass conservation), `ricci_flow_homogenises` (the checkerboard
curvature field → constant curvature in one step, spread `1→0` — `lazy_checker_collapses`).  **A6 conquest
core closed on the discrete (Forman) side** (rungs 2–3 of the A6 Ricci-core ladder, `research-notes/frontiers/`);
the smooth-Perelman wall stays (the Ricci-flow smooth-core frontier, `research-notes/frontiers/`).  Bundled as `discrete_ricci_apriori` (one step: curvature stays in `[4A,4B]` incl. **lower-bound preserved** `ricci_lower_bound_preserved` (Perelman's key property), total curvature conserved, energy non-increasing) — the discrete analogue of Perelman's a-priori estimates.  Convergence is also a genuine **A6 FLOW (`flow_reaches`)** instance: `ricci_flow_reaches_normalized` — the curvature-spread monovariant `spreadFlow` strictly descends (by 2/step) to the normalised state `spread ≤ 1` (`spreadFlow_fixed_le_one`), realising rung 3's "drive the flow to constant curvature via A6 FLOW on a curvature-spread monovariant" (3 more PURE).

### Marathon T4 (foundation) — integer floor square root `isqrt` (2026-06-05)

`E213.Lib.Math.NumberTheory.IntSqrt` — **PURE / 0 DIRTY**.  `isqrt n = ⌊√n⌋` via a downward scan
(`isqrtAux`), with the correctness **bracket** `isqrt_bracket`: `isqrt n · isqrt n ≤ n < (isqrt n + 1)²`
(so `isqrt n` is the largest `k` with `k² ≤ n`).  Lower bound `isqrtAux_sq_le` (only `k` with `k²≤n` is
ever returned) + maximality `isqrtAux_max` (every candidate above the result, up to the scan start, fails);
the upper bound dispatches `n<2` by `decide` and `n≥2` via `isqrt n < n` (else `n²≤n` ⟹ `n≤1`).  The
discrete foundation of the real `sqrt` (marathon T4): `Real213` `sqrt` is the limit of `isqrt` on dyadic
rescalings.  Purity: NatHelper's pure `le_of_add_le_add_left` (Lean-core `Nat.le_of_add_le_add_right` leaks
`propext`).  Extended (4 more PURE): `le_isqrt_of_sq_le` (`k²≤n ⟹ k≤isqrt n`, the defining largest-property),
`isqrt_mono`, `isqrt_perfect` (`isqrt(k·k)=k`), and ★ `isqrt_four_mul` — the **dyadic refinement**
`2·isqrt n ≤ isqrt(4n) ≤ 2·isqrt n + 1` (doubling resolution adds ≤1 unit error), the convergence-rate
certificate making `isqrt(a·4ᵏ)/2ᵏ → √a` Cauchy.  §5 packages this as the **dyadic √ sequence** `dyadicSqrtSeq a k = isqrt(a·4ᵏ)`: `dyadicSqrtSeq_bracket` (`(s_k)²≤a·4ᵏ<(s_k+1)²`, brackets `√a` to width `1/2ᵏ`) + `dyadicSqrtSeq_step` (`2·s_k ≤ s_{k+1} ≤ 2·s_k+1`, the Cauchy modulus `1/2ᵏ`) — the rational-level convergence certificate for `√a` (cut-level `sqrtCut` packaging remains).

### Marathon T5 CORE — general two-variable binomial theorem (2026-06-05)

`E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTwoVar` — **2 PURE / 0 DIRTY** (+ helpers).
`binom2_theorem`: **`(a+b)ⁿ = Σ_{k=0}^{n} C(n,k)·aᵏ·bⁿ⁻ᵏ`** — the b=1 case (`binom_theorem_b_eq_one`)
extended to general `b`.  Proven via `binomSum2_step` (`(a+b)·binomSum2 a b n = binomSum2 a b (n+1)`):
both `(a+b)·binomSum2` and `binomSum2 (n+1)` reduce to the common form `bⁿ⁺¹ + A + thirdterm` via
`sumTo_split_first` + Pascal `choose_succ_succ` + `sumTo_add_func` + `ring_nat`, with the `b`-exponent
congruences `n+1−(k+1)=n−k` (`Nat.succ_sub_succ`) and `n−(k+1)+1=n−k` for `k<n` (`bexp_shift`, from
NatHelper `sub_one_add_one`+`sub_pos_of_lt`); the boundary term `C(n,n+1)=0` drops the tail.  Purity needed
explicit-typed `have`s for `Nat.pow_succ`/`Nat.succ_sub_succ` (the `rw` patterns are `Nat.succ`-shaped, the
goals `_+1`-shaped) + `show` beta-reduction of the `sumTo_congr` lambdas.  This is the **exp functional
equation** `exp(a+b)=exp(a)exp(b)` engine: cross-multiplying the Cauchy convolution `Σ(aʲ/j!)(bᵏ/k!)` by `n!`
gives exactly this (via `choose_mul_factorials`).

### Marathon T5 (enabling) — `choose`↔factorial bridge (2026-06-05)

`E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial` — **1 PURE / 0 DIRTY**.  `choose_mul_factorials`:
`C(k+j, k) · (k!·j!) = (k+j)!` — the division-free `C(n,k) = n!/(k!(n−k)!)` (parametrized by `n=k+j` to
dodge `Nat`-subtraction).  Proven from the absorption identity `choose_succ_mul`
(`(k+1)·C(n+1,k+1)=(n+1)·C(n,k)`) by induction on `k`: multiply the goal by `k+1`, rewrite the head via
`choose_succ_mul` + `(k+1)!=(k+1)·k!`, apply IH, cancel `k+1` (`Nat.eq_of_mul_eq_mul_left`, pure).  This is the
bridge the **exp functional equation** `exp(a+b)=exp(a)exp(b)` needs: cross-multiplying the Cauchy convolution
`Σ(aʲ/j!)(bᵏ/k!)` by `n!` gives `Σ C(n,j)aʲbⁿ⁻ʲ = (a+b)ⁿ` (binomial theorem) via exactly `C(n,j)·j!·(n−j)!=n!`.
Connects the combinatorial `choose` (Pascal) to the analytic `factorial`; reusable across combinatorics /
probability.  Purity: needed NatHelper's pure `mul_assoc` (Lean-core `Nat.mul_assoc` leaks `propext`).
Two clean corollaries: `choose_symm` (`C(k+j,k)=C(k+j,j)`, cancelling the common `k!·j!` from two bridge
instances) and `pascal_row_sum` (`Σ_{k=0}^n C(n,k) = 2ⁿ`, the binomial theorem at `a=1` — in `BinomialTheorem`).
Plus `choose_le_two_pow` (`C(n,k) ≤ 2ⁿ`, each binomial ≤ the row sum, via `sumTo_term_le`) — the standard
coefficient bound (Chernoff/probability).  `hockey_stick` (`Σ_{j=0}^{m} C(r+j,r) = C(r+m+1,r+1)`, the Pascal-diagonal sum, by induction via Pascal).

### Marathon T3 — formal derivative rules (coefficient level): exp/sin/cos self-reproduce via one factorial shift (2026-06-05)

**3 PURE / 0 DIRTY** (`exp_deriv_coeff_fixed` in `CutExpModulus`; `sin_deriv_coeff`, `cos_deriv_coeff` in
`CutTrigModulus`).  The formal power-series derivative `Σcₙxⁿ ↦ Σ(n+1)c_{n+1}xⁿ` acts on exp/sin/cos
through the single factorial shift `(n+1)·n! = (n+1)!`: exp (`cₙ=1/n!`) is its **fixed point** (`d/dx exp =
exp`); sin/cos are a **2-cycle** (`d/dx sin = cos` at even powers, `d/dx cos = −sin` at odd powers, the
sign in the Int213 difference-Lens).  Coefficient-level T3 core; the cut-level termwise
`d/dx expPartialSum N = expPartialSum (N−1)` (via the `IsDifferentiable` instances) is the remaining bridge.

### Marathon T2 — sin/cos Taylor convergence modulus by comparison to exp (2026-06-05)

`E213.Lib.Math.NumberSystems.Real213.ExpLog.CutTrigModulus` — **4 PURE / 0 DIRTY** (+ `expTerm_le_of_ge`
gap-antitone added to `CutExpModulus`).  The `sin`/`cos` Taylor term magnitudes *are* the `exp` terms at
odd/even indices (`cos` term `k` = `exp` term `2k`, `sin` term `k` = `exp` term `2k+1`), so the whole
`CutExpModulus` engine transfers by comparison: `cosTerm_geom_decay`/`sinTerm_geom_decay` (geometric
majorant at the even/odd sub-sequence, decay `term(m)/2^{2k}`) + `cosTerm_antitone`/`sinTerm_antitone`
(terms non-increasing past the threshold — the alternating-series-test hypothesis the signed `sinCut`/`cosCut`
bracketing will use).  Rung **T2** of the transcendentals marathon (term-magnitude convergence rate);
remaining: the signed cut-level series replacing the `Core/Functions.lean` stubs.

### Marathon P1 — discrete heat maximum principle (2026-06-05)

`E213.Lib.Math.Analysis.ODE.HeatEq.Discrete` (extended) — **4 new PURE / 0 DIRTY**.  The discrete heat step
is an average of two neighbours, so it neither rises above the field max nor falls below the min — the
discrete maximum principle, seed of all parabolic a-priori estimates.  In the numerator convention
`heatStepNum = 2·u_new = u_left + u_right`: `heatStep_le_two_max` (`u ≤ B` ⟹ `heatStepNum ≤ 2B`, no hot
spots), `heatStep_two_min_le` (`A ≤ u` ⟹ `2A ≤ heatStepNum`, no cold spots), `heatStep_range` (the doubled
value stays in `[2A,2B]` — sup-norm contraction), `heatStep_osc_bound` (the oscillation `max−min` does not
grow — the monovariant feeding P2).  **Iterated to all time** (`heatField`, `heatIter`): `heatIter_le` /
`heatIter_ge` / `heatIter_range` — data in `[A,B]` ⟹ the `t`-step field stays in `[2ᵗ·A, 2ᵗ·B]` (averaged
field in `[A,B]`) for *every* `t`, the discrete maximum principle for the whole heat evolution
(`‖u(t)‖∞ ≤ ‖u(0)‖∞`).  All uniform in the grid length `n` (hence in the mesh) — the uniformity that lets
the `Real213` limit promote it to the continuous maximum principle.

**P2 obstruction + lazy-step fix** (same file, 6 more PURE): strict *oscillation* decay is **false** for the
non-lazy stencil `(½,0,½)` — the checkerboard mode `0,1,0,1` maps to `2,0,2,0 = 2·checkerboard` (eigenvalue
`cos π = −1`, no gap).  The genuine smoothing operator is the **lazy** step `lazyHeatStepNum = u_{x−1}+2u_x+u_{x+1}`
(stencil `(¼,½,¼)`): `lazyHeatStep_const` (`= 4c`), `lazyHeatStep_le_four_max`/`_four_min_le` (its maximum
principle), and the concrete spectral-gap witness `lazy_checker_collapses` (length-4 checkerboard `→`
constant in one lazy step, osc `1→0`) vs `nonlazy_checker_hot`/`_cold` (non-lazy preserves it).  The
`−1`-eigenmode the non-lazy step preserves is annihilated by the self-weight.

**Strong (strict) maximum principle** (same file, 2 more PURE): `heatStep_strict_at_max` /
`lazyHeatStep_strict_at_max` — a max site with a strictly-below neighbour drops *strictly* (`< 2B` resp.
`< 4B`): heat cannot sustain a strict interior extremum (the strong maximum principle's discrete seed).
Honest nuance: holds for *both* stencils, yet the non-lazy step still fails global oscillation decay because
the max **relocates** (`[0,1,0,1]→[2,0,2,0]`) — local strict drop ≠ global spectral gap; the lazy
self-weight pins the extremum.

**Comparison principle** (same file, 4 more PURE): `heatStep_mono` / `lazyHeatStep_mono` (order-preservation
`u ≤ v ⟹ heatStep u ≤ heatStep v`, both stencils), `heatIter_mono` (preserved for all time), and
`heatStep_le_two_max_via_comparison` (the maximum principle re-derived as comparison against a constant
field — the two P1 estimates are one principle).  Rung **P1** of the discrete-PDE-estimates marathon;
next: oscillation decay rate (P2) + the `Real213` limit step.

### Discrete (Forman) Ricci curvature — the 213-native route to the A6 core (2026-06-05)

`E213.Lib.Math.Geometry.GeometrizationConjecture.DiscreteRicci` — **6 PURE / 0 DIRTY**.  A6's smooth-metric
conquest core is walled (Riemannian geometry + PDE); the 213-native route is **combinatorial** Ricci
curvature (Forman/Ollivier), no smooth manifold.  `formanEdge du dv = 4 − du − dv` (triangle-free
unweighted edge); complete-bipartite `K_{NS,NT}` uniform value `4 − NS − NT` (`forman_bipartite`).  Sign ↔
topology (`discrete_curvature_topology`): `K_{1,1}` `+2` / `K_{1,3}` `0` / `K_{3,2}` `−1` ↔ `b₁` 0/0/8 —
the trivial-loop ↔ rich-loop split the Poincaré pillar reads off `b₁`, here off curvature.  Rung 1 of the
A6-core marathon; next: weighted
Forman + a discrete Ricci-flow step driven to its normalized fixed point via `flow_reaches`.

### Cross-determinant number field = trace field + Eisenstein period arithmetic (2026-06-04)

The cross-determinant's number-field reading, promoted to
`theory/math/numbertheory/eisenstein_period_arithmetic.md` — **38 PURE / 0 DIRTY** across:

- `Real213.CrossDetTraceField` (**20 PURE**) — `fixForm_disc_eq_traceDisc`: the fixed-point
  form `(c, d−a, −b)` of a Möbius `M` has discriminant `tr²−4` (ring identity, ∀ `M`);
  `crossdet_number_field_is_trace_field` (golden `+5` / cusp `0` / Eisenstein `−3` faces);
  `fixForm_automorph` (monodromy preserves its form up to `det`); `disc_sign_is_line_cusp_curve`.
- `ModArith.EisensteinFormCharacter` (**11 PURE**) — `eisCyc_mod3_ne_two`: `a²+ab+b² ≢ 2 (mod 3)`,
  the χ₋₃ fingerprint; `mod3` shown a ring hom (`mod3_add`, `mod3_mul`).
- `Integer.EisensteinSplitting` (**5 PURE**) — `eisForm_composition` (disc-`−3` Brahmagupta
  multiplicativity); `eisenstein_local_splitting` (split `7,13` / ramified `N(1−ω)=3` / inert `2`).
- `Integer.EisensteinClassNumber` (**1 PURE**) — `reduced_disc_neg3_unique`: `h(−3)=1`, the only
  reduced form is `x²+xy+y²`.
- `Integer.EisensteinEuclidean` (**1 PURE**) — `covering_bound`: covering radius² `≤ 3/4 < 1`,
  why `ℤ[ω]` is norm-Euclidean.

Open frontier (recorded in `research-notes/frontiers/`): the split converse (`p≡1 mod3 ⟹` value,
needs the primitive-root theorem + Euclidean descent) and the transcendental period value
(`Γ(1/3)`, needs the cubic AGM / `L(1,χ₋₃)`).

### Invert universal property + deep-research additions (2026-06-03)

`E213.Lens.Number.FoundingDialUnification` — **4 PURE / 0 DIRTY**.  The number-tower founding
meets the concurrent non-holonomicity discriminant-dial marathon at one order-2 companion
`comp p q`, split along its two coordinates: `founding_unit_floors_dial_trace_runs_tiers` — the
founding unit `q = NS − NT` is the dial's fixed determinant (`det (comp p q) = q`); the trace `p`
runs the discriminant (`disc = p² − 4q`); the forced atomic counts are the tier boundaries —
`p = 0` elliptic (founding swap `S`), `p = NT` parabolic (`disc = 0`), `p = NS` hyperbolic (golden,
`disc = NS² − 4 = NS + NT = d`).  (Det-floor + trace-dial parametric; `p = NT`/`p = NS` landing on
the tiers is atomic — pins `NS = 3`.)  And `parabolic_at_NT_is_difference_lens_depth1` — the
parabolic tier (trace `NT`) is the **difference-Lens rung**: `liftKZ 1 s n = s(n+1) − s n` is the
`ℤ`-difference, and parabolic ⟺ that output is constant (`polyDepthZ 1`, depth-1).  And
`hyperbolic_at_NS_is_ratio_cauchy_rung` — the hyperbolic tier (trace `NS`, det = unit `NS−NT`,
disc = `d`) is the ratio/Cauchy rung: the convergents' cross-det is the *same* unit
(`convergent_lowest_terms_is_det`), completing to `φ` (`phiCauchy_limit_eq_phiCut`).  So the
founding number-rungs *are* the tiers: `ℤ`-sign = elliptic, `ℤ`-difference (depth-1) = parabolic,
`ℚ`/`ℝ` ratio/Cauchy = hyperbolic.  And `count_constants_are_difference_fixed_below_parabolic` —
`ℕ` (count, depth-0 constants) is the difference-Lens **fixed locus** (`liftKZ 1 (const) = 0`),
sitting at the bottom of the parabolic (depth-1) tier.  So *every* founding rung is placed on the
dial: `ℕ` difference-fixed bottom of parabolic, `ℤ`-difference full parabolic, `ℤ`-sign elliptic,
`ℚ`/`ℝ` hyperbolic.  Builds on `FoundingDynamicBridge`.

`E213.Lens.Number.Nat213.Tower.PairCompletionUniversal` — **19 PURE / 0 DIRTY**.  The invert
move's **complete universal property** (existence ∧ uniqueness), Quot-free and choice-free,
**validated concretely**: `intTarget` (`Int` as an `AbTarget` from the PURE `Int213` kit),
`natToInt_hom`, `liftZ`, and `addCCS_completion_is_Int` — the additive completion of
`(Nat213, +)` is `ℤ` (`liftZ` is the integer-difference map; `(2,1) ↦ +1`, `(1,2) ↦ −1`), and by
the capstone it is the unique factoring hom.  The universal property is non-vacuous.
`AbTarget` (abelian-group target, laws as ∀-equalities); `lift M H f (a,b) = f a − f b`;
existence — `lift_respects_pairEquiv` (well-defined on the completion), `lift_combine`
(homomorphism), `lift_eta` (factors `f` through `η m = (m∘a,a)`); uniqueness — `lift_unique`
(any `g` respecting `pairEquiv` + `combine` + `η` equals `lift`), via `pair_equiv_eta_combine`
(every pair `~ η(a) ∘ inv(η(b))`); capstones `invert_factors_through_any_group` and
`invert_is_the_universal_group_completion`.  Group-algebra toolkit `ab_neg_add`,
`ab_add_add_add_comm`, `ab_add_{left,right}_cancel`, `ab_neg_unique`.  Makes "invert is one
move" precise: the invert move is *the* universal group completion, unique up to iso (initiality,
not an imported adjunction).

`E213.Lens.Number.Nat213.Tower.PairCompletion` — **+2 PURE (17 total)**.
`diagonal_is_combine_identity` (the emergent diagonal *is* the `combine`-identity, unit-free —
the no-exterior principle in a readout) and `invert_branch_two_distinct_instances`
(`ℤ ⊥ ℚ_+`: `add 1 1 ≠ mul 1 1`, two instances of one move joined at the diagonal).

`E213.Lib.Math.CassiniUnimodular` — **+2 PURE (13 total)**.  `qpow_one` and
`multiplier_unit_magnitude_sign_order_NT`: the unimodular multiplier `q = ±1` factors as (unit
magnitude `qpow 1 n = 1`, order-`NT` sign `qpow (−1) NT = 1 ∧ qpow (−1) 1 ≠ 1`) — the genuine
`(unit, period) = (1, NT)` factorization (the arithmetic re-readings of `NS = NT+1` are
numerology).

### Number-tower founding + invert-move addition (2026-06-03)

`E213.Lens.Number.SharedUnitAcrossReadings` — **1 PURE / 0 DIRTY**.  The honest unification
of the axis-readings: `the_unit_is_one_across_readings` — the unit `1` is one value across
count-difference (`NS − NT`, `ns_minus_nt_is_one`), the Möbius/ratio determinant
(`mobius_det_eq_ns_minus_nt`, `mobius_det_is_unit`), the Cassini oscillation
(`toggle_det_unit`), and the reciprocal law (`qpair_mul_swap_eq_qOne`).  Identity-of-the-unit
(downward), not an operator monoid (which has no shared carrier).

`E213.Lens.Number.Nat213.Tower.PairCompletion` — **15 PURE / 0 DIRTY**.  Includes
`swap_order_eq_NT` (the swap's order is exactly `NT = 2`: involution + non-identity, so
period-2 is forced by the count, not chosen — no period-`k` on a pair).  The **invert
move as one theorem**: a generic `CommCancelSemigroup` on `Nat213` (op + comm + assoc +
right-cancel, **no unit**) with pair-completion `pairEquiv M p q := M.op p.1 q.2 =
M.op p.2 q.1`, equivalence-relation proofs (`pairEquiv_{refl,symm,trans}`), the `swap`
involution, and `combine`.  `combine_swap_equiv_diagonal` — `x ∘ inv(x)` lands on the
diagonal, so the completed group's identity **emerges** as the diagonal class, unit-free
(forced: `Nat213` has no additive `0`, yet its additive completion has an identity).
Instances `addCCS` (`op=+` → ℤ model) and `mulCCS` (`op=·` → ℚ_+); `mulCCS_recovers_qpairEquiv`
(`Iff.rfl`) recovers `NatPairToQPos.qpairEquiv`; capstone `invert_is_one_move`.  ℤ and ℚ_+
are one construction read on the two operations.

`E213.Lens.Number.Nat213.Order` — **8 PURE / 0 DIRTY**.  Native strict order
`lt a b := ∃ c, add a c = b` (no Lean `Nat` order — `Nat.lt_or_ge` / `Nat.le_antisymm` /
`Nat.mul_lt_mul_right` all pull `propext` + `Classical.choice` + `Quot.sound`).
`add_ne_self`, `lt_irrefl`, `lt_ne`, `succ_lt_succ_of_lt`, `lt_trichotomy` (structural
double recursion), `lt_mul_self` (strict square-monotonicity, **purely from
distributivity** — no order lemma), and the payoff `mul_self_inj` (`a·a = b·b → a = b`).

`E213.Lens.Number.Nat213.Tower.NatPairToQPos` — **+8 PURE (19 total) / 0 DIRTY**.  The
**reciprocal involution**, multiplicative twin of `NatPairToInt`'s negation: `qSwap`
(period-2, `qSwap_involutive`), `qpair_mul_swap_eq_qOne` (`x·(1/x)=1`, the reciprocal law),
`qOne_reciprocal_fixed` (`1/1=1`), `qpair_diagonal_collapse` (diagonal ~ unit `1`),
`reciprocal_fixed_of_unit` + `reciprocal_fixed_iff_unit` (the *exact* fixed-point
characterization `qSwap p ~ p ↔ p ~ qOne`, full twin of `zero_unique_negation_fixed`, via
`Order.mul_self_inj`), and the bundle `reciprocal_is_multiplicative_twin_of_negation`.  One
swap, two folds, two units (`0` for `+`, `1` for `·`).

### Non-holonomicity finite-state escape + depth-monotone bridge + discriminant dial (2026-06-03)

The non-holonomicity / holonomicity-hierarchy thread, closed end to end (all **0 DIRTY**):

`E213.Meta.Int213.Order` — **34 PURE**.  The ∅-axiom `Int` ordering layer (Lean-core
`Int.le_trans` / `lt_trichotomy` carry `propext`), rebuilt from the inductive `Int.NonNeg` +
the `ring_intZ` reflection tactic: `le_trans` / `lt_trans` / `lt_of_le_of_lt` / `lt_of_lt_of_le`,
`lt_irrefl` (the contradiction engine), `le_of_lt`, `add_le_add_{left,right}`, the sign trichotomy
`pos_zero_or_neg`, negation-reverses-order (`lt_of_neg_lt_neg`, `neg_pos_of_neg`), and the `ofNat`
order embedding (`ofNat_le`, `le_of_ofNat_le`).  Reusable foundation.

`E213.Lib.Math.Analysis.Cauchy.PolyDepthMonotone` — **11 PURE**.  `polyDepthZ_evMono`: every finite-Δ-depth
integer sequence is eventually monotone (non-decreasing or non-increasing).  LPO-free via the
constant-top-difference sign trichotomy — `c>0` ⟹ eventual strict increase (`posTop_evStrictMonoZ`,
the faithful-`Int` port of `positive_floor`'s descent + the eventual-positivity telescope
`evStrictMonoZ_eventually_pos`), `c<0` ⟹ negation (`liftKZ_negS_apply`, pointwise to dodge
`funext`'s `Quot.sound`), `c=0` ⟹ genuine depth-drop (faithful `Int` difference — the branch the
`ℕ` truncated version could not close).

`E213.Lib.Math.Analysis.Cauchy.ThueMorseRingEscape` — **4 PURE**.  `s2Z_not_polyDepthZ`: the binary digit-sum
(popcount) has no finite difference-depth (`MonoFromZ` contradicts `s2_not_eventually_monotone`,
`AntiFromZ` ⟹ bounded ⟹ contradicts `s2_unbounded` via `s2 (ones k) = k`).

`E213.Lib.Math.Analysis.Cauchy.DepthMonotoneSynthesis` — **2 PURE**.  Joins the algebraic and order-theoretic
readings of depth: `newtonZ_evMono` (every Newton polynomial is eventually monotone) and
`s2Z_not_polynomial` (popcount equals **no** polynomial `newtonZ c d`, the ring-escape read through
`DepthCharacterization.finite_depthZ_iff`).

`E213.Lib.Math.Analysis.Cauchy.HomogRecPeriodic` — **1 PURE**.  `evPeriodic_homogRec`: eventually periodic ⟹
`HomogRec` (the elementary half of the bounded-`HomogRec` characterization; order `k=p`, prefix
killed by an `if`-guarded `lead`/`R`).

`E213.Lib.Math.Analysis.Cauchy.CFiniteHomogRec` — **3 PURE**.  C-finite ⊆ P-recursive: `order2_homogRec` /
`order3_homogRec` (a constant-coefficient recurrence *is* `HomogRec`), `trib_homogRec` (Tribonacci is
holonomic — the opposite pole from Thue–Morse).

`E213.Lib.Math.Analysis.Cauchy.EllipticPeriodicTier` — **17 PURE**.  The order-2 companion discriminant as the
holonomicity-hierarchy dial: `comp_disc` (`disc (comp p q) = p²−4q` = the `HyperbolicEllipticTrace`
discriminant), `comp_eq_S` / `comp_eq_U` (the elliptic generators *are* the companions of the
periodic recurrences), the trichotomy — *elliptic* `periodic_elliptic_{S,U}` (periodic floor),
*parabolic* `parabolic_iff_depth1` (`disc=0` ⟺ linear depth-1, an iff), *hyperbolic*
`hyperbolic_strictMono` / `hyperbolic_grows` (strictly increasing, unbounded).  **The dial is
special to order 2 — it does not lift**: `cubic_disc` + `cubic_disc_witnesses` show `Δ₃`'s sign does
not classify periodicity (periodic `(0,0,1)` and growing Tribonacci `(1,1,1)` both `Δ₃<0`); the
order-3 periodicity dial is root-location (cyclotomic, `|c|=1`), witnessed by
`periodic_elliptic_order3_p4` / `periodic_elliptic_order3_p6`.

`E213.Lens.Number.FoundingDynamicBridge` — **1 PURE**.  `founding_swap_is_elliptic_floor`: the
number-tower founding's static invert-**swap** (= negation, period-2 by `NT`, `NatPairToInt.
swap_realizes_negation`) is the **elliptic floor** of the dynamic discriminant dial — `comp 0 1 = S`,
`Mat2.det (comp 0 1) = NS − NT` (floor determinant = the shared founding unit), `disc < 0`,
`S² = −I` (negation-of-identity), `zero_unique_negation_fixed`.  The static number-tower founding and
the dynamic non-holonomicity dial pinned as one structure (shared floor = unit `1`; shared ceiling =
the residue).

`E213.Lib.Math.Foundations.CeilingSchema` — **5 PURE**.  The residue ceiling is **one phenomenon**, not five
engines: `ReachedByNoStage gen target := ∀ s, gen s ≠ target`, `not_surjective_of_reachedByNoStage`
(the schema *is* non-surjectivity), and `ceilings_are_nonsurjectivity` bundling the universal
diagonal (`diag_reached`, Cantor archetype `∀ f, ¬Surjective f`), the non-holonomicity escape
(`s2Z_poly_reached`, popcount = no `newtonZ c d`), and the foundational residue
(`object1_not_surjective`) as one shape — the finite-stage map missing its target.  Classically one
Cantor/cardinality argument; ∅-axiom forces named constructive witnesses (the "engines" are
realizers, the domains Lens-carvings).

`E213.Lib.Math.Analysis.Cauchy.DetZeroCollapse` — **6 PURE**.  The determinant spectrum of the order-2
recurrence read on the Cassini / discrete-Wronskian `cas s n := s n · s(n+2) − s(n+1)²`:
`geometric_cas_zero` (order-1 ⟹ `cas ≡ 0`, the `det = 0` collapse — the orbit is a geometric ray,
one ratio value), `cas_step` (Abel–Liouville: `cas s (n+1) = q · cas s n`, so the Wronskian's
geometric ratio *is* the determinant `q`), `cas_conserved_unit` (`q = 1` ⟹ `cas` conserved) and
`cas_period2_neg_unit` (`q = −1` ⟹ `cas s (n+2) = cas s n`).  `det` is the quotient-space
characteristic value: `0` collapse, `±1` unit, `|q| ≥ 2` expansion.

`E213.Lib.Math.Analysis.Cauchy.WronskianDepth` — **8 PURE**.  The unit's two faces have **opposite
additive-depth status**: `cas_unit_depth0` (`det = +1` ⟹ the conserved Wronskian is `polyDepthZ 0`,
additively trivial — the magnitude unit) and `cas_neg_unit_no_finite_depth` (`det = −1` with
`W₀ ≠ 0` ⟹ the period-2 sign-flipping Wronskian is **not eventually monotone**, so has **no finite
depth** — additively maximal, the sign unit), bundled in `unit_faces_opposite_depth`.  Support:
`int_ne_neg_self`, `cas_neg_unit_ne_zero`, `cas_neg_unit_consecutive_ne`,
`period2_nonconst_not_evMono`.  One multiplicative unit, two opposite additive readings (the §5.2
`NT = 2` sign carries the additive richness).

`E213.Lib.Math.Analysis.Cauchy.GoldenPiFaces` — **3 PURE**.  φ and π named as the two unit faces:
`golden_companion_sign_face` (`comp 1 (-1)`, the Fibonacci companion `x²−x−1`, has `disc = 5 =
NS+NT` and `det = −1` — φ is the **sign face**), `golden_cassini_period2` (any golden orbit's
Cassini is period-2, the classical `F(n+2)F(n)−F(n+1)² = (−1)^{n+1}`), and
`golden_cassini_no_finite_depth` (with nonzero initial Cassini, φ's Cassini has no finite
difference-depth — additively maximal).  π is the `det = +1` magnitude (elliptic/rotation) face at
an irrational angle — the open pole where the periodic floor fails.

`E213.Lib.Math.Analysis.Cauchy.ZeroInfinityHole` — **5 PURE**.  `0` and `∞` as **one hole, not two dual
values** — the single point where the reciprocal fold `x ↦ 1/x` returns no value, named twice (`0`
from inside the values, `∞` through the reciprocal).  `zero_no_reciprocal` (`q · 0 ≠ 1` — `0` is the
unique non-invertible point, the value-side name of `∞`), `self_reciprocal_iff_unit` (`q·q = 1 ↔ q =
±1`, via the PURE `Int213.int_sq_le_one` — the reciprocal-fixed core is exactly the units) and its
contrapositive `non_unit_not_self_reciprocal`, `cas_zero_collapses` (`det = 0` ⟹ the Casoratian
vanishes from the next step — the hole's value-image is the area crushed to `0`), bundled in
`zero_is_hole_units_are_core`.  Treating `0` as a value smuggles half of an `∞`-system: a
reciprocal-closed value-system admitting `0` is forced to admit `1/0`; the founding's `ℚ₊` excludes
both symmetrically (`qSwap` total, unique fixed point `1`).  Collapse at the hole, conservation on the
reciprocal-fixed core `±1`.

`E213.Lib.Math.MaxEntropy` — **8 PURE**.  Structurelessness as a **positive intrinsic property**.
`MaxEntropy s := ¬ ∃ d, polyDepthZ d s` — no finite holonomic certificate generates `s` (the
*incompressibility* / measure-free reading of maximum entropy; the measure reading would smuggle an
exterior ruler).  `maxEntropy_reachedByNoStage` / `maxEntropy_not_surjective` (a max-entropy
sequence forces the universal Newton generator `newtonGen` to be non-surjective — the ceiling's own
non-surjection, read as a property of `s` not of a tactic).  The proven escapes collected under the
one predicate: `thueMorse_maxEntropy` (the dense automatic popcount counter) and
`golden_cassini_maxEntropy` (the `det = −1` sign face), joined in `maxEntropy_two_faces`.  The
non-holonomic pole is not a blank left open but the *presence* of maximal genericity —
source-without-enclosure named in information terms; not stipulated (the residue's genericity is the
theorem `object1_not_surjective`, and a `MaxEntropy` sequence is its constructive realizer).

`E213.Lib.Math.DetSpectrumPoles` — **1 PURE**.  The capstone uniting the two ends of the
det-spectrum as the **two folds' non-values**: `det_spectrum_poles_and_center` — for an order-2 orbit
read on its Casoratian, `q = 0` collapses into the **multiplicative hole** (`cas s (n+1) = 0`,
`ZeroInfinityHole`); `q = −1` (nonzero seed) is the **additive ceiling** (`MaxEntropy (cas s)`, no
finite handle, `WronskianDepth`); and the magnitude unit `q = +1` (nonzero seed) is the
**doubly-finite center** — never `0` (away from the hole, via conservation) and `polyDepthZ 0` (away
from the ceiling).  The two degeneracies bracketing the live region are not unrelated pathologies but
the multiplicative fold's hole (`0`/`∞`) and the additive fold's ceiling (maximum entropy /
non-surjection) — the two non-values the number tower excludes; the unit is where a genuine
distinguishing survives.

`E213.Lens.Number.IntFoldForms` — **13 PURE**.  Realizes canon §6.9 (status-symmetric folds): ℤ's
own fold is negation `x ↦ −x`, and a fold is correct only if `0` and `∞` carry the same status (both
genuine carrier elements).  Plain ℤ is torsioned (`0` present, `∞` absent); there are exactly **two**
correct closures.  **One-point** `ℤ̂ = Option Int` with `∞ = −∞`: `negHat` is an involution
(`negHat_involutive`) whose fixed points are exactly `{0, ∞}` (`negHat_fixed_iff`) — both fixed
(`negHat_zero_and_inf_fixed`), the form reciprocal reads by *swapping* `0 ↔ ∞`.  **Two-point**
`ℤ̄ = IntBar` with `+∞ ≠ −∞`: `negBar` fixes only `0` (`negBar_fixed_iff`) and **swaps** `±∞`
(`negBar_zero_fixed_inf_swapped`).  In both the genuine integers `n ≠ 0` are proper 2-cycles `{n, −n}`
(`negHat_value_two_cycle`) — `0`/`∞` are the fold's symmetry centres, not stratum-values.  Bundled in
`int_correct_fold_forms`.  `neg_neg_int` / `neg_self_zero` (constructor-matched Int helpers, the
`int_ne_neg_self` pattern); literal `−0 = 0` closures by `decide`.

`E213.Lens.Number.FoldDuality` — **13 PURE**.  The two founding folds meet on the shared four-point
fixture `Q4 = {∞, 0, +1, −1}` (the reciprocal-closed core of `ℤ̂`) and are **exact mirror images**:
negation `negQ` **fixes** the 영무한대 pair `{0, ∞}` (`negQ_fixes_zeroInf`) and **swaps** the units
`{±1}` (`negQ_swaps_units`); reciprocal `recQ` **swaps** `{0, ∞}` (`recQ_swaps_zeroInf`) and **fixes**
`{±1}` (`recQ_fixes_units`).  Both involutions (`negQ_involutive`, `recQ_involutive`); fixed-point
characterizations `negQ_fixed_iff` (`= {0,∞}`) / `recQ_fixed_iff` (`= {±1}`); status-symmetry
predicates `BothFixed` / `Swapped`; capstone `two_folds_dual_on_pairs`.  Each ℤ/2 fold fixes the
two-element orbit the other swaps — the additive and multiplicative folds exchange the roles of the
hole pair and the unit pair (the sharpest "0 is to `+` as 1 is to `×`").  All by `rfl` / `decide`.

`E213.Lens.Number.FoldKlein` — **9 PURE**.  The two folds **generate a Klein four-group** on the
fixture.  Their composite `bothSwap := negQ ∘ recQ = recQ ∘ negQ` (the two folds **commute**,
`negQ_recQ_comm`) is the **third non-identity involution** — it **swaps both** orbits
(`bothSwap_swaps_both`) and so is **fixed-point-free** (`bothSwap_no_fixed`).  `klein_four_group`
bundles the full `ℤ/2 × ℤ/2` table (each involutive + the three pairwise products close among them);
`klein_fixed_orbit_profile` distinguishes the three non-identity elements by which orbit they fix —
`negQ` the hole pair `{0,∞}`, `recQ` the units `{±1}`, `bothSwap` neither.  The additive fold, the
multiplicative fold, and their antipode product exhaust the involutive symmetries of the hole/unit
fixture.  All by `rfl` / `decide`.

`E213.Lib.Math.NumberSystems.Real213.FoldReflections` — **11 PURE**.  The matrix witness of `FoldKlein`: the two
folds are the integer matrices `N = [[−1,0],[0,1]]` (negation) and `R = [[0,1],[1,0]]` (reciprocal),
both **involutive reflections** (`N_involutive`, `R_involutive`; `N_det = R_det = −1`), and their
product is the founding elliptic swap `N · R = S` (`negation_recip_eq_swap`, `ModularElliptic.S`,
`det = +1` — two reflections compose to a rotation).  `S² = −I` (`S_sq_central`) — matrix order `4`
halving to projective order `2`; the folds commute only projectively (`recip_negation_eq_neg_swap`:
`R · N = −I · S`, differing by the central Cassini sign).  Capstone
`two_reflections_compose_to_founding_swap`.  All by `decide`.  Closes the cross-frame link
`FoldKlein` left narrative.

`E213.Lib.Math.NumberSystems.Real213.EllipticCycleFixtures` — **7 PURE**.  The two elliptic generators of
`PSL(2,ℤ) = ℤ₂ * ℤ₃` as cyclic fixtures.  `S` (the folds' product, `FoldReflections`) has projective
order 2 (`S_proj_order_2`, `S² = −I`) — the 영무한대 swap.  `U = [[0,−1],[1,1]]` has projective
order 3 (`U_proj_order_3`, `U³ = −I`): its Möbius action `z ↦ −1/(z+1)` is a fixed-point-free
**3-cycle** `∞ ↦ 0 ↦ −1 ↦ ∞` on the Eisenstein fixture `{∞, 0, −1}` (`uCyc`, `uCyc_cube`,
`uCyc_no_fixed`, `uCyc_sq_no_fixed`).  Capstone `elliptic_generators_are_two_and_three`: projective
orders `2, 3` are the free factors of the modular group; the matrix orders `4, 6` reduce through the
central `−I`.  All by `rfl` / `decide`.

`E213.Lib.Math.NumberSystems.Real213.HyperbolicBoost` — **11 PURE**.  The hyperbolic face of "product of two
reflections": the golden iterator `G = [[2,1],[1,1]]` (φ's Möbius map, `det = 1`) factors as
`A · B` (`golden_boost_eq`) with `A = [[1,0],[−1,−1]]`, `B = [[2,1],[−3,−2]]` both involutive
reflections (`A_involutive`, `B_involutive`; `A_det = B_det = −1`).  `G` is **hyperbolic**
(`G_hyperbolic`: `trace 3 > 2`, `disc = tr²−4 = 5 = NS+NT`, real eigenvalues, infinite order — no
periodic floor), the boost to the elliptic `S = N·R`'s rotation (`FoldReflections`).  Capstone
`two_reflections_compose_to_golden_boost`: every `SL(2,ℤ)` element is a product of two reflections;
`|trace|` against `2` selects rotation (elliptic, periodic) vs boost (hyperbolic, aperiodic) — the
same `tr²−4` dial.  All by `decide`.

`E213.Lib.Math.NumberSystems.Real213.ParabolicTranslation` — **10 PURE**.  Completes the trichotomy's third face:
the parabolic translation `T = [[1,1],[0,1]]` (`det = 1`, `trace = 2`, `disc = 0`, `T_parabolic`)
factors as `Aₚ · Bₚ` (`parabolic_translation_eq`) with `Aₚ = [[1,0],[0,−1]]`, `Bₚ = [[1,1],[0,−1]]`
both involutive reflections in **parallel** mirrors.  Capstone `sl2_trichotomy_as_two_reflections`:
the whole `SL(2,ℤ)` order-2 trichotomy is one frame — product of two reflections — with `tr²−4`
selecting the face: elliptic `S = N·R` (`disc = −4`, rotation), parabolic `T = Aₚ·Bₚ` (`disc = 0`,
translation, the difference-Lens depth-1 rung), hyperbolic `G = A·B` (`disc = 5`, boost).  All by
`decide`.

`E213.Lib.Math.NumberSystems.Real213.Mat2CayleyHamilton` — **4 PURE**.  The root of the dial:
`cayley_hamilton` — every `Mat2` satisfies `M² = tr(M)·M − det(M)·I` (`= charComb`), proved
**generally** by `ring_intZ` (not `decide`).  `char_poly_discriminant`: `disc = tr²−4·det` is the
discriminant of the characteristic quadratic `λ² − tr·λ + det`; `dial_is_char_discriminant` bundles
the two — Cayley–Hamilton is the primitive, the elliptic/parabolic/hyperbolic trichotomy is the sign
of its discriminant.  (`S²=−I`, `U²=U−I`, `T²=2T−I`, `G²=3G−I` are the `(tr,det)` specializations.)
Proved propext-free via `show` + entry `rw` (`Mat2.mk.injEq` / `simp` pulls `propext`).

`E213.Lib.Math.NumberSystems.Real213.Mat2Assoc` — **1 PURE**.  `mul_assoc` — `Mat2` multiplication is associative,
`(M·N)·P = M·(N·P)`, proved **generally** by `ring_intZ` (propext-free, `show` + entry `rw`).  The
monoid law the dial's readings presuppose: with `I2` it makes `Mⁿ` well-defined and the
Cayley–Hamilton trace recurrence `tr(Mⁿ⁺¹) = tr·tr(Mⁿ) − det·tr(Mⁿ⁻¹)` available — the bridge from
the static dial to iteration dynamics (elliptic orders, hyperbolic growth).

`E213.Lib.Math.NumberSystems.Real213.Mat2TraceRecurrence` — **5 PURE**.  The trace recurrence, Cayley–Hamilton
iterated: `trace_recurrence` — `tr(Mⁿ⁺²) = tr(M)·tr(Mⁿ⁺¹) − det(M)·tr(Mⁿ)` (via `mul_assoc` +
`cayley_hamilton` + `tr_mul_charComb`).  The matrix powers' traces are a constant-coefficient
recurrence whose characteristic discriminant is the dial `disc = tr²−4·det` — the trichotomy made
dynamic (elliptic bounded/periodic, hyperbolic growing).  Golden boost: `golden_trace_recurrence`
(`tr(Gⁿ⁺²) = 3·tr(Gⁿ⁺¹) − tr(Gⁿ)`, the Lucas recurrence) + `golden_trace_seed` (`2, 3` → `2,3,7,18,…`
strictly increasing, so `G` is aperiodic — the hyperbolic infinite order, dynamic shadow of
`disc = 5 > 0`).  `pow` matrix power; `tr_mul_charComb` trace-linearity over the CH combination.

`E213.Lib.Math.NumberSystems.Real213.HolonomyLattice` — **25 PURE / 0 DIRTY**.  Holonomy of a loop of
state-transitions: `holonomy : List Mat2 → Mat2`, the ordered fold-product of a path — the §6.6
collapse (state-transition = state) made computational, since a loop of *transitions* composes to a
*state* of the same kind (the modular/Möbius matrix is the representation in which the two readings
coincide).  Three faces: ★ `holonomy_append` (**functoriality** — `holonomy (p++q) = holonomy p ·
holonomy q`, a monoid hom from the free path monoid to `(Mat2,·)`); ★ `det_holonomy_eq_one`
(**flatness** — every step `det = 1` ⟹ holonomy `det = 1` around the whole loop; `det = 1 = NS − NT`
the founding shared unit, the conserved invariant); ★ `positive_loop_trivial` (**the ℕ⁺ sector is
loop-free** — no non-empty word in the Stern–Brocot generators `L = [[1,0],[1,1]]`, `R = [[1,1],[0,1]]`
returns to `I`, via the strictly-growing entry-sum `positiveWord_entrySum_gt_two` on the positive
interior `Pos`; the positive monoid `⟨L,R⟩` is a tree).  ★ `first_loop_is_the_fold` — the first
non-trivial loop appears **exactly when the negation-fold composite `S` is admitted**: `holonomy
[S,S] = −I ≠ I` (order 4, the elliptic Gaussian period), `S.b = −1` the sign the ℕ⁺ sector excludes —
holonomy is the residue-internal signature of the fold ℕ⁺ → ℤ (the sign-Lens of §6.7).  Supporting:
`one_mul` (Mat2 left identity), `det_mul` (Cauchy–Binet `2×2`, `ring_intZ`), `mul_{L,R}_eq`,
`pos_mul_{L,R}`, `entrySum_{mul_L,mul_R,lt_L,lt_R,ge_two}`, `holonomy_pos`.  Builds on
`HyperbolicEllipticTrace` (`Mat2`) + `Mat2Assoc` (`mul_assoc`) + `Int213.Order`.

`E213.Lib.Math.NumberSystems.Real213.GoldenAperiodic` — **3 PURE**.  The hyperbolic infinite order made a theorem:
`golden_trace_mono` (the Lucas trace is monotone above `2` — `2 ≤ tr(Gⁿ) < tr(Gⁿ⁺¹)`, induction on
the recurrence with the `Int213.Order` inequalities), `golden_trace_gt_two` (`tr(Gⁿ⁺¹) > 2 = tr I`),
and ★ `golden_aperiodic` (`Gⁿ⁺¹ ≠ I` for every `n` — the trace exceeds `tr I`, so `G` never returns).
The golden boost has **infinite order**, the dynamic signature of `disc = 5 > 0` (contrast the
elliptic `S⁴ = I`, `U⁶ = I`); φ's iterator never comes back.

`E213.Lib.Math.NumberSystems.Real213.EllipticTracePeriodic` — **4 PURE**.  The mirror of `GoldenAperiodic`: the
elliptic trace recurrence collapses to `tr(Sⁿ⁺²) = − tr(Sⁿ)` (`S_trace_recurrence`, `tr S = 0`,
`det S = 1`), so the trace is **period 4** (`S_trace_period4`) and **bounded**, cycling `2, 0, −2, 0`
(`S_trace_seed`).  Boundedness is the `disc < 0` elliptic signature, opposite the `disc > 0`
hyperbolic unbounded Lucas growth.  Capstone `elliptic_trace_periodic`.  (Local ∅-axiom `nneg`
`− −x = x`; `zero_mul` / `one_mulZ` / `Order.zero_sub` collapse the recurrence.)

`E213.Lib.Math.NumberSystems.Real213.UTracePeriodic` — **5 PURE**.  The second elliptic generator `U` (`tr 1`,
`det 1`, `disc = −3`) carries the period-6 trace: `U_trace_recurrence` (`tr(Uⁿ⁺²) = tr(Uⁿ⁺¹) −
tr(Uⁿ)`) → `U_trace_step3` (`tr(Uⁿ⁺³) = −tr(Uⁿ)`) → `U_trace_period6` (period 6), cycling
`2,1,−1,−2,−1,1` (`U_trace_seed`).  Capstone `elliptic_orders_four_and_six`: `S` (period 4,
`|ℤ[i]^×|`) and `U` (period 6, `|ℤ[ω]^×|`) carry the `{4,6}` Gaussian/Eisenstein trace periods, both
bounded (`disc < 0`), against the hyperbolic unbounded growth.

Also extended this thread (already cataloged elsewhere): `Cauchy.ThueMorseAperiodic` (42 PURE — the
canonical dense witness, run-length ≤ 2, automatic structure `tm_eq_popParity`, dyadic
self-similarity, witness unification `isPow2_eq_s2_one`, the continued fraction `tmCF`) and
`Cauchy.MorseHedlund` (16 PURE — `bool_autoRec_iff_evPeriodic`).

### Real-number stratification addition (2026-06-01)

`E213.Lib.Math.NumberSystems.Real213.RateStratification` — **28 PURE / 0 DIRTY**.
The constructed-modulus generator's smallness law made a layer-by-layer
**W-vs-d comparison**, graded by probe schedule: `DominatesS W d ρ i` (the
ladder note's `Dominates_s`; `Dominates` is the `ρ = id` instance),
`htelS_iff_dominatesS` (the graded rate certificate `HtelS a d ρ` is
*exactly* `ρ`-domination at every layer, for any schedule — `htel_iff_dominates`
the identity instance), `dominated_free_modulus` / `dominatedS_graded_modulus`
(domination everywhere ⟹ modulus `k+2` / `k^s+1`), `overtakeS_breaks_layer`
(any layer where the cross-determinant overtakes the scheduled denominator
quantum breaks it), the unimodular det-1 floor as the trivially-free bottom
(`floor_dominates_all` / `floor_carries_Htel` / `tower_stratification`),
and ★★★ the **strict-separation witness**: `sepDen` (`d_{i+1} = (⌊√i⌋+2)·d_i`,
`W = d`) is root-2-dominated at *every* layer (`sep_dominatesS_all`) yet
breaks `Dominates` at layer 4 (`sep_breaks_unit_schedule`, `1296 ≤ 1080` fails)
— rescue is graded the way `CompletabilityGrade` grades break
(`graded_stratification` capstone).  The witness is carried end to end:
`sepNum` (`a_{i+1} = (⌊√i⌋+2)·a_i + 1` solves the cross-det relation over ℕ,
`sep_cross_det`: `W = d` exactly) makes `sepNum/sepDen` an actual presentation
completing through the degree-2 schedule with constructed modulus `N = k²+1`
(★★★ `sep_graded_modulus`) — a real rescued outside the degree-1 class.
The **schedule comparison law**: ★★ `dominatesS_schedule_mono` — a slower
schedule inherits domination iff (beyond `d` non-decreasing + `ρ' ≤ ρ`) the
**gap law** holds (`1/ρ' − 1/ρ` non-increasing across the layer,
cross-multiplied); ★★ `schedule_comparison_needs_gap` — the gap law is not
dispensable (`W ≡ 1, d ≡ 6` at layer 2: identity dominates `18 ≤ 18`, root-2
fails `7 ≤ 6`): pointwise the ladder is *not* a chain — rungs are independent
comparisons.  The forward additive-cancel used the PURE
`NatHelper.le_of_add_le_add_left` (Lean-core `Nat.le_of_add_le_add_left` is
propext-dirty); the floor polynomial identity is discharged by the
`Meta.Nat.PolyNat` reflection ring.

`E213.Lib.Math.NumberSystems.Real213.RateModulus` — **11 PURE / 0 DIRTY**.  ★★★
**The graded rate generator** (modulus-degree ladder rung 1).  The margin
telescope is parametrized by a probe schedule `ρ`: `HtelS a d ρ` (the margin
`e_i + 1/(ρ_i·d_i)` is non-increasing) plus one admitted layer (`k ≤ ρ i₀`)
yields the cut constant past `i₀+1` (`rateS_cut_const` / `rateS_total_modulus`).
The identity schedule recovers `Htel` definitionally (`htelS_of_htel`) and
`rate_total_modulus`'s `N(m,k) = k+2`; the degree-`s` root schedule
`ρ = rootFloor s` admits `k` at layer `k^s` (`rootFloor_pow`), giving ★★★
`graded_total_modulus`: **`N(m,k) = k^s + 1`** — at the admission layer
`i = r^s` the schedule defends slack `1/(r·d_i)` where the identity schedule
defends `1/(r^s·d_i)`, an `r^{s-1}` factor of overtake forgiven, paid as
modulus degree.  `Htel_of_crossdet` (the W-smallness bridge) unchanged;
`hmono_of_hmonoS` (full monotonicity from the one-step strict inequality +
positive denominators) so instances supply only `hmonoS`.

`E213.Meta.Nat.PowBasic` — **6 PURE / 0 DIRTY**.  The arbitrary-base power
toolkit (`powBase_le`, `powBase_lt`, `one_le_pow`, `self_le_pow`,
`pow_mul_pure`, `one_pow_pure`) — Lean-core counterparts are propext-dirty;
base-2 specializations live in `Meta.Tactic.Pow213`.

`E213.Meta.Nat.RootFloor` — **11 PURE / 0 DIRTY**.  The integer `s`-th root,
floor reading: `rootFloor s x` = largest `r ≤ x` with `r^s ≤ x` (bounded
descent `rootFloorGo`), sandwich characterization (`rootFloor_pow_le` /
`rootFloor_succ_pow_gt`), exact calibration on powers (`rootFloor_pow :
rootFloor s (k^s) = k`), monotone in the radicand (`rootFloor_mono`).  The
degree-`s` probe schedule of the graded rate generator.

`E213.Lib.Math.NumberSystems.Real213.BracketModulus` — **3 PURE / 0 DIRTY**.  ★★★
**The conversion-law engine** (`N = rate⁻¹ ∘ distance`, ladder rung 2 form) for
two-sided bracket presentations: strictly increasing lower fold `a/d`,
non-increasing upper companion `A/D`, per-layer sandwich `a_n/d_n < A_n/D_n`.
A probe not strictly `Inside` the layer-`n₀` bracket exits to one of two stable
sides (`below_fwd`: the fold passes it, cut false forward; `above_fwd`: the
companion caps it, cut true forward) — `bracket_cut_const`.  One hypothesis,
the **exclusion depth** `B` (`Inside at n ⟹ n ≤ B k`), yields the total
∅-axiom modulus `N(m,k) = B k + 2` (`bracket_total_modulus`).  Unconditional
engine; the measure enters only through `B`.

`E213.Lib.Math.NumberSystems.Real213.ExpLog.PiMeasureModulus` — **16 PURE / 0
DIRTY**.  ★★★ **π/2 (and π) conditionally degree-`s`** — ladder rung 2, first
named instance.  The Wallis fold gets a decreasing upper companion
`U_n = W_n·(2n+2)/(2n+1)` (`upNum/upDen`, `up_mono` via the exact identity
`4(n+1)²(2n+4)(2n+1) + 2(n+1)(2n+1) = (2n+2)(2n+1)(2n+3)²`, `ring_nat`),
giving a per-layer shrinking bracket of width `W_n/(2n+1) ≤ 2/(2n+1)`.
`PiHalfMeasure C s` — the effective irrationality measure of π/2 in pure ℕ
bracket form (probe inside layer `n` ⟹ width ≥ `1/(C·k^s)`); classically
`μ(π) ≤ 7.103` (Zeilberger–Zudilin 2020), not formalized — the analytic cost
isolated in this one inequality.  `measure_exclusion` (depth `n ≤ C·k^s`, via
`wallisNum_le_two_den` from `wallis_upper_inv`), then ★★★
`halfPi_measure_modulus` / `pi_measure_modulus`: total modulus
**`N(m,k) = C·k^s + 2`** (π: `C·(2k)^s + 2`).  π moves from "completion
modulus as opaque hypothesis" to "conditional degree-`s` modulus".  §4, the
unconditional negative: `wallis_cross_det` — **the Wallis cross-determinant is
the full product `W_n = a_n·d_n`** (`(2n+1)(2n+3)+1 = 4(n+1)²`; why the
presentation's divergence depth is 6, ratio degree 4) — and ★★★
`wallis_overtakes_every_schedule` / `wallis_no_graded_certificate`: for
**every** positive schedule `ρ`, scheduled domination fails at every layer
`n ≥ 2` (`(2n+1)(2n+3) < wallisNum n` from layer 2), so
`HtelS wallisNum wallisDen ρ` fails — **the Wallis pointing's rung is `∞`**,
proved, not estimated; the rung is a property of the pointing, not of π.

`E213.Lib.Math.NumberSystems.Real213.FiniteOrderSpectrum` — **29 PURE / 0
DIRTY**.  ★★★ **The finite-order spectrum of `SL(2,ℤ)`, uniform** — the
crystallographic restriction as a single structural theorem (every matrix,
every exponent), upgrading the range-13 totient census
(`CyclotomicTraceDegree.crystallographic_restriction`).  Trace trichotomy on
one engine (`Mat2TraceRecurrence.trace_recurrence`): `tr ≥ 3` — strict trace
growth from floor 2 (`trace_mono_of_ge_three`, generalizing
`golden_trace_mono` off `t = 3`) ⟹ no return; `tr ≤ −3` — the square has
`tr(M²) = tr² − 2 ≥ 7` (`tr_sq`) and inherits the order ⟹ no return;
`tr = ±2` — **parabolic rigidity**: the closed form `Mᵏ = I + k·(M − I)`
(`parabolic_pow`, componentwise ℤ induction) forces `M = I` / `M² = I`;
`tr ∈ {0, ±1}` — unconditional elliptic orders from Cayley–Hamilton
(`M² = −I`, `M³ = ∓I` via `cube_entries`).  Capstones ★★★
`finite_order_spectrum` (`M^{n+1} = I ⟹ M = I ∨ M² = I ∨ M³ = I ∨ M⁴ = I ∨
M⁶ = I`) and ★★★ `finite_order_divides_twelve` (`⟹ M¹² = I`): six is the
last finite period of the integer rotation family; `S⁴ = I`/`U⁶ = I` realize
the top orders, `golden_aperiodic` sits just past the wall.  The ∀-form
debate's build item: the finite side of "whatever modulus you bring" is now
one uniform theorem.  (Power algebra `I_mul`/`mul_I`/`pow_add`/`pow_pow`/
`det_mul` included; `ring_intZ` does the component identities — note its
normal form does not prune explicit `0·x`/`1·x` terms, use
`zero_mul`/`one_mulZ`/`mul_one` first.)  §6, the two-sided spectrum: ★★★ `no_order_five`
(`det M = 1`, `M⁵ = I ⟹ M = I` — **no five-fold lattice symmetry**, the
crystallographic crown jewel / pentagon-forbidden axis) and `no_order_seven`,
both via `finite_order_spectrum` + Bezout-free coprime collapse (each realized
order is coprime to 5 / 7); `exact_order_four`/`exact_order_six` (`S`/`U`
realize orders 4/6 exactly, by `decide` on the non-identity powers); capstone
★★★ `crystallographic_spectrum` — the finite-order spectrum of `SL(2,ℤ)` is
exactly `{1,2,3,4,6}`, five the first forbidden (so the only prime orders are
2, 3: `PSL(2,ℤ) = ℤ₂ ∗ ℤ₃`).

`E213.Lib.Math.Analysis.Cauchy.DepthAperyCubic` — **23 PURE / 0 DIRTY**.  The Apéry
zeta coefficient-degree statistic: the minimal-holonomic recurrence coefficients
of ζ(2) (`(n+1)²uₙ₊₁=(11n²+11n+3)uₙ+n²uₙ₋₁`, degree 2) and ζ(3)
(`n³aₙ=(34n³−51n²+27n−5)aₙ₋₁−(n−1)³aₙ₋₂`, degree 3) are discrete polynomials whose
finite-difference depth equals their degree.  `zeta2_to_zeta3_degree_step`,
`apery_cubic_rung` (`aperyTop=n³`, `aperyLead=34n³−51n²+27n−5`, `aperyBot=(n−1)³` all
`polyDepth 3`, floors `6,204,6`), `zeta2_quadratic_rung` (floors `2,22,2`).  Exactness:
`aperyTop_depth_exact` / `zeta2Top_depth_exact` (`polyDepth d ∧ ¬ polyDepth (d−1)`).
ζ(3)'s cubic coefficients reindexed to `n=m+2` (all-positive); cubic/quadratic
difference identities discharged by the `Meta.Nat.PolyNat` reflection ring; lower bounds
by `decide`.  Degree is *incidental to irrationality* (ζ(4) order 2, Catalan β(2) open) —
ζ(3) degree 3 is the exception above the order-2 degree-2 Apéry-like family.

`E213.Lib.Math.NumberTheory.{AperyRecurrence, AperyIntegrality, FactorialLcmDvd,
LcmGrowthChebyshev, Legendre, PrimeValuation, FTALite, FactorialRatioBound,
LcmBoundMain}` + `E213.Lib.Math.NumberSystems.Real213.Zeta3Apery` — **140 PURE / 0
DIRTY** (the ζ(3) Apéry arithmetic; narrative
`theory/math/numbertheory/apery_zeta3_arithmetic.md`).  **The nucleus**:
`AperyRecurrence.apery_recurrence` (Apéry's recurrence `(j+2)³B(j+2)+(j+1)³B(j)=
aperyLead(j)B(j+1)` for `B(n)=ΣC(n,k)²C(n+k,k)²`, the WZ/creative-telescoping
identity, found by exact interpolation then re-derived: `reduced_wz_identity`
polynomial core in `j=k+d`, `colrec`/`lowrec` + `R0/R1/R2/G1` `W`-factoring,
`redid_eq`, `per_k`, `sumTo_shift_eq` telescope).  `Zeta3Apery.zeta3Den_eq`
(`zeta3Den n=(n!)³B(n)`, denominator orbit↔sum bridge).  **I2 (lcm race)**:
`LcmBoundMain.lcmUpTo_le` (`lcm(1..n)≤10^{15⌈n/30⌉}≈√10ⁿ`) via `legendre`
(`vₚ(n!)`), `vp_lcmUpTo`, `count30`, `key_divisibility`, `step3`.  **I1 (Brick 2)**:
`keydiv` (KeyDiv `m·C(k,m)∣lcm`, via the even/odd-ℕ finite-difference identity, no
ord_p), `heart` (L2), `heart_lcm`/`cube_dvd_lcm_cube`, `two_lcmCube_dvd_factCube`
(`2lcm³∣(n!)³`).  All-`ℕ` throughout (no `ℚ`, no `Int`); `ring_nat` kept additive
(`Q>0` in range).  Open: numerator integrality (harmonic, no clean certificate;
`Zeta3Numerator.harmonic_part_recurrence` lands the `H₃` part).

`E213.Lib.Math.Analysis.Cauchy.DepthSelfReference` — **3 PURE / 0 DIRTY**.  The `diff` ladder
realises self-reference's Converge / Escape outcomes (`Lens.SelfReferenceThreeOutcomes`) on
`Nat` sequences: `floor_converges` (`W` `reachesFloor`, settles at the unit `1 = det P =
NS−NT`, the Lambek terminating descent) and `geom_escapes` (`2ᵏ` `¬ reachesFloor`, the
residue's top-less ascent), bundled in `diff_converge_or_escape`.  Naming capstone — no
operator forced across the Raw-peel vs `Nat`-`diff` types; parallel readings of the §5.2
self-pointing sharing the count-Lens unit `1`.

`E213.Lib.Math.Analysis.Cauchy.DepthResidueFloor` — **2 PURE / 0 DIRTY**.  The self-pointing depth
ladder anchored at the residue floor: `diff` as a pointing event, depth as the count of
re-pointings to self-coincidence.  `floor_polyDepth0` (`P`/φ Cassini `W` is depth 0 — the
self-same rule that is its own fixed point) and `self_pointing_depth_ladder` (`polyDepth 0
W ∧ polyDepth 1 ratio ∧ polyDepth 2 zeta2Top ∧ polyDepth 3 aperyTop`): from the `P`/φ floor
the depth climbs by one degree of `n`-dependence per rung (e:1, ζ(2):2, ζ(3):3).  Reads the
divergence-depth count as drift-from-pure-self-reference, placing it inside the
residue/no-exterior canon (`DepthCeilingResidue` = infinite depth = residue).

`E213.Lib.Math.Analysis.Cauchy.DepthQuadraticGeneric` — **7 PURE / 0 DIRTY**.  Every quadratic
discrete polynomial has divergence-depth 2: `quadratic_polyDepth` — `∀ A B C, polyDepth 2
(fun n => A·n²+B·n+C)` (floor `2A`), capping the whole order-2 degree-2 Apéry-like (Zagier
sporadic: ζ(2)-Apéry, Domb, Almkvist–Zudilin, Catalan-β(2), …) family in one statement.
Newton-form transfer `A·n²+B·n+C = newton (C,A+B,2A) 2` (via `binom n 1 = n`, `n² =
2·binom n 2 + n`) along the new reusable `polyDepth_congr` + `newton_polyDepth`; the one
nonlinear identity by the `Meta.Nat.PolyNat` reflection ring.  Dissolves the
multivariate-`Nat`-AC obstruction (no `ring`/`omega`).

`E213.Lib.Math.Analysis.Cauchy.CasoratianSigned` — **17 PURE / 0 DIRTY**.  The *signed* Casoratian law
+ its signed telescope (incl. concrete `cube_casoratian_telescope`), sign carried 213-natively as a ℕ-pair
(`Lens.Number.Nat213.Tower.NatPairToInt`: integer = pair `(a,b)` = `a−b`, negation = axis
swap).  `casoratian_signed` — `npairEquiv (scale c₂ Cₙ) (scale c₀ (neg Cₙ₋₁))` *is*
`c₂Cₙ = −c₀Cₙ₋₁`, unfolding to `casoratian_step` verbatim — signed law ∅-axiom over ℕ, **no
`ℤ` type, no propext**.  Pair-congruences (`scale_mul/comm/congr`, `neg_congr`), `neg_neg`
(swap involution = period-2 Oscillate), `iterNeg` (accumulated sign, `iterNeg_succ_succ`
period 2).  **Signed telescopes**: `telescope_pair` — ζ(3) constant-sign shape `scale (∏ P)
Cₙ ~ scale (∏ Q) C₀` (`P=n³`, `Q=(n−1)³`: the `+6/n³` Casoratian); `telescope_pair_alt` —
ζ(2) alternating shape `scale (∏ P) Cₙ ~ iterNeg n (scale (∏ Q) C₀)` (`P=(n+1)²`, `Q=n²`: the
`±5/n²` Casoratian, sign `(−1)ⁿ`).  The signed `±5/n²`,`±6/n³` closed forms realized ∅-axiom
over ℕ-pairs (the sign = the residue's binary axis-distinguishing).  The Casoratian's
magnitude (Converge/Escape, `CasoratianStep.telescope`) and sign (Oscillate, `iterNeg`) are
the two non-trivial `SelfReferenceThreeOutcomes` readings of one object.

`E213.Lib.Math.Analysis.Cauchy.CassiniSigned` — **2 PURE / 0 DIRTY**.  The residue floor's cross-determinant as the depth-0 signed Casoratian: the Fibonacci Cassini `fib(n+2)·fib(n) − fib(n+1)² = (−1)ⁿ⁺¹` in ℕ-pair form — `cassini_pair`: `npairEquiv (fib(n+2)·fib(n), fib(n+1)²) (iterNeg (n+1) (1,0))`, the unit pair `(1,0)` toggled `n+1` times.  Magnitude `1` (the `det P = 1` floor, Converge depth 0) with the sign carried entirely by the period-2 axis swap (Oscillate); `cassini_step` is the subtraction-free Fibonacci identity, the `c₂=c₀=1` floor instance of `casoratian_signed`.  ∅-axiom over ℕ — the floor's `±1` with its sign, no `ℤ`.

`E213.Lib.Math.Analysis.Cauchy.DepthCubicGeneric` — **5 PURE / 0 DIRTY**.  Every cubic discrete polynomial has divergence-depth 3: `cubic_polyDepth` — `∀ A B C D, polyDepth 3 (A·n³+B·n²+C·n+D)` (cubic analog of `quadratic_polyDepth`, completing depth=degree to 3), via `cubic_eq` (cubic = `newton (D,A+B+C,6A+2B,6A) 3`) + `newton_polyDepth` + `polyDepth_congr`.  Crux `cube_eq` — `n³ = 6·binom n 3 + 6·binom n 2 + n` (the subtraction-free `n³ = 6·C(n,3)+6·C(n,2)+C(n,1)`, cube analog of `DepthQuadraticGeneric.sq_eq`), via the univariate `(n+1)³=n³+3n²+3n+1` (`poly_id`) + `sq_eq` + `cube_reorder` (the combine/reorder identity, PURE via `NatHelper.{add_mul,mul_assoc}` + `Nat.add_right_comm`, no propext-dirty `ring`/`ac_rfl`).  All multivariate reorders (the `cube_reorder` combine + the two collect steps in `cubic_eq`) are one-line `Meta.Nat.PolyNatM.poly_idM` calls.

`E213.Lib.Math.Analysis.Cauchy.DepthCharacterization` — **13 PURE / 0 DIRTY**.  ★ The capstone of the divergence-depth thread: **finite divergence depth ⟺ polynomial**, over ℤ.  `finite_depthZ_iff` — `polyDepthZ d s ↔ ∃ c, ∀ n, s n = newtonZ c d n` (degree-≤d Newton form).  ⟹ is `NewtonGregory.reconstruct` (cⱼ=Δʲs0); ⟸ is `polyDepthZ_newtonZ` (Newton form has depth d), built on the new **ℤ binom-column depth** `polyDepthZ_binomColZ` (`polyDepthZ k (C(·,k):ℤ)`) via the ℤ-Pascal difference `diffZ_binomColZ` (`Δ C(·,k+1)=C(·,k)`) + the finite-depth ring (`polyDepthZ_add/smul`, `polyDepthZ_mono`).  Unifies the ℕ depth ladder ⊕ the concurrent-session ℤ reconstruct into one equivalence.  **Exactness** (`newtonZ_depth_drop`): a degree-`(e+1)` Newton form drops to depth `e` iff its top coefficient `c_{e+1}=0` — via `liftKZ_newtonZ_const` (`Δ^d(Newton form)=c_d`, from the shift `diffZ_newtonZ`).  So divergence depth = degree *exactly*.

`E213.Lib.Math.Analysis.Cauchy.PolynomialDepth` — **13 PURE / 0 DIRTY**.  Every degree-`d` polynomial sequence has divergence-depth `d`, general: `polyDepthZ_polySeq` — `∀ a d, polyDepthZ d (polySeq a d)` where `polySeq a d n = Σ_{i≤d} aᵢ·nⁱ` (any `ℤ`-coefficients).  Via the finite-depth **ring** (`FiniteDepthAlgebra.polyDepthZ_{add,smul,mul}`): `idZ` (n↦n) depth 1 (`diffZ_id`, PURE Int213 `add_assoc`/`add_neg_cancel`), `powSeq i` (n↦nⁱ) depth `i` (`polyDepthZ_mul` ×`i`), `polyDepthZ_mono` lifts, `polyDepthZ_add` sums.  Subsumes the quadratic/cubic rungs in one — no Stirling, no per-degree reorder; the ring does the bookkeeping.  Unifies the ℕ depth ladder (`DepthAperyCubic` etc.) with the concurrent ℤ finite-depth ring.  `aperyLeadZ_depth` (instance): the ζ(3) Apéry leading coefficient `34n³−51n²+27n−5` (negative coeffs) has depth 3 over ℤ with **no reindex** (the ℕ `DepthAperyCubic.aperyLead` needed `n=m+2`); `aperyLeadZ_value` checks it `= 117` at `n=2`.

`E213.Lib.Math.Analysis.Cauchy.OrbitDimension` — **32 PURE / 0 DIRTY**.  The C-finite rung strictly above the polynomials, the first step on the orbit-dimension ladder past `DepthCharacterization.finite_depthZ_iff`.  The divergence-depth axis is coarse above the polynomials (it bins `2ⁿ`, `e`'s value sequence, Fibonacci, Liouville all at `∞`); the **orbit dimension** of `⟨s, Δs, Δ²s, …⟩` separates them.  ★ `twoPow_is_diffZ_fixed` — the geometric **eigen-identity** `Δ(2ⁿ)=2ⁿ` (`2·2ⁿ−2ⁿ=2ⁿ`, via `ring_intZ` over the core-free `powInt`); `liftKZ_twoPow_fixed` — every iterate fixes it, the orbit is the single line `⟨2ⁿ⟩`.  `CFiniteZ s := ∃ k c, ∀ n, Δᵏs n = Σ_{i<k} cᵢ·Δⁱs n` (a monic constant-coefficient `Δ`-orbit recurrence; finite orbit dimension).  ★ `polyDepthZ_cfiniteZ` — **polynomial ⟹ C-finite** (zero lower part, annihilator `Δ^{d+1}`).  ★ `cfiniteZ_twoPow` — **`2ⁿ` is C-finite** (annihilator `Δ−1`, orbit dim 1).  ★★★ `twoPow_not_polyDepthZ` — **`2ⁿ` is not a polynomial** (`Δᵏ(2ⁿ)=2ⁿ`, never `≡0` since `2⁰=1≠0` via `Int.ofNat.inj`+`Nat.noConfusion`), the **strict inclusion** `polynomial ⊊ C-finite`.  `cfiniteZ_smul` / `cfiniteZ_shift` — C-finite is a module, shift-stable (same annihilator); `cfiniteZ_add_sameRec` — closed under `+` of two sequences sharing one annihilator (general `+` closure is `CFiniteRing.cfiniteZ_add`).  **The general geometric family** `geomZ c = cⁿ`: `geom_diffZ` (`Δ(cⁿ)=(c−1)·cⁿ`), `liftKZ_geomZ` (`Δᵏ(cⁿ)=(c−1)ᵏ·cⁿ`), `cfiniteZ_geom` (every geometric sequence is C-finite, orbit dim 1, annihilator `Δ−(c−1)`), `geom_not_polyDepthZ` (`c≠1 ⟹` not polynomial, via `powInt_eq_zero`: `xᵏ⁺¹=0⟹x=0`).  **Fibonacci** `fibZ`: `cfiniteZ_fib` — `fibZ` is C-finite with **orbit dimension 2** (`Δ²f=f−Δf` from `E²−E−I=Δ²+Δ−I`), the cleanest non-geometric, non-polynomial witness.  **Abelian-group structure**: `cfiniteZ_congr` (respects pointwise eq), `cfiniteZ_zero`, `cfiniteZ_neg` (`−s=(−1)·s`); `cfiniteZ_geom_mul` (`cⁿ·dⁿ=(cd)ⁿ`, the geometric Hadamard instance, orbit dims multiply `1·1=1`).  **Conserved unit**: `cassini_fibZ_step`/`cassini_fibZ_zero` — the Fibonacci Cassini cross-determinant `Cₙ=fibₙfibₙ₊₂−fibₙ₊₁²` oscillates `Cₙ₊₁=−Cₙ` (period-2), the conserved unit `±1` (= `det Qⁿ` = the number-tower's shared unit `det P=NS−NT=1`, the period-2 flip being the count-Lens negation).

`E213.Lib.Math.Analysis.Cauchy.CFiniteRing` — **82 PURE / 0 DIRTY**.  The **difference-operator algebra** and the **C-finite ring closure under `+`**.  `applyOp p s = Σ_i pᵢ·Δⁱs` (coefficient list low-to-high `Δ`-power); linearity (`applyOp_add`/`applyOp_smul`), `Δ`-commutation (`applyOp_diffZ`), and ★★★ `applyOp_comm` (`p(Δ)q(Δ)s = q(Δ)p(Δ)s` — difference operators commute).  `conv` (coefficient convolution = operator product) with `applyOp_conv` (`(p·q)(Δ) = p(Δ)∘q(Δ)`).  ★★★ **the ring law** `conv_annih_add`: if `p` annihilates `s` and `q` annihilates `t`, the product `conv p q` annihilates `s+t` — the constant-coefficient annihilators *multiply* (orbit dimensions add).  **Bridge** (both directions): `cfiniteZ_to_annih` (`CFiniteZ s ⟹ ∃ monic `opOf`-operator annihilating `s`, via `applyOp_opOf` evaluating `Δᵏ−ΣcᵢΔⁱ` and `opOf_getLastD` proving leading `1`) + `annih_snoc_to_cfiniteZ` (a monic `lo++[1]` annihilator *is* the orbit recurrence `Δ^{|lo|}s=ΣcᵢΔⁱs`, via `applyOp_snoc_one` + `applyOp_eq_linComb`).  So **C-finite ⟺ has a monic constant-coefficient annihilator** — the orbit-recurrence definition coincides with the standard annihilating-polynomial one.  ★★★ **the capstone** `cfiniteZ_add`: `CFiniteZ s → CFiniteZ t → CFiniteZ (s+t)` — the monic annihilators multiply (`conv_snoc`: leading coefficients multiply, `1·1=1`; `+0`/`*1` syntactic noise absorbed by an existential-value `conv_snoc`), so `polynomial ⊊ C-finite` is a genuine **ring** under `+`, with the `conv`-monic toolkit `length_snoc`/`smulL_snoc`/`addL_snoc_right`/`length_addL_right_ge`/`opOf_snoc` (all `Nat.max`-free).  `cfiniteZ_one_add_twoPow`: `1+2ⁿ` is C-finite, a concrete sequence `+` generates that is neither polynomial nor geometric.  `cfiniteZ_sub` (with `OrbitDimension`'s `cfiniteZ_zero`/`cfiniteZ_neg`) completes the **abelian group under `±`**.  **§8 the shift as a difference operator** (toward C-D): `applyOp_shift` (`applyOp [1,1] = E`, the forward shift *is* `I+Δ`), `ePow k` (= `[1,1]` convolved `k` times = `Eᵏ`), `applyOp_ePow` (`applyOp (ePow k) s n = s(n+k)` — the `k`-shift is a polynomial in `Δ`).  So a monic shift recurrence is a monic `Δ`-annihilator.  **§9 C-D reverse direction** `cfiniteZ_of_shiftRec`: a sequence satisfying a monic order-`k` shift recurrence `s(n+k)=Σ_{i<k} bᵢ s(n+i)` (`ShiftRecZ`) is C-finite (`Δ`-orbit dim ≤ k) — via `eCombo` (shift→`Δ` operator `Σ bᵢ ePow i`, no binomial sums), `ePow_eq_snoc` (`ePow k` monic degree k), `eCombo_length_le`, `addL_snoc_right`.  So the standard constant-recursive definition ⟹ the `Δ`-orbit-recurrence one; `cfiniteZ_fib_via_shift` validates it end-to-end (Fibonacci's shift recurrence ⟹ `CFiniteZ fibZ`).  **§10–§11 C-D forward** — the dual shift-operator algebra `applyShift` (`Δ = applyShift [-1,1] = E−I` via `applyShift_diffBase`; `Δᵏ` as a shift operator `applyShift_dPow`; conv = composition `applyShift_conv`), `sCombo`/`dPow_eq_snoc`, and `shiftRec_of_cfiniteZ` (`CFiniteZ ⟹ ∃ monic shift recurrence`, the exact mirror of the reverse, no binomial sums).  ★★★ `cfiniteZ_iff_shiftRec`: **`CFiniteZ s ↔ ∃ K b, ShiftRecZ K b s`** — the full **"orbit dimension = recurrence order"** equivalence; `CFiniteZ` is exactly the standard constant-recursive class.  **§12 Hadamard, geometric factor** `cfiniteZ_geomScale`: `cⁿ·s` is C-finite for every C-finite `s` (a geometric weight rescales the shift coefficients `aᵢ↦aᵢ·c^{k−i}`, via `cfiniteZ_iff_shiftRec` + `geom_shiftSum`), generalizing `cfiniteZ_geom_mul` to `cⁿ·(n²)`, `cⁿ·fib`, ….  **§13 Hadamard, explicit-spectrum factor** `cfiniteZ_geomCombo_mul`: `(Σ aᵢcᵢⁿ)·t` is C-finite for every C-finite `t` (`geomCombo` = explicit `ℤ`-combination of geometrics; via `cfiniteZ_geomScale`+`cfiniteZ_add`, no determinant) — covers `(2·3ⁿ−5·2ⁿ)·fib`, `(3ⁿ+5ⁿ)·n²`.  (The *general* product `s·t`, both factors non-split, needs the monic resultant = `det(zI−M)` — **now closed** by `CFiniteHadamard.cfiniteZ_mul` via integer Cayley–Hamilton.)

`E213.Lib.Math.Analysis.Cauchy.CFiniteHadamard` — **21 PURE / 0 DIRTY**.  ★★★ **The C-finite Hadamard (pointwise) product** `cfiniteZ_mul`: `CFiniteZ s → CFiniteZ t → CFiniteZ (s·t)` — the last open ring operation, closed via the Kronecker companion + integer Cayley–Hamilton.  **§1 grid-sum**: `append_nil'`/`append_assoc'` (clean), `iota_add`, ★ `sumZ_grid` (`sumZ` over `iota (p·q)` = the double sum over the `p×q` grid).  **§2–§3 the flat↔grid bijection** (∅-axiom, since core `Nat./`/`%` are propext/Quot-dirty): a **fuel-structural** `qof`/`rof` (`divmod` via clean `Nat.sub`), `divmod_spec` (division algorithm), `decA`/`decB`/`dec_spec`, `divmod_unique` + `decA_encode`/`decB_encode` (the encode roundtrip).  **§4 the factored Kronecker companion**: `shiftSum_eq_sumZ`, the *factored* rows `Ms`/`Mt` (s- and t-shifts are independent), `Wvec` (product vector `w(n)_J = s(n+J/q)·t(n+J%q)`), `Mmat = Ms·Mt`, `Ms_sum`/`Mt_sum` (each shift row reproduces the boundary recurrence), and ★★ `vecRec` — **`w(n+1) = M·w(n)`** (the grid sum factors into the product of the two shift sums).  **§5 the assembly** ★★★ `cfiniteZ_mul`: `CharPolyAdj.ch_recurrence` at the `(0,0)` component ⟹ `Σ_{m≤pq} c_m·(s·t)(n+m) = 0` with `c_{pq}=1` (`PolyDet.charPoly_monic`) ⟹ `ShiftRecZ pq (−c) (s·t)` ⟹ `CFiniteRing.cfiniteZ_of_shiftRec` (edge cases `p=0`/`q=0` ⟹ a zero factor ⟹ `cfiniteZ_zero`).  The full C-finite Hadamard program (Leibniz determinant → cofactor/adjugate → integer Cayley–Hamilton → Hadamard) closed, ∅-axiom.

`E213.Lib.Math.Analysis.Cauchy.CasoratianRank` — **6 PURE / 0 DIRTY**.  The **forward half of "Casoratian rank = orbit dimension"**: ★★ `casoratian_det_zero` — a sequence with a monic order-`k` shift recurrence has its `(k+1)×(k+1)` Casoratian/Hankel determinant `det [s(n+i+j)]_{i,j≤k} = 0` (the bottom row `s(n+k+j)` is exactly the recurrence combination `Σ_{a<k} bₐ·s(n+a+j)` of the upper rows, so `RowDependence.det_row_combo_zero` applies after `shiftSum_eq_sumZ` + `add_right_comm` index massaging); `casoratian_det_zero_ge` (every Casoratian of size `> k` vanishes ⟹ **rank ≤ order**), `casoratian_det_zero_of_cfiniteZ` (any `CFiniteZ` sequence).  **§2 the Fibonacci witness** ★ `fib_casoratian_rank` — Fibonacci's `3×3` Casoratian `= 0` while its `2×2` is the unit `(−1)ⁿ⁺¹ ≠ 0`, so its Casoratian **rank is exactly 2 = its orbit dimension** (`fib_shiftRec` + `FibCassiniDet`).  The first reuse of the integer determinant tower beyond Cayley–Hamilton.

`E213.Lib.Math.Algebra.Linalg213.DetN` — **19 PURE / 0 DIRTY**. The general `n×n` **determinant over `ℤ`** (first-row cofactor / Laplace expansion), the foundational gap for the C-finite **Hadamard product** (monic annihilator = resultant = a determinant) and the **Casoratian rank**. A matrix is `M : Nat → Nat → Int`; `det (n+1) M = Σⱼ (−1)ʲ·M 0 j·det n (minor M j)`, base `det 0 _ = 1` (`altSign`, `minor`, `cofSum`, `det`; sanity `det_one`, `det_two`). ★ `det_congr` — `det` respects **pointwise** matrix equality (the ∅-axiom matrix-work pattern: `funext` is `Quot.sound`-dirty, so all matrix-as-function reasoning goes through pointwise congruence). **§2 multilinearity in the first row**: `setRow0`, `detMinor_setRow0` (cofactor is row-0-independent), ★ `det_row0_add`/`det_row0_smul` (`det` is a linear functional of row 0). **§3 the column-skip commutation** (the geometric core of the alternating property): `colShift j l = if l<j then l else l+1` (factored from `minor`), `colShift_lt`/`colShift_ge`, ★ `colShift_comm` (`a≤c ⟹ colShift a ∘ colShift c = colShift (c+1) ∘ colShift a` — deleting two columns in either order is the same; ∅-axiom via `Nat.lt_or_ge` case-splits, no propext), and `detMinorMinor_comm` (lifts it to the double minor's `det`, pointwise via `det_congr`). (The full alternating property — two equal rows ⟹ `det=0` — reduces to one base case "top two rows equal ⟹ 0" whose per-term inputs are `colShift_comm`/`detMinorMinor_comm`; the remaining build is a nested-sum sign-reversing-involution ⟹ 0 lemma.  See `theory/math/algebra/linalg213.md`.)

`E213.Lib.Math.Algebra.Linalg213.FibCassiniDet` — **3 PURE / 0 DIRTY**.  The bridge closing the loop between the determinant program and the C-finite orbit theory it serves.  `fibCas n i j = fibZ (n+i+j)` (the `2×2` Fibonacci Casoratian = companion power `Qⁿ` window); `cassini_fibZ_eq_altSign` (the Cassini cross-determinant in closed form `fibₙ·fibₙ₊₂−fibₙ₊₁² = altSign(n+1) = (−1)ⁿ⁺¹`, via `cassini_fibZ_zero`+`cassini_fibZ_step`); ★ `fibCas_det_eq_unit` — **`det 2 (fibCas n) = (−1)ⁿ⁺¹`**, the general determinant's `2×2` base *is* the orbit's conserved unit, the same unimodular `det = ±1` as the number-tower founding's shared unit `det = NS−NT = 1` (`PnFibonacciUniversal.det_pn_universal`, `det Qⁿ = unit`).  "Monic = the preserved unit" made concrete; `DetN` validated against real C-finite content.

`E213.Lib.Math.Algebra.Linalg213.Permutation` — **30 PURE / 0 DIRTY**. The permutation/sign substrate and the **Leibniz determinant**, where the **alternating** property is antisymmetrization (`theory/essays/algebra/determinant_as_quotient_characteristic.md`). **§1**: `LPerm` (the four-constructor list permutation-equivalence `nil`/`cons`/adjacent-`swap`/`trans`), `LPerm.refl`/`LPerm.symm`, `sumZ` (Int list sum), ★ `sumZ_lperm` — **a sum is invariant under `LPerm`** (reordering preserves the sum, via Int213's propext-free `add_left_comm`); the "row swap reindexes the Leibniz sum, value unchanged" engine. **§2**: `ltCount`/`inversions`/`psign` (`psign l = (−1)^(inversions l) = DetN.altSign (inversions l)`), ★ `psign_swap_adj` — **an adjacent swap of two distinct values flips the sign** (`psign (y::x::l) = −psign (x::y::l)` for `x≠y`), the concrete `sign(σ∘τ) = −sign σ` for an adjacent transposition (`ac_form` Nat inversion-rearrangement + `altSign_succ`, propext-free). **§3**: `ltCount_append`, `ltCount_cons2_comm`, `psign_cons` (head factorization via `DetN.altSign_add`), ★ `psign_swap_prefix` — the sign flip for a swap of two distinct adjacent entries **after any prefix** (the bridge to swapping rows `i,i+1`). **§4**: `prodDiagFrom`/`leibTerm`/`insertEverywhere`/`permsOf`/`perms`/`leibDet` (`leibDet n M = Σ_σ sign(σ)·Πᵢ M i (σ i)`), `leibDet_two_id` sanity (`rfl`), and the assembly lemmas `sumZ_map_neg` (pointwise negation negates the sum) + `map_lperm` (`map` is an `LPerm` congruence). **§5**: `prodDiagFrom_append`, `rowSwapAt`/`rowSwapAt_{other,at,at1}`, `prodDiagFrom_eq_{below,above}` (rows outside `{k,k+1}` unaffected), `prodDiag_rowSwap` (diagonal products agree via `mul_left_comm`), and ★ `leibTerm_rowSwap` — an adjacent row swap (rows `k=pre.length`, `k+1`) sends the Leibniz term at `pre++y::x::l` to `−(term at pre++x::y::l)` for `x≠y`, the determinant's core combinatorial content.

`E213.Lib.Math.Algebra.Linalg213.PermGroup` — **19 PURE / 0 DIRTY**.  The **symmetric-group operation on permutation value-lists** — the foundation for the sign theory (`psign(σ∘τ) = psign σ·psign τ`) toward the transpose determinant `det Mᵀ = det M`.  A permutation is its value list `[σ 0, σ 1, …]`; **§1** `iota`-indexing infra (`iota_cons`, `length_iota`, ★ `getD_iota` — the identity permutation reads off its index).  **§2** `composeList σ τ := τ.map (σ.getD · 0)` realizing `(σ∘τ) i = σ(τ i)`, with `composeList_length` and the defining ★ `composeList_getD`.  **§3 monoid laws** (by `getD`-extensionality `list_ext_getD`, with entry-bound hypotheses replacing `perms`-membership to stay enumeration-independent): ★ `composeList_iota_left`/`composeList_iota_right` (`iota n` is a two-sided identity) and ★ `composeList_assoc`.  **§4 the inverse**: `idxOf` (first position of a value) + ★ `idxOf_getD` (recovers the value), `invPerm σ := (iota |σ|).map (idxOf · σ)` with `invPerm_length`/`invPerm_getD`, and ★★ `composeList_invPerm_right` — **`σ ∘ σ⁻¹ = iota n`**.  **§5 the left inverse** (`getD_mem`, `idxOf_lt`, `idxOf_getD_self` — the first position of `σ i` is `i` for nodup `σ`): ★★ `composeList_invPerm_left` — **`σ⁻¹ ∘ σ = iota n`** for a position-injective in-range `σ`.  Together: `invPerm` is a **two-sided inverse** — the value-list model of `iota n`-permutations is a group.  All by `getD`-extensionality, ∅-axiom (`List`-based, no `Multiset` quotient).

`E213.Lib.Math.Algebra.Linalg213.PermSign` — **30 PURE / 0 DIRTY**.  ★★★ **Sign-multiplicativity** `psign(σ∘τ) = psign σ·psign τ` (the keystone for the transpose determinant `det Mᵀ = det M`), proved by the **bubble-sort reduction** of `τ` to `iota n`.  **§1–2 the position-swap action**: `map_swapAt`/`composeList_swapAt` (`σ∘swapAt k τ = swapAt k (σ∘τ)`), `psign_swapAt`, `swapAt_mem_perms`.  **§3 directed inversion-decrease**: ★ `inv_prefix_swap` (ordering an out-of-order adjacent pair removes exactly one inversion) + `composeList_cons`/`composeList_append`.  **§4 descent**: `Sorted`, `sorted_or_descent`, ★ `descent_of_inv_pos`.  **§5 ★★ `Q_swap`** — the swap-**invariant** `psign(σ∘τ)·psign τ` (both factors flip).  **§6 base** ★ `sorted_lperm_eq` (two sorted lists with the same multiset are equal) ⟹ `sorted_perm_eq_iota` (`inversions τ = 0 ⟹ τ = iota n`).  **§7** `perms_inj` (a permutation is position-injective, via `cnt_ge_two`), `perms_entry_lt`, `altSign_self`.  **§8** the fuel-induction `psign_mul_aux` (structural on `inversions τ ≤ fuel`, no well-founded recursion) and ★★★ `psign_mul`.  Entirely `List`-based, ∅-axiom (the `Multiset`-quotient and `Nat.succ_ne_zero`'s `propext` both sidestepped — `Nat.noConfusion`).

`E213.Lib.Math.Algebra.Linalg213.DetMul` — **39 PURE / 0 DIRTY**.  ★★★ **The multiplicative determinant** `det_matMul` (`det n (A·B) = det n A · det n B`), ∅-axiom from scratch — the second payoff of `PermSign.psign_mul` (after the transpose).  **§1**: ★★ `composeList_mem_perms` — **composition of permutations is a permutation** (`composeList α β ∈ perms n`), completing `perms n` as a group.  **§2**: `composeList_rightInv`/`composeList_leftInv` (the cancellations `(τρ)ρ⁻¹ = τ`, by `getD`-extensionality) ⟹ ★★ `perms_closed_rightMul` (**right translation `τ ↦ τ∘ρ` is a bijection of `perms n`**).  **§3**: `rowPerm` (permute rows by `σ`), `prodDiag_rowPerm_eq`, `leibTerm_rowPerm`, ★★★ `leibDet_rowPerm` — **permuting the rows of `B` by `σ` scales the determinant by `psign σ`** (`leibDet (rowPerm σ B) = psign σ · leibDet B`).  **§4**: `leibDet_rowPerm_zero` (**equal rows ⟹ `leibDet = 0`**, via the swap-transposition fixed point), `tuples`/`funcs` (the `n^n` index functions `[0,n)→[0,n)` as value lists).  **§5–§7 the Cauchy–Binet expansion**: `prodChoice`, ★★ `prodDiag_matMul_expand` (the diagonal product of `A·B` distributes into a sum over functions `f∈funcs n`), `pB`/`prodChoice_split`, and ★★★ `leibDet_matMul_expand` — `leibDet (A·B) = Σ_{f∈funcs n} prodDiagFrom A 0 f · leibDet (rowPerm f B)` (`sumZ_swap`).  **§8**: ★★★ `leibDet_perms_assembly` — the **permutation** functions contribute `Σ_{f∈perms n} prodDiagFrom A 0 f · psign f · leibDet B = leibDet A · leibDet B` (`leibDet_rowPerm` + `sumZ_map_smul`).  **§9 the partition (the non-permutations vanish)**: `tuples_entries`/`mem_tuples`/`perms_subset_funcs`/`nodup_funcs`; the **constructive pigeonhole** — `firstDup` (the first repeated value, scanned by the *pure* `cnt`-decision, **no `Decidable (a ∈ l)` instance** — that membership instance carries `propext`/`Quot.sound`), `firstDup_some`/`firstDup_none`, `listNodup_of_cntNodup`/`cntNodup_of_listNodup` (the two `Nodup` notions bridge), ★★ `mem_of_card_le` (a nodup `L₁ ⊆ L₂` with `|L₂| ≤ |L₁|` exhausts `L₂`) ⟹ ★★★ `nodup_imp_perm` (**a nodup index function is a permutation**), `term_zero_of_nonperm` (a **non**-permutation `f` repeats a row ⟹ its term is `0`).  **§9c assembly**: `cnt_filter_le`, ★★ `funcs_filter_perms_lperm` (`(funcs n).filter (0 < cnt · (perms n))` is `LPerm` to `perms n` — the pure `cnt` predicate, again sidestepping the membership instance) ⟹ ★★★ `leibDet_matMul` ⟹ ★★★ `det_matMul` (via `Laplace.leibDet_eq_det`).

`E213.Lib.Math.Algebra.Linalg213.DetTranspose` — **16 PURE / 0 DIRTY**.  ★★★ **The transpose determinant** `det_transpose` (`det n Mᵀ = det n M`), the classical Leibniz proof, ∅-axiom from scratch — the payoff of `PermSign.psign_mul`.  **§1 the inverse is a permutation**: `nodup_map_restrict` (cnt-`Nodup` under a map injective *on the list's elements*), `perms_contains`, ★ `invPerm_mem_perms` (`invPerm σ ∈ perms n`).  **§2 the sign of the inverse**: `psign_iota` (`psign (iota m) = 1`) and ★★★ `psign_inv` (`psign (σ⁻¹) = psign σ`, a one-liner from `psign_mul`).  **§3**: ★★ `invPerm_invol` (`(σ⁻¹)⁻¹ = σ`) ⟹ ★★ `perms_closed_invPerm` (`LPerm ((perms n).map invPerm) (perms n)` — the sum-reindex).  **§4 the product-reindex** (the crux): `transpose`, `zipDiag` (the diagonal-product factor list, `prodDiagFrom_eq_prodZ`), `list_self_map_getD`, and ★★★ `prodDiag_transpose_eq` (`∏ᵢ Mᵀ(i,σᵢ) = ∏ⱼ M(j,σ⁻¹ⱼ)`, the two factor lists are the same multiset reordered by `σ`, `LPerm` via `map_lperm` + `ProdLperm.prodZ_lperm`).  **§5**: `leibDet_transpose` (each `leibTerm Mᵀ σ = leibTerm M σ⁻¹`, reindex by `perms_closed_invPerm`) ⟹ ★★★ `det_transpose` (via `Laplace.leibDet_eq_det`).

`E213.Lib.Math.NumberTheory.ModArith.ZolotarevCycle` — **47 PURE / 0 DIRTY**.  Primitive-root marathon brick 7 — **the odd-cycle witness**, closing the **full Zolotarev identity**.  ★★★★★ `zolotarev_full` — for an odd prime `p` (`2m = p−1`, `m ≥ 1`), unit `1 ≤ a < p`:  `psign (mulPerm a p) = 1 ⟺ a` is a QR mod `p` (Zolotarev's lemma `(a/p) = sign(x ↦ a·x mod p)` in full).  The single odd witness is a **primitive root** `g`: ★★★ `psign_mulPerm_primitive` — `psign (mulPerm g p) = −1`.  Mechanism: `mulPerm g` (fixing `0`, a `(p−1)`-cycle on the units) is **conjugate** to the standard rotation `cycS = [0,p−1,1,2,…,p−2]` via the discrete-log list `τ(i) = g^(p−1−i) mod p` — `conj_eq` (`composeList (mulPerm g) τ = composeList τ cycS`, by `getD`-extensionality + the per-index `conj_pointwise` `g·τ(i) ≡ τ(S(i))` using `g_mul_pow`/`exp_step`/`fermat`) — so `psign` (a class function via `psign_mul` + `±1` self-cancel `altSign_self`/`psign_pm`) gives `psign (mulPerm g) = psign (cycS)`.  `psign_cycS = −1`: `inversions_cycS = p−2` (the `asc` ascending-block calculus `ltCount_zero`/`ltCount_asc_all`/`inversions_asc` on `cycS = 0 :: (p−1) :: asc 1 (p−2)`), and `altSign_odd` (`p−2 = 2(m−1)+1`).  Both `cycS` and `τ` are permutations (`cycS_mem_perms` via `sFun_inj`; `tau_mem_perms` via the **discrete-log injectivity** `pow_inj_mod` — `res_cancel` cancellation + `ord_dvd` with `ord g = p−1`, periodicity `pow_period` from `pow_split_eq`).  `primitive_not_qr` — a primitive root is a non-residue (`ord g = 2m ∤ m`).  Pure `mul_neg_one_int`/`Int213.mul_one` Int plumbing (core `Int.mul_one` carries propext).

`E213.Lib.Math.NumberTheory.ModArith.ZolotarevConverse` — **4 PURE / 0 DIRTY**.  Primitive-root marathon brick 6 — **the Zolotarev converse reduction** (full Legendre/sign iff, modulo one odd-cycle witness).  `qr_dec` — quadratic-residue membership is decidable on a unit range (bounded `firstSqrt` search; `none`-branch refutes via `firstSqrt_none`).  Pure `mul_neg_one_int` (`x·(−1) = −x` over `ℤ` by `Int` constructor cases; core `Int.mul_neg_one` carries propext).  ★★★ `nonqr_psign_neg` — *given* one non-residue `a₀` with `psign (mulPerm a₀ p) = −1`, **every** non-residue `a` is odd (`psign (mulPerm a p) = −1`): `a·a₀` is a residue (non·non = residue, `legendre_mul`) so even (`psign_mulPerm_qr_pred`), and the homomorphism (`psign_mulPerm_hom`) makes that `psign (mulPerm a)·(−1)`, forcing `−1`.  ★★★★★ `zolotarev_iff` — the **full** equivalence `psign (mulPerm a p) = 1 ⟺ a` is a QR (given the single odd witness `a₀`): forward by `qr_dec` + `nonqr_psign_neg` (a non-residue would give `−1 ≠ 1`), backward by `psign_mulPerm_qr_pred`.  The remaining input — one primitive root's permutation is a `(p−1)`-cycle of sign `−1` — is brick 7.

`E213.Lib.Math.NumberTheory.ModArith.PrimitiveRoot` — **9 PURE / 0 DIRTY**.  Primitive-root marathon brick 5.  `pow_maxOrd_eq_one` (every unit `x` has `x^maxOrd ≡ 1`, from `every_ord_dvd_maxOrd`); the units list `segInt 1 (p−1) = [1,…,p−1]` over `ℤ` with `segInt_pairwise` (pairwise-distinct mod `p`, via `int_diff_not_dvd`) and `segInt_roots` (each a root of `X^maxOrd − 1`).  ★★★ `maxOrd_eq_pred` — `maxOrd p = p − 1`: else `maxOrd+1 ≤ p−1`, so `RootBound.eval_zero` on `pmoSucc (maxOrd−1) = X^maxOrd−1` (length `maxOrd+1`) with the `p−1` distinct units forces `eval … 0 = −1 ≡ 0`, contra.  ★★★★ `exists_primitive_root` — `∃ g, 1 ≤ g ≤ p−1 ∧ ordModP g p = p − 1` (the `maxOrd`-achiever).

`E213.Lib.Math.NumberTheory.ModArith.EveryOrdDvdMax` — **3 PURE / 0 DIRTY**.  Primitive-root marathon brick 4b-iv — **the exponent argument** (the crux).  ★★★★ `every_ord_dvd_maxOrd` — for a unit `a`, `ordModP a p ∣ maxOrd p`.  By the pure decidable case-split on `maxOrd % ord` (no Classical `by_contra`): if `¬ ord a ∣ maxOrd`, `exists_prime_vp_gt` gives a prime `q`, `e = vp_q(ord a) > f = vp_q(maxOrd)`; build `x = (a^(ord a/A))%p` of order `A = qpart q (ord a)` (helper `ord_pow_eq_of_dvd` + `ord_mod_eq`; unit by `not_dvd_pow`) and `y = (g^(qpart q d))%p` of order `B = d/qpart q d` (`ord_pow_div`); `gcd(A,B)=1` (`gcd_qpow_qfree`), so `ord((x·y)%p) = A·B ≥ qᶠ⁺¹·(d/qᶠ) = q·d > d` (`ord_mul_coprime`) — contradicting `maxOrd_ge`.

`E213.Lib.Math.NumberTheory.ModArith.ValuationAlg` — **5 PURE / 0 DIRTY**.  Primitive-root marathon brick 4b-iii.  ★ `vp_mul` (`vp q (a·b) = vp q a + vp q b`, `q` prime — via the `q`-free cofactors `a/qpart`, `b/qpart` + `nat_prime_dvd_mul`).  ★★★ `exists_prime_vp_gt` — `α ∤ d` ⟹ `∃ prime q, vp q α > vp q d`, the extraction: a prime `q ∣ α/gcd(α,d)` (`exists_prime_factor`, `α/g ≥ 2`) is coprime to `d/g` (brick 1 `gcd_div_coprime`), so `vp_q(d/g)=0` ⟹ `vp(d)=vp(g)`, while `vp(α)=vp(g)+vp(α/g) ≥ vp(g)+1`.  Plus `vp_eq_of`, `vp_eq_zero`, `one_le_vp`.

`E213.Lib.Math.NumberTheory.ModArith.QPart` — **6 PURE / 0 DIRTY**.  Primitive-root marathon brick 4b-ii: the `q`-part `qpart q n := q^(vp q n)`.  `qpart_dvd` (`∣ n`), `qpart_pos`; `gcd_eq_of_dvd` (`b∣a ⟹ gcd a b = b`); ★ `q_not_dvd_quot` (`q ∤ (n/qpart)` — else `q^(vp+1)∣n`, contra `vp_not_dvd_succ`); ★ `gcd_qpow_qfree` (`gcd(qᵉ,B) = 1` for `q` prime, `q∤B`, via `dvd_prime_pow_cases`).

`E213.Meta.Nat.Valuation` — **15 PURE / 0 DIRTY**.  Primitive-root marathon brick 4b-i: the `q`-adic **valuation** `vp q n` (largest `k` with `qᵏ ∣ n`), a downward search.  Notable: the core `Nat` dvd/mod API (`Decidable (·∣·)`, `dvd_refl`/`dvd_trans`/`dvd_of_mod_eq_zero`/`mul_mod_right`/`pow_dvd_pow`) **all carry propext**, so the search decides on `n % qᵏ = 0` (structural `decEq`) and all divisibility runs through pure helpers (`drefl`, `dtrans`, `mod_zero_of_dvd` via `div_add_mod` + `mul_div_cancel_left_pure` + `add_left_cancel_pure`, `pow_dvd_add`/`pow_dvd_of_le`).  ★ `pow_vp_dvd` (`q^(vp q n) ∣ n`), ★ `vp_ge`, ★★ `vp_not_dvd_succ` (exactness; uses `vp_lt`: `vp q n < n` since `qⁿ > n`), `le_vp_iff`.

`E213.Lib.Math.NumberTheory.ModArith.MaxOrder` — **13 PURE / 0 DIRTY**.  Primitive-root marathon brick 4a (the exponent-argument scaffolding): `maxOrd p` = the maximum of `ordModP a p` over the units `[1,p−1]`.  Pure `nmax` + `le_nmax_left`/`le_nmax_right`/`nmax_le` (core `Nat.max` lemmas carry propext).  `maxOrd_ge` (every unit's order `≤ maxOrd`), ★★ `maxOrd_achieved` (`maxOrd = ordModP g p` for some unit `g ∈ [1,p−1]`), `one_le_maxOrd`, `maxOrd_le_pred` (`1 ≤ maxOrd ≤ p−1`).  The hard core "every order ∣ maxOrd" (brick 4b) needs the coprime lcm decomposition.

`E213.Lib.Math.NumberTheory.ModArith.CoprimeOrder` — **1 PURE / 0 DIRTY** (+2 private).  Primitive-root marathon brick 3.  ★★★ `ord_mul_coprime` — `gcd(ord a, ord b) = 1 ⟹ ordModP ((a·b)%p) p = ord a · ord b`.  `γ ∣ αβ` (the product collapse `(aᵅ)ᵝ·(bᵝ)ᵅ ≡ 1`); `α∣γ`, `β∣γ` from `(ab)^{γβ} ≡ 1 ⟹ a^{γβ} ≡ 1 ⟹ α∣γβ` (`euclid_of_coprime`); then `αβ = lcm(α,β) ∣ γ` (`coprime_mul_dvd`, reusing brick 1's `lcm_dvd` + `gcd_mul_lcm`).

`E213.Lib.Math.NumberTheory.ModArith.OrderPow` — **3 PURE / 0 DIRTY**.  Primitive-root marathon brick 2.  `ord_mod_eq` — the multiplicative order depends only on the base mod `p` (`findOrd_mod`: the search is unchanged by reducing the base, `aᵏ ≡ (a%p)ᵏ`).  ★★★ `ord_pow` — **the order of a power**: `ordModP (aᵏ) p = ordModP a p / gcd(ordModP a p, k)` for a unit `a`, `k ≥ 1`.  Both directions by `ord_dvd`: `(aᵏ)^(o/g) ≡ (aᵒ)^(k/g) ≡ 1` (so `ord(aᵏ) ∣ o/g`), and `(aᵏ)^ord ≡ 1 ⟹ o ∣ k·ord ⟹ (o/g) ∣ (k/g)·ord`, finished by `gcd_div_coprime` (`gcd(o/g,k/g)=1`) + `euclid_of_coprime`; `dvd_antisymm_213`.  The base-representative wrinkle (`aᵏ % p`) is dissolved by `ord_mod_eq`.

`E213.Lib.Math.NumberTheory.Lcm213` — **11 PURE / 0 DIRTY**.  The ℕ **least common multiple** `lcm213 a b = a·b / gcd a b` — the first brick of the primitive-root marathon.  Universal property **without Bezout**: `dvd_lcm_left`/`dvd_lcm_right`, and ★★★ `lcm_dvd` (`a∣m → b∣m → lcm∣m`) via `lcm = a·(b/g)`, `m = a·u` ⟹ reduce to `(b/g)∣u`, supplied by ★★ `gcd_div_coprime` (`gcd(a/g,b/g)=1`, the gcd-reduced parts are coprime — `d·g ∣ g` collapse) + `euclid_of_coprime`.  Plus `lcm_eq_left`/`_right`, `lcm_pos`, `gcd_mul_lcm` (`g·lcm = a·b`), `gcd_pos`, `mul_div_cancel_of_dvd`.

`E213.Lib.Math.NumberTheory.ModArith.MulOrder` — **12 PURE / 0 DIRTY**.  The **multiplicative order** `ordModP a p` (least `k ≥ 1` with `aᵏ ≡ 1 mod p`), the reusable foundation toward primitive roots (`(ℤ/p)*` cyclic) and the Zolotarev nontriviality witness.  `fermat` (`a^(p−1) % p = 1`, wrapping `universal_flt_main`); the upward search `findOrd` with `findOrd_some`/`findOrd_min`/`findOrd_found` (exists/minimal/found); `pow_ord` (`a^ord ≡ 1`), `ord_pos`, `ord_min`.  ★★★ `ord_dvd` — `aᵏ ≡ 1 ⟹ ord ∣ k` (by `k = ord·q + r`, `aᵏ ≡ aʳ` via the `(a^ord)^q ≡ 1` collapse `pow_split_eq`, minimality forces `r = 0`).  ★★ `ord_dvd_p_sub_one` — `ord ∣ (p−1)`.

`E213.Lib.Math.NumberTheory.ModArith.Zolotarev` — **12 PURE / 0 DIRTY**.  The multiplication-by-`a` permutation `mulPerm a p = [a·0,…,a·(p−1) mod p]` and the **homomorphism half** of Zolotarev's lemma (`(a/p) = sign(x ↦ a·x mod p)`).  `mulPerm_mem_perms` — `mulPerm a p ∈ perms p` (a permutation: `res_cancel` modular cancellation ⟹ `mul_inj` ⟹ `nodup_map_restrict` + `nodup_imp_perm`).  ★★ `mulPerm_comp` — **multiplication ↦ composition** (`composeList (mulPerm a)(mulPerm b) = mulPerm ((a·b)%p)`, both `getD i = (a·b·i)%p`, by `list_ext_getD` + `mul_mod_left/right_pure`).  ★★★ `psign_mulPerm_hom` — the sign is multiplicative (`psign_mul`).  ★★★ `psign_mulPerm_qr`/`psign_mulPerm_qr_pred` — **a quadratic residue's permutation is even** (`mulPerm (z²) = mulPerm z ∘ mulPerm z` ⟹ `psign = psign(mulPerm z)² = 1` via `altSign_self`): the `(a/p)=+1 ⟸ a` QR direction as the permutation sign.  Pure `length_map_pure` (core `List.length_map` carries propext).  The converse (non-residue ⟹ odd) is the documented Gauss-count / primitive-root residual.

`E213.Lib.Math.Algebra.Linalg213.ColumnLaplace` — **2 PURE / 0 DIRTY**.  ★★ **Laplace expansion along an arbitrary column** `cofactor_col_k` (`det (n+1) M = Σ_{j<n+1} (−1)^(k+j)·M j k·det n (minorAt j k M)`), the column dual of `Laplace.cofactor_row_i`, free from `DetTranspose.det_transpose`: expanding along column `k` of `M` is expanding along row `k` of `Mᵀ`, and `detMinor_transpose_swap` (`det n (minorAt k j Mᵀ) = det n (minorAt j k M)`) holds because the minor of a transpose is the transpose of the minor — the row-skip and column-skip reindexers are the *same* `colShift` function, so the two minors are defeq.

`E213.Lib.Math.Algebra.Linalg213.PermMatrixDet` — **8 PURE / 0 DIRTY**.  ★★★ **The determinant of a permutation matrix is its sign** `det_permMatrix` (`det n (permMatrix σ) = psign σ`), identifying the two readings of a permutation (matrix vs. inversion-count sign).  Reuses the **bubble-sort reduction** of `PermSign.psign_mul`: `permMatrix_swap_pointwise` (an adjacent `swapAt` is a row swap of `permMatrix`) feeds `DetRowOps.det_swapRows` (negates `det`) in lockstep with `psign_swapAt` (negates the sign); `descent_of_inv_pos` drives `σ` to `iota n` where `det_permMatrix_iota` (`det_lower_triangular`, value `1`) meets `psign (iota n) = 1`.  `getD_at_len`/`getD_at_len_succ`/`getD_swap_outside` are the `getD`-at-the-swapped-pair lemmas; the fuel induction `det_permMatrix_aux` is structural (no well-founded recursion).  Unlocks the Zolotarev bridge.

`E213.Lib.Math.Algebra.Linalg213.PermClosure` — **76 PURE / 0 DIRTY**.  Toward the Leibniz determinant's **alternating** property: the enumeration `perms n` realizes the symmetric-group action.  **§0** clean ∅-axiom `List` membership (`mem_append'`/`mem_map'`/`mem_flatMap'`/`mem_singleton'` — structural on the `List.Mem` constructors, since core's `mem_*` iff-lemmas are `propext`/`Quot.sound`-tainted).  **§1** `LPerm.mem` (membership preserved), `lperm_swap_prefix`.  **§2** soundness `insEv_sound`/`permsOf_sound` (every enumerated list is a genuine rearrangement of its input).  **§3** `LPerm.length_eq`, occurrence count `cnt` + `cnt_lperm` (LPerm-invariant).  **§4** ★ `lperm_of_cnt_eq` — **count-equality ⟹ `LPerm`** (the cancellation engine: `cnt_append`/`cnt_eq_zero_nil`/`cnt_pos_mem`/`mem_split`/`lperm_mid_to_front`, with `add_left_cancel'` a propext-free replacement for the tainted `Nat.add_left_cancel`).  **§5** `swapAt_invol` + `cnt_map_inv` (count under an involution-map).  **§6** completeness `permsOf_complete` (`LPerm q xs → q ∈ permsOf xs`) — with soundness, `q ∈ permsOf xs ⟺ LPerm q xs`.  **§7** `nodup_permsOf` (the enumeration has no repeats — `removeFirst` retraction + `nodup_flatMap`/`nodup_map`/`nodup_insEv`; `Nodup L := ∀a, cnt a L ≤ 1`).  **§8** ★★★ `perms_swap_closed` — the enumeration is closed under an adjacent position-swap up to `LPerm` (via `cnt_map_inv` involution + `cnt_eq_of_iff_mem` under nodup + sound/complete); uses a clean self-defined `iota` (`List.range`'s lemmas are propext/Quot-dirty).  **§9** ★★★ `leibDet_rowSwap` — **an adjacent row swap negates the Leibniz determinant** (the per-term `leibTerm_rowSwap` over a `split_at` decomposition, `sumZ_map_neg` for the sign, `perms_swap_closed`+`map_map'`+`sumZ_lperm` for the reindex).  **§10** ★★★ `leibDet_eq_zero_of_rows_eq` — **two equal adjacent rows ⟹ `leibDet = 0`** (`leibDet_congr` pointwise + `int_eq_zero_of_eq_neg` over ℤ).  The determinant is **alternating**, ∅-axiom, via antisymmetrization — no funext/propext/Quot.  Clean ∅-axiom `List` substrate built throughout (core's `mem_*`/`length_append`/`map_map`/`range` lemmas are propext/Quot-tainted).

`E213.Lib.Math.Algebra.Linalg213.Laplace` — **53 PURE / 0 DIRTY**.  The **cofactor (Laplace) expansion** of the Leibniz determinant — the gate toward integer Cayley–Hamilton.  **§1 relabeling**: `unshift j` = inverse of `DetN.colShift j` on `[0,…,n]∖{j}` (`colShift_unshift`/`unshift_colShift`).  **§2 per-element**: A′ `psign_map_colShift` (sign preserved under the order-embedding `colShift j` — `colShift_lt_mono` ⟹ `inversions_map_colShift`); B′ `prodDiag_minor` (diagonal product = the minor's); C′ `ltCount_perm_colShift` (leading inversion count `= j`, via `ltCount_iota`); ★ `leibTerm_cons_colShift` (`leibTerm M (j :: rel.map (colShift j)) = (−1)ʲ · M 0 j · leibTerm (minor M j) rel`).  **§2 reindex**: `lperm_of_nodup_mem_iff` (Nodup + same-membership ⟹ `LPerm`), `lperm_cons_inv`, `map_inj_list`, `canonical_lperm`, ★★ `perms_succ_lperm` (every permutation of `[0,…,n]` decomposes uniquely by its head).  **§2 assembly**: `sumZ_append`/`map_append'`/`map_flatMap`/`sumZ_flatMap`/`cofactor_term`, and ★★★ `cofactor_row0`: **`leibDet (n+1) M = Σ_{j≤n} (−1)ʲ · M 0 j · leibDet n (minor M j)`** — the full cofactor expansion, ∅-axiom from scratch.  **§3 bridge**: `cofSum_eq_sumZ_iota`, `cofSum_congr`, ★★ `leibDet_eq_det` (the Leibniz determinant = the recursive `DetN.det`), and the property transfers `det_rows_eq_ne` / `det_setRow_add` / `det_setRow_smul` — `DetN.det` is now a full determinant (alternating + multilinear + cofactor recursion).

`E213.Lib.Math.Algebra.Linalg213.PermBridge` — **7 PURE / 0 DIRTY**.  The **bridge between the two permutation developments**: the Leibniz index enumeration (`Permutation.permsOf`, with sound/complete/nodup via `PermClosure`) and the generic `Combinatorics.Permutations.perms` (carrying the count `perms_length = fact`) are the **same list** — they differ only in propext-free `flatMap213` vs core `List.flatMap`, which concatenate identically.  `flatMap_eq` (the two `flatMap`s agree), `cflatMap_congr` (pointwise congruence, no `funext`), `insEv_eq` (the two `insertEverywhere`s agree), ★ `permsOf_eq` (`permsOf xs = perms xs`), `iota_length`, ★ `perms_card` (**the Leibniz index set has `n!` members**: `(perms n).length = fact n`), and ★★ `leibDet_card` — **the Leibniz determinant is a sum of exactly `n!` signed diagonal products**.  Transports the factorial count to the determinant's index set, ∅-axiom.

`E213.Lib.Math.Algebra.Linalg213.CayleyHamilton` — **25 PURE / 0 DIRTY**.  The **matrix ring** over `Nat → Nat → Int` (with `Laplace`'s adjugate identity `M·adj M = det M·I` already in hand), toward the integer Cayley–Hamilton telescoping `χ_M(M)=0` for the C-finite Hadamard product.  **§1 Fubini**: `sumZ_map_zero`, ★ `sumZ_swap` (finite double-sum swap), `sumZ_map_smul_right`.  **§2**: ★★ `matMul_assoc` (matrix multiplication is associative, via Fubini).  **§3 ring core**: `matId`/`matAdd`/`matNeg`/`matZero`/`matScalar`, the Kronecker-delta sums `sumZ_iota_delta_ge`/`_lt`, ★ `matMul_id_left`/`_right` (`I·M = M`, `M·I = M` at in-range indices).  **§4**: distributivity `matMul_addL`/`_addR`, `matMul_scalarL`, `matMul_negL` (with `sumZ_map_neg`, `neg_zero'`), and `matPow` (`M^0 = I`, `M^{k+1} = M·M^k`).  **§5 matrix sums**: `matSumZ` (entrywise sum over a `List Nat`), ★ `matMul_matSumZ_right`/`_left` (matMul distributes over a matrix sum, via Fubini), `matSumZ_add`.  The ring laws the Cayley–Hamilton telescoping consumes.

`E213.Lib.Math.PolyZ` — **33 PURE / 0 DIRTY**.  **Integer-coefficient polynomials** (the `ℕ`-valued `Polynomial213` cannot carry the signed `XI − M`).  `PolyZ := List Int` (low-to-high), Horner `eval`, and `C`/`Xp`/`addP`/`negP`/`scaleP`/`shiftP`/`mulP`/`coeff`.  ★ **eval soundness** — each operation commutes with evaluation: `eval_C`/`eval_Xp`/`eval_addP`/`eval_scaleP`/`eval_shiftP`/`eval_negP`/★★`eval_mulP`; `PolyZ` is a commutative-ring reflection of `Int`.  **Uniqueness** (the gate that transports the `Int` adjugate identity into a `PolyZ` coefficient identity): `coeff_addP`/`coeff_negP`; the synthetic-division quotient `synth` with the ★ **factor theorem** `eval_synth` (`p(x) = p(r) + (x−r)·(synth p r)(x)`) + `length_synth_cons`; ★ `roots_bound` (a polynomial of length `≤ L` with `L` distinct integer roots is the zero function — induction on `L`, factoring at a root, `Int213.mul_eq_zero` integral domain); ★ `coeff_zero_of_eval_zero` (vanishes everywhere ⟹ all coefficients `0` — peel the constant term, bridge `x=0` via `roots_bound` at nodes `1,2,…`); ★★ `coeff_unique` (two polynomials agreeing at every integer have equal coefficients).  Plus the coefficient convolution for degree-`≤1` factors (`coeff_nil`/`coeff_scaleP`/`coeff_shiftP_*`/`coeff_mulP_single`/`coeff_mulP_pair_zero`/`coeff_mulP_pair_succ`), feeding the Cayley–Hamilton relation extraction.

`E213.Lib.Math.Algebra.Linalg213.PolyDet` — **20 PURE / 0 DIRTY**.  The **polynomial determinant** `pdet n A` (determinant of a `PolyZ`-entried matrix, by the same row-0 cofactor recursion as `DetN.det`) and the **characteristic polynomial**.  **§1**: `pminor`/`pcofSum`/`pdet`, `evalMat` (entry-wise evaluation), `evalMat_pminor`, `eval_pcofSum`, and ★★ `eval_pdet` — **evaluation soundness** `eval (pdet n A) x = det n (evalMat A x)` (evaluating the polynomial determinant = the integer determinant of the evaluated matrix; lets the char poly be obtained as actual integer coefficients while identities are proven by evaluation, reusing the `Int` determinant theory rather than re-deriving cofactor/adjugate over `PolyZ`).  **§2**: `charMat M = X·I − M` (poly-matrix), `charPoly M N = pdet N (charMat M)`, `evalMat_charMat`, and ★ `eval_charPoly` — **`eval (charPoly M N) x = det N (x·I − M)`** for every integer `x` (the characteristic polynomial as a concrete integer polynomial with the right values).  **§3 the degree bound**: `degLe_pcofSum` + ★ `degLe_pdet` (`pdet` of an `n×n` matrix with degree-`≤1` entries has degree `≤ n`).  **§4 monicity**: `pcofSum_congr`/`pdet_congr` (pointwise congruence), `degLe_charMat`, `pminor_charMat_zero` (the `(0,0)`-minor of `X·I−M` is the char-matrix of the shifted `M`), `charMat_cofactor_coeff_top`/`charMat_pcofSum_coeff_top`, and ★★ `charPoly_monic` — **`coeff (charPoly M N) N = 1`** (the characteristic polynomial is monic).

`E213.Lib.Math.Algebra.Linalg213.CharPolyAdj` — **31 PURE / 0 DIRTY**.  The **polynomial adjugate identity** `(X·I − M)·adj(X·I − M) = χ_M·I` over `ℤ[X]` — the seed of integer Cayley–Hamilton.  Matrix products / adjugates over `PolyZ` carry **evaluation soundness** (eval = the `Int` operation on the evaluated matrix), so the identity is lifted from the `Int` adjugate identity (`Laplace`, every `x` at `A = xI−M`) by evaluation + `PolyZ.coeff_unique` — no cofactor/adjugate theory re-derived over `PolyZ`.  **§1**: `psumZ`/`eval_psumZ`, `pmatMul` (`PolyZ` matrix product) + ★ `eval_pmatMul`.  **§2**: `pminorAt`, `padj` (poly-adjugate, mirrors `Laplace.adj`) + ★ `eval_padj` (`eval (padj n A a b) x = adj n (evalMat A x) a b`).  **§3**: `matMul_congr` (matMul respects pointwise factor equality), `charScalarId` (`χ_M·I`), ★ `padj_identity_eval` (entry `(i,k)` of `(XI−M)·adj` evaluated = the `Int` adjugate value, by `matMul_adj_diag`/`matMul_adj_offdiag`), and ★★★ `padj_identity` — **the entries of `(X·I − M)·adj(X·I − M)` and of `χ_M·I` are equal integer polynomials** (`coeff_unique`).  **§4 the Cayley–Hamilton coefficient relations**: `coeff_pmatMul`/`coeff_charScalarId`, and ★★ `cayley_rel_zero` (`−(M·B₀) = c₀·I`) + ★★ `cayley_rel_succ` (`Bₘ − M·B_{m+1} = c_{m+1}·I`) — reading `padj_identity` coefficient-wise (`Bₖ(i,j) := coeff (adj(X·I−M) i j) k`, `cₖ := coeff χ_M k`).  **§5 the degree bound**: `degLe_charMat` (`X·I−M` entries have degree `≤1`) + ★ `padj_coeff_top_zero` (`B_{n+1} = 0`, i.e. `adj(X·I−M)` has degree `≤ n` — via `PolyDet.degLe_pdet`); the telescoping's vanishing boundary term.  **§6 matrix-form relations**: `Bm`/`cm`, `matMul_eq_neg_sumNeg`, and ★★ `matMul_Bm_zero` (`M·B₀ = −c₀·I`) + ★★ `matMul_Bm_succ` (`M·B_{m+1} = Bₘ − c_{m+1}·I`).  The inputs the final telescoping consumes.  **§7 ★★★ integer Cayley–Hamilton**: `sumZ_map_sub`, `charSum`/`charSum_zero`/`charSum_succ`, the telescoping step `tele_step` (`Mᴺ⁺²·B_{N+1} = Mᴺ⁺¹·B_N − c_{N+1}·Mᴺ⁺¹`, via `matPow_succ_right` + `matMul_assoc` + bounded `matMul_congr`), ★ `telescope` (`Σ_{m=0}^{N} cₘ·Mᵐ = −Mᴺ⁺¹·B_N`), and ★★★ **`cayley_hamilton`** — `Σ_{m=0}^{n+1} (coeff χ_M m)·(Mᵐ)_{ik} = 0`, i.e. **the characteristic polynomial annihilates its own integer matrix** (`χ_M(M) = 0`), ∅-axiom from scratch (boundary `−Mⁿ⁺²·B_{n+1} = 0` since `B_{n+1}=0`).  **§8 the recurrence bridge**: `wPow` (`w(n+1)=M·w(n) ⟹ w(n+m)=Mᵐ·w(n)`) and ★★★ `ch_recurrence` — **a vector sequence evolving by `w(n+1)=M·w(n)` has every component satisfy the monic order-`(N+1)` recurrence `Σ_{m} (coeff χ_M m)·w(n+m) = 0`** (the payoff feeding `cfiniteZ_mul`).

`E213.Lib.Math.Algebra.Linalg213.RowDependence` — **6 PURE / 0 DIRTY**.  **Row dependence ⟹ `det = 0`**, feeding the Casoratian rank bridge.  `sumZ_iota_succ`, `det_zero_row` (a zero row ⟹ `det=0`), `setRow_eq`, ★ `det_setRow_sumZ` (multilinearity over a finite `ℤ`-combination), and ★★ `det_row_combo_zero` — **row `i` = a `ℤ`-combination of other rows ⟹ `det = 0`** (`det_setRow_add`/`_smul` + `det_rows_eq_ne`); and ★★ `det_addRowMul` — **adding a multiple of one row to another preserves `det`** (the elementary row operation, basis of Gaussian elimination).

`E213.Lib.Math.Algebra.Linalg213.DetTriangular` — **15 PURE / 0 DIRTY**.  ★★ **The triangular determinant** `det_lower_triangular`: a lower-triangular matrix (`M i j = 0` for `i < j`) has `det n M = Π_{i<n} Mᵢᵢ` (`prodZ` of the diagonal).  Row-`0` cofactor expansion collapses to the single `M₀₀·det(minor M 0)` term (`cofSum_lowerTri`, since the rest of row `0` is zero), and the `(0,0)`-minor is again lower-triangular with shifted diagonal (`minor0_lowerTri`); induction accumulates the product (front-peel `iota_cons`: `iota (n+1) = 0 :: (iota n).map succ`).  Corollary ★ `det_matId` — **`det matId = 1`** (the identity is lower-triangular with unit diagonal; `prodZ_map_one`).  ★★ **The dual** `det_upper_triangular`: an upper-triangular matrix (`M i j = 0` for `j < i`) likewise has `det n M = Π_{i<n} Mᵢᵢ` — proved by **last-row** cofactor expansion (`cofExpand_lastRow` via `Laplace.cofactor_row_i` at `k=n`: the last row is `0,…,0,M n n`, so only the `j=n` term survives with sign `(−1)^(n+n)=1`), the `(n,n)`-minor again upper-triangular (`minorAt_nn_upperTri`) with diagonal preserved (`minorAt_nn_diag`); back-peel `prodZ_snoc`.  Corollaries ★ `det_diagonal` (a diagonal matrix is in particular lower-triangular) and ★ `det_diag_fun` (`det diag(d₀,…,d_{n−1}) = Π dᵢ`).

`E213.Lib.Math.Algebra.Linalg213.DetRowOps` — **11 PURE / 0 DIRTY**.  The **elementary row operations** behind Gaussian elimination, all with *no new sign theory*.  ★★ `det_addRowMul` — **adding a multiple of one row to a distinct row leaves `det` unchanged** (`rowᵢ ← rowᵢ + t·rowⱼ`, `i ≠ j`): row-multilinearity (`Laplace.det_setRow_add`/`det_setRow_smul`) splits `det(rowᵢ + t·rowⱼ) = det M + t·det(rowᵢ ← rowⱼ)`, and the last term has two equal rows so vanishes (`Laplace.det_rows_eq_ne`), leaving `det M + t·0 = det M` (`setRow_self`, `addRowMul`/`addRowMul_at`/`addRowMul_off`).  Corollary ★ `det_addRow` (the `t = 1` case).  ★★ `det_swapRows` — **an arbitrary row swap negates `det`** (`i ≠ j`), the alternating property for *any* row pair (`Laplace.det_rowSwap` covers only the adjacent case): a swap factors into three `det`-preserving adds (`rowᵢ += rowⱼ`, `rowⱼ −= rowᵢ`, `rowᵢ += rowⱼ` lands at `(rowⱼ, −rowᵢ)`) plus negating `rowⱼ` (`det_setRow_smul` by `−1`); `swapRows`/`swapRows_i`/`swapRows_j`/`swapRows_other`.

`E213.Lib.Math.Algebra.Linalg213.DetScale` — **4 PURE / 0 DIRTY**.  ★★ **The scaling determinant** `det_smul`: `det n (c·M) = cⁿ · det n M` (each of the `n` rows of a Leibniz term contributes one factor `c`; via `prodDiagFrom_smul` (`prodDiagFrom (c·M) = c^{|p|}·prodDiagFrom M`) + `leibTerm_smul` + `sumZ_map_smul`, `perm_length` pinning `|p|=n`).

`E213.Lib.Math.Algebra.Linalg213.DetZeroCol` — **3 PURE / 0 DIRTY**.  ★★ **A zero column ⟹ `det = 0`** (`det_zero_col`) — the column analog of `det_zero_row`, proved *directly from the Leibniz form* (no transpose): every permutation hits the zero column once (`mem_perm_of_lt`, via `LPerm.mem`+`mem_iota_of_lt`), so every diagonal product carries a zero factor (`prodDiagFrom_zero_of_mem`).

`E213.Lib.Math.Algebra.Linalg213.ProdLperm` — **3 PURE / 0 DIRTY**.  The multiplicative analog of `sumZ`/`sumZ_lperm`, the **foundation for the transpose determinant** `det Mᵀ = det M`.  `prodZ` (product of an `Int` list), ★ `prodZ_lperm` (**a product is invariant under `LPerm`** — reordering the factors, via `Int213.mul_left_comm`, mirroring `sumZ_lperm`), `prodZ_append`.  (Transpose itself then needs: the Leibniz term of `Mᵀ` = that of `M` at the inverse permutation, via the inverse on the list rep + `prodZ_lperm` on the diagonal-product factor list + `psign p = psign p⁻¹` + `perms` closed under inverse.)

`E213.Lib.Math.Analysis.Cauchy.CasoratianStep` — **5 PURE / 0 DIRTY**.  The discrete-Wronskian
(Abel/Liouville) law for a 3-term recurrence in subtraction-free `ℕ` form, + its telescoping:
`telescope` — `P(n+1)g(n+1)=Q(n+1)g(n) ⟹ (∏P)·g(n)=(∏Q)·g(0)` (the sign-definite ζ(3)
Casoratian `P=n³=aperyTop`, `Q=(n−1)³=aperyBot`, `g=|Cₙ|` ⟹ the cube-product telescoping
whose ratio is the `1/n³` denominator), with non-vacuous `telescope_geometric` (`rⁿ`).
`casoratian_step` — for any solutions `a,b` of `c₂·x₂=c₁·x₁+c₀·x₀`,
`c₂·(a₂·b₁)+c₀·(a₁·b₀) = c₂·(a₁·b₂)+c₀·(a₀·b₁)` (both sides `=
c₁a₁b₁+c₀a₀b₁+c₀a₁b₀`), the minus of `c₂Cₙ=−c₀Cₙ₋₁` moved across.  The middle coefficient
`c₁` cancels ⟹ the Casoratian propagates by the *outer* coefficients alone, grounding why
the Apéry-tower invariant is `deg c₂ = deg c₀` (`DepthAperyCubic`).

`E213.Lib.Math.NumberSystems.Real213.Zeta3Cut` — **40 PURE / 0 DIRTY**.  ★★★ **ζ(3) as a
constructed fold.**  The Apéry recurrence (the `DepthAperyCubic` degree-3 coefficients
`aperyLead`/`aperyBot`), factorial-cleared to the all-ℕ orbit `x_{m+2} = aperyLead m·x_{m+1}
− (aperyBot m)²·x_m`, *generates* the ζ(3) convergents: the growth invariant
`aperyOrbit_inv` (`(m+1)³·xₘ ≤ xₘ₊₁`, from the seed condition `x0+8x1 ≤ 117x1`) proves the
ℕ subtraction never truncates (`aperyOrbit_exact`), the Casoratian comes out in closed form
(`zeta3_cross_det`: cross-det `= aperyCasDet m = 6·(m!)⁶`, sign-definite), and the
convergents are an `AbCutSeq` (`zeta3Ab`) — full cut interface, with localization
`601/500 < ζ(3) ≤ 1203/1000` (`zeta3Cut_in_bracket`; upper bounds are themselves orbits of
the same recurrence, `aperyOrbit_linear`) and completion to a `ValidCut` limit carrying the
bracket (`zeta3Limit_in_bracket`).  Honest stratum: `zeta3_presentation_overtakes` *proves*
this presentation rate-free (`W = 6·(m!)⁶` overtakes the denominator quantum at layer 9,
`RateStratification.overtake_breaks_layer`), so the completion modulus stays a hypothesis —
the π-posture; the e-grade constructed modulus lives in the reduced presentation (Apéry
integrality + lcm bound), a recorded frontier.  `zeta3_fold_is_apery` bundles the working
recurrence with `apery_cubic_rung` (the degree-3 holonomic signature).  §8:
★★ `aperyOrbit_geom` — **geometric orbit growth** `x_{m+1} ≥ 28·(m+1)³·xₘ`
from layer 7 (base sharp: the layer-6 ratio is `≈27.2`), where `28 > 27 = 3³`
is exactly the reduced presentation's race margin against Hanson's
`lcm(1..n) < 3ⁿ` (instances `zeta3Den_geom`/`zeta3Num_geom`, bases by kernel
computation); ★★★ `zeta3_reduced_conditional` — the **engine end of the
e-grade route**: given I1 (integrality: the convergents factor through a
reduced pair `zeta3Num = c·p`, `zeta3Den = c·q`) and I2 (the reduced
smallness law from a layer `n₀` — what Hanson's bound buys), ζ(3)'s original
cut carries the constructed total modulus `N(m,k) = k + n₀ + 2` (the
from-layer generator runs on `(p,q)`; the cut transfers through the common
factor).  Only the two classical Apéry inputs remain.

`E213.Lib.Math.NumberSystems.Real213.CubeRootTwoCut` — **31 PURE / 0 DIRTY**.  ★★★ **∛2:
the degree-3 form-margin modulus — the algebraic exit from the rate race.**  Side-decision
against a probe `m/k` reduces to the all-additive `ε_i·k³ < d_i³` (the form margin
`|m³−2k³| ≥ 1` arriving as `Nat` strictness `+1`; the degree enters as the probe exponent
`k³`) — no cross-determinant race.  Dyadic bisection presentation (`cbrtNum i / 2^i`,
cube-bracket invariant `cbrtNum_inv`, slack `ε ≤ 24·4^i` vs `d³ = 8^i`) ⟹ **total ∅-axiom
modulus `N(m,k) = 3k+5`** (`cbrtCauchySeq`): ∛2 joins φ/e/Liouville in the unconditional
class, the first degree-3 member, by the *form* mechanism rather than the rate certificate.
Capstone `cbrt_limit_eq_form`: the completed fold **equals** the frozen closed-form cut
`decide (2k³ ≤ m³)` (degree-3 analog of `cs_eq_phiCut`); `cbrt2Cut_valid`, bracket
`5/4 < ∛2 ≤ 13/10`.  The degree-2 shadow of the same `ε·k^s < d^s` schema is
`FibCassiniNat.qb_lt_pk` (`4k² < b²`); the rate race and its presentation-dependence
(`Zeta3Cut`) are thereby isolated as the transcendental-only regime.

`E213.Lib.Math.NumberSystems.Real213.ModulusComposition` — **28 PURE / 0 DIRTY**
(the arbitrary-base power toolkit lives in `Meta.Nat.PowBasic`).  ★★★
**Schedules with irrational degree — receipts taking receipts.**  `powSched c B k =
⌈k^{p/2^k}⌉` with the exponent `p = dyUp c B k` read off a *cut* `c` level by level
(`dyUp_true`: sound from an integer witness + forward doubling `c m k → c (2m) (2k)`;
`rootCeil_sound`/`rootCeil_least`: the exact integer root ceiling).  Calibration
`powSched_rat`: an integer exponent returns exactly `k^s` — the functional extends the
polynomial ladder.  Instances: degree **∛2** (`cbrtPow_at_two`: `powSched cbrt2Cut 2 2 = 3
= ⌈2^{3/2}⌉`, soundness via `cbrt2Cut_double`) and degree **e** (`ePow_at_two`:
`powSched eulerModCut 3 2 = 7 = ⌈2^{11/4}⌉`, where `eulerModCut` is e's limit written
through `eulerCauchySeq.N` — the kernel runs e's constructed modulus *inside* the
schedule).  Cascade rung 1: `reschedule` (modulus weakening, limit-preserving) +
`eSelfScheduled` — e carrying a modulus that queries e's own modulus.  The operational
content of "irrational degree": the receipt ladder is a call tree of folds.  §8
`powSched_mono` (+ `dyUp_mono`, `rootCeil_mono`): **degree order transports to schedule
order** — the backbone making "the degree of a real" a cut-shaped (monotone) threshold
over exponent cuts; its decidability is the effectivity question (frontier).

`E213.Lib.Math.Analysis.Cauchy.DepthOverflowDuality` — **15 PURE / 0 DIRTY**.
The analysis ↔ logic single engine: `Overflow bound val i := bound i <
val i` (= `bound i + 1 ≤ val i`, the unit surplus).  `overflow_escapes`
(overflow ⟹ value is no level of the family; recovers `diag_not_in_seq`),
`overflow_breaks` (overflow ⟹ domination breaks = `overtake_breaks_layer`),
`overflow_dual_reading` (both readings of one operation).  Bridges
`DepthCeilingResidue` (Cantor residue) and `RateStratification` (¬Htel).
Plus the unit-generator layer: `minOverflow bound = bound + 1` is the
pointwise-least overflow (`least_overflow`, `minOverflow_overflows`), the
diagonal achieves it (`diag_is_minOverflow`), overflow is monotone /
shift-stable (`overflow_mono_val`, `overflow_shift`), the least overflow is
unique (`minOverflow_unique`, the honest universal property), and the surplus
is the conserved quantity under shift (`gap_shift_invariant`, via the PURE
`NatHelper.add_sub_add_right`).

`E213.Lib.Math.NumberSystems.Real213.IntensionalCompletability` — **3 PURE / 0 DIRTY**.
The intensional reduction of completability: `crossDetSmall_rescale_antitone`
(the sufficient bridge `CrossDetSmall (c²·W) (c·d) → CrossDetSmall W d` — rescaling
up only loses it, so the gcd-reduced presentation is canonical; `Nat.mul_assoc` is
propext-dirty, used the PURE `NatHelper.mul_assoc`), `modulus_rescale_invariant`
(the completion is presentation-invariant, via `rcut_rescale`), bundled in
`completability_is_intensional`.  The test is presentation-relative; the truth is not.

`E213.Lib.Math.NumberSystems.Real213.ScalingOrbit` — **7 PURE / 0 DIRTY**.  The rescaling
orbit `(c·a, c·d)` of a presentation: `scaleBy` a monoid action (`scaleBy_one`,
`scaleBy_comp`), the cut its complete invariant (`scaleBy_preserves_cut`),
`CrossDetSmall` antitone along it (`orbit_free_implies_base_free`), and the
`Reduced` base unique (`reduced_scaling_trivial`).  Bundled in
`scaling_orbit_structure`.  Advances completability direction C2: the reduced base is the
rung-minimal presentation within a rescaling orbit (scope: rescaling sub-family,
not all presentations).

The signed-ℤ Eisenstein/golden signature dichotomy is closed canonically in
`E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSignature` (`eisForm_nonneg`,
`eisenstein_norm_nonneg`, `golden_indefinite`, `signature_dichotomy`) via the
bivariate Int reflection prover `Meta.Int213.PolyInt2` — the genuine `0 ≤ a²−ab+b²`
over ℤ, tied to `ZOmega.normSq`.  (The earlier ℕ-visible sidestep
`Real213.CrossDetDiscriminant` is removed — superseded once `PolyInt2` landed.)

`E213.Lib.Math.NumberSystems.Real213.FloorReferenceForm` — **2 PURE / 0 DIRTY**.  The
completability-side (disc+5, line) complement: the det-one floor's conserved golden
form `m²−mk−k²` (`ProbeTwistConic.Q_preserved`) is indefinite (`golden_indefinite`,
`Q(2,1)=+1`, `Q(1,1)=−1`) → unbounded → convergent line → the completing bottom rung
(`floor_reference_is_indefinite`).

`E213.Lib.Math.NumberSystems.Real213.SpiralRotationInvariant` — **3 PURE / 0 DIRTY**.  The
spiral rotation invariant conserved at every turn: `Q_iterate_preserved` —
`Q(Pseq (m,k) n) = Q(m,k)` (sign-free golden form `a²+mk+k² = ab+b²+m²`) for all `n`,
by induction on the one-step `ProbeTwistConic.Q_preserved` chained through the pure
additive `add_cancel_chain` (the dirty `Nat.add_right_cancel` replaced by
`NatHelper.add_right_cancel`).  The golden form (disc `5 = NS+NT`) is the scale-invariant
of the self-similar `P`-shift.

`E213.Lib.Math.Analysis.Cauchy.DepthHeightDiagonal` — **4 PURE / 0 DIRTY**.  Naming the
whole `ω^r` height-tower escapes every finite height: `heightTower c r n = expTower
c r n`, and `height_diagonal_escapes` — `diag (heightTower c) ≠ expTower c r` for
every `r` (via `DepthCeilingResidue.diag_not_in_seq`).  The residue at the height
scale, the frontier *toward* `ε₀` (no `Ordinal` constructed); `epsilon_direction`
bundles it with `coord_layer_dominates` (each layer ×`ω`).

`E213.Lens.ResidueReentry` — **2 PURE / 0 DIRTY**.  The residue re-enters as the
next operand, and the self-cover never closes: `residue_reentry_never_closes` — the
composite `P ↦ Object1 (predicateToRaw n P)` (encode the predicate to a Raw, point at
it) is not surjective (its image ⊆ `Object1`'s, which misses the residue), so re-pointing
the re-entered residue leaves a fresh residue.  `residue_perpetually_reenters` bundles:
pointing faithful-but-not-total (`object1_injective`/`object1_not_surjective`), the
residue re-encodes to a Raw (`predicateToRaw`), re-pointing never closes.  The
foundational-pointing instance of the gapless self-applying re-entry
(`Cauchy/DepthHeightDiagonal.diag_self_applies`).

`E213.Lens.Bool213.SelfReferenceForms` — **2 PURE / 0 DIRTY**.  The two
structural forms of Raw self-reference (`05_no_exterior` §5.2): `bool_not_no_fixed_point`
(the Bool `not` has no fixed point on its values `{T,F}` — the liar oscillation, period 2
never period 1) contrasted with the Nat-style Lambek period-1 self-fixed-point
(`decompose`) + well-founded descent (`depth_drops`); `self_reference_two_forms` bundles
the dichotomy.

`E213.Lib.Math.FiveFloorUnification` — **1 PURE / 0 DIRTY**.  The completability
floor and the McKay E₈ endpoint are the same atomic `P = [[2,1],[1,1]]` (disc
`5 = NS+NT`): `five_floor_unifies` bundles the det-one floor's indefinite golden form
(`FloorReferenceForm.floor_reference_is_indefinite`, the completing line bottom) with
`P mod 5` being the order-10 E₈ icosian endpoint (`MobiusPIcosian.mobius_P_meets_icosian_endpoint`).
Bottom-of-completability meets top-of-McKay at the `5`-floor (a convergence, not a
derivation; `seed/AXIOM/05_no_exterior.md` §5.6).

`E213.Lib.Math.Algebra.CayleyDickson.Integer.ParabolicSignature` — **4 PURE / 0 DIRTY**.
Completes the signature dichotomy to a trichotomy: the degenerate disc-0 form
`parabForm m k = (m−k)²` is semi-definite (`parab_nonneg`, a square) with a non-origin
zero (`parab_nonorigin_zero`, `parabForm 1 1 = 0`, vanishing on a line) — the parabolic
cusp between the indefinite golden line (disc+5) and the definite Eisenstein curve
(disc−3).  `signature_trichotomy` bundles all three.

`E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegTwoSquare` — **11 PURE / 0 DIRTY**.
★★★★★ **The disc-`−8` representation iff** `disc_neg_eight_iff` (`p = a²+2b² ⟺ p ≡ 1,3 mod 8`
for an odd prime), the `ℤ[√−2]` twin of `GaussianTwoSquare.two_square_iff`.  Sufficiency
(`rep_of_mod8`): the character `(−2/p) = (−1/p)·(2/p)` from the **Legendre homomorphism**
(`LegendreMultiplicative.legendre_mul` at `a=p−1`, `b=2`, via `((p−1)·2) % p = p−2`), the two
factors the closed first/second supplements (`neg_one_qr_iff`, `second_supplement`); the
characters agree on `p ≡ 1,3 mod 8` ⟹ `p ∣ z²+2` ⟹ `ZSqrtNegSplit.split_form_two`.  Necessity
(`mod8_of_rep`): a square/`2·square`-mod-8 enumeration (`int_small8`/`sq8`/`two_sq8`/`form8_residue`).
The `−2`-character supplies the Pillar-I input the bare non-residue search lacked.

`E213.Lib.Math.NumberSystems.Padic.SetoidMul` — **11 PURE / 0 DIRTY**.  The multiplicative twin of `SetoidAssoc` (which gave the additive abelian group): `Zp.mul` commutativity / associativity / identity / left-distributivity at the **Setoid level** (`ZpSeqEquiv`).  `Zp.mul_trunc` descends each law to `ℤ/pⁿ` — `mul_comm_trunc` (`Nat.mul_comm`), `mul_assoc_trunc` (`mul_mod_left/right_pure` + `ring_nat` for the `Nat.mul_assoc` whose core proof carries `propext`), `mul_one_trunc` (`trunc_one_succ` + no-wraparound), `mul_add_trunc` (`mul_mod_right_pure` + `add_mod_gen` + `Nat.mul_add`) — then `digits_eq_of_trunc_eq` lifts trunc-equality-at-every-`n` to `ZpSeqEquiv` (funext-free).  ★★★★★ `zp_setoid_comm_ring_capstone`: with the additive group, `ZpSeq / ZpSeqEquiv` is a **commutative ring**.  Unblocks `i₅ = teichmuller`.

`E213.Lib.Math.NumberSystems.Padic.TeichmullerI5` — **5 PURE / 0 DIRTY**.  ★★★★ **`i₅ = teichmuller(2-lift)`** (`i5_eq_teichmuller`): the 5-adic imaginary unit `i₅ = √(−1)` equals the Teichmüller representative of `lift2` (digit 0 = `2`) at every truncation.  `i5_pow4_mod` lifts `i_5_pow_four_trunc` (`i₅⁴ ≡ 1`) to power form `(i₅.trunc(n+1))⁴ % 5ⁿ⁺¹ = 1` (pulling the inner mods); `i5_frob_fixed` then gives `i₅⁵ ≡ i₅` cleanly via `Zp.pow_trunc` (`(pow x n).trunc m = (x.trunc m)ⁿ % pᵐ` — the whole thing in `ℤ/5ᵐ`), and `teichmuller_eq_of_fixed` (`prime_gcd_5` discharges the `p=5` coprimality) pins `i₅` as the unique Frobenius-fixed lift of its residue.  `Nat.pow_add`/`Nat.mul_assoc`'s propext sidestepped via `Nat.pow_succ` + `ring_nat`.

### p-adic library closure addition

`E213.Lib.Math.NumberSystems.Padic.*` — Real213-p-adic library — adds **308 PURE
declarations** across 8 modules (`Foundation`, `Arith`, `Pow`,
`Norm`, `Hensel`, `Teichmuller`, `Field`, `DRLT`).  Headline
closures:

  · `Zp.add_trunc` / `Zp.mul_trunc` — ring-quotient theorems for
    truncation `ZpSeq p → ℤ/p^n`; full ring axioms at trunc level
    (comm, assoc, distrib, additive inverse via `add_neg_self_trunc`).
  · `Zp.mul_invSeq_correct` / `Zp.mul_invFull_correct` /
    `Zp.inv_trunc_unique` — Hensel-lifted multiplicative inverse
    with existence + uniqueness at every level.
  · `Zp.sqr_sqrtSeq_correct` / `Zp.sqr_sqrtFull_correct` /
    `Zp.sqr_unique_trunc` — Hensel-lifted square root via
    `SqrtBase`, with existence + uniqueness.  Concrete instances:
    `i_5 = √(-1) ∈ ℤ_5`, `i_13 ∈ ℤ_13`, `sqrt_two_7 ∈ ℤ_7`.
  · `Zp.valAtLeast_add` / `Zp.valAtLeast_mul` / `Zp.valEq_add_of_lt`
    / `Zp.valEq_mul` / `Zp.valEq_neg` — full strong ultrametric
    (additive + multiplicative + negation, precise valEq forms).
  · `Zp.pow` / `Zp.pow_trunc` / `Zp.pow_add_trunc` /
    `Zp.pow_mul_trunc` — natural-number power with ring-quotient
    homomorphism properties.
  · `Zp.pow_p_trunc_one` / `Zp.pow_p_minus_one_trunc_one` — Fermat's
    little theorem at digit 0 (for p prime via `prime_gcd`).
  · `Zp.frobenius_lift` / `Zp.teichmuller_iter_cauchy` — Frobenius
    lift `y ≡ z mod p^k → y^p ≡ z^p mod p^(k+1)` and Cauchy
    convergence of the iteration `x ↦ x^p`.  Notable: the proof
    avoids binomial coefficients entirely and holds for any p ≥ 1.
  · `QpSeq` ℚ_p localization with add/sub/mul/neg/inv/div/sqrt.
  · `canonical_5adic_p` — 5-adic lift of the base prime `5`,
    with digit smoke-tests.

Follow-on (directions A/B): the explicit Teichmüller
representative and the unit-group decomposition, all PURE:

  · `Zp.teichmuller` — `ω(x)` as the diagonal of the iteration
    `x ↦ x^p`; `Zp.teichmuller_pow_p_trunc` — the Frobenius fix
    `ω^p ≡ ω` (`Padic.Teichmuller`).
  · `Zp.teichmuller_pow_pred_trunc` — `ω(x)^(p−1) ≡ 1` for units
    (`(p−1)`-th root of unity); `Zp.teichmullerCofactor` +
    `Zp.teichmullerCofactor_trunc_one` — the principal-unit split
    `x = ω·u`, `u ≡ 1 mod p`, i.e. `ℤ_p^× ≃ μ_{p−1} × (1+p·ℤ_p)`
    (`Padic.TeichmullerUnit`).
  · `Zp.teichmuller_unique` (`Padic.Teichmuller`) — Teichmüller
    uniqueness: two Frobenius-fixed lifts agreeing mod `p` agree at
    every truncation (engine: `frobenius_lift` + the fix, no Hensel
    derivative).  `Zp.unit_decomp_unique_equiv` (`Padic.TeichmullerUnit`)
    — the `ω·u` decomposition is unique in the **canonical 213 equality**
    `ZpSeqEquiv`, via the funext-free bridge `ZpSeqEquiv.of_trunc_all`
    (`SetoidFramework`).  Raw Lean `=` on `ZpSeq` is a Lens artifact
    (needs funext); `ZpSeqEquiv` is the equality the residue carries.

Follow-on (direction G): general p-adic division, all PURE:

  · `Zp.shiftRight` + `Zp.shiftLeft_shiftRight_digit_of_low_zero`
    (`Padic.Arith`) — the unit-part extractor and factorisation
    exactness `x = p^v·u` (bottom-v digits zero).
  · `QpSeq.invGeneral` / `QpSeq.divGeneral` (`Padic.Field`) — inverse
    and division for a denominator of arbitrary valuation, via the
    valuation shift; `QpSeq.invGeneral_unit_eq_inv` reduces them to the
    unit-only `QpSeq.inv` at `v=0`.  Correctness `Zp.div_general_value`:
    `y · u⁻¹ ≡ p^v` at every truncation (the numerator side of
    `y · (1/y) ≡ 1` in ℚ_p, the `p^v` matched by the shift `p^(−v)`).
  · `Zp.neg_one_sq_trunc` (`Padic.Arith`) — `(−1)·(−1) ≡ 1` at every
    level (the missing ring identity for `−1`); `Zp.i_5_pow_four_trunc`
    (`Padic.TeichmullerUnit`) — `i₅⁴ ≡ 1` at every level, the concrete
    5-adic imaginary unit is a 4-th root of unity (`i₅ ∈ μ₄`), the
    explicit `p=5` instance of the μ_{p−1} result.
  · `Zp.shiftLeft_shiftRight_trunc_of_low_zero` (`Padic.Arith`) —
    factorisation exactness `x = p^v·u` at every truncation level (the
    structural engine of general division).

Chapter: `theory/math/numbersystems/padic_real213.md`.

**2026-05-09 (later, marathon batch 1)**: User directive "seal
없애버리고 다 213 native로" — emptied SEALED_DIRTY_PREFIXES.  Full
scan post-seal-empty: **2491 PURE / 164 DIRTY / 0 sealed**.

After batch 1-10 fixes (27 theorems converted): **2519 PURE / 137
DIRTY / 0 sealed**.

**Lens-equality refactor marathon (continuation)**:
Continuation of marathon under "Lens equality 재정의 strategy"
directive.  Phase 1 + Phase 2 complete with eqPW infrastructure:

Phase 1 — Infrastructure (`lean/E213/Lens/EqPW.lean`):
  - `Lens.eqPW L M` — pointwise Lens equality definition
  - `eqPW_refl`, `eqPW_symm`, `eqPW_trans` — equivalence
  - `eqPW_view_a`, `eqPW_view_b`, `eqPW_combine_sym_transfer`
  - `eqPW_view_of_sym` — view bridge under symmetric combine
  - `Lens.fold_slash_eqPW` — fold/slash compatibility for eqPW sym
  All ∅-axiom (PURE).

Phase 2 — Cat 1 conversions (11 PURE + 4 PURE companions + 2 partial):

PURE (was DIRTY):
  - SemanticAtom.isLensExpressible_iff_foldStructured  [Quot.sound] → ∅
  - SemanticAtom.raw_initial                          [Quot.sound] → ∅
  - Morphism.FoldStructured.fold_structured_lens_expressible      → ∅
  - Morphism.FoldStructured.lens_expressible_iff_fold_structured  → ∅
  - Lattice.IndexedJoin.iProdLens_view              [Quot.sound] → ∅
  - Lattice.IndexedJoin.iProdLens_refines_each      [Quot.sound] → ∅
  - Instances.Cauchy.pointwise_limit_match          [Quot.sound] → ∅
  - Characterisation.Core.R4_conj_unique_of_surjective [Quot.sound] → ∅
  - Compose.OnLens.lensUniversalMorphism            [Quot.sound] → ∅
  - Compose.OnLens.lensUniversalMorphism_a          [Quot.sound] → ∅
  - Compose.OnLens.lensUniversalMorphism_b          [Quot.sound] → ∅

NEW PURE eqPW companions (alongside existing DIRTY originals):
  - Compose.OnLens.lensXor_comm_eqPW
  - Compose.OnLens.lensCombineGeneric_comm_eqPW
  - Compose.OnLens.lensUniversalMorphism_slash_eqPW

Partial (Quot.sound removed but propext remains):
  - Leaves.Mod3.leavesMod3Lens_view_eq    [propext, Quot.sound] → [propext]
  - Leaves.Mod3.leaves_refines_mod3       [propext, Quot.sound] → [propext]
  - App.Simplex.block_constant_implies_aut_invariant
                                          [propext, Quot.sound] → [propext]

Patterns added to playbook:
9. Function-eq capstone (`f = g : Raw → α`) → pointwise (`∀ r, f r = g r`)
   to avoid funext.  Trivial change at the leaf, downstream consumers
   adjust.
10. Index-pointwise iProdLens — split on canonical-form cmp at the
    index level instead of going through function-level Raw.fold_slash.
11. eqPW companion pattern — for Cat 1 `L = M : Lens α` lemmas, add
    `(L).eqPW M` sibling without removing the DIRTY original; new
    consumers migrate gradually.

**Post-session scan (verified, final)**: **2654 PURE / 129 DIRTY** (2783 total).
(Mid-session checkpoint: 2644/133 — continuation batch +10 PURE, -4 DIRTY.)

DIRTY breakdown (cumulative session):
  - 54  [propext]                              (was 50 at session start)
  - 46  [propext, Quot.sound]                  (was 50)
  - 18  [Quot.sound]                           (was 33 — **−15** from Cat 1 work)
  - 9   [propext, Classical.choice, Quot.sound] (Lean.Elab plumbing)
  - 2   [propext, Quot.sound] (split format)

The `[Quot.sound]`-only category dropped 33 → 18 (−15, ~45% reduction) —
direct hit of the Lens-equality refactor.

**Continuation batch**: more PURE wins via the eqPW-companion + typeclass-
bypass patterns:
  - `Compose.OnLens.universalMorphismLevelTwo`             [Quot.sound] → ∅
  - `Compose.OnLens.universalMorphismLevelThree`           [Quot.sound] → ∅
  - `Lens.Instances.FunctionSpace.funUniversalMorphism`    [Quot.sound] → ∅
  - `Lens.Instances.FunctionSpace.boolFunUniversal`        [Quot.sound] → ∅

New PURE eqPW companions (alongside DIRTY originals):
  - `EqPW.Lens.view_unique_eqPW`              (∅-axiom view-unique companion)
  - `OnLens.lensXor_eqPW_cong`                (eqPW-congruence of lensXor)
  - `OnLens.lensCombineGeneric_eqPW_cong`     (eqPW-congruence of generic)
  - `OnLensImage.lensUniversalMorphism_factors_eqPW`     (factor PURE)
  - `OnLensImage.lensUniversalMorphism_image_eqPW`       (image PURE)
  - `OnLensImageGeneric.lensUniversalMorphism_factors_generic_eqPW`
  - `Lattice.IndexedJoin.iProdLens_is_greatest_pw`        (per-index PURE)

DIRTY breakdown:
  - 54  [propext]                                     (was 50)
  - 46  [propext, Quot.sound]                         (was 50)
  - 22  [Quot.sound]                                  (was 33 — **Cat 1 hit**)
  - 9   [propext, Classical.choice, Quot.sound]       (was 9 — Lean.Elab plumbing)
  - 2   [propext, Quot.sound] (split format)          (was 2)

The `[Quot.sound]`-only column dropping 33 → 22 (-11) is the
direct Cat 1 conversion signal — those were genuine "Lens equality
via funext on combine" leaks, exactly the refactor's target.

The remaining DIRTY split:
  - Inherent Prop-codomain (`Raw → Prop` from `universalLens`):
    [propext, Quot.sound] — universalLens / FamilyJoinEquiv / Lattice.Join
  - Inherent Lens-eq-on-Bool (Cat 1 with no eqPW migration yet):
    [Quot.sound] — lensBoolHasDistinguishing chain, Tower levels
  - Inherent simp-from-omega: [propext] — Mod3, Cauchy, etc.
  - Heavy ring polynomial: [propext, Quot.sound] — CayleyHeavy, Sedenion
  - Lean.Elab plumbing: [propext, Classical.choice, Quot.sound] —
    NativeGuard, DepthJoin (uses Classical.choice indirectly)

Patterns established (8 reusable):
1. omega → Nat.le_trans + Nat.le_add_right + Nat.add_le_add
2. cases h (impossible Nat eq) → absurd h (by decide)
3. injEq.mp .2 → congrArg <projector>
4. cmp_eq_iff.mp → cmp_eq_to_eq (existing direct lemma)
5. simp [...] → show <expanded> + rw [explicit lemma] / absurd
6. Iff lemma cascade → direct .mp/.mpr lemmas (cmp_gt_to_lt_swap etc.)
7. simp only [def, h] → show <unfolded match form>; rw [h]
8. inline 213-native max_comm via case-split (avoid Nat.max_comm propext)

Cascade fix found: Raw.swap_slash → Lens.Swap (5 fixes from 1 source).

After batch 1-5 fixes: 2507 PURE / 148 DIRTY.

Earlier batch 1 fixes (5 theorems):

Modules now PURE:
- E213.Lens.Properties.Leaf (was 2 dirty)
- E213.Lens.Diagonal (was 1 dirty)
- E213.Lib.Math.Algebra.CayleyDickson.LipschitzLens (was 1 dirty)
- E213.Lens.Instances.RawAChar (was 1 dirty)
- E213.Lens.Instances.SumNotCoproduct (was 1 dirty)
- E213.Lens.Instances.SumNotCoproductGeneric (was 1 dirty)
- E213.Lens.Instances.CompoundBool (was 4 dirty)
- E213.Lens.Instances.Sum (was 3 dirty)
- E213.Lens.Properties.Characterisation.Core (was 3 dirty, now 1 — funext only)

Patterns established (5 reusable):
1. omega → Nat.le_trans + Nat.le_add_right + Nat.add_le_add
2. cases h (impossible Nat eq) → absurd h (by decide)
3. injEq.mp .2 → congrArg <projector>
4. cmp_eq_iff.mp → cmp_eq_to_eq (existing direct lemma)
5. simp [...] → show <expanded> + rw [explicit lemma] / absurd

Earlier batch 1 fixes (5 theorems converted): **2496 PURE / 159
DIRTY / 0 sealed**.  Patterns established:
- `omega` → `Nat.le_trans` + `Nat.le_add_right` + `Nat.add_le_add`
- `cases h` (impossible Nat eq) → `absurd h (by decide)`
- `injEq.mp` → `congrArg <projector>`
- `Tree.cmp_eq_iff.mp` → `Tree.cmp_eq_to_eq` (∅-axiom direct lemma)
- `simp [this]` (using Iff hypothesis) → `decide_eq_true` direct

Files now PURE (was DIRTY):
- E213.Lens.Properties.Leaf (was 2 dirty)
- E213.Lens.Diagonal (was 1 dirty)
- E213.Lib.Math.Algebra.CayleyDickson.LipschitzLens (was 1 dirty)
- E213.Lens.Instances.RawAChar (was 1 dirty)

**Remaining marathon**: 159 items.  Categorization:
  62  [propext]                          — most tractable
  55  [propext, Quot.sound]              — Lens funext typically
  31  [Quot.sound]                       — funext usage
   9  [propext, Classical.choice, Quot.sound]  — Lean.Elab plumbing
   2  [propext, Quot.sound] (split format)

Top remaining DIRTY modules:
  25  E213.Lens.SemanticAtom (Prop-level "atom of meaning")
  14  E213.Lens.Compose.OnLens (Lens funext-by-design)
  10  E213.Lens.Instances.Leaves.DepthJoin (JoinEquiv on Raw + Classical)
  10  E213.Lens.Properties.Morphism.BoolProp
   6  Lens.Instances.Reach, Lens.Lattice.IndexedJoin, Lib.Math.
       CayleyDickson.CayleyHeavy

**Hard categories requiring structural refactor**:
- Lens equality redefinition (avoid funext): ~90 items
- Math.Infinity Iff/Cantor proofs: ~5 items
- Heavy ring polynomials (CayleyHeavy etc.): ~15 items
- Lean.Elab Tactic plumbing: 9 items

**2026-05-09** (post-Möbius-extension session, pre-merge audit):
seal list updated to use single-`Lens.*` prefixes (was `Lens.Lens.*`
— stale from earlier nesting).  Tree-wide scan after seal-list fix
reports **2491 PURE / 75 DIRTY + 89 sealed-DIRTY-by-design** (2655
total).  Real DIRTY breakdown: 32 [propext, Quot.sound] + 32
[propext] + 7 [propext, Classical.choice, Quot.sound] +
2 [Quot.sound] + 2 [propext, Quot.sound] (split format).

The 75 real DIRTY items are **pre-existing** from before the
Möbius-extension session.  All 102 ∅-axiom theorems newly added
in `Theory/Nat213/` + `Theory/Tower/` + `Lib/Math/Foundations/UniverseChain/
MobiusChain.lean` are PURE.

Topical breakdown of remaining DIRTY:
- Lens.Leaves.DepthJoin (10): JoinEquiv-on-Raw uses Classical.choice
- Lens.Morphism.BoolProp (10): BoolProp morphisms via propext
- Lib.Math.CayleyDickson.CayleyHeavy (6): heavy ring polynomial
  identities via simp
- Lens.Universal.QuotLens (5): Lens funext-by-design
- Lib.Math.CayleyDickson.ZOmegaDomain (5): ring axioms via simp
- Lens.Instances.Swap, Sum, CompoundBool (3-4 each): Lens patterns
- Misc Lens + Math files (1-3 each): scattered residuals

These need separate marathons; many would seal under expanded
"Lens funext-by-design" or "heavy polynomial identity" categories,
but proper triage requires per-theorem inspection.

**2026-05-05** (post-AXIOM.md §9.1 rename audit pass): tree-wide
scan reports approximately **541 PURE / 18 DIRTY / 14 sealed-DIRTY-
by-design** (573 total counted).  Real DIRTY breakdown: 10 [propext]
+ 7 [propext, Quot.sound] + 1 [propext, Classical.choice, Quot.sound]
(NativeGuard internal; Classical.choice via Lean.Elab API, sealed
upstream).  Compared to pre-rename 2026-05-04 baseline (511/14/22),
the rename caused +30 PURE (newly counted), +4 DIRTY (newly counted
pre-existing items), -8 sealed (entries reclassified after seal-list
update for `Meta.SelfRecognising` + `DeriveConjugationCodomain` +
`VerifyConjugation`).  No new actual axiom dependencies were
introduced by the rename.

**Earlier session 27 milestone (2026-05-03)**: scan reported **2077
PURE / 0 real DIRTY / 19 sealed**.  The 2077 count reflected a more
permissive scanner regex catching additional ★-marked theorems
across the Real213 marathon.  Cumulative arc 394 → 0 real DIRTY
across sessions 19-27 via Plan 2 parallel-struct refactor PLUS
deletion of ALL function-eq facade + consumer migration to `_at`
pointwise form.

**Genuine final state** (no cheat seal):
  - The function-eq facade across Phase capstones, Flux*/FTC*
    capstones, ClassicCalc/Passthrough/HasDyadicMVTWitness struct
    families, and leaf cut lemmas (CutMulOne/SumZero/PowConst/MidSelf)
    has been **completely deleted**.  All ~25 consumer files
    migrated to use only `_at` pointwise variants.
  - Function-eq cut equality on `Nat → Nat → Bool` would require
    funext = Quot.sound — but it's no longer needed: every theorem
    is now stated and proved pointwise.
  - The 6 propext-bearing residuals (CubeDerivativeAtZero × 3,
    PolySumDerivativeModulus × 3) refactored using
    cutSumAux_congr / cutMulOuter_congr cascades + manual Nat
    arithmetic avoiding `omega`/`Nat.max_eq_left`.

**The 19 sealed items** are mathematically inherent (NOT facade):
  - Lean-core boundary: Nat.lcm/gcd/add_mod/Int from kernel use
    propext via well-founded recursion proofs (8 modules).
  - Lens funext-by-design: higher-order Lens equality requires
    funext on the combine field — restating it would redefine what
    Lens IS (~18 modules under SEALED_DIRTY_PREFIXES).
  - SemanticAtom: Iff/propAsDistinguishing inherently uses propext
    (the "atom of meaning" thesis).
  - Math.Infinity.Godel: Cantor-style countability/equipotence
    proofs use Iff between cardinality propositions.
  - DyadicTrajectory: Cauchy-limit structural inequality preserved by
    ∅-axiom regime.
  - Bridges: intentional axiom-demonstration cluster.

**This is the canonical 213 axiom standard** (formalized 2026-05-02,
CLAUDE.md `## Strict ∅-axiom standard`).  The 213 axiom set is ∅.

A theorem in `lean/E213/` meets the standard iff `#print axioms`
returns:
> "does not depend on any axioms"

Equivalently: no `propext`, no `Quot.sound`, no `Classical.choice`,
no `native_decide`, no `sorryAx`.

This file maintains the running catalog of theorems that meet the
standard.  Theorems still on the migration backlog
(carrying `[propext, Quot.sound]` from `omega` / `funext` / etc.) are
listed in CLAUDE.md `## Strict ∅-axiom standard → Migration backlog`.

Verification: `python3 tools/scan_axioms.py <module>` — every
theorem reports `[PURE]` (meets the standard) or `[DIRTY]` with
the exact axiom dependency listed.

## Top-level achievements (all STRICT 0-AXIOM)

| theorem | content |
|---|---|
| `pure_atomic_observables_capstone` | 17-conjunct atomic ratios |
| `invAlphaEm_precision_theorem` | 0.2 ppb 1/α_em structural precision |
| `alpha_em_so10_capstone` | SO(10) tail correction |
| `alpha_em_gram_capstone` | Gram self-energy correction |
| `tower_native_completeness_program` | completability = two-growth-axes comparison: boundary (`CrossDetOvertake`, 10/0), Liouville `W=d` free modulus (`LiouvilleModulus`, 13/0), finite-coordinate closure under `×`/exponent (`DepthClosure`, 16/0), coordinate generator (`DepthCoordGenerator`, 10/0), residue tie (`DepthCeilingResidue`).  Narrative `theory/math/analysis/tower_native_completeness.md` |

## STRICT 0-AXIOM additions from Phase 5 batch 1+2 (2026-05-01)

Batch 1 (commit 08b02e1, omega→decide on trivial bounds):

| theorem | content |
|---|---|
| `pellFSMmod3_has_degree2` | Pell-mod-3 has algebraic degree ≤ 2 |
| `tribFSMmod2_has_degree3` | Tribonacci-mod-2 has algebraic degree ≤ 3 |
| `pisano_crt_framework_complete` | full Pisano CRT framework (was strict 0 already, retained) |

Batch 2 (commit 1cc9667, omega→Nat-lemma in BitFSM core):

| theorem | content |
|---|---|
| `fsmJointAt` | joint state encoding for BitFSM signature trajectory |
| `jointState`  | joint state encoding (general, ForwardPeriodicity) |
| `bs_periodic_multiple` | bs(n+kp)=bs(n) at multiples of period |

(Sample — full list grows as we audit downstream theorems whose
last-mile dependency was a trivial `by omega` decidable bound.)

## Number theory generals (STRICT 0-AXIOM after omega→Nat.succ_add)

| theorem | content |
|---|---|
| `ArithFSM2.run_period_of_init` | universal Pisano period theorem |
| `ArithFSM2.bits_period_of_init` | universal bits period |
| `ArithFSM3.run_period_of_init` | cubic-class universal period |
| `signature_period_of_bits_period_and_anchor` | universal sig period (TIGHT) |
| `pellFSMmod{11,19,31,47,59}_signature_period_X` | TIGHT sig instances (5×) |
| `pellFSMmod{3,5}_signature_period_X` | TIGHT sig instances (2×) |
| `tribFSMmod{3,5,19,29,31}_bits_period_X` | Tribonacci doubling bits |
| `pellFSMmod47_bits_period_48` | triple-anchor reshape via rfl |

## Pisano predictor + Legendre (STRICT 0-AXIOM after obtain→.proj)

| theorem | content |
|---|---|
| `legendre213` | 213-native Legendre symbol (definition) |
| `pisano_predict` / `_correct` | Pell-5 predictor base |
| `pisano_predict_realises_pell` | 4-prime Pell match |
| `pisano_predict_correct_6` / `_realises_pell_6` | 6-prime Pell |
| `pisano_predict_realises_pell_7` | 7-prime Pell |
| `pisano_predict_realises_pell_8` | 8-prime Pell |
| `pisano_predict_realises_pell_11` | 11-prime Pell |
| `pisano_predict_realises_pell_14` | 14-prime Pell |
| `pisano_predict_realises_pell_17` | 17-prime Pell |
| `signature_predict_realises_pell_7` | 7-prime signature |
| `two_layer_predictor_capstone` | Bit + sig layers bundled |
| `fib_pisano_predict_realises_8` | 8-prime Fibonacci |
| `legendre_5_mod_X` (X=13..89) | 14 Legendre symbols |
| `pellProper_8prime_capstone` | Pell-proper 8-prime |
| `three_family_pisano_capstone` | 3-family Galois capstone |
| `pellProper{3,5,7}_run_period_*` | 3 PellProper TIGHT |
| `pellProper{11,13,17,19,23}_bits_period_*` | 5 PellProper bits |

## Atomic identities (all STRICT 0-AXIOM via decide)

  - All Famous Coincidences (I-IV)
  - All Magic Numbers atomic
  - Per-prime Pisano (Pell, Pell-proper, Fibonacci, Tribonacci)
  - All atomic structural identities (NS·NT=6, d²-1=24, etc.)

## Significance

STRICT 0-AXIOM is the **absolute best** epistemic position in
Lean.  These theorems are checked by Lean's kernel WITHOUT any
axiom dependence — purely definitional.

External reviewers cannot challenge these via "what if propext
is wrong" since propext is not used.

## omega → propext lesson

Lean's `omega` tactic typically introduces propext + Quot.sound
dependencies.  Replacing omega with explicit kernel-level Nat
lemmas (Nat.succ_add, Nat.zero_add, etc.) UPGRADES proofs to
STRICT 0-AXIOM.

Example (commit 304723f):
  Before: `have : k+1+N = (k+N)+1 := by omega`  → propext dep
  After:  `rw [Nat.succ_add k N]`  → STRICT 0-AXIOM

## omega → decide lesson (Phase 5 batch 1, commit 08b02e1)

For `by omega` calls used purely for **decidable bounds on literals**
(e.g. `(by omega : 0 < 3)` or `(by omega : 1 < 5)`), `by decide`
is a strict 0-axiom drop-in.  In Phase 5 batch 1, 111 such
omega calls across 19 files in `Math/Cohomology/Dyadic/`
were converted, with the following measured upgrades:

  - `pellFSMmod3_has_degree2` : [propext, Quot.sound] → STRICT 0
  - `tribFSMmod2_has_degree3` : [propext, Quot.sound] → STRICT 0
  - `number_theory_213_capstone` (v1) : [propext, Quot.sound] → [propext]
  - `number_theory_213_capstone_v2`    : [propext, Quot.sound] → [propext]
  - `number_theory_213_capstone_v3`    : already [propext]
  - `pell_crt_capstone`, `pell_crt_fsm_capstone` : [propext] (kept)
  - `pisano_crt_framework_complete`   : STRICT 0 (kept)
  - `pellLens_3x5_period_20` (etc.)   : [propext] (kept)

The Quot.sound was being dragged in by inner `omega` calls in the
HasDegree witnesses (`⟨n, by omega, m, fun _ => rfl⟩`) — pure decidable
positivity that `decide` handles strictly axiom-free.  Capstones
dropping Quot.sound is a **genuine epistemic upgrade** at the trust
contract level: anything ≤ {propext, Quot.sound} is DRLT-allowed,
but the strict-0 standard rejects Quot.sound — so v1 and v2 now
qualify for the broader-still "no quotient axiom" tier.

## Audit command

```
cat > /tmp/axcheck.lean << END
import <module>
#print axioms <theorem>
END
cd lean && lake env lean /tmp/axcheck.lean
```

If output is "does not depend on any axioms", STRICT 0-AXIOM.

## Future cleanup

Many theorems at ≤ {propext, Quot.sound} could be upgraded by:
  1. Replacing omega with kernel-level lemmas
  2. Replacing simp[...] (uses propext) with rw
  3. Avoiding funext (uses Quot.sound) when not needed

Estimated upgrades: ~50-100 theorems possible.

### Tier 5.1 CLEARED — `Lib/Math/Algebra/GRA/` (Marathon 16, 2026-05-28)

`E213.Lib.Math.Algebra.GRA.*` — 22 files (umbrella + Common + 7 Phases 1–6 +
5 Phases 7–11 + 1 unified `Enrichment` + 3 Phases 12–15
support (Naturality + SectionRetraction + Monoidal) + 1 each
from Phases 16–18 + 1 unified `HasDistinguishing213` for
Phases 19–21 + Phase 22),
~3500 lines, **all PURE / 0 DIRTY** (verified by `tools/scan_axioms.py`
plus direct `#print axioms` for the multi-namespace `HigherAlgebra.lean`
that the scanner's last-namespace heuristic mis-attributes).

Upgrade pattern applied throughout:
  · `Nat.gcd 2 3 = 1` (DIRTY [propext] via well-founded
    recursion) → switch `GRAModel.ax_coprime` to
    `E213.Tactic.NatHelper.gcd213 gen1 gen2 = 1`, which kernel-
    reduces to `rfl` for the (2, 3) instance.
  · `*_grade_oplus` / `*_grade_otimes` / `*_greedy` `by simp [...]`
    → `rfl` or `Nat.le.refl` (the definitions are kernel-equal
    to the goals).
  · `nt_reach` and the 5 Reading variants `by omega` per literal
    case → shared PURE `Common.reach_23`, which uses strong
    recursion + a 2-step lemma `reach_step` proving
    `(k+2 = 2a + 3b) → ((k+2)+2 = 2(a+1) + 3b)` via explicit
    `Nat.mul_succ` / `Nat.add_assoc` / `Nat.add_comm`.
  · `*_depth_eq` `by_cases ... omega` → shared PURE
    `Common.depth_formula`, which splits on `n % 3 ∈ {0,1,2}`
    via `cases_lt_three` and the helper lemmas
    `div3_3k_{1,2,3,4}` (inductive PURE divisor identities)
    plus `Meta.Nat.AddMod213.div_add_mod`.
  · `universal_depth_comparison` `by omega` → shared PURE
    `Common.ceil3_le_ceil2`, proved by 6-step strong induction
    over the LCM(2,3) cycle with `Meta.Nat.NatDiv213.add_div_right_pos`.
  · `transport_depth_bound` / `master_translation*` /
    `reach_translation` `simp [...]` → explicit `exact` with
    typed witnesses.
  · `depth_times_3_lower` `by omega` → explicit cancellation
    via `Meta.Nat.AddMod213.div_add_mod` +
    `NatHelper.le_of_add_le_add_left`.

Shared helpers added in `lean/E213/Lib/Math/Algebra/GRA/Common.lean`
(7 public PURE theorems): `coprime_2_3`, `two_lt_three`,
`reach_offset`, `reach_23`, `depth_formula`, `greedy_form`,
`ceil3_le_ceil2`.

Phases 7–11 (category theory + enrichment, all PURE):

  · `Category.lean` (9 PURE): 213-native `Cat` typeclass
    (universe-polymorphic), `GRACat`, `ReadingCat`,
    connectedness witness.
  · `Groupoid.lean` (10 PURE): `Groupoid` typeclass on top of
    `Cat`; pointwise `HEq`-form of identity (carrier types are
    syntactically distinct but defeq Nat, so `HEq` is the natural
    form); `ConnectedHub` structure; `Reading.hubAtNT` witness.
  · `Hom.lean` (10 PURE): `GRAHom` (data-preserving, not
    necessarily invertible); `id`/`comp` category laws; forgetful
    `GRAIso → GRAHom`; grade-agreement and grade-oplus-via-hom
    theorems.
  · `DepthFunctor.lean` (9 PURE): depth as constant functor on
    the (2, 3)-sub-category; `Reading_depth_const` shows all 6
    Readings agree on `⌈n/3⌉` for `n ≥ 2`.
Phases 11–15 (unified bipartite enrichment + naturality +
retraction + monoidal, all PURE):

  · `Enrichment.lean` (11 PURE): one parametric enrichment for
    all five Readings.  `BipartiteCarrier` is a `Nat` tagged with
    the bipartite constraint `n = 0 ∨ n ≥ 2` (excluding `n = 1`,
    which `gcd(2, 3) = 1` excludes from `{2a + 3b}`).
    `BipartiteCarrier.{zero, two, three}` carrier values;
    `BipartiteCarrier.combine` (additive on `n`, serving as both
    `⊕` and `⊗`).  `GRA23_Bipartite` is the enriched (2, 3)-GRA
    model; `forgetHom : GRA23_Bipartite → GRA23_NT` is the
    canonical projection.  The five domain flavours (Walk-length,
    Cochain-degree, Truncation-level, Operad-level, Resolution-
    exponent) are decompositions of one structure — the domain
    names were commentary, not mathematical content.
  · `Naturality.lean` (5 PURE): translation between enriched and
    simplified is natural with respect to the forgetful.
    `bipartite_depth_natural` + `DepthNaturality` capstone +
    `depth_naturality_witness`.  `bipartite_grade_match` and
    `bipartite_depth_match` give cross-reading translation via
    the hub.
  · `SectionRetraction.lean` (3 PURE): the forgetful has a
    section on its valid image (`n = 0 ∨ n ≥ 2`).
    `Bipartite.section` with retraction identity
    `forget ∘ section = id` and section identity
    `section ∘ forget = id`.  `BipartiteRetract` structures the
    data.
  · `Monoidal.lean` (14 PURE): `product : GRAModel → GRAModel →
    GRAModel` is the (2, 3)-monoidal product with component-wise
    `⊕` and `⊗` and additive grade.  `trivial23` is the unit
    (one-element carrier, grade ≡ 0).  `leftUnitHom` and
    `rightUnitHom` are the unit `GRAHom`s for `trivial23 ⊗ M`
    and `M ⊗ trivial23`.

Phase 16 (Lens bridge — Cat / HoTT as Readings, all PURE):

  · `LensBridge.lean` (11 PURE): the canonical Raw-level grade
    map `canonicalGradeMap := Raw.fold 2 3 (· + ·)`.
    `canonicalGradeMap_slash` uses `Nat.add_comm` PURE.  The
    bipartite enrichment grade map (`bipartiteGradeMap`) is
    *definitionally* `canonicalGradeMap`; pairwise agreement
    theorems across the five domain Readings reduce to
    `bipartite_canonical_agree` and follow by `rfl`.  Carrier-
    level realization theorems (`bipartite_realize_a`,
    `bipartite_realize_b`) show that the enriched Raw.fold
    projects to the canonical value on atoms.  Avoids
    `HasDistinguishing`-typeclass plumbing (which would bring
    `propext`); uses `Raw.fold` with literal `Nat`-arithmetic
    directly.

Phase 17 (carrier realization — closes Phase 16 open frontier,
all PURE):

  · `CarrierRealization.lean` (7 PURE): proves
    `canonical_ge_2 : ∀ r : Raw, canonicalGradeMap r ≥ 2` by
    Raw induction (atoms map to 2 or 3; slash adds two ≥-2
    values, hence ≥ 4).  This enables *direct* construction of
    `bipartiteRealize : Raw → BipartiteCarrier`, bypassing
    `Raw.fold` on the enriched type entirely.  The realization
    is `⟨canonicalGradeMap r, Or.inr (canonical_ge_2 r)⟩`, so
    the grade-projection equals `canonicalGradeMap` by `rfl`.
    Avoids the PURE `combine_sym` problem on the `Prop`-field-
    carrying enrichment (which would force structural equality
    reasoning that brings `propext`).

Phase 18 (universal property — 1-cat proxy for GRACat-as-Cat,
all PURE):

  · `Universality23.lean` (5 PURE): `canonicalGradeMap_universal`
    proves any `f : Raw → Nat` with `f Raw.a = 2`, `f Raw.b = 3`,
    and slash-additive (`f (Raw.slash x y h) = f x + f y`) equals
    `canonicalGradeMap` pointwise.  Proof is direct Raw induction,
    closes by `rfl` at atoms.  Capstones with
    `canonical_arithmetic_forced` (the parameterless forcing
    statement) and `two_atoms_slash_agree` (uniqueness of the
    (2, 3)-profile function).  `bipartiteGradeMap_forced` and
    `bipartiteRealize_grade_forced` derive the enrichment-level
    grade equations as instances of the universal property —
    making the *forced-by-arithmetic* nature explicit rather
    than relying on `rfl` by definition.  This is the
    1-categorical proxy for the "GRACat-as-Cat is a Reading"
    frontier.

Phases 19–21 (unified `HasDistinguishing213` — universe-polymorphic
typeclass, all PURE):

  · `HasDistinguishing213.lean` (23 PURE): consolidation of
    Phases 19–21's three exploratory variants
    (`HasDistinguishingU`, `HasDistinguishingW`,
    `HasDistinguishingWFull`) into a single universe-polymorphic
    typeclass `HasDistinguishing213.{u, v} α` — fields `a, b : α`,
    `combine : α → α → α`, `Equiv : α → α → Sort v` (with
    refl/symm/trans), `combine_sym` up to `Equiv`, and
    `distinct_equiv : Equiv a b → False`.  Strict case
    instantiates `Equiv := Eq` (`v = 0`); categorical case
    instantiates `Equiv := GRAIso` (`v ≥ 1`).  Two closed
    instances:
      · `liftedReadingHasDistinguishing213 :
        HasDistinguishing213.{1, 0} (ULift.{1, 0} Reading)` —
        strict case on a `Type 1` carrier via `ULift`, with
        `readingCombine r s := if r = s then r else .NT` strictly
        commutative by case-split on `r = s` (`Reading` is
        enriched with `deriving DecidableEq`).  Atoms `NT`,
        `Graph` distinguishable by `decide`.  Realises the
        strict 2-categorical universe-lifting Phase 18 named
        as open.
      · `gra23HasDistinguishing213 :
        HasDistinguishing213.{1, 1} GRA23` — categorical case
        on the (2, 3)-packaged GRA-model type, with
        `combine := gra23Combine` (monoidal product),
        `Equiv := gra23Equiv` (`GRAIso` between underlying
        models), `combine_sym := gra23Combine_sym` (the
        swap iso `(a, b) ↦ (b, a)`, grade-comm via
        `Nat.add_comm`), `distinct_equiv :=
        trivial23_gra23_not_iso_ntGRA23` (cardinality argument
        on `TrivialCarrier` subsingleton vs `Nat`'s `0 ≠ 1`,
        applied through `iso.right_inv`).
    Headline lemmas: `productSwapIso`,
    `productSwapIso_involutive`, `product_grade_sym`,
    `product_combine_sym_witness`, `trivial23_not_iso_NT`,
    plus the two instances above and existence witnesses
    (`hasDistinguishing213_GRA23_witness`,
    `hasDistinguishing213_ULiftReading_witness`).

Phase 22 (Lens.Unified × GRA capstone — Raw 연결, all PURE):

  · `LensIsoCapstone.lean` (27 PURE): the deepest 213-native
    statement of GRA's content.  `gradeLens : Lens Nat :=
    ⟨2, 3, (· + ·)⟩` is the canonical (2, 3) Lens whose
    `Lens.view r = Raw.fold 2 3 (· + ·) r = canonicalGradeMap r`
    by definitional unfolding.  `profile_view_eq_canonical`
    re-expresses Phase 18's universal property in Lens
    vocabulary: any Lens whose view obeys the (2, 3) atomic
    profile coincides pointwise with `gradeLens.view`.  By
    `Lens.Unified.lensIso_iff_kernel_eq`,
    `profile_lens_LensIso_gradeLens` proves every (2, 3)-profile
    Lens on Nat is `Lens.Unified.LensIso` to `gradeLens`.  Five
    `*Lens` defs (`walkLens` etc.) are explicit equivalence-class
    members; five `*Realize_grade_eq_lens` theorems show that
    Phase 17 realizations project to `gradeLens.view` by `rfl`.
    Master capstone `gra_lens_iso_class_capstone_holds` packages
    the universal property + 5 Reading `LensIso`s.

## Cross-reference

  - `CAPSTONE_INDEX.md` — all capstones (mixed axiom levels)
  - `LESSONS_LEARNED.md` — finitist guardrails
  - `HANDOFF.md` — current state

**2026-05-09 (later, marathon batches 1-12 continued)**: 30 theorems
converted to ∅-axiom (with some net adjustments due to new helpers).
Final scan: **2542 PURE / 144 DIRTY / 0 sealed**.

Cumulative session reduction: **164 → 144 DIRTY (12.2% reduction)**.

Additional modules PURE in batches 11-12:
- E213.Lib.Math.Foundations.Choice.Canonical (was 1 dirty)
- E213.Lens.Compose.OnLensImage (4 → 2, 2 fixes)


## Session history

Per-session running-total entries that previously lived in this
file have been removed.  The PURE/DIRTY status of any theorem is
the live `#print axioms` output:

```bash
tools/scan_axioms.py <module>            # one module
tools/scan_all_axioms.py                 # full tree scan
```

Migration patterns that recur across sessions are catalogued in
`LESSONS_LEARNED.md` (omega → decide / kernel rewrite, simp →
rw, funext avoidance via Setoid/Bundled-subtype) and detailed in
`theory/essays/methodology/pure_funext_avoidance.md`.  Git log preserves the
per-session record of conversions.
