# G17 — Theorem Pattern Audit: Raw Empirical Fingerprint

**Author:** Claude (data extraction); Mingu Jeong (methodology directive)
**Date:** 2026-05-XX (after G16, prior to any classification attempt)
**Companion files:**
  - `tools/theorem_audit.py` (extraction script)
  - `research-notes/G17_audit_raw.csv` (per-decl fingerprint, 6052 rows)
  - `research-notes/G17_audit_summary.json` (aggregated tallies)

## §0  Methodology directive

Mingu (this session):

> 한땀한땀 정리들과 증명들의 패턴을 연구하고 작성해보면서 해야하는거임.
> 무엇이 실제 패턴인가, 지금까지 작성해왔던 lean들은 어떤 식으로 기술해온
> 것이었나 등.  그 패턴과 논리가 어떤 양태를 표현한 것이었나 등.

Translation: classification must EMERGE from patient stitch-by-stitch
study of the actual proofs we've written.  What were the actual patterns?
In what way have these Lean theorems been expressed?  What aspects did
the patterns and logic express?

**Per this directive, this note records raw empirical data ONLY.**
No classification, no taxonomy, no spectrum.  Subsequent passes will
look at the data and let structure emerge from frequency, co-occurrence,
and inspection of concrete specimens.

## §1  Scope

  · 985 .lean files under `lean/E213/`
  · 6,052 declarations (theorem / def / abbrev / instance)
  · Each decl tagged with: name, namespace, kind, body length,
    statement-token counts, proof-method-token counts, infrastructure-
    token counts.

## §2  Aggregate kind distribution

```
   4624  theorem
   1365  def
     45  abbrev
     11  instance
      4  noncomputable def
      2  protected theorem
      1  lemma
```

76% of decls are `theorem`; 22% are `def`.  noncomputable count is 4.

## §3  Top namespaces (by decl count)

```
   1387  E213.Math.Cohomology
    835  E213.Math.Real213
    490  E213.Hypervisor.Lens
    305  E213.Physics.AtomicCorrespondences
    274  E213.Physics.Atomic
    224  E213.Math.CayleyDickson
    148  E213.Physics.Couplings
    144  E213.Physics.Foundations
    131  E213.Physics.AlphaEM
    125  FluxCut
    120  E213.Math.Cauchy
    117  E213.Physics.Library
    108  E213.Physics.Substrate
     85  E213.Physics.Hadron
     80  E213.Kernel.Cap
```

Top three: Cohomology > Real213 > Lens.  Math/Physics roughly even
in cumulative count.

## §4  Body size distribution

```
       0–100   chars : 1793  (30%)
     100–500   chars : 3456  (57%)
     500–2000  chars :  752  (12%)
    2000–10000 chars :   51  (0.8%)
```

87% of decls are ≤500 chars.  Only 51 are >2000 chars (typically large
capstones and complex mass-formula derivations).

## §5  Proof-method token frequencies (top tier)

```
   3953  decide                  (occurrences across all decls)
   3132  by decide
   2219  ⟨   (anon constructor)
   1888  rw
   1520  exact
   1305  rfl
    892  intro
    691  fun
    557  cases
    515  left
    505  refine
    467  right
    330  <;>
    269  apply
    227  omega                   (← migration backlog)
    204  match
    202  simp                    (← migration backlog)
    150  absurd
    111  Or.inr
     76  rcases
     70  Or.inl
     49  constructor
      8  Classical.choose
      5  Classical.byContradiction
      4  Classical.choose_spec
      2  noncomputable
```

By decl (de-duplicated):
```
  decls using decide:         2670  (44%)
  decls using rfl:             935  (15%)
  decls using refine:          456  (7.5%)
  decls using ⟨ (anon ctor):  1105  (18%)
  decls using match:           162
  decls using cases:           287
  decls using omega:           111
  decls using simp:            130
  decls using Classical.*:       9
  decls using intro:           630
  decls using <;> + decide:    105  (refine/<;>decide capstone pattern)
```

**Classical.* decls (full list — only 9 across the whole codebase):**
all in my G7Vacuity.lean and G9ReductioVoid.lean (the deliberate
demos).  Outside those two files, Classical.* count is **zero**.

## §6  Statement-shape token frequencies

```
   9582  =                       (equality dominates)
   3766  ∧
   3349  Nat
   1930  →
   1227  ∀
    873  >
    805  Bool
    431  <
    424  Fin
    318  Type
    305  ≠
    267  ≥
    246  ∃                       (rare!)
    244  Prop
    206  ≤
```

By decl:
```
  pure equality (no ∃/∀/∧/¬):  2548  (42%)
  conjunction (∧):              959  (16%)
  existential (∃):              170  (2.8%)
  universal (∀):                708  (12%)
  negation (¬):                  91  (1.5%)
  implication (→):              855  (14%)
```

42% of decls are pure equalities (no logical connectives, no quantifiers).
Existential proofs are rare (3%); when present, anon-constructor
witness style dominates.

## §7  Infrastructure token frequencies (curated subset)

```
    819  σ                       (group/permutation/spin)
    683  binom
    489  cup
    471  Cochain
    225  parity
    131  hodgeStar
    119  half
    111  Hodge
     71  energy
     54  cocycleObstruction
     52  Nat.ble
     49  Galois
     44  fixed
     41  foldl
     39  delta0
     34  mkSpin
     32  List.range
     22  List.finRange
     22  group
     19  Frobenius
     18  Nat.beq
     14  Beilinson
     13  frustrationCount
     12  foldr
     10  delta1
     10  orbit
      9  spinAt
      2  bitOf
      1  List.any
```

σ (permutation/spin variable name) is the most-used infrastructure token.
binom and cup are the structural workhorses for cohomology calculations.

## §8  Concrete specimens per fingerprint cluster

(Spot-check examples from the CSV; no implication of taxonomy.)

### Pure rfl (small body, no other tactics)
```
  E213/Firmware/Atomicity/Alive.lean :: survives_iff_odd
  E213/Firmware/Atomicity/Alive.lean :: alive_iff_odd_pair
  E213/Firmware/Atomicity/Five.lean :: atomic_five
  E213/Firmware/Atomicity/PairForcing.lean :: count
  E213/Firmware/Atomicity/PrimitiveSizes.lean :: pairSize_nondecomposable
  E213/Firmware/Raw/CmpIndependence.lean :: RawBy
```

### `by decide` on equality
```
  E213/Hypervisor/Lens/Instances/AB.lean :: leaves_equates
  E213/Hypervisor/Lens/Instances/F9.lean :: F3, F9 (multiple)
```

### ⟨witness⟩ for ∃ + decide
```
  E213/Firmware/Atomicity/ArityForcing.lean :: reachable3_only_object
  E213/Firmware/Atomicity/ArityForcingGeneral.lean :: reachable_base_only
  E213/Hypervisor/Lens/Instances/Cauchy.lean :: cauchy_iff_eventually_class
  E213/Hypervisor/Lens/Instances/Cauchy.lean :: pointwise_limit_match
```

### `refine ⟨...⟩ <;> decide` capstones
```
  E213/Hypervisor/Lens/Leaves/RefinesParity.lean :: parityLens_view_eq_leaves_odd
  E213/Math/CayleyDickson/CDDouble.lean :: mul_generators_ne_zero
  E213/Math/Cohomology/Audit.lean :: alpha_3_two_derivations
  E213/Math/Cohomology/Dyadic/Fib/PisanoCapstone.lean :: fib_pisano_predict_correct
  E213/Math/Cohomology/Dyadic/NumberTheory213.lean :: number_theory_213_capstone_v3
```

### cases / match (case-split, no decide)
```
  E213/App/Simplex.lean :: classify
  E213/Firmware/Atomicity/ArityForcing.lean :: no_reachable_rel3
  E213/Firmware/Raw/Cmp.lean :: Tree
  E213/Firmware/Raw/CmpIndependence.lean :: Ordering_swap_swap
```

### omega (migration backlog)
```
  E213/Firmware/Atomicity/PairForcing.lean :: count_eq_one_iff
  E213/Hypervisor/Lens/Kernel/CardinalityLB.lean :: leavesModNat_kernel_neq
  E213/Hypervisor/Lens/Leaves/Mod3.lean :: leavesMod3Lens
  E213/Hypervisor/Lens/Properties/Leaf.lean :: leafLens, leafLens_view_eq
```

### Classical.* (all 9 occurrences, full list)
```
  Bridge/G7Vacuity.lean :: exists_pattern_213
  Bridge/G7Vacuity.lean :: classicalWitness  (noncomputable)
  Bridge/G7Vacuity.lean :: classicalWitness_correct
  Bridge/G7Vacuity.lean :: classicalWitness_lt_32
  Bridge/G7Vacuity.lean :: witness_213_specifically_3
  Bridge/G9ReductioVoid.lean :: exists_213_constructive
  Bridge/G9ReductioVoid.lean :: exists_classical_reductio
  Bridge/G9ReductioVoid.lean :: reductio_existence_universal
  Bridge/G9ReductioVoid.lean :: g9_capstone_pure
```

## §9  First-order observations (no classification yet)

These are the things the *raw data* shows, presented as observations
to be revisited later:

  1. The codebase is dominated by **short equalities proven by
     decide or rfl**.  ~30% are body ≤100 chars; ~57% are 100-500 chars.
  2. **Existential statements are rare** (3%); when present, they
     supply an explicit witness via anonymous constructor, not via
     `Classical.choose`.
  3. **Classical.* usage is essentially zero** (9 decls out of 6052,
     all in the deliberate G7/G9 vacuity demos).  This is empirical
     confirmation that 213 actually maintains the strict ∅-axiom
     standard outside the demonstrative files.
  4. The capstone pattern `theorem cap : a ∧ b ∧ c ∧ ... :=
     by refine ⟨?_, ?_, ?_⟩ <;> decide` is identifiable: 105 decls
     match this fingerprint.
  5. **omega and simp persist** (227 + 202 occurrences) in the
     migration backlog; the strict-∅-axiom upgrade has not yet
     fully cleaned them out.
  6. σ (sigma — permutation/spin) is the most-used variable name
     in the infrastructure, suggesting heavy use of group actions
     and permutation-based reasoning.

## §10  No classification proposed

This note deliberately stops at observations.  No spectrum, no
taxonomy, no levels.  Next pass: look at concrete decl bodies in
each fingerprint cluster, see what they *express*, and let any
structure emerge from that inspection.

The raw CSV (`G17_audit_raw.csv`) is the data; the JSON summary
is the pre-aggregation; this note is the read-out.  Anything
beyond is for a future session, after Mingu has had a chance to
look at the specimens directly.
