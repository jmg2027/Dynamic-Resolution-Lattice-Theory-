# G99 — rw-cascade analysis: mul_left_comm / add_left_comm adoption gap

**Date**: 2026-05-21  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Tool**: `tools/syntax_rw_cascade_scan.py` (k-gram mining over
`_syntax_arg_cites.tsv`)  
**Companion**: G98 (unfold-graph), G92 (citation graph), G91
(syntax skeletons).

---

## Question

G98 (unfold-graph) had a 17 % hit rate for new implicit-lemma
candidates and a 83 % confirmation rate for existing abstractions.
Its weakness: `unfold` is rare (4.6 % of decls) and 70 % of
unfolders are single-def.

`rw` is the dominant tactic at **17 % of all tokens** (G91), and
G91 measured 528 `rw → rw` bigrams — densely structured cascades.
Are there k-gram cascades that correspond to named composite
lemmas (= adoption gaps) or that should be lifted to one (= missing
lemmas)?

---

## Method

For each decl, extract the ordered sequence of `rw`-kind cited
lemma names from `_syntax_arg_cites.tsv` (filtering
hypothesis-shaped names: `h`, `ih`, `h1`, `this`, `rfl`,
`trivial`).  Then for k = 2, 3, 4, count k-grams by both
total occurrences and distinct-decl count.

**Population**: 1,072 decls have at least one rw cite; 3,993 total
rw cite occurrences (substantially denser than unfold's 231).

---

## Top rw 2-grams (37 decls max)

| decls | occ | cascade |
|------:|----:|---------|
| **37** | 68 | `NatHelper.mul_assoc → Nat.mul_comm` |
| 31 | 62 | `Nat.mul_comm → NatHelper.mul_assoc` |
| 24 | 33 | `Nat.add_assoc → Nat.add_comm` |
| 22 | 38 | `Nat.add_assoc → Nat.add_assoc` (self-repeat) |
| 20 | 33 | `Nat.add_comm → Nat.add_assoc` |
| 17 | 21 | `Nat.mul_add → Nat.mul_one` |
| 15 | 19 | `if_pos → if_neg` |
| 11 | 12 | `Nat.pow_succ → Nat.mul_comm` |

Pure-arithmetic bigrams dominate.

## Top rw 3-grams (25 decls max)

| decls | occ | cascade |
|------:|----:|---------|
| **25** | 48 | `NatHelper.mul_assoc → Nat.mul_comm → NatHelper.mul_assoc` |
| **18** | 27 | `Nat.add_assoc → Nat.add_comm → Nat.add_assoc` |
| 17 | 23 | `NatHelper.mul_assoc → NatHelper.mul_assoc → Nat.mul_comm` |
| 12 | 19 | `Nat.mul_comm → NatHelper.mul_assoc → NatHelper.mul_assoc` |
|  9 |  9 | `dif_pos → dif_pos → dif_neg` |
|  9 | 10 | `dif_pos → dif_neg → dif_neg` |
|  9 | 13 | `h_lhs → h_rhs1 → h_rhs2` (local-let, ignore) |
|  7 | 11 | `if_pos → if_pos → if_neg` |
|  7 | 10 | `Nat.add_comm → Nat.add_assoc → Nat.add_assoc` |
|  7 | 12 | `Nat.mul_zero → Nat.mul_zero → Nat.mul_zero` (self-repeat) |

The **`assoc → comm → assoc`** rotation pattern is the
single dominant 3-gram — manually executing the well-known
**`mul_left_comm`** identity `a * (b * c) = b * (a * c)`.

---

## ★ The key finding — adoption gap

`E213.Tactic.NatHelper.mul_left_comm` **already exists**
(`Meta/Tactic/NatHelper.lean:293`):

```lean
theorem mul_left_comm (a b c : Nat) : a * (b * c) = b * (a * c) :=
  -- term-mode proof via assoc + comm + assoc
```

A parallel `add_left_comm` lemma exists in
`Meta/Algebra213/Core.lean:107` (generic over `Ring213`) and
`Meta/Int213/Core.lean:651` (for Int).

**Yet `mul_left_comm` is cited only ONCE in the corpus**
(`Lib/Math/Mobius213.lean:232`).  The 25 decls that perform the
3-rewrite manual rotation are not using the lemma that already
encodes that exact identity.

Same shape: `add_left_comm` (18 decls × 3 rewrites manual) used
sparingly via direct cites; the 27 manual `assoc → comm → assoc`
rotations could collapse to one `rw [add_left_comm]` each.

**This is not a missing-abstraction finding — it's a
documented-abstraction-not-adopted finding.**  Different
remediation: not "add a lemma", but "redirect 43 decls' rewrite
chains to use existing named lemmas".

---

## Quantified savings

  · **mul rotations**: 25 decls × (3 → 1) cite = **50 cite-tokens saved**.
  · **add rotations**: 18 decls × (3 → 1) cite = **36 cite-tokens saved**.
  · **Total**: 43 decls, ~86 cite-tokens.

File distribution of the mul rotations:

```
   5   Real213/Sum/CutSumOne.lean
   4   Cauchy/Euler.lean
   4   Cauchy/Wallis.lean
   2   Cauchy/MonotonicBounded.lean
   2   Irrational/Sqrt2Cut.lean
   1   Analysis/DyadicSearch/DyadicBracket.lean
   1   Analysis/ResolutionShift.lean
   1   Cauchy/Archimedean.lean
   1   Cauchy/Convergent.lean
   ...
```

`CutSumOne.lean` heads the list with 5 — consistent with G94 §2
+ §7 finding that CutSumOne is a heavily-arithmetic ladder family.

File distribution of the add rotations:

```
   3   Cauchy/PellSeq.lean
   2   Meta/Int213/Core.lean
   2   Meta/Nat/EncodePair213.lean
   1   Lens/Number/Nat213/Tower/NatPairToInt.lean
   1   Cohomology/Cup/LeibnizLexListLevel.lean
   1   Cohomology/Cup/LeibnizLexStructural.lean
   1   Extras/CauchySchwarz.lean
   1   Functional/InnerProduct.lean
   ...
```

**0 decls do both mul + add rotations** — the contexts are
disjoint, suggesting the rotations are situationally specific (a
proof is either multiplicatively-heavy or additively-heavy, not
both).

---

## Other observations

### h_components × 4 pattern (5 decls)

The 30-occurrence 4-gram `h_components × 4` appears in exactly
**5 decls** — the L1 LeibnizAlgLift family + LeibnizAlgLift21:

```
  · LeibnizAlgLift.leibniz_via_β_decomp_lens
  · LeibnizAlgLift21.leibniz_via_β_decomp_21
  · LeibnizAlgLift21Alpha.leibniz_via_α_decomp_21
  · LeibnizAlgLift22.leibniz_via_β_decomp_22
  · LeibnizAlgLift22Alpha.leibniz_via_α_decomp_22
```

These are exactly the L1 ladder (G94 §1 + §8.1) + one sibling
(LeibnizAlgLift21).  The 4-fold `h_components` invocation is
the operational signature of the **4-component Leibniz
expansion**.  Already-templated; the abstraction candidate L1
(G94 §8) would absorb this naturally.

### cupAW_add × 4 / delta_cupAW_add × 4 patterns

13 decls each for `cupAW_add_right × 4` and `delta_cupAW_add_right × 4`
(left variants: 12 each).  These are 4-fold applications of the
cup-addition bilinearity lemma — likely from 4-way Leibniz
expansion at a fixed bidegree.  The bilinearity lemma is in
`Bilinear.lean` (G98 Chunk 2a), so these are confirmed
existing-abstraction usages — not new candidates.

### Conditional cascades (dif_pos / if_pos chains)

9 decls do `dif_pos → dif_pos → dif_neg` and 9 do `dif_pos →
dif_neg → dif_neg`.  These are decidable-branch chains where the
proof discharges a 3-case nested-if computation.  Not a clear
abstraction candidate — the chains depend on the specific
predicates being decided.

---

## N-action surface

  · **N8** — adopt `NatHelper.mul_left_comm` in the 25 manual-rotation
    sites.  Mechanical sed-style rewrite: replace
    `rw [NatHelper.mul_assoc, Nat.mul_comm, NatHelper.mul_assoc]`
    with `rw [NatHelper.mul_left_comm]`.  ~50 tactic-tokens saved,
    proofs more readable.  Blast radius: 8 files.

  · **N9** — adopt `add_left_comm` (NatHelper / Algebra213) in the
    18 manual-rotation sites.  Mechanical replacement.  ~36
    tactic-tokens saved.  Blast radius: 8 files.

After N8 + N9: 43 decls would cite a single rotation lemma each
instead of 3 manual rewrites.  Code becomes more readable, and
the citation-graph hub `NatHelper.mul_left_comm` / `add_left_comm`
becomes visible (currently both have 1 caller; would jump to
26 + 19 = ~45 callers).

These are not blocking, but they are the **lowest-friction
N-action** the meta-scans have surfaced — pure rewrites, no new
lemmas, no proof-content changes.

---

## Method evaluation vs G98

| dimension | G98 (unfold) | G99 (rw-cascade) |
|-----------|--------------|------------------|
| Population | 152 decls    | 1,072 decls |
| Density    | 231 occurrences | 3,993 occurrences |
| Multi-pattern signal | 5 decls ≥ 3 defs | 24+ trigrams at ≥ 5 decls |
| Hit rate (new candidates) | 17 % (1/6) | adoption-gap surface: 2 lemmas / 43 decls |
| Confirmation rate | 83 % (existing abstr) | most cascades trace to existing lemmas |

rw-cascade is **a more productive layer** for cascade discovery —
17× denser citation pattern, surfacing a different KIND of finding:
**adoption gaps** rather than missing lemmas.

The two layers are complementary:

  · `unfold`-graph surfaces **missing abstractions** (rare events
    where multi-def operational opens reveal joint algebra).
  · `rw`-cascade surfaces **adoption gaps** (frequent events
    where manual rewrite chains shadow existing named lemmas).

For pure mass-reduction, **rw-cascade adoption gaps are the
cheaper win** — no new lemmas to prove, just mechanical rewrites.
For structural discovery, **unfold-graph chunks are deeper** —
when they hit, they expose architectural gaps in the abstraction
layer.

---

## Pointers

  · Run: `python3 tools/syntax_rw_cascade_scan.py --k 3 --top 30`
  · Data: `tools/_syntax_arg_cites.tsv`
    (produced by `syntax_arg_scan.py`).
