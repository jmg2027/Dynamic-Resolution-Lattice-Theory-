# Proof-pattern census — what 213's Lean proofs actually look like (empirical)

A **code-level** pattern analysis of the Lean corpus itself (not the prose): the
empirical distribution and structure of how the 14,058 theorems are *proved*.
Complements `theory/meta/methodology_patterns.md` (human-side heuristics) and
`seed/THEOREM_METHODOLOGY_SUITE.md` §TH-3 (the decide-finitism slice) with a
broad, current, multi-axis census + the structural law it reveals.

**Status**: empirical (numbers regenerable, will drift as the corpus grows — see
§Regeneration).  Snapshot: 1980 `.lean` files, 290,007 lines, 14,058 `theorem`
(only **2** `lemma` — the corpus uses `theorem` exclusively), 4,640 `def`, 263
`instance`, 231 `structure`, 92 `inductive`.

---

## 1. The headline: proof style is the *shadow of the ∅-axiom constraint*

213 forbids Mathlib (hence no `simp`-set, no `ring`, and `omega`/`propext` are
avoided).  The proof corpus is exactly the negative image of that constraint:

| automation tactic | uses | what replaced it |
|---|---:|---|
| `simp` | 158 | explicit `rw`-chains (**12,961** `rw`) over hand-listed semiring axioms |
| `ring` (Mathlib) | 0 | **`ring_nat` (714) + `ring_intZ` (720)** — a hand-built `elab` ring |
| `omega` | 116 | `decide` (finite) / `Int.NonNeg` constructor inversion / `omega213` |
| `native_decide` | 0 | `decide` (the 4 textual hits are docstrings listing what is avoided) |

So the three pillars of the proof corpus are **`decide`** (finite computation),
**`rw`** (manual normalization), and a **hand-rolled tactic stack**:

- `Meta/Nat/PolyNatMTactic.ring_nat` — an `elab` tactic that reifies a `Nat`
  polynomial goal `lhs = rhs` and discharges it via `PolyNatM.poly_idM` (a genuine
  ∅-axiom `ring` for ℕ); `ring_intZ` is the ℤ twin (720 uses).
- domain elaborators: `omega213` (propext-free `omega`), `quad_norm` /
  `quad_extension` (Cayley-Dickson / `ZSqrt D` norms), `int_square`, `hurwitz_ring`.

**The hand-rolled `simp`-set, made concrete.**  The most-`rw`'d lemmas are exactly
the semiring axioms Mathlib's `ring`/`simp` would apply automatically:
`Nat.{add_zero, mul_one, one_mul, zero_add, mul_zero, zero_mul, add_assoc,
mul_add, pow_succ, mul_comm, add_comm}`, `mul_assoc`, `Int.{add_zero, one_mul}`,
`add_sub_cancel_right` — plus local hyps (`h`, `h1`, `h2`, `ih`, `e2`).  The corpus
re-implements normalization by hand, one axiom-`rw` at a time.

## 2. The decide-finitism fingerprint, quantified

| signature | count | share of 14,058 theorems |
|---|---:|---|
| `:= by` (tactic mode) | 13,965 | **99.3 %** (term-mode proofs are rare) |
| `decide` token (any) | 13,603 | — |
| `:= by decide` one-liner | 2,839 | 20 % |
| `:= rfl` one-liner (term) | 1,701 | 12 % |
| ⇒ literal one-line proofs | ~4,540 | **~32 %** |

Nearly a third of the corpus is a *single* `decide`/`rfl` — finite computation
certified, not a general ∀-derivation.  (Consistent with §TH-3's "~44 % decide-
routed".)  Statement shapes match: `∧` 10,781 (heavy conjunction-bundling),
`∀` 6,943, `≠` 2,228 (the distinguishing/negation signature), `∃` 1,133,
`↔` ~1,061.  Term structure inside tactic blocks: **12,844 anonymous constructors
`⟨…⟩`** (≈ one per theorem — the `∧`-bundles closed by `⟨_, _, …⟩`) and 6,767
`fun` (term-mode sub-proofs).

## 3. The structural law: proof style is a function of layer

The *same* corpus proves in dramatically different styles by architectural layer —
and the gradient mirrors the abstraction gradient (foundations prove *structure*;
physics proves *numbers*):

| layer | theorems | `by decide` | decide tok | `rw` tok | dominant style |
|---|---:|---:|---:|---:|---|
| `Theory/` (Raw axiom) | 358 | 18 (5 %) | 127 | 274 | structural / **induction on Raw** |
| `Lens/` | 851 | 71 (8 %) | 395 | 615 | structural + Lens-algebra |
| `Meta/` | 736 | 4 (0.5 %) | 116 | **1,167** | **the rewrite-algebra engine room** (builds `ring_nat`/`Int213`) |
| `Lib/Math/` | 11,192 | 2,295 (20 %) | 11,472 | 10,735 | mixed (decide + rw, the bulk) |
| `Lib/Physics/` | 864 | **478 (55 %)** | 1,486 | **125** | **decide-computation** (numeric/bracket checks) |

Reading: **Meta** is rw-heavy and almost decide-free — it is where the propext-free
arithmetic stack is *built* (so the rest of the corpus can `decide`/`ring_nat`).
**Physics** is the inverse: 55 % one-line `decide`, almost no algebraic rewriting —
its proofs are finite numeric verifications (the bracket-containment shape).
**Theory/Lens** barely `decide` — they prove *structure* by `induction … with` on
Raw.  The proof-pattern gradient *is* the abstraction gradient.

## 4. The skeleton: forward-explicit, no black-box closure

Recursor usage: explicit `.rec` = 0, written `casesOn` = 6 — raw recursors are
*never* hand-written; always structured `induction … with` (585) / `match` (378),
and Nat-induction (`| zero | succ`, 1,264) is the dominant scheme.  `Bool.casesOn`
dominates at the elaborated level (§TH-3: 1,681 invocations).

The dominant *adjacent-tactic* bigrams (global, line-leading) are the proof
skeleton:

```
have → have   4221     show → rw    2546     rw → have   1775
have → rw     2913     rw → rw      2492     rw → show   1652
                       rw → exact   2315     exact → have 1285
refine → refine 496    cases → cases 463
```

This is a **forward, explicit, rewrite-driven** style: stage intermediate facts
(`have → have`), reshape the goal to a defeq form (`show → rw` — the no-`simp`
normalization dance), run a manual rewrite chain (`rw → rw`), close (`rw → exact`).
No tactic in the skeleton is a black-box (`simp`/`ring`/`omega`/`tauto` are
absent); every step is an explicit named move.

Length is **bimodal**: 351 files < 60 lines (the one-line `decide`/`rfl` clusters)
vs 59 marathons > 500 lines, where the hardest content concentrates —
`SternBrocotMarkov` (2,797), `JsjDeep` (geometrization, 1,912), `Padic/Hensel`
(1,731), `Padic/Arith` (1,624), `MarkovUniqueness` (1,601), `CoResidue` (1,527),
`Lambert​Bridge` (1,428).  The marathons are `have→have` (Markov) or `show→rw`
(p-adic/analysis) chains; the small files are `<;> decide` / `<;> rfl` case bundles
(clustering in `Cohomology/Bipartite` and `Geometry/Geometrization`).

## 5. The insight: the proof corpus is the *proof-level* Trajectory Principle

`LESSONS_LEARNED.md` Lesson 11 (the Trajectory Principle): ∅-axiom keeps a
mathematical object's *trajectory* explicit because `propext`/`Quot.sound` are
exactly the axioms that *collapse a trajectory to its endpoint*.  The proof-pattern
census shows the **same principle one level up, at the proof scale**:

> Just as the ∅-axiom regime keeps the *object's* trajectory explicit (no quotient
> collapse), the **Mathlib-free regime keeps the *proof's* trajectory explicit** —
> `simp`/`ring`/`omega` are exactly the tactics that *collapse a derivation to a
> black-box closure*, and their suppression forces every proof to be written as an
> explicit `have → show → rw → exact` trajectory of named moves.

So the corpus's characteristic proof shape is not incidental style — it is the
proof-level shadow of the framework's own principle.  The hand-rolled tactic stack
(`ring_nat`/`ring_intZ`/`omega213`) is precisely the *re-explicitation* of the
collapses Mathlib would perform: a `ring` that one can `#print axioms` through, a
trajectory where Mathlib offers a teleported endpoint.  This is why `Meta/` is the
rw-heavy engine room (it *builds* the explicit replacements) and why automation
density falls toward the foundations and rises (as `decide`, the one *permitted*
finite collapse) toward physics.

(Genuine connection, not a slogan: the suppressed tactics are *named* —
`simp`/`ring`/`omega` — and each is a derivation-collapse; the permitted finite
collapse is `decide` (deterministic, ∅-axiom), the proof-level analogue of a
*terminating* trajectory.  Open question this opens: is there a proof-level analogue
of the µF/νF split — `decide` (terminating, µF-like) vs an *unbounded* tactic
trajectory (νF-like) that no finite `decide` closes?  The `DECIDE`-wall at König
(`theory/essays/proof_isa/konig_boundary.md`) is a candidate instance.)

## 6. Skeleton convergence + the Expr-level (elaborated) substrate

**Syntax-level skeleton convergence** (`tools/syntax_tactic_scan.py`, comment-stripped,
9,992 tactic-bodied decls — the rest are term-mode).  The proofs collapse to a *tiny*
micro-skeleton vocabulary:

| tactic-name sequence | count | share |
|---|---:|---:|
| `[decide]` | 2,980 | **30 %** |
| `[refine, decide]` | 462 | |
| `[rw]` | 337 | |
| `[show, rw]` | 229 | |
| `[rw, exact]` | 121 | |
| `[show, rw, exact]` | 96 | |
| `[show, exact]` / `[apply,rw,exact]` / `[intro,exact]` / `[have,rw,exact]` | ~265 | |

Sequence-length distribution is a steep decay off a single-tactic spike:
**len=1: 3,418 (34 %)**, len=2: 1,374, len=3: 988, … long thin marathon tail (len > 30).
Dominant (first→last) pairs: `decide→decide` 2,996, `have→exact` 692, `refine→decide`
666, `intro→exact` 568, `rw→rw` 524, `show→rw` 413.  So the answer to "how many
distinct skeletons do the proofs collapse to" is: **a handful cover the bulk** — a single
`decide` alone is ~30 %, and the top ~12 micro-skeletons dominate.

**Expr-level recursor substrate** (`catalogs/recursor-inventory.md`,
`tools/ast_callgraph_scan.py`; 185 inductive types with recursor edges).  The proofs
recurse, at the kernel level, almost entirely on **ambient logical types**, not on
domain structures:

| rank | recursor | invocations | role |
|---:|---|---:|---|
| 1 | `Bool.casesOn` | 1,681 | case-split on `decide` outputs |
| 2 | `Nat` (`brecOn`/`casesOn`/`recAux`) | 803 | arithmetic induction |
| 3 | `Eq` (`rec`/`casesOn`) | 572 | **the elaborated `rw` mechanism** |
| 4 | `Decidable.casesOn` | 562 | split on `Decidable` instances |
| 5–8 | `And`/`Exists`/`Or`/`Prod` `casesOn` | 1,202 | hypothesis destructuring |
| 10 | **`Term.Internal.Tree`** | 104 | **the Raw substrate — the *only* E213-internal type in the top 11** |

This is the decide+rw character confirmed at the kernel-recursion level: the proof
machinery is **decision (`Bool`/`Decidable`) + equality (`Eq`) + logical destructuring
(`And`/`Or`/`Exists`)** over a *thin* Raw (`Tree`) layer.  Domain richness lives in the
*statements* and the *`def` layer*, not in the proof-recursion.

**Expr complex-end** (`tools/ast_shape_scan.py`, boilerplate-filtered, 4,430 real decls):
median 112 elaborated nodes, mean 1,184 (heavy right-skew).  The structural cost
concentrates in three places: (a) the **hand-rolled tactic engine** is the *depth* peak
(`omega213` 356, `ring_nat`/`ring_intZ` reifiers, `elabDeriveConjugation` — the engine
room is literally the deepest code); (b) **foundational lemmas proved by brute structural
expansion** are *node-count* peaks (`Raw.swap_slash` 66k, `Raw.slash_comm` 32k,
`Int213.mul_assoc` 38k); (c) the **hard analysis / Cayley-Dickson tail**
(`WallisSeq.wallis_upper_inv` 102k, `QuadIdentities.int_quad_diophantus*` 52–86k,
Casoratian, Euler).  Note `decide`/`rfl` proofs store *small* terms (the decision runs at
kernel-check, not in the term) — which is precisely *why* the syntax-level `[decide]`
clusters are huge while the corpus median node-count stays modest.

## 7. The compositional backbone, and the marathon anatomy

**The citation hubs** (`catalogs/internal-hubs.md`, surface + Expr call-graph).  What the
14k proofs are built *from* — the highest-blast-radius names:

| internal hub | cites | callers | external hub | cites |
|---|---:|---:|---|---:|
| `Tactic.NatHelper.mul_assoc` | 174 | 58 | `absurd` | 177 |
| `Tactic.NatHelper.add_mul` | 45 | 27 | `Nat.mul_comm` | 165 |
| `Meta.Int213.mul_comm` | 20 | 6 | `Nat.add_assoc` | 149 |
| `Meta.Int213.{neg_mul,neg_add,add_comm,mul_neg}` | 10–14 | | `Nat.add_comm` | 145 |
| `NatHelper.add_sub_cancel_right` | 12 | 12 | `decide_eq_true` | 84 |
| `Term.Internal.Tree.noConfusion` | 7 | 5 | `Nat.one_mul` / `Nat.mul_add` | 71–82 |

5 of the top-10 internal hubs are **`NatHelper.*`** (the propext-free `Nat.*` replacement
layer), second tier **`Int213.*`**.  The external backbone is the **semiring axioms** + the
**decide bridge** (`decide_eq_true`) + **`absurd`** (the negation/`≠` closer).  This is the
*same* finding as §1 (the hand-rolled simp-set) and §6 (the Bool/Eq/Decidable recursor
substrate), now from the dependency-hub angle.

**Triple convergence (the structural conclusion).**  Three independent measurements —
the most-`rw`'d lemmas (§1), the dominant recursors (§6), the citation hubs (§7) — all name
the *same* small kernel:

> 213's 14k proofs compose from a **thin, hand-rolled, ∅-axiom-clean arithmetic + decision
> kernel** (`NatHelper`/`Int213` + the semiring axioms + `Bool`/`Eq`/`Decidable` +
> `decide_eq_true`/`absurd`), massively reused.  The mathematical richness lives in the
> **statements and the `def` layer**, *not* in the proof-recursion — the proofs are
> overwhelmingly *compute* (`decide`) and *rewrite* (`rw`/`Eq.rec`) over that kernel.

This is the structural complement to §5: not only is each proof an explicit trajectory
(no black-box tactic) — the *whole corpus* is a trajectory built on one small, explicit,
re-explicitated base (`NatHelper` is to 213 what `Mathlib.Algebra` is to a Mathlib proof,
but ∅-axiom and ~200 lemmas instead of ~10⁵).

**Marathon anatomy** (the 59 files > 500 lines — where the *hard* content lives).  Dominant
proof style, classified: **20 `rw`-dominant** (algebraic / p-adic rewrite-chains —
`Padic/Hensel` 213 rw, `Padic/Arith`), **18 `have`-dominant** (number-theory forward
reasoning — `MarkovUniqueness`, `SternBrocotMarkov`; some are def-heavy `PatternCatalog`
files), **17 `decide`-dominant** (geometry / cohomology enumeration — `Geometrization/*`,
`Cohomology/Bipartite/*`), 2 `cases`-bundle, 1 `show`.  So the hard proofs split ~evenly
into three camps **by domain** — the per-layer style law (§3) extends to the marathon tail:
algebra rewrites, number-theory chains forward, geometry/combinatorics enumerates.

---

## Regeneration (the numbers drift; the structure should not)

```sh
# decl counts
rg -c '^\s*theorem ' lean/E213 -g '*.lean' | awk -F: '{s+=$2} END{print s}'
# tactic frequencies
for t in decide rfl simp exact rw omega have show; do printf "%-8s " $t; rg -o "\b$t\b" lean/E213 -g '*.lean' | wc -l; done
# hand-rolled stack
for t in ring_nat ring_intZ omega213; do printf "%-10s " $t; rg -o "\b$t\b" lean/E213 -g '*.lean' | wc -l; done
# per-layer profile: loop layers, count theorem / ':= by decide' / decide tok / rw tok
# global tactic bigrams
rg -oN --no-filename '^\s*(rw|exact|have|show|cases|rcases|obtain|refine|apply|decide|rfl|intro|induction)\b' lean/E213 -g '*.lean' -r '$1' \
  | awk 'NR>1{print prev" -> "$0} {prev=$0}' | sort | uniq -c | sort -rn | head
```

For Expr-level shape/recursor data (deeper than text), the Lean scanners exist:
`tools/{ast_shape_scan, ast_fold_scan, ast_callgraph_scan, syntax_tactic_scan,
syntax_rw_cascade_scan}.py` (`seed/META_SCAN_ARCHETYPES.md`; require a build, TSVs
gitignored/regenerable).

## Open threads (deeper code-pattern analysis to continue)

1. **Expr-level skeleton clustering** — run `ast_shape_scan` (name-retaining; cf.
   `reflexivity_gap.md` action 2) to cluster proofs by elaborated shape, not text;
   measure how many distinct *proof skeletons* the 14k theorems collapse to.
2. **`ring_nat`/`ring_intZ` coverage** — what fraction of `rw`-chains could be
   replaced by the hand-rolled ring (the adoption-gap of methodology Pattern #10,
   measured corpus-wide)?
3. **The marathon anatomy** — a structural diff of the 59 marathon files: are they
   `have`-chains (number theory), `show→rw` (analysis), or `cases`-bundles
   (combinatorics)?  First pass: the three clusters are visible; quantify.
4. **Statement→proof law** — formalize the §3 layer-law and the ≠→decide /
   ∧→⟨⟩ / ↔→constructor correlations as a predictor of proof shape from goal shape.
