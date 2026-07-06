# R2 — Refutation attack on `order_invariance.md` (SPEC Q1)

**Referee**: adversarial track. **Target**: `rederive/theory/order_invariance.md`.
**Scope discipline**: read only `seed/ORIGIN_RAW.md`, `rederive/SPEC.md`,
`research-notes/drafts/independent_rederivation_program.md`, `rederive/` (the
deliverable, its Lean file `Rederive/Tree.lean`, and the enumerator). Classical
math from own knowledge. **Verdict: CONFIRMED** — the four commissioned attack
vectors all fail against the actual proof; core Q1 survives hand-recomputation
and an independent re-implementation. Three non-fatal caveats recorded in §7.

---

## 1. Attack vector A — the Persistence Lemma case analysis (Lemma 3.1)

**Attack.** Persistence (`e≠f` both enabled ⟹ `e` enabled after `f`) is the
load-bearing step; a missed case or a guard silently not preserved would sink
everything downstream.

**Finding: the case split is complete and correct.** The opening move — "if
`e,f` carry the same pair they have different kinds, and Lemma 2.4 forbids
co-enabledness, so the pairs differ" — is valid: with distinct events on the
same pair `p`, one is `link p` and the other `resolve p`, and `link p` needs
`p∉U` while `resolve p` needs `p∈U`, so they are never simultaneously enabled.
Hence `p≠q` for the two pairs, and the four kind-combinations exhaust the cases.

I recomputed **Case 2** (the only case with nontrivial content — flagged by the
author as the sole place C1/T1 bite). `e=link{x,y}`, `f=resolve{u,v}`,
`{x,y}≠{u,v}`. After `f`: `T'=T∪{pair{u,v}}`, `U'=U∖{{u,v}}`. Guards of `e`:
`x,y∈T⊆T'` ✓; `{x,y}∉U'` since `U'⊆U` and `{x,y}∉U` ✓; and the C1 guard
`pair{x,y}∉T'` needs `pair{x,y}∉T` (hypothesis) **and** `pair{x,y}≠pair{u,v}`.
The latter is exactly `Tree.pairing_inj` applied to `{x,y}≠{u,v}` — and
`pairing_inj` is machine-checked axiom-free in `Rederive/Tree.lean` (I read it:
lines 151–176, a clean `injection`-based proof with no `Classical`/`Quot`).
The other three cases preserve their guards by monotonicity of `T` and by
`U'⊆U` (link case) / set-difference on a distinct element (resolve case). **No
gap.** The attack fails.

*Note on honesty (Remark 3.2).* The document itself concedes that the "effect
unchanged" half of the informal persistence statement is true-by-construction,
because effects are modelled as fixed state-updates keyed by the event name.
This is a modelling choice, disclosed, not concealed; the substantive content
(enabledness-preservation 3.1, result-agreement 4.1) is genuinely proved.

## 2. Attack vector B — local commutation ⟹ "state = function of the event SET"

**Attack (the one the prompt flags hardest).** Going from *adjacent* co-enabled
events commuting (Diamond, Lemma 4.1) to "any two runs with the same event set
reach the same state" is the classic soft spot: it silently assumes
adjacent-transpositions connect all enumerations of the set, and that every
such transposition is at a point where the swapped pair is *co-enabled* (else
commutation doesn't apply). For runs this needs justification, and confluence
alone is not obviously enough.

**Finding: the attack misses because the proof does NOT take that route.** The
document proves set-determinacy **directly** via the explicit state formula:

> `T(E)={a,b}∪{pair p : resolve p∈E}`, `U(E)={p : link p∈E, resolve p∉E}`
> (Lemma 5.1, induction on run length), whence Theorem 5.3 is immediate.

The adjacent-transposition argument appears only in a **parenthetical** after
Theorem 5.3 ("can also be derived abstractly … by the standard permutation
argument"), explicitly demoted in favour of the formula. So the entire attack
surface — is the transposition chain valid for runs? are the swapped pairs
always co-enabled? — is **irrelevant to the actual proof**. This is the
document's strongest design decision: it routes around the very gap the attack
targets.

I re-verified the crux (Lemma 5.1) line by line. Both inductive cases
(`link p`, `resolve p`) correctly recompute `T(E∪{e})` and `U(E∪{e})` from the
guards; the `link` case's "`pair p∉T(E) ⟹ resolve p∉E`" step is a direct
contrapositive of the definition of `T(E)` needing **no** injectivity (as
claimed), while the *reachable-states-are-a-bijection* direction (Cor 5.8) does
use T1 — correctly separated. **No gap.**

**Independent recomputation (3-event reordering, by hand + code).** From the
forced opening `link{a,b}, resolve{a,b}` (state `T={a,b,c}`, `c=(ab)`, `U=∅`),
take the event set `S={link{a,c}, resolve{a,c}, link{b,c}}` with the single
induced dependency `link{a,c}≺resolve{a,c}` (g1). Its three valid linear
extensions:

| order | final state |
|---|---|
| `link{a,c}, resolve{a,c}, link{b,c}` | `T={a,b,c,d}, U={{b,c}}` |
| `link{a,c}, link{b,c}, resolve{a,c}` | `T={a,b,c,d}, U={{b,c}}` |
| `link{b,c}, link{a,c}, resolve{a,c}` | `T={a,b,c,d}, U={{b,c}}` |

with `d=(a(ab))`. All three agree, and match the formula on the full set
`E={link{a,b},resolve{a,b},link{a,c},resolve{a,c},link{b,c}}`:
`T(E)={a,b}∪{pair{a,b}=c, pair{a,c}=d}={a,b,c,d}`,
`U(E)={ab,ac,bc}∖{ab,ac}={bc}`. ✓. The *invalid* ordering (`resolve{a,c}`
before `link{a,c}`) is not a run — `resolve{a,c}` needs `{a,c}∈U=∅` — so the
"same set, different state" pathology cannot arise. I confirmed all of this
with an independent re-implementation (`enabled/effect` re-coded from scratch,
not the shipped enumerator): `o1==o2==o3` True, invalid ordering rejected.

## 3. Attack vector C — ω-fairness, weak vs strong, limit well-definedness, choice

**Attack.** (a) Is *weak* fairness enough, or is a completeness gap hiding that
needs strong fairness? (b) Is the limit well-defined without AC?

**Finding (a): weak fairness is provably sufficient, and the proof is sound.**
Theorem 6.5 (⟹) uses **stability** (Cor 3.3: once enabled, an event stays
enabled until it fires — a consequence of Persistence + no-conflict) to turn
"never executed" into "continuously enabled", i.e. a weak-fairness violation.
I checked Step 2's structural induction on `Tree` (atoms in `T₀`; composite
`pair{x,y}` handled via the three cases pair-present / linked / neither, each
reducing to Step 1) — it closes. Remark 6.9's collapse "weak = strong here"
is correct: with no conflict, "enabled infinitely often" and "enabled
continuously from some point" coincide. The document also correctly insists
fairness be indexed **per-event, not per-kind**, with a counterexample
(infinitely many links fire yet one specific link starves) — this is the
subtle trap and it is handled. **No gap.**

**Finding (b): the main results are choice-free; one peripheral claim is not.**
Existence of maximal runs (Cor 6.4) and Fairness⟺Completeness (Thm 6.5) and the
common limit (Thm 6.7) all operate on `E_all`, which is *explicitly* enumerable
(`Tree` injects into finite words; `≤_D` is decidable via finite principal
downsets), so Lemma 6.3's surjection `ν:ℕ→E_all` is constructive — no AC. The
limit `T∞=⋃T_k` is a monotone union (well-defined); `U∞` is a pointwise limit,
each `p`'s membership eventually constant (enters once at `link p`, leaves once
at `resolve p`). Well-defined. The **only** soft spot is **Proposition 6.8 (⊇)**:
"every infinite downset `F` of `D` is the executed set of some infinite run",
which applies Lemma 6.3 to an *arbitrary* order ideal `F`. A general downset of
`D` need not be decidable (there are uncountably many order ideals of a
countable poset), so producing the surjection `ℕ→F` is not choice-free for
arbitrary `F` — contradicting §11's blanket "all proofs constructive except as
noted". The *result* is classically true (`F⊆E_all` countable ⟹ enumerable);
only the constructivity claim overreaches, and Prop 6.8 is peripheral to Q1
(the Q1 headline needs only maximal runs = all of `E_all`, fully explicit).
**Caveat, not refutation** (§7.1).

## 4. Attack vector D — is `D` defined independently of the invariance theorem? (circularity)

**Attack.** If `D` were defined *as* "the order shared by all runs", then
Theorem 7.3 (`⋂<_ρ = <_D`) would be a tautology and the causal order would be
smuggled from the conclusion.

**Finding: no circularity.** Definition 5.4 fixes `≺` **purely combinatorially**
on the alphabet, before any mention of runs:

- (g1) `link p ≺ resolve p`;
- (g2) `resolve q ≺ link p` whenever `pair q ∈ p`.

These reference only the event alphabet and the tree-subterm relation — not
runs, not executed sets, not the invariance theorem. `≤_D` is its
reflexive-transitive closure; Proposition 5.5 proves it a partial order via an
**independent** rank `φ(link p)=2|p|`, `φ(resolve p)=2|p|+1` (I re-verified g2
strictly increases `φ`: `φ(link p)=2(|q|+1+|y|)≥2|q|+4 > 2|q|+1=φ(resolve q)`
since `|y|≥1` — correct). Theorem 5.7 then *connects* `D` to runs (executed
sets = finite downsets), and Theorem 7.3 *earns* the identification
`⋂<_ρ=<_D`. Because `D` is built first and the run-connection is proved, 7.3 is
a genuine theorem, not a definition-chasing tautology. **The attack fails.**

*Sub-check — is `D` the "right" order (missing dependencies)?* To fire
`link{x,y}` with a composite endpoint `x=pair q`, g2 forces `resolve q` first;
both composite endpoints are covered; `link p ≺ resolve p` (g1) covers the
draw-before-resolve dependency; the C1 "`pair p∉T` at link time" is enforced by
`link p <_D resolve p` + once-only, not a missing edge. No dependency is
absent.

## 5. Counterexample hunt (commissioned) — the only break requires dropping C1

I attempted to construct a genuine "same executed set, different final state"
pair of *valid runs* under the pinned system. It cannot be done, and the reason
is structural: Lemma 5.1 makes the state a *function* of the set, and
Corollary 5.2 (once-only, C1-driven) makes the executed multiset a set. The
document's own §5.5 exhibits the *only* place a counterexample lives — the
**C1-alternative** (drop `pair{x,y}∉T` from the link guard):

```
ρ  = link{a,b}, resolve{a,b}                 executed set {link{a,b}, resolve{a,b}}
ρ' = link{a,b}, resolve{a,b}, link{a,b}      executed set {link{a,b}, resolve{a,b}}
```

Same set, different `U` (`∅` vs `{{a,b}}`). I confirmed by re-implementation
that in the alternative, `link{a,b}` **is** re-enabled after `resolve{a,b}`
(guard `enabled_link_alt` returns True), so `ρ'` is a legal run there. This is
not a refutation of the deliverable — it is the deliverable's *own*
demonstration that C1 is necessary, and it is correct. Under the pinned C1
system the third step is not enabled, so no counterexample exists. **Nothing
to break here.**

## 6. Cross-check against the enumerator

The shipped enumerator (`enumerator/RESULTS.md`) exhaustively verifies, for all
runs of length ≤14 (4,674,890 transitions), that on every transition the
executed set grows by exactly the new event and `reconstruct(event_set(s))=s`,
with **zero** set-determinacy violations, plus 1000 random length-40
re-scheduling trials with zero mismatches. This is independent empirical
corroboration of Theorems 5.1/5.3, and the level-3 first-divergence witness
`((ab)(a(ab)))` (size 5, depth 3) it reports is consistent with — though not
part of — the Q1 claims. My own re-implementation reproduces the small-`k`
behaviour.

## 7. Non-fatal caveats (recommended fixes; none sink Q1)

1. **Prop 6.8(⊇) constructivity overreach.** §11's "all proofs constructive
   except as noted" is false for Proposition 6.8's converse over *arbitrary*
   infinite downsets `F` (undecidable ideals need a non-constructive
   enumeration). Fix: restrict the constructivity claim to `E_all` and to
   decidable downsets, or classify Prop 6.8(⊇) explicitly as classical.

2. **T3 (size) and T4 (countability) are prose-only.** `Rederive/Tree.lean`
   machine-checks T1 (`pairing_inj`), T2 (`pairing_ne_a/b`, `a_ne_b`) — I read
   the file — but **not** T3 or T4. Yet T3 underwrites the rank `φ` (hence
   `D` being a partial order, Prop 5.5) and T4 underwrites existence of maximal
   runs (Lemma 6.3). They are routine structural recursions, but the "carrier
   inputs already machine-checked axiom-free" phrasing should say "T1,T2 only".
   §11 already hedges ("T3,T4 are structural recursions") — tighten §1.1
   likewise to avoid overclaim.

3. **The demoted adjacent-transposition sketch (parenthetical after Thm 5.3)**
   asserts "any two enumerations of the same finite set of pairwise-commuting,
   at-most-once events are connected by adjacent transpositions" without noting
   that each transposition must occur at a state where the swapped pair is
   co-enabled. Immaterial (not load-bearing — the formula is), but if kept it
   should cite the co-enabledness precondition or be cut.

## 8. Verdict

**CONFIRMED.** Every commissioned attack vector fails against the actual proof:
persistence is complete (Case 2 rests on the machine-checked `pairing_inj`);
the local→global jump is *sidestepped* by an explicit, independently
hand-verified state formula rather than the fragile transposition argument;
weak fairness is provably sufficient via stability and the limit is
well-defined and choice-free for all Q1-relevant claims; and `D` is defined by
a purely combinatorial rule (g1,g2) prior to any run, so Theorem 7.3 is earned,
not circular. A 3-event reordering, the forced opening, and the C1-necessity
counterexample were all recomputed by hand and by an independent
re-implementation. The three caveats in §7 are overstatements of constructivity
/ mechanization scope and a dispensable parenthetical — they do not touch the
Q1 result.
