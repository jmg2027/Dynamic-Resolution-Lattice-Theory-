# R3 — Adversarial referee report on `grading_obstruction.md` §6 (Q3) and the §9 boundary

**Target**: `rederive/theory/grading_obstruction.md`, §6 (category of gradings,
Theorems 6.2–6.7) and the §9 ledger, plus the §9-of-ORIGIN_RAW "level 2"
identification carried by §1.1/§3/Remark 3.6.
**Sources consulted**: `rederive/SPEC.md`, `seed/ORIGIN_RAW.md`,
`rederive/theory/grading_obstruction.md`. No corpus files.
**Mandate**: break the claim. Verdict earned only by surviving the best attack.

**Bottom line**: the two headline claims survive — (Q3) "no number scale;
the universal grading is the causal order itself" is *not* rigged to a false
conclusion, and (§9) the level-2 boundary is *forced* by ORIGIN_RAW's own
generation counting, not retrofitted, and is *not* off by one. Every theorem
I recomputed by hand checks out (Prop 3.4 Hasse, the 6.3 incomparable pairs,
the 6.7 collision, the 5.4 reversal). But the attack lands two real defects
of *argument/presentation* that must be fixed: (D1) Theorem 6.2 is genuinely
content-free and the document's own concession is not fully cashed out; (D2)
**Remark 3.6's "exact" is argued in the wrong framing** and is literally false
as stated in that framing — the stratification provably survives *past* the
five level-≤2 objects, through the four λ=4 depth-3 combs, so the first
failure is not adjacent to the level-2 zone in the λ-order the remark invokes.
The correct exact statement is depth-framed and the document proves it but
buries it. Verdict: **confirmed**, with required fixes below.

---

## Part (a) — Tautology audit of `Grad(D)` (Def 6.1) and Theorems 6.3–6.7

### A1. Is D rigged to win?

`Grad(D)` (Def 6.1) is by construction the **coslice (under-)category** of `D`
in `Pos` (posets + monotone maps), restricted to strict objects. In *any*
coslice under an object `X`, the pair `(X, id)` is initial — this is true of
every poset whatsoever and carries zero information about `D`. So **Theorem
6.2 ("(D, id) initial") is tautological**. This is the exact hazard SPEC Q3
flags ("Q3 risks tautology; refuters must check"). The document concedes it
head-on (lines 698–705, 840–848: "On its own this is deflationary"). Concession
noted; but it must be weighed, not waved (see D1).

The live question is therefore **not** 6.2 but whether the morphism class is
rigged so that the *contentful* claims (6.3–6.7, "no canonical number scale")
come out the way the author wants. I checked three rigging vectors.

**Rig vector 1 — objects strict (G1) but morphisms only monotone (G0).**
This asymmetry is exactly what powers the non-existence proofs (6.3): a
morphism `h` into a natural labeling `(ω, ℓ₂)` need only be monotone, and
monotonicity alone yields the contradiction (a strict order in the source
chain `L₀` forced to map to a reversed order in `ω`). But this is the
**standard** `Pos` coslice, not a gerrymander — `Pos` morphisms are monotone
maps by definition. Requiring morphisms to be *strict* would be the
non-standard move, and even then the labeling-morphism argument survives
(`g₀(e) < g₀(f') ⟹ h(g₀(e)) ≤ h(g₀(f'))` is used, which strict monotone `h`
also satisfies). **Not rigged.**

**Rig vector 2 — "no terminal object" depends on G1.** Under (G0) the trivial
one-point grading is a legitimate object and becomes terminal; under (G1) it is
excluded (a strict map to a point requires `D` to have no strict relations,
false), so `Grad(D)` has no terminal object. So the *phrasing* "no terminal
object" is G1-dependent. But the *substance* is invariant: under (G0) the
terminal object is the information-destroying collapse, i.e. "the only
canonical grading-from-above is the one that forgets everything." The document
states this in §6.3(d). Phrasing-dependent, substance-invariant. **Not
rigged.**

**Rig vector 3 — the deep one.** The positive claim "the universal grading is
`D`" is *guaranteed* by writing gradings as maps `g : D → S` (D pre-baked as
the domain). A non-rigged formulation would define a grading as a poset `S`
with a map from the **event set / generator data** `E_all` respecting
(g1),(g2) — *not* presupposing `D`. Under that formulation the initial object
is the poset presented by (g1),(g2), whose transitive closure *is* `D` by
definition ([grading_obstruction §1.2]). So "the universal grading is `D`"
unwinds to the honest, non-circular statement **"D is the free strict grading
on the generating relations."** The document's Def 6.1 obscures this by baking
in `D`, which is precisely what makes 6.2 look like a tautology. The content
is real but mis-packaged.

**Conclusion of A1**: `Grad(D)` is the standard, unrestricted `Pos`-coslice.
The competitor-disfavoring one would be a *narrowed* target class (chains/ℕ
only) — and narrowing the class *destroys* the universal object (6.3) rather
than manufacturing `D` as winner. Including `D` (a poset) among poset-valued
targets is not special-casing. **The category is not rigged to make D win a
contest it would otherwise lose.** What "D wins" reduces to is (i) a tautology
(6.2, conceded) plus (ii) genuine structural facts about `D` carried by
6.3–6.7 and Q2.

### A2. Do 6.3–6.7 survive a non-rigged definition?

I stripped the categorical dress and asked whether each theorem rests on a
real property of `D` or on the framing. Recomputations by hand:

**6.3 (no initial/terminal chain-grading).** Rests entirely on: *`D` is not a
chain, and its incomparable pairs are realized in both orders by linear
extensions.* I re-derived the witnessing incomparabilities from Lemma 2.2(iv)
directly:

- `e = link{a,(ab)}`, `f' = link{b,(ab)}`: `link c(s) ≤ link c(t) ⟺ s=t ∨
  s⊲t`. Here `s=(a(ab))`, `t=(b(ab))`. Subterms of `(b(ab))` are
  `{(b(ab)), b, (ab), a}` — no `(a(ab))`; symmetrically subterms of `(a(ab))`
  are `{(a(ab)), a, (ab), b}` — no `(b(ab))`. So **incomparable**, and the
  atom-swap `σ` exchanges them. ✓
- Terminal-object triple `e=link{a,(ab)}`, `m=link{b,(ab)}`,
  `f=resolve{a,(ab)}`: `e ≺ f` by (g1); `m` incomparable to `e` (above) and to
  `f` (need `(b(ab)) ⊲ (a(ab))` or reverse — neither holds). ✓

The argument (linear target forces a decision, a labeling reverses it,
monotone morphism contradicts) uses *only* non-linearity + both-orders — both
established independently of the category. A chain `D` would have an initial
LinGrad; `D` does not, because concurrency is real. **Survives; non-rigged.**

**6.4 (unit-step numeric gradings empty beyond the zone).** Downstream of 3.5
(stratification dies at `ℓ*`) and 4.1 (rank dies at `E*`). These are the Q2
obstruction — concrete, framing-independent. **Survives.**

**6.5 (height least but not initial/not a rank).** `h(link{a,(ab)}) =
2·2−2 = 2 = h(link{b,(ab)})` while any labeling separates the two — a genuine
height-collision. **Survives.**

**6.6 (fold-or-gauge dilemma).** Rests on the swap automorphism `σ` moving
`link{a,(ab)}`: an injective chain grading cannot be `σ`-invariant. Elementary
group action, no category needed. **Survives.**

**6.7 (multigrading non-separating).** I recomputed the beyond-symmetry
collision (6.7(ii)):
- `(a(a(a(ab))))`: depths `1,2,3,4`, leaves `a,a,a,a,b` → `M=(resolve,4,5)`.
- `(a(b(a(ab))))`: depths `1,2,3,4`, leaves `a,b,a,a,b` → `M=(resolve,4,5)`.
  Equal. `σ`-orbit of the first is `{(a(a(a(ab)))), (b(b(b(ab))))}`; the second
  is in neither slot → **different orbit**, so `M` fails to separate even
  modulo symmetry. ✓ **Survives.**

**Verdict (a).** The morphism class is *not* rigged. Theorem 6.2 is a
tautology (conceded); Theorems **6.3–6.7 all survive** a non-rigged
reformulation because each rests on a genuine, independently-proved property of
`D` (non-linearity, non-gradedness, height-collision, swap symmetry with
growing orbits/fibers). The categorical packaging is *gratuitous* — the same
content reads more honestly as "no number scale grades `D` because `D` is not
a chain (6.3), is not graded (6.4/6.5), and its best numeric folds break the
forced symmetry (6.6) and blow up fibers (6.7)" — but gratuitous ≠ false.

---

## Part (b) — Retrofit audit of the "level 2" boundary + Prop 3.4 recomputation

### B1. Is "level = depth" the raw text's notion, or imposed?

ORIGIN_RAW §9: *"even viewed sequentially, natural-number strata can be
assigned up to level 2 (2층위), but beyond that it does not seem to work"*
(hedged: 안되는거같아서 = "seems not to"). "Level/layer" (층위) is **not** defined
in §9. The document (§1.1) fixes level = depth `δ`, justified via Prop 5.1
(gen = depth) tying it to §5's generation process.

I checked this against §5's **own** procedure, read literally:
- Round 0: `a, b` exist.
- Round 1: create `(ab)`.
- Round 2: create `(a(ab)), (b(ab))`.
- Round 3: link the round-2 points to all unjoined points → combs
  `(a(a(ab)))…` *and* `((ab)(a(ab)))`, `((a(ab))(b(ab)))`, …

Round = depth = generation (Prop 5.1, which I verified: `gen((a(ab)))=δ=2`,
etc.). So **"level 2" = through round 2 = the five objects `{a,b,(ab),(a(ab)),
(b(ab))}`** is fixed by §5's own counting, not by a post-hoc choice.
Independently, ORIGIN_RAW's own annotation table (the "Natural-number strata
reach level 2" row) glosses level 2 as "2 atoms + 3 composites" = these same
five. **The identification is forced by the raw text, not retrofitted.**

### B2. Off-by-one check.

If "level 2 boundary" is real, the maximal *depth-complete* downset admitting a
stratification should be exactly `{δ ≤ 2}`.

- `Z = {δ(tree) ≤ 2}` (the five composites-events set, = `D_3`): stratifiable
  (Prop 3.4, recomputed below). ✓
- `{δ ≤ 3}`: contains `ℓ* = link{(ab),(a(ab))}` with composite
  `((ab)(a(ab)))`, `δ=3`, a **skew link** (`δ(ab)=1 ≠ δ(a(ab))=2`) → no
  stratification (Thm 3.3(i)). ✗

So the largest `k` for which *all* of `{δ ≤ k}` admits a consistent stratum
assignment is `k = 2`. That is **exactly** §9 ("up to level 2 works, above does
not"), and the boundary sits **between** level 2 and level 3 — the failing
object `((ab)(a(ab)))` is level 3. **Not off by one.** (An off-by-one document
would have placed the boundary at level 3 / first failure at level 4.)

### B3. The real defect — Remark 3.6's "exact" is argued in the wrong framing.

Here the attack lands. Remark 3.6 (and Thm 3.5(ii)) present the boundary in the
`(λ, canonical string)` **leaf-count order**, in which the first failure is at
`λ = 5`. But the document itself proves (Thm 3.5(i)) that the stratification
**survives on all of `D_4`**, and states "**`D_4 ⊋ Z`: the stratification
survives through the four depth-3 combs of `λ=4`.**" Those combs
`(a(a(ab))), (b(a(ab))), (a(b(ab))), (b(b(ab)))` are **level-3 objects**
(`δ=3`), strictly above the level-2 zone, and they are stratifiable.

Therefore, in the λ-order that Remark 3.6 invokes, the first failure `ℓ*`
(`λ=5`) is **not** "just past the five level-≤2 objects": between the five
objects (`λ ≤ 3`) and `ℓ*` (`λ=5`) sits an entire shell of four stratifiable
level-3 combs (`λ=4`). Calling the match "exact" **in that framing is literally
false** — it is off by one λ-shell, exactly as the document *admits* for the
weaker rank reading (Remark 4.5) but does *not* admit for the stratification
reading.

The claim is *rescuable* — and true — only in the **depth-downset** framing of
B2: `Z = {δ≤2}` is the maximal depth-complete stratifiable downset. The
individual stratifiability of the `λ=4` combs is irrelevant there, because a
stratification is a *global* function on a downset and `{δ≤3}` has none. So the
document has the correct exact statement (Prop 3.4 gives `Z = D_3 = {δ≤2}`; Thm
3.3 gives the skew-link criterion) but **foregrounds the wrong order** (λ)
and thereby overclaims "exact" for an adjacency that does not hold in that
order. This is a genuine argument defect, not a mere wording nit: as written,
Remark 3.6's justification ("the first violation … lies just past the five
level-≤2 objects") is contradicted by the document's own Thm 3.5(i).

### B4. Prop 3.4 Hasse diagram — recomputed by hand, independently.

Composites of depth ≤ 2: `δ=1` forces two distinct atom children → `(ab)`;
`δ=2` forces one child `(ab)` (only shallower composite) + one atom →
`(a(ab)), (b(ab))`. Three composites, six events:

Generators (g1) `link p ≺ resolve p`, (g2) `resolve q ≺ link p` when `pair q`
is an endpoint of `p`:
- `link{a,b} ≺ resolve{a,b}` (g1)
- `link{a,(ab)} ≺ resolve{a,(ab)}`, `link{b,(ab)} ≺ resolve{b,(ab)}` (g1)
- `resolve{a,b} ≺ link{a,(ab)}` and `≺ link{b,(ab)}` (g2; `(ab)` an endpoint)
- `link{a,b}`: both endpoints atoms → no (g2) predecessor.

Chord check (Lemma 2.4(iii)): a (g2) relation is a chord iff `pair q` is a
*proper* subterm of the *other* endpoint. In `link{a,(ab)}` the other endpoint
is the atom `a`, so `(ab)` is not buried → **cover**, not chord. Same for
`link{b,(ab)}`. No chords inside `Z`.

Hasse (each node exactly one lower cover — a tree):

```
      link{a,b}           h = 0
         |
      resolve{a,b}        h = 1
       /         \
 link{a,(ab)}  link{b,(ab)}   h = 2
     |             |
 resolve{a,(ab)} resolve{b,(ab)}   h = 3
```

Heights via Lemma 2.5 (`h(link c t)=2δ−2`, `h(resolve c t)=2δ−1`):
`0, 1, 2, 2, 3, 3`. Strata sizes `1, 1, 2, 2`.
`r = h` is simultaneously (S1)+(S2) stratification — `resolve{a,b}=1=0+1`;
`link{a,(ab)}=2=resolve{a,b}+1`; `resolve{a,(ab)}=3=2+1` — and a rank function
(every cover steps `+1`: `0→1→2→3`). **Prop 3.4 reproduced exactly.** No skew
link exists in `Z` (a link with two composite endpoints needs `λ ≥ 5`).

### B5. Cross-check that the level-3 split is real (not the retrofit's artifact).

At round/level 3 the process produces both stratifiable and non-stratifiable
objects. The dividing line is **number of composite endpoints of the link**:
- one composite endpoint (`link{a,(a(ab))}`, comb) → single (S2) constraint →
  stratifiable;
- two composite endpoints of unequal depth (`ℓ* = link{(ab),(a(ab))}`) → two
  conflicting (S2) constraints (`r=2` from the `(ab)` side, `r=4` from the
  `(a(ab))` side) → impossible.

I verified the conflict: normalizing `r(⊥)=0`, the `(ab)`-side forces
`r(ℓ*) = r(resolve{a,b}) + 1 = 1+1 = 2`; the `(a(ab))`-side forces
`r(ℓ*) = r(resolve{a,(ab)}) + 1 = 3+1 = 4`. `2 ≠ 4`. ✓ So the *first*
appearance of a two-composite-different-depth contrast is the failure, and it
is a level-3 object — the failure genuinely *begins* at level 3, precisely as
§9 (hedged) says.

**Verdict (b).** The level-2 identification is **forced** by §5's own
generation counting and confirmed by ORIGIN_RAW's own gloss; the boundary is
**not off by one** (maximal stratifiable depth-downset is exactly `{δ≤2}`); and
Prop 3.4 recomputes correctly. **But Remark 3.6's "exact" is justified in the
wrong (λ) order and is false there** — the stratification demonstrably survives
past the level-2 zone through the `λ=4` combs, so the first λ-order failure is
one shell removed from the five objects. The claim is true only in the
depth-downset framing, which the document proves but does not lead with.

---

## Required fixes

1. **Remark 3.6 — re-ground "exact" in the depth framing.** State the exact
   theorem as: *the maximal depth-complete downset `{δ≤k}` admitting a
   stratification is exactly `k=2` (`= Z`); the first level-3 object, the first
   two-composite skew link `ℓ*`, breaks it.* Delete or qualify the current
   λ-order justification ("just past the five level-≤2 objects"), which
   contradicts Thm 3.5(i)'s own "`D_4 ⊋ Z`, stratification survives the four
   `λ=4` combs." As written, the remark claims an adjacency that its own
   neighbouring theorem refutes.

2. **§6.2 — cash out the concession.** State plainly that 6.2 carries *zero*
   information about `D` (true in every coslice) and that the entire Q3 content
   lives in 6.3–6.7 + the Q2 obstruction. Optionally re-present the universal
   property in the non-rigged form "`D` = free strict grading on the
   generators (g1),(g2)," which is the honest, non-circular statement the
   coslice framing hides.

3. **Optional (clarity, not correctness).** Note that 6.3–6.7 need no category
   theory: they are "`D` is not a chain / not graded / has swap symmetry with
   growing fibers." The categorical wrapper is decoration; keeping it is fine,
   but the load-bearing facts should be stated bare so the reader can see the
   content is not the coslice tautology.

None of these alter a theorem statement or a numeric result. The Q3 answer and
the §9 level-2 boundary both **hold**.

## Recomputed cases (independent, by hand)
- Prop 3.4 Hasse diagram, heights `0,1,2,2,3,3`, strata `1,1,2,2` — reproduced (B4).
- `ℓ*` stratification conflict `r=2` vs `r=4` — reproduced (B5).
- 6.3 incomparable witnesses `link{a,(ab)} ∥ link{b,(ab)}`, and the terminal
  triple — reproduced from Lemma 2.2(iv) (A2).
- 6.7(ii) beyond-symmetry `M`-collision `(resolve,4,5)` in distinct `σ`-orbits
  — reproduced (A2).
- 5.4 reversal `δ(a(a(a(ab))))=4 > 3=δ((a(ab))(b(ab)))`,
  `λ=5 < 6` — reproduced.
