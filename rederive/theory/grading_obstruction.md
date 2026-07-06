# The grading obstruction and the universal grading (Q2, Q3)

**Status**: deliverable for SPEC Q2 + Q3 (task M3), object-primary track.
**Inputs**: `rederive/SPEC.md`, `seed/ORIGIN_RAW.md` (§5, §6, §8, §9, §10),
`seed/ORIGIN.md`, the program memo, and the results already proved in
`rederive/theory/order_invariance.md` (cited below as **[OI]**).  Nothing
else from the repository.  The enumerator findings
(`rederive/enumerator/RESULTS.md`) were used only as *predictions*: every
witness and every number relied on below has been re-derived by hand in
this file; no theorem depends on machine output.  Classical mathematics is
used freely and recorded in §9 for the bilingual ledger.

**Result in one sentence.**  The causal order **D** of the asynchronous
distinction system carries a canonical height function but — in three
precise senses, each a theorem with an explicit minimal witness — no
natural-number stratification beyond the level-2 zone: (i) the
lockstep-generation stratification exists on a downset iff the downset
contains no "skew link", and the first skew link is
`link{(ab),(a(ab))}` (composite `((ab)(a(ab)))`, 5 leaves), immediately
past the five level-≤2 objects; (ii) **D** admits *no rank function at
all* — the λ-truncations `D_n` are graded exactly for `n ≤ 6`, with first
absolute failure at `link{(a(ab)),(a(b(ab)))}` (7 leaves, two saturated
bottom-chains of lengths 4 and 6), and the defect is unbounded; (iii) the
natural ℕ-folds depth, size, generation coincide as one ladder up to
level 2 (indeed on all trees with ≤ 4 leaves) and diverge at
`((ab)(a(ab)))`, eventually ordering trees oppositely.  On Q3: in the
category of gradings, the initial object is **D** itself; the category of
*chain-valued* gradings has **no** universal object in either direction;
the least ℕ-grading is the height and it provably fails to be a
stratification.  The answer to ORIGIN_RAW §10 — "which number scale grades
the layers above level 2?" — is therefore a computation, not a choice:
**no scale; the order itself**, and this answer is contentful precisely
because of the impossibility theorems (i)–(iii) and the no-universal-chain
theorem.  The layer widths of the height grading are identified with the
classical sequences A103410 = A002658 (per layer) and A108225 (cumulative);
the size-fold widths are A063894; the nearby classical candidate
(Wedderburn–Etherington, A001190) is provably *not* the right sequence.

---

## 1. Setting and notation

### 1.1 Trees

`Tree` is the F-obj carrier of SPEC §1: atoms `a`, `b`, closed under the
unordered pairing `pair{x,y}` of two *distinct* trees.  We write `(xy)`
for `pair{x,y}` in examples.  From [OI] §1.1 we import the facts
T1 (pairing injective, children recoverable), T2 (composites are not
atoms, `a ≠ b`), T3 (size), T4 (countability).

For a tree `t`:

- `λ(t)` := number of **leaves** (`λ(a) = λ(b) = 1`,
  `λ(pair{x,y}) = λ(x) + λ(y)`).  This is the enumerator's "size".  The
  node-count of [OI] T3 is `ν(t) = 2λ(t) − 1`; the two are related by a
  strictly increasing affine map, so all order statements transfer.
- `δ(t)` := **depth** (`δ(atom) = 0`,
  `δ(pair{x,y}) = 1 + max(δ(x), δ(y))`).
- `c(t)` := the child pair `{x, y}` of a composite `t = pair{x,y}`
  (well-defined by T1).
- `s ⊴ t` := `s` is a **subterm** of `t` (reflexive); `s ⊲ t` if proper.
  A proper subterm of `t` is a subterm of a child of `t`.
- A **comb** is a tree in which every composite subterm has at least one
  atom child: `a`, `b`, `(ab)`, `(x₁(x₂(…(ab)…)))` with `xᵢ ∈ {a,b}`.

**Levels.**  The *level* of an object is its depth `δ` — Proposition 5.1
below proves that ORIGIN_RAW §5's lockstep generation number equals depth,
so this is the raw text's own stratum where it is defined.  The **five
level-≤2 objects** of ORIGIN_RAW §9 are

    a, b, (ab), (a(ab)), (b(ab))       (δ = 0, 0, 1, 2, 2).

### 1.2 The causal order D

From [OI] Definition 5.4: on the event alphabet
`E_all = {link p, resolve p : p ∈ P₂(Tree)}`, `≤_D` is the
reflexive–transitive closure of

- **(g1)** `link p ≺ resolve p`;
- **(g2)** `resolve q ≺ link p` whenever `pair q` is an endpoint of `p`.

Imported from [OI]: `D` is a partial order with finite principal downsets
and unique minimum `⊥ = link{a,b}` (Prop 5.5); executed sets of runs =
downsets of `D`, maximal runs = ω-type linear extensions = natural
labelings (Thm 5.7, 7.1); every `D`-incomparable pair is scheduled both
ways by maximal runs (Lemma 7.2, Thm 7.3); the atom swap `σ : a ↔ b` is an
automorphism of everything (§8.2).

Every event `e` carries a **kind** (`link`/`resolve`) and a composite tree
`tree(e) := pair p` for `e ∈ {link p, resolve p}`.  We freely write
`link c(t)`, `resolve c(t)` for the two events that draw and resolve the
line reified as `t`.

**Poset vocabulary** (classical; Stanley, *Enumerative Combinatorics* I,
ch. 3).  In a poset `P`: `e ⋖ f` (**cover**) iff `e < f` with nothing
strictly between.  A **chain** is a totally ordered subset; a finite chain
`e₀ < … < e_n` has **length** `n`; it is **saturated** if each step is a
cover.  The **height** `h(e)` is the maximum length of a chain with top
`e` (finite here, by finiteness of principal downsets).  A **rank
function** is `r : P → ℕ` with `r(f) = r(e) + 1` for every cover
`e ⋖ f`; `P` is **graded** if one exists.  A **downset** (order ideal) is
downward-closed.  A relation `e < f` that holds but is not a cover is a
**chord** of the generator presentation.

**Truncations.**  For `n ≥ 1` let

    D_n := { e ∈ E_all : λ(tree(e)) ≤ n }.

By Lemma 2.2(iii) below each `D_n` is a downset of `D`, so its covers and
heights agree with those computed in `D`.

---

## 2. The structure of D: downsets, comparability, covers, height

### 2.1 The bottom composite

**Lemma 2.1.**  `(ab) ⊴ t` for every composite tree `t`.

*Proof.*  Induction on `λ(t)`.  If both children of `t` are atoms they are
distinct atoms, hence `{a, b}`, so `t = (ab)`.  Otherwise `t` has a
composite child `x`; by induction `(ab) ⊴ x ⊴ t`.  ∎

### 2.2 Principal downsets and comparability

**Lemma 2.2.**  For composite trees `s, t` and any composite trees
`x, y` with `x ≠ y`:

(i) `↓resolve c(t) = { link c(s), resolve c(s) : s ⊴ t, s composite }`.

(ii) `↓link{x,y} = {link{x,y}} ∪ ↓resolve c(x') ∪ ↓resolve c(y')` where
the unions run over the composite endpoints `x', y'` among `x, y` (with
`resolve c(u)` read as its principal downset for each composite
endpoint `u`).

(iii) Every event in `↓e` has `tree ⊴ tree(e)`; in particular
`λ(tree(f)) ≤ λ(tree(e))` for `f ≤_D e`, so each `D_n` is a downset.

(iv) **Comparability characterization.**
`resolve c(s) ≤_D resolve c(t) ⟺ s ⊴ t`;
`link c(s) ≤_D resolve c(t) ⟺ s ⊴ t`;
`resolve c(s) ≤_D link c(t) ⟺ s ⊲ t`;
`link c(s) ≤_D link c(t) ⟺ s = t or s ⊲ t`.

*Proof.*  The generator rules give: the only `≺`-predecessor of
`resolve p` is `link p` (rule (g2) targets links only), and the
`≺`-predecessors of `link p` are exactly the events `resolve q` with
`pair q` a composite endpoint of `p` — one such `q` per composite
endpoint, unique by T1.  Hence

    ↓resolve c(t) = {resolve c(t)} ∪ ↓link c(t),
    ↓link{x,y}    = {link{x,y}} ∪ ⋃_{u ∈ {x,y} composite} ↓resolve c(u).

(i) now follows by induction on `λ(t)`: the events on composite subterms
of `t` are `t`'s own two events plus, for each composite child `u`, the
events on composite subterms of `u`; and `s ⊴ t` iff `s = t` or `s` is a
subterm of a child.  (ii) is the second display.  (iii) is immediate from
(i)–(ii) since subterms have no more leaves.  (iv) reads membership off
(i)–(ii): e.g. `resolve c(s) ∈ ↓link c(t)` iff `s` is a composite subterm
of a child of `t`, i.e. `s ⊲ t`.  ∎

**Corollary 2.3 (proper subterms are strictly shallower).**  If
`s ⊲ t` then `δ(s) < δ(t)`.

*Proof.*  `s` is a subterm of a child `u` of `t`; subterm implies
`δ(s) ≤ δ(u)` (induction on the definition of subterm, since `δ` of a
child is `< δ` of the parent and `δ` is monotone along ⊴ by the same
induction), and `δ(u) ≤ δ(t) − 1`.  ∎

### 2.3 Covers

**Lemma 2.4 (cover classification).**

(i) `link p ⋖ resolve p` for every `p`, and `link p` is the **unique**
lower cover of `resolve p`.

(ii) The lower covers of `link{x,y}` are exactly the events
`resolve c(u)` for those composite endpoints `u ∈ {x,y}` that are **not**
a proper subterm of the other endpoint.  Consequently `link{x,y}` has

- 0 lower covers iff `{x,y} = {a,b}`;
- 1 lower cover if exactly one endpoint is composite, or both are
  composite and ⊴-comparable;
- 2 lower covers iff both endpoints are composite and ⊴-incomparable.

(iii) The relation `resolve q ≺ link p` of rule (g2) is a **chord** (not
a cover) exactly when `pair q` is a proper subterm of the other endpoint
of `p`.

*Proof.*  (i) `↓resolve p ∖ {resolve p} = ↓link p`, whose maximum is
`link p`; nothing lies strictly between.  (ii) By Lemma 2.2(ii) the
maximal elements of `↓link{x,y} ∖ {link{x,y}}` are among the
`resolve c(u)`.  `resolve c(x)` fails to be maximal iff
`resolve c(x) <_D resolve c(y)`, which by Lemma 2.2(iv) is `x ⊲ y`.  If an
endpoint is an atom it contributes no predecessor.  The count follows:
`p = {a,b}` is the only pair with no composite endpoint (both endpoints
atoms and distinct), hence the only link with no lower cover ([OI] Prop
5.5: it is the global minimum).  (iii) is the complement of (ii).  ∎

**Remark.**  By Lemma 2.1, whenever `(ab)` is an endpoint of `p` and the
other endpoint is composite, `(ab)` is a proper subterm of it, so
`resolve{a,b} ≺ link p` is always a chord in that situation.  This is the
chord the enumerator discovered (`RESULTS.md` E4 caveat); it is hereby
confirmed by hand and located structurally.

### 2.4 Height

**Lemma 2.5 (height formula).**  For every composite tree `t`:

    h(link c(t))    = 2 δ(t) − 2,
    h(resolve c(t)) = 2 δ(t) − 1.

Hence height determines and is determined by the kind and the depth of
the composite: links sit at even heights, resolves at odd heights, and
the events at heights `{2m, 2m+1}` are exactly the link/resolve pairs of
the composites of depth `m + 1`.

*Proof.*  Every maximal chain with top `e` steps down through some
`≺`-predecessor of `e` (any `f <_D e` satisfies `f ≼ g ≺ e` for some
generator-predecessor `g`), so

    h(e) = 1 + max { h(g) : g ≺ e }        (max ∅ := −1).

Induction on `λ(tree(e))`.  For `resolve c(t)`:
`h = 1 + h(link c(t)) = 1 + (2δ(t) − 2)`.  For `link{x,y}` with composite
endpoints `u`: `h = 1 + max_u h(resolve c(u)) = 1 + max_u (2δ(u) − 1) =
2 max_u δ(u)`, and `max_u δ(u) = max(δ(x), δ(y))` because atoms have depth
0 ≤ any composite's depth — careful at the bottom: for `{x,y} = {a,b}`
there is no predecessor and `h = 0 = 2·max(0,0)`.  Since
`δ(pair{x,y}) = 1 + max(δ(x), δ(y))`, in all cases
`h(link{x,y}) = 2 δ(pair{x,y}) − 2`.  ∎

**Corollary 2.6.**  `h` is strictly monotone on `D` (a chain below `e`
extends any chain below any `f <_D e`), and by Lemma 2.5 it is constant on
each kind×depth class.  It reproduces the enumerator's E3/E4 heights:
`link{a,b}, resolve{a,b}` at 0, 1; the four level-2-composite events at
2, 3; `link{(ab),(a(ab))}` at `2·3−2 = 4`; `resolve{a,(b(ab))}` at
`2·3−1 = 5`; `link{(a(ab)),(a(b(ab)))}` at `2·4−2 = 6`.  (All checked by
hand; they match `RESULTS.md` E4.)

---

## 3. Q2, first reading — the lockstep stratification: works to level 2, fails at `((ab)(a(ab)))`

ORIGIN_RAW §5 describes generation-by-generation growth; §6 suspects the
lockstep; §9 reports that "natural-number strata can be assigned up to
level 2, but beyond that it does not seem to work."  The strongest
faithful formalization of "assigning natural-number strata" to the
process is: *a stage function under which every event happens exactly one
stage after each of its immediate causes* — that is what a synchronized
foliation ("now all lines resolve!") provides, and what "the k-th layer
is produced by the (k−1)-th" means.

**Definition 3.1 (stratification).**  Let `F ⊆ E_all` be a downset of
`D`.  A **stratification** of `F` is a function `r : F → ℕ` such that

- (S1) `r(resolve p) = r(link p) + 1` whenever `resolve p ∈ F`;
- (S2) `r(link p) = r(resolve c(u)) + 1` for **every** composite endpoint
  `u` of `p`, whenever `link p ∈ F`.

(Both generator sorts advance by exactly one stage; a line is drawn one
stage after the reification of *each* of its composite endpoints.)

**Definition 3.2 (skew link).**  A **skew link** is an event `link{x,y}`
with both `x, y` composite and `δ(x) ≠ δ(y)`.

**Theorem 3.3 (existence criterion, uniqueness, forced form).**  Let `F`
be a nonempty downset of `D`.  Then:

(i) `F` admits a stratification **iff** `F` contains no skew link.

(ii) If it does, the stratifications of `F` are exactly
`r = c + h|_F` for a constant `c ∈ ℕ`: natural-number strata, where they
exist at all, are the height strata.

*Proof.*  (⇐ of (i), and (ii) existence.)  Suppose `F` has no skew link;
set `r := c + h`.  (S1): `h(resolve p) = h(link p) + 1` by Lemma 2.5.
(S2): for `link{x,y} ∈ F` with composite endpoint `u`, we need
`h(link{x,y}) = h(resolve c(u)) + 1`, i.e.
`2 max(δ(x), δ(y)) = 2δ(u) − 1 + 1`, i.e. `δ(u) = max(δ(x), δ(y))`.  If
the other endpoint is an atom this is trivial; if both are composite,
no-skew gives `δ(x) = δ(y)`.  ✓

(ii) uniqueness.  In a nonempty downset, `⊥ = link{a,b}` is the unique
element without `≺`-predecessors (every other event has one, and a
nonempty downset contains `⊥` since `⊥ ≤_D` everything, [OI] Prop 5.5).
(S1)–(S2) determine `r(e)` from `r` at the `≺`-predecessors, so by
induction along `↓e` (finite), `r(e) = r(⊥) + h(e)` using the height
recursion of Lemma 2.5 — the recursion for `r` and for `h` coincide
exactly when no skew link is present, which is the hypothesis.

(⇒ of (i).)  Suppose `F` contains a skew link and a stratification `r`.
Choose `ℓ = link{x,y}` a `≤_D`-minimal skew link in `F` (possible:
`↓ℓ` is finite).  Then the downset `↓ℓ ∖ {ℓ}` is skew-free, so by the
part already proved, `r = r(⊥) + h` on it.  (S2) at `ℓ` for both
endpoints gives

    r(ℓ) = r(⊥) + h(resolve c(x)) + 1 = r(⊥) + h(resolve c(y)) + 1,

hence `2δ(x) − 1 = 2δ(y) − 1`, contradicting `δ(x) ≠ δ(y)`.  ∎

**Proposition 3.4 (the level-≤2 zone is stratified — positive half of
ORIGIN_RAW §9).**  The level-≤2 zone is the downset

    Z := { e : δ(tree(e)) ≤ 2 } = D_3

(the composites of depth ≤ 2 are exactly `(ab), (a(ab)), (b(ab))`, the
composites with ≤ 3 leaves).  `Z` has six events and its full order
structure is:

    h=0   link{a,b}
            |
    h=1   resolve{a,b}
           /         \
    h=2  link{a,(ab)}   link{b,(ab)}
          |               |
    h=3  resolve{a,(ab)}  resolve{b,(ab)}

Every element has a unique lower cover (the Hasse diagram is a tree), all
six generator relations are covers, there are no chords and no skew
links, and `r = h` is simultaneously a stratification (Def 3.1) and a
rank function (§4).  The strata have sizes 1, 1, 2, 2.

*Proof.*  Composites of depth ≤ 2: depth 1 forces two atom children, so
`(ab)`; depth 2 forces one child `(ab)` (the only shallower composite)
and one atom, so `(a(ab))`, `(b(ab))`.  These are also exactly the
composites with `λ ≤ 3` (a composite with `λ ≤ 3` has an atom child and a
child in `{a, b, (ab)}`), so `Z = D_3`, a downset by Lemma 2.2(iii).  The
six events and their generator relations are enumerated directly:
`link{a,b} ≺ resolve{a,b}`; `resolve{a,b} ≺ link{a,(ab)}, link{b,(ab)}`
(rule (g2), `(ab)` an endpoint); `link{a,(ab)} ≺ resolve{a,(ab)}`;
`link{b,(ab)} ≺ resolve{b,(ab)}`.  No pair `{x,y} ⊆ Z`-composites with
both composite exists inside `Z` (such a link would have `λ ≥ 5`), so no
skew links and — by Lemma 2.4 — every listed relation is a cover with
uniqueness as drawn.  Heights from Lemma 2.5.  Both (S1)–(S2) and the
rank condition hold by inspection.  ∎

**Theorem 3.5 (first failure — the Q2 witness, stratification reading).**
Order events by `(λ(tree(e))`, then canonical string of `tree(e))`.  Then:

(i) Every link whose endpoints are not both composite satisfies (S2) with
a single constraint; a skew link requires two composite endpoints, hence
`λ(tree) ≥ 2 + 3 = 5`.  All events with `λ(tree) ≤ 4` — the downset `D_4`
— are skew-free, so `D_4` admits the stratification `r = h` (Theorem
3.3).  Note `D_4 ⊋ Z`: the stratification survives through the four
depth-3 combs of `λ = 4`.

(ii) The **first two-composite link in this order is already skew**: the
composites of `λ = 5` with two composite children are
`((ab)(a(ab)))` and `((ab)(b(ab)))` (split `2+3`; a `λ = 5` split `1+4`
has an atom endpoint), and both are skew (`δ = 1` vs `δ = 2`).  The first
in canonical order is

    ℓ* := link{(ab), (a(ab))},   composite ((ab)(a(ab))),  λ = 5, δ = 3.

(iii) No downset containing `ℓ*` admits a stratification.  Concretely,
normalizing `r(⊥) = 0`: the `(ab)`-side constraint forces
`r(ℓ*) = r(resolve{a,b}) + 1 = 2`, the `(a(ab))`-side constraint forces
`r(ℓ*) = r(resolve{a,(ab)}) + 1 = 4`.

*Proof.*  (i) A composite of `λ ≤ 4` decomposes as `1+1`, `1+2`, or
`1+3` (a `2+2` split would need two *distinct* composites with 2 leaves,
but `(ab)` is the only one), so it has an atom child; hence no
two-composite link in `D_4`.  Theorem 3.3 applies.  (ii) Enumerate the
`λ = 5` splits: `1+4` (atom endpoint) and `2+3`: the 2-leaf endpoint is
`(ab)` (δ=1), the 3-leaf endpoint is `(a(ab))` or `(b(ab))` (δ=2) — skew.
(iii) Theorem 3.3(i)(⇒), with the explicit values from Proposition 3.4
(`r = h` forced on `↓ℓ* ∖ {ℓ*} ⊆ D_3`-events plus nothing else:
`↓ℓ* = {ℓ*} ∪ ↓resolve{a,b} ∪ ↓resolve{a,(ab)}`, all inside `Z`).  ∎

**Remark 3.6 (exactness of the SPEC prediction).**  Both endpoints of
`ℓ*` are level-≤2 objects.  `ℓ*` is literally *the first event one can
attempt that involves only the five objects and is not itself in their
zone* — the first contrast **between** two of the reified differences —
and its stage is overdetermined (2 by one parent, 4 by the other).  So
"natural-number strata work up to level 2 and provably fail at the first
element beyond" holds in the exact form SPEC Q2 predicted: the first
violation is computable, lies just past the five level-≤2 objects, and
its composite `((ab)(a(ab)))` is a level-3 object.  Every violation is
above the level-2 zone: a skew link has two composite children, so its
composite has `δ ≥ 1 + max(1, 2) = 3`.

---

## 4. Q2, second reading — D admits no rank function at all

The stratification of §3 demands unit steps along the *generator*
relations, some of which are chords (Lemma 2.4(iii)).  The weaker —
purely order-theoretic — demand is a **rank function**: unit steps along
*covers* only.  This section shows even that fails, with the first
witness slightly higher, and with unbounded defect.

**Theorem 4.1 (no rank function; explicit minimal witness).**  Let

    E* := link{(a(ab)), (a(b(ab)))},   composite ((a(ab))(a(b(ab)))),  λ = 7, δ = 4.

Then the two chains

    C₁ : link{a,b} ⋖ resolve{a,b} ⋖ link{a,(ab)} ⋖ resolve{a,(ab)} ⋖ E*                                  (length 4)
    C₂ : link{a,b} ⋖ resolve{a,b} ⋖ link{b,(ab)} ⋖ resolve{b,(ab)} ⋖ link{a,(b(ab))} ⋖ resolve{a,(b(ab))} ⋖ E*   (length 6)

are both saturated chains from the minimum `⊥` to `E*`.  Consequently no
downset of `D` containing `E*` admits a rank function; in particular `D`
does not, and `h` is a strict grading that is not a rank (the cover
`resolve{a,(ab)} ⋖ E*` jumps height by 3).

*Proof.*  Every step must be verified as a cover (Lemma 2.4):

- `link p ⋖ resolve p`: always a cover (2.4(i)) — steps 1, 3, 5 of `C₂`,
  steps 1, 3 of `C₁`.
- `resolve{a,b} ⋖ link{a,(ab)}` and `⋖ link{b,(ab)}`: the links have one
  atom endpoint and one composite endpoint `(ab)`; unique lower cover
  `resolve c((ab)) = resolve{a,b}` (2.4(ii)).  ✓
- `resolve{b,(ab)} ⋖ link{a,(b(ab))}`: endpoint `a` atom, endpoint
  `(b(ab))` composite with `c((b(ab))) = {b,(ab)}`; unique lower cover
  `resolve{b,(ab)}`.  ✓
- `resolve{a,(ab)} ⋖ E*` and `resolve{a,(b(ab))} ⋖ E*`: the endpoints
  `x = (a(ab))` and `y = (a(b(ab)))` of `E*` are both composite and
  **⊴-incomparable** — the subterms of `y = (a(b(ab)))` are
  `y, a, (b(ab)), b, (ab)`, which do not include `x`, and `λ(y) > λ(x)`
  excludes `y ⊴ x`.  By Lemma 2.4(ii) **both** `resolve c(x) =
  resolve{a,(ab)}` and `resolve c(y) = resolve{a,(b(ab))}` are lower
  covers of `E*`.  ✓

Both chains start at `⊥` and end at `E*`; lengths 4 and 6 by counting.
If `r` were a rank function on a downset containing `E*` (hence
containing both chains, which lie in `↓E*`), then walking each saturated
chain gives `r(E*) = r(⊥) + 4` and `r(E*) = r(⊥) + 6`.  Contradiction.
Height jump: `h(E*) = 2·4 − 2 = 6` while `h(resolve{a,(ab)}) = 3`
(Lemma 2.5).  ∎

**Theorem 4.2 (exact gradedness threshold).**  `D_n` is graded **iff**
`n ≤ 6`, and for `n ≤ 6` the rank functions of `D_n` are exactly
`c + h|_{D_n}`.  The elements of `D` with two lower covers at different
heights are exactly the links `link{x,y}` with `x, y` composite,
⊴-incomparable, and `δ(x) ≠ δ(y)`; the minimum possible leaf count for
such a link is 7, attained exactly by the four events

    link{(a(ab)), (a(b(ab)))},  link{(a(ab)), (b(b(ab)))},
    link{(b(ab)), (a(a(ab)))},  link{(b(ab)), (b(a(ab)))}.

*Proof.*  *Covers increment `h` by 1 except in the skew-incomparable
case.*  By Lemma 2.4 the covers are: (a) `link p ⋖ resolve p`: `h`-step
1 (Lemma 2.5).  (b) `resolve c(u) ⋖ link{x,y}` with `u` the unique
composite endpoint (other endpoint an atom): step
`2δ(pair) − 2 − (2δ(u) − 1) = 2(δ(u)+1) − 2 − 2δ(u) + 1 = 1`.  (c) both
endpoints composite, ⊴-comparable, say `x ⊲ y` (then `δ(x) < δ(y)` by
Corollary 2.3, and the unique cover is `resolve c(y)`): step
`2(δ(y)+1) − 2 − (2δ(y) − 1) = 1`.  (d) both composite, ⊴-incomparable:
covers `resolve c(x)` at `2δ(x) − 1` and `resolve c(y)` at `2δ(y) − 1`;
the step from the deeper one is 1, from the shallower one is
`2|δ(x) − δ(y)| + 1`.  So all covers are `h`-unit except case (d) with
`δ(x) ≠ δ(y)`.

*Minimal λ of a skew-incomparable link is 7.*  Both endpoints composite:
`λ ≥ 2 + 2`.  If an endpoint is `(ab)`, Lemma 2.1 makes it a subterm of
the other — comparable; so both endpoints have `λ ≥ 3`, giving `λ ≥ 6`.
At `λ = 6` the only two-composite split with both `λ ≥ 3` is `3+3`:
endpoints among `(a(ab))`, `(b(ab))`, distinct — incomparable (neither is
a subterm of the other: their proper subterms are atoms and `(ab)`) but
of **equal** depth 2: not skew.  At `λ = 7` the split `3+4`: the 3-leaf
endpoint `x ∈ {(a(ab)), (b(ab))}` (δ=2), the 4-leaf endpoint `y` among
the four combs `(a(a(ab))), (b(a(ab))), (a(b(ab))), (b(b(ab)))` (δ=3) —
skew; incomparability must be checked: the subterms of `y` with 3 leaves
are exactly its depth-2 subterm (`(a(ab))` for the first two, `(b(ab))`
for the last two), so exactly 4 of the 8 combinations are
⊴-incomparable — the four listed.  (Split `2+5` has endpoint `(ab)`:
comparable.)

*Gradedness of `D_6`.*  `D_6` is a downset (Lemma 2.2(iii)), so covers
and heights inside `D_6` are those of `D`.  Every element of `D_6` has
`λ(tree) ≤ 6 < 7`, so no cover of case (d)-skew occurs among its
elements, so `h` steps by exactly 1 along every cover in `D_6`: `h` is a
rank function.  Uniqueness up to constant: `D_6` has the unique minimum
`⊥`, and every element is reachable from `⊥` by a saturated chain (climb
covers within `↓e`), so a rank is forced to be `r(⊥) + h`.

*Non-gradedness of `D_n`, `n ≥ 7`.*  `E* ∈ D_7 ⊆ D_n` and Theorem 4.1
applies.

*Minimality claim of the witness.*  A poset with `⊥` and finite heights
is graded iff every element's saturated `⊥`-chains have one length; the
`h`-unit computation above shows that an element all of whose lower
covers sit at height `h(e) − 1`, in a downset where all lower elements
are already graded with rank `h`, is itself graded; hence a minimal
non-graded element must have two lower covers at different heights —
i.e. be a skew-incomparable link — and any such link has `λ ≥ 7`.  So
every element with `λ(tree) ≤ 6` is graded and the four `λ = 7` events
are the absolute first failures (in the `(λ, canonical string)` order the
first is `E*`, matching the enumerator's E4 report, which is hereby
confirmed by hand).  ∎

**Proposition 4.3 (the defect is unbounded).**  For every `B ∈ ℕ` there
is an element of `D` with two saturated `⊥`-chains whose lengths differ
by more than `B`.  Hence no "approximate rank" with uniformly bounded
cover-defect exists either: `sup {h(f) − h(e) − 1 : e ⋖ f} = ∞`.

*Proof.*  Let `e₁ := (ab)`, `e_{k+1} := (a e_k)` (the `a`-combs,
`δ(e_k) = k`) and `d₂ := (b(ab))` (δ = 2).  For `k ≥ 3`:
subterms of `e_k` are `{a, b} ∪ {e_i : i ≤ k}`, which exclude `d₂`; and
`λ(e_k) = k + 1 > 3 = λ(d₂)` excludes `e_k ⊴ d₂`; so `d₂, e_k` are
⊴-incomparable, and `L_k := link{d₂, e_k}` has two lower covers
(Lemma 2.4(ii)): `resolve{b,(ab)}` at height 3 and `resolve c(e_k) =
resolve{a, e_{k−1}}` at height `2k − 1` (Lemma 2.5).  Both extend to
saturated `⊥`-chains through those covers: via `d₂`, the chain
`⊥ ⋖ resolve{a,b} ⋖ link{b,(ab)} ⋖ resolve{b,(ab)} ⋖ L_k` (length 4,
covers as in Theorem 4.1); via `e_k`, the comb ladder
`⊥ ⋖ resolve{a,b} ⋖ link{a,e₁} ⋖ resolve{a,e₁} ⋖ … ⋖ resolve{a,e_{k−1}}
⋖ L_k` (length `2k`; each rung is a cover by Lemma 2.4(i)/(ii), each
link having one atom endpoint).  Difference `2k − 4 → ∞`; the cover
`resolve{b,(ab)} ⋖ L_k` has `h`-jump `2(k−2) + 1 → ∞`.  ∎

**Remark 4.4 (object-level mirror).**  The same obstruction lives one
level down, on the poset `(Tree, ⊴)`: with `t* := ((a(ab))(a(b(ab))))`,

    a ⋖ (ab) ⋖ (a(ab)) ⋖ t*                        (length 3)
    a ⋖ (ab) ⋖ (b(ab)) ⋖ (a(b(ab))) ⋖ t*           (length 4)

are two saturated chains (in the subterm order, `s ⋖ t` iff `s` is a
child of `t` not a proper subterm of the other child — same proof shape
as Lemma 2.4), so the tree poset is not graded either.  `D` is the
two-fold interleaving of this object poset (Lemma 2.2(iv): `resolve`
events with the subterm order, with `link` events interposed); every
statement in §3–§4 has an object-level half-resolution shadow.

**Remark 4.5 (reconciling the two readings; the enumerator caveat).**
The task statement's cover list ("`link_p < resolve_p`;
`resolve_x < link_{x,y}`") is the *generator presentation* (g1)–(g2),
not the cover relation: by Lemma 2.4(iii) a (g2) relation is a chord
whenever one endpoint is buried in the other, and by Lemma 2.1 this
happens *at the very first two-composite link* (`resolve{a,b} ≺ ℓ*` is a
chord since `(ab) ⊲ (a(ab))`).  Hence the two theorem-shaped versions of
Q2, with different first witnesses:

| Reading | Unit-step demand along | First violation | λ | Result |
|---|---|---|---|---|
| Stratification (§3, the lockstep/§5 semantics) | every generator relation | `ℓ* = link{(ab),(a(ab))}` | 5 | Thm 3.5 |
| Rank function (§4, order-theoretic) | every cover | `E* = link{(a(ab)),(a(b(ab)))}` (any of 4) | 7 | Thm 4.1/4.2 |

Both firsts are computable; both lie strictly above the level-2 zone;
SPEC Q2's "just past the five level-≤2 objects" is *exact* for the
stratification reading — which is the reading that formalizes
ORIGIN_RAW §5's generation picture — and off by one λ-shell for the
strictly weaker cover reading.  The enumerator reported both witnesses
correctly; both are hereby re-derived by hand.

---

## 5. Q2, third reading — fold divergence: depth, size, generation

The per-object ℕ-folds a sequential analyst would try as strata: depth
`δ`, size `λ`, and the lockstep generation number.

**Definition.**  `G₀ := {a, b}`, `G_{k+1} := G_k ∪ {pair{x,y} : x ≠ y ∈
G_k}`; `gen(t) := min {k : t ∈ G_k}` (ORIGIN_RAW §5's stage of first
appearance).

**Proposition 5.1 (generation = depth).**  `G_k = {t : δ(t) ≤ k}` for all
`k`; hence `gen = δ` identically.

*Proof.*  Induction.  `G₀` = atoms = depth ≤ 0.  If `G_k = {δ ≤ k}`:
any `pair{x,y}` with `x, y ∈ G_k` has `δ = 1 + max ≤ k + 1`, and `G_k ⊆
{δ ≤ k+1}`, so `G_{k+1} ⊆ {δ ≤ k+1}`; conversely a composite `t` with
`δ(t) ≤ k+1` has children of depth ≤ k, which lie in `G_k` by induction,
so `t ∈ G_{k+1}`; atoms are everywhere.  ∎

So the third fold adds nothing: the enumerator's finite check
(`gen(t) = depth(t)` for all 44 trees of `λ ≤ 6`) is a theorem for all
trees, and the operative divergence is depth vs size.

**Proposition 5.2 (lockstep ladder below λ = 5).**  Every tree with
`λ ≤ 4` is a comb, and on combs `λ = δ + 1`.  Hence on the first nine
trees (all `λ ≤ 4`) the three folds form one bijective ladder

    (δ, gen, λ) = (k, k, k+1),   k = 0, 1, 2, 3;

in particular on the five level-≤2 objects.

*Proof.*  A composite with `λ ≤ 4` splits as `1+1`, `1+2`, `1+3` (no
`2+2`: only one 2-leaf tree exists and children are distinct — SPEC C4 at
work), so it has an atom child, and its composite child (if any) has
`λ ≤ 3`: induction gives combs.  On a comb, each wrap adds one leaf and
one depth unit from `(ab)` (`λ = 2, δ = 1`): `λ = δ + 1`.  Count: sizes
1..4 hold 2, 1, 2, 4 trees = 9.  ∎

**Theorem 5.3 (first divergence, hand-verified).**  In the
`(λ, canonical string)` order, the first tree at which the ladder
`λ = δ + 1` fails is

    w := ((ab)(a(ab))),    λ(w) = 5,  δ(w) = gen(w) = 3.

Moreover at `w` the folds *decouple as strata*: depth 3 co-occurred only
with size 4 on all earlier trees; from `w` on, the depth-3 class contains
sizes 4 and 5 — depth no longer determines size, so "the stratum of `t`"
stops being well-defined across the folds.  `w` is a level-3 object whose
two children `(ab)`, `(a(ab))` are both level-≤2 objects, and `w` is the
composite of the §3 witness `ℓ*` — the three Q2 readings point at the
same first object.

*Proof.*  By Proposition 5.2 all nine trees with `λ ≤ 4` satisfy
`λ = δ + 1`.  Trees with `λ = 5`: splits `1+4` (combs: `λ = 5, δ = 4` —
ladder holds) and `2+3`: `((ab)(a(ab)))`, `((ab)(b(ab)))` with
`δ = 1 + max(1,2) = 3 ≠ 5 − 1`.  Canonical order puts `((ab)(a(ab)))`
first.  The depth-3 trees of `λ = 4` are the four combs of Prop 5.2.  ∎

**Theorem 5.4 (order reversal — no monotone rescaling reconciles the
folds).**  The pair

    t₁ := (a(a(a(ab))))       λ = 5, δ = 4      (a comb)
    t₂ := ((a(ab))(b(ab)))    λ = 6, δ = 3

satisfies `δ(t₁) > δ(t₂)` and `λ(t₁) < λ(t₂)`, and it is a
minimal-λ(t₂) such pair.  Hence there is no strictly increasing
`θ : ℕ → ℕ` with `λ = θ(δ)` or `δ = θ'(λ)` on trees — the two folds do
not merely decouple, they order trees discordantly.

*Proof.*  Values: `t₁` is the depth-4 comb (`λ = δ + 1 = 5`);
`δ(t₂) = 1 + max(2,2) = 3`, `λ(t₂) = 3 + 3 = 6`.  Reversal: `4 > 3`,
`5 < 6`.  Minimality: a reversal needs `λ(u) < λ(v)`, `δ(u) > δ(v)`.
For `λ(v) ≤ 5`: all trees with `λ ≤ 4` have `δ = λ − 1`, so among them
`δ` and `λ` are concordant; a `v` with `λ(v) = 5` has `δ(v) ∈ {3, 4}`,
and a `u` with `λ(u) ≤ 4` has `δ(u) = λ(u) − 1 ≤ 3`, so `δ(u) > δ(v)` is
impossible.  For `λ(v) = 6`: `δ(v) = 3` is the minimum possible depth at
6 leaves (depth ≤ 2 trees have `λ ≤ 3`, so a 6-leaf tree of depth ≤ 2 is
impossible; the `3+3` split attains 3), and `u` must then have
`δ(u) = 4`, `λ(u) = 5`: the depth-4 combs.  ∎

**Corollary 5.5 (event-level fold divergence).**  Define the **size
grading** `g_λ(link p) := 2λ(pair p) − 2`, `g_λ(resolve p) := 2λ(pair p)
− 1`.  Then both `h` (Lemma 2.5) and `g_λ` are strictly monotone
ℕ-gradings of `D`; on `D_4` they coincide up to the constant 2
(`λ = δ + 1` there, so `g_λ = h + 2`) — in particular they induce the
same strata on the level-≤2 zone — and on `D` they are discordant:

    E₁ := resolve c(t₁):  h = 7,  g_λ = 9
    E₂ := resolve c(t₂):  h = 5,  g_λ = 11

(`t₁, t₂` from Theorem 5.4; `E₁, E₂` are `D`-incomparable by Lemma
2.2(iv), neither tree a subterm of the other).  No strictly monotone
reparametrization of ℕ carries one grading to the other.

*Proof.*  Strict monotonicity of `g_λ`: along (g1) the step is `+1`;
along (g2), `resolve q ≺ link p` with `pair q` an endpoint of `p` gives
`λ(pair p) = λ(pair q) + λ(other) > λ(pair q)`, so
`g_λ(link p) − g_λ(resolve q) = 2λ(other) − 1 > 0`; strictness propagates
to the transitive closure.  The rest is arithmetic from Theorems 5.3–5.4
and Lemma 2.5.  ∎

So "the natural ℕ-folds agree up to level 2 and provably diverge at level
3" (SPEC Q2, second clause) is Theorem 5.3 + Corollary 5.5, with the
explicit level-3 witness `((ab)(a(ab)))` — the same tree as `ℓ*`'s
composite — and the divergence is irreparable by rescaling (Theorem 5.4).

---

## 6. Q3 — the category of gradings and the universal object

### 6.1 What a grading must be (the design choice, made explicit)

A "grading" or "layer assignment" of the process must at minimum respect
causality.  Three nested compatibility strengths present themselves:

- **(G0) monotone**: `e ≤_D f ⟹ g(e) ≤ g(f)`.  Too weak alone: constant
  maps qualify; but see Remark 6.8 — the universal result is the same.
- **(G1) strict**: `e <_D f ⟹ g(e) < g(f)`.  This is the pinned notion:
  ORIGIN_RAW §8's events are *pure single happenings*; a layer assignment
  in which some event fails to advance past its strict causes conflates
  cause with effect.  Both event sorts are treated identically (each
  advances); no extra sort-compatibility datum is needed — by Lemma
  2.4(i) `link p ⋖ resolve p`, so any strict grading automatically
  separates the two events of each pair, and by Lemma 2.5 the sorts
  alternate with parity in the canonical grading.
- **(G2) unit-step**: increments exactly 1 along generators (§3) or
  covers (§4).  This is the lockstep semantics — **refuted** on `D` by
  Theorems 3.5 and 4.1; it survives only on truncations (`D_4`, resp.
  `D_6`).

**Definition 6.1 (the category of gradings).**  `Grad(D)` has as objects
the pairs `(S, g)` with `S` a poset and `g : D → S` strict monotone
(G1), and as morphisms `(S, g) → (S', g')` the monotone maps `h : S → S'`
with `h ∘ g = g'`.  Full subcategories: `LinGrad` (targets are linear
orders — "number scales" in the widest sense, including all ordinals),
`NGrad` (target `ℕ`), `RankGrad(P)` / `StratGrad(P)` (the unit-step
variants of §4 / §3 on a downset `P`).

`Grad(D)` is the coslice (under-) category of `D` in posets-with-
monotone-maps, restricted to strict objects; the following triviality is
therefore stated only to be immediately weighed.

**Theorem 6.2 (universal object).**  `(D, id_D)` is initial in
`Grad(D)`: for every grading `(S, g)` there is exactly one morphism
`(D, id) → (S, g)`, namely `g` itself.

*Proof.*  `id` is strict monotone; a morphism `h` must satisfy
`h ∘ id = g`, so `h = g`, which is a legitimate morphism (monotone,
since strict monotone implies monotone).  ∎

**On its own this is deflationary** — in any coslice category the
identity is initial; the statement would be true of *every* poset and
carries no information about `D`.  SPEC Q3 demands the additional content
that makes "the universal grading is D itself" a *finding*.  That content
is Theorems 6.3–6.6: the numeric subcategories are empty or
universal-object-free, so the initial object of `Grad(D)` genuinely
cannot be pushed into any number scale without loss — for *this* poset
the coslice triviality is the whole truth, and that is the theorem.

### 6.2 No number scale is canonical

**Theorem 6.3 (chain-valued gradings have no universal object, either
way).**  `LinGrad` has no initial object and no terminal object.  The
same holds for `NGrad`, and `Grad(D)` itself has no terminal object.

*Proof.*  Recall ([OI] Thm 7.1(ii), Lemma 7.2): natural labelings — the
position functions of maximal runs — are strict monotone *injections*
`D → ω`, and for any `D`-incomparable `e, f` there are natural labelings
`ℓ₁, ℓ₂` with `ℓ₁(e) < ℓ₁(f)` and `ℓ₂(f) < ℓ₂(e)`.

*No initial object.*  Suppose `(L₀, g₀)` initial in `LinGrad` (or
`NGrad`).  Fix the incomparable pair `e := link{a,(ab)}`,
`f' := link{b,(ab)}`.  `L₀` is linear, so trichotomy on
`g₀(e), g₀(f')`:
if `g₀(e) < g₀(f')`, the morphism `h` to `(ω, ℓ₂)` (with
`ℓ₂(f') < ℓ₂(e)`) gives `ℓ₂(e) = h(g₀(e)) ≤ h(g₀(f')) = ℓ₂(f')`,
contradiction; symmetrically for `>` via `ℓ₁`; if `g₀(e) = g₀(f')` then
`ℓ₁(e) = ℓ₁(f')`, contradicting injectivity of a labeling.

*No terminal object (also in `Grad(D)`).*  Suppose `(S, g₁)` terminal.
Take the triple `e = link{a,(ab)}`, `m = link{b,(ab)}`,
`f = resolve{a,(ab)}`: here `e <_D f`, while `m` is `D`-incomparable to
both (`(a(ab))` and `(b(ab))` are ⊴-incomparable and neither pair's tree
is a subterm of the other's — Lemma 2.2(iv)).  For each of the pairs
`(e,m)` and `(m,f)` pick labelings scheduling them both ways; the
morphisms from those four labelings to `(S, g₁)` give
`g₁(e) ≤ g₁(m) ≤ g₁(e)` and `g₁(m) ≤ g₁(f) ≤ g₁(m)`, so
`g₁(e) = g₁(m) = g₁(f)` — contradicting strictness `g₁(e) < g₁(f)`.  ∎

**Theorem 6.4 (unit-step numeric gradings: empty beyond the zone).**
`StratGrad(F) = ∅` for every downset `F ∋ ℓ*` (Theorem 3.5) — in
particular for `D` and every `D_n`, `n ≥ 5`; `RankGrad(P) = ∅` for every
downset `P ∋ E*` (Theorem 4.1) — in particular for `D` and every `D_n`,
`n ≥ 7`.  Conversely `StratGrad(D_4) ≠ ∅` and `RankGrad(D_6) ≠ ∅`, both
inhabited exactly by `c + h` (Theorems 3.3, 4.2).  So unit-step
natural-number layers exist precisely on the initial truncations, and
there they are unique up to the constant.

**Theorem 6.5 (the least numeric grading, and its failure).**  Among
strict monotone `g : D → ℕ` normalized by `g(⊥) = 0`, the height `h` is
pointwise least: `g(e) ≥ h(e)` for all `e`.  But:

(i) `(ω, h)` is **not** initial in `NGrad`: for a natural labeling `ℓ`
there is no monotone `θ : ω → ω` with `θ ∘ h = ℓ`, since
`h(link{a,(ab)}) = 2 = h(link{b,(ab)})` while `ℓ` separates them.

(ii) `h` is not a rank function, with *unbounded* cover-defect
(Theorem 4.1, Proposition 4.3): its layers are not generations — a
height-6 element (`E*`) has an immediate cause at height 3.

*Proof of leastness.*  Take a chain of maximum length `h(e)` with top
`e`; its bottom is `⊥`, since `⊥` is the unique minimal element of `D`
and a maximal chain descends to a minimal element.  `g` increases
strictly along the chain's `h(e)` steps from `g(⊥) = 0`, so
`g(e) ≥ h(e)`.  ∎

**Lemma 6.6 (the numeric dilemma: fold or gauge).**  Let `(L, g)` be any
chain-valued grading of `D`.  Then exactly one of:

(i) `g` is non-injective — it conflates `D`-distinct events (a genuine
fold, losing order information); or

(ii) `g` is injective — and then `g` is **not** `σ`-invariant (it breaks
the atom-swap symmetry: `g ∘ σ ≠ g`), and the pair `(L, g)`, `(L, g∘σ)`
are two isomorphic gradings that order the incomparable pair
`link{a,(ab)}, link{b,(ab)}` oppositely — the injective numeric reading
is a *gauge choice*, not an invariant.

*Proof.*  If `g` injective: `σ` swaps `link{a,(ab)} ↔ link{b,(ab)}`
([OI] §8.2), so `g(σ(link{a,(ab)})) = g(link{b,(ab)}) ≠ g(link{a,(ab)})`
by injectivity, whence `g ∘ σ ≠ g`; `g ∘ σ` is again strict monotone
(`σ` is an automorphism), and since `L` is a chain, `g` and `g ∘ σ` order
the two events oppositely iff they order them at all — injectivity
forces strict order both times, in swapped directions.  ∎

**Theorem 6.7 (the (depth, size) multigrading does not separate D).**
Let `M(e) := (kind(e), δ(tree(e)), λ(tree(e))) ∈ {link, resolve} × ℕ ×
ℕ`, ordered componentwise on the numeric part.  Then `M` is strictly
monotone in the product order (both folds are strict gradings, Corollary
5.5), but:

(i) `M` is not injective, already for symmetry reasons: `M` is
`σ`-invariant, and `σ` moves e.g. `link{a,(ab)}`.

(ii) `M` is not injective *beyond* symmetry: `resolve c((a(a(a(ab)))))`
and `resolve c((a(b(a(ab)))))` have equal `M`-value
`(resolve, 4, 5)` but lie in different `σ`-orbits (the swap of the first
is `resolve c((b(b(b(ab)))))`).

(iii) The fibers grow without bound: the `2^{k−1}` combs of depth `k`
all share `M`-value `(·, k, k+1)`, so the fiber over it has `2^{k−1}`
events of each kind.

(iv) No family of `σ`-invariant folds whatsoever separates `D` (any
`σ`-invariant map conflates each 2-element `σ`-orbit); separation
requires breaking the swap symmetry, i.e. a gauge (Lemma 6.6(ii)).

*Proof.*  (i) `δ, λ`, and kind are defined tree-recursively with symmetric
clauses, hence `σ`-invariant.  (ii) Both trees are depth-4, 5-leaf combs;
distinctness and non-orbit by inspection.  (iii) Combs of depth `k`:
choose the added atom at each of the `k−1` wraps above `(ab)`:
`2^{k−1}` trees (matches the by-hand counts 1, 2, 4, 8 for
`k = 1..4` used in §7).  (iv) Immediate.  ∎

### 6.3 The resolution of ORIGIN_RAW §10

> *"Then, if strata are to be assigned above that, research
> mathematically which number scale (or scales) would be appropriate."*

The computation is now complete, and the honest answer has four clauses.

**(a) Why natural numbers worked below.**  Up to the level-2 zone — in
fact up to `D_4` — all candidate layer assignments coincide in one
ladder: stratification = rank = height = size-shift = generation
(Theorems 3.3, 4.2, Prop 5.2, Cor 5.5), and the zone's Hasse diagram is a
tree with unit covers (Prop 3.4).  The experience "natural-number strata
work to level 2" is the theorem that on `D_3` (and even `D_4`) the
unit-step grading exists and is unique.

**(b) No number scale above — as impossibility, not failure to find.**
The lockstep stratification dies at `ℓ* = link{(ab),(a(ab))}` (λ=5,
Theorem 3.5); the rank function dies at `E*` (λ=7, Theorem 4.1) with
unbounded defect (Prop 4.3); the candidate numeric folds diverge at the
same first tree `((ab)(a(ab)))` and eventually order events oppositely
(Theorems 5.3–5.4, Cor 5.5).  **Ordinals do not help**: an ordinal-valued
grading is chain-valued, so Theorem 6.3 applies; moreover `ω` already
*suffices* for existence (natural labelings), so larger ordinals add
nothing — the obstruction is linearity itself, not the supply of numbers.
And no chain-valued grading is canonical: no initial, no terminal object
(Theorem 6.3); each individual one is either a lossy fold or a
symmetry-breaking gauge (Lemma 6.6).

**(c) The universal grading is the order itself.**  `(D, id)` is initial
in `Grad(D)` (Theorem 6.2).  This is contentful — not the coslice
tautology — precisely in conjunction with (b): for a *graded* poset the
initial grading factors as (poset) ≅ (rank fibration over ℕ) and a number
scale tells the whole story of layers; for `D` this is provably
impossible (RankGrad(D) = ∅), every chain shadow strictly loses
(Theorem 6.7(iii): fibers of the best numeric folds blow up doubly
exponentially — §7), and the finest numeric approximation `h` is least
but not universal and not a stratification (Theorem 6.5).  So "which
number scale grades the layers above level 2?" has the computed answer:
**none — above level 2 the grading *is* the causal partial order, and
every numeric scale is either a strictly lossy fold of it or an arbitrary
linearization gauge.**  What survives of "layers" is exactly the height
`h` (the least numeric fold, with layer widths computed in §7) — usable
for bookkeeping, provably not for generation semantics.

**(d) Scope and honesty.**  The theorems above are relative to the pinned
category (Definition 6.1).  Robustness checks, proved: with (G0) in place
of (G1) the initial object is still `(D, id)` (same one-line proof) and
the terminal object becomes the trivial one-point grading — confirming
that strictness is what makes "grading" nondegenerate; requiring
surjectivity of `g` changes nothing (id is surjective; the proofs of
Theorem 6.3 use only composition).  What is *not* proved and is left as
the residual open part of the full universal-property claim:

**Conjecture 6.8 (rigidity of the universal object).**
`Aut(D) = {id, σ}`.  If true, the universal grading is canonical up to
exactly the one forced symmetry (the atom swap of SPEC C2), and "no
scale; the order itself" closes with no hidden gauge freedom inside `D`
itself.  Status: conjecture.  What is proved toward it: every
automorphism preserves height, hence (Lemma 2.5) preserves kind (parity)
and composite-depth; hence it induces a ⊴-automorphism on composite trees
(via `resolve c(t) ↦ resolve c(t')`, Lemma 2.2(iv)); on
subterm-incomparable-children links, the child pair is recoverable from
the two lower covers (Lemma 2.4(ii)), forcing tree-recursion; the missing
step is rigidity at subterm-*comparable* links, where one cover is a
chord and the recursion is not directly forced.  Nothing else in this
file depends on the conjecture.

---

## 7. Layer widths of the height grading

Write `W_j := #{e ∈ D : h(e) = j}` (well-defined by Lemma 2.5), and for
the truncations `W_j(D_n)` likewise.  Let

    N_d := #{t : δ(t) = d, t composite},   G_d := #{t : δ(t) ≤ d}   (atoms included in G).

**Theorem 7.1 (widths = depth-census, doubled).**  For all `m ≥ 0`:

    W_{2m} = W_{2m+1} = N_{m+1},

and the same holds in each `D_n` with the census restricted to
`λ ≤ n`.  (The equal link/resolve pairs of widths observed in E3 are
structural: heights `2m` and `2m+1` hold the link and resolve events of
the same composites — Lemma 2.5.)

*Hand verification of the E3 table.*  `n = 2`: composites of `λ ≤ 2`:
`(ab)` (δ=1): widths `{0: 1, 1: 1}` ✓.  `n = 3`: add `(a(ab)), (b(ab))`
(δ=2): `{2: 2, 3: 2}` ✓.  `n = 4`: add the four λ=4 combs (δ=3):
`{4: 4, 5: 4}` ✓.  `n = 5`: λ=5 trees: eight combs (δ=4) and the two
`2+3` splits (δ=3): depth-3 census becomes `4 + 2 = 6`, depth-4 census
8: `{4: 6, 5: 6, 6: 8, 7: 8}` ✓.  All four rows match `RESULTS.md` E3
exactly.

**Theorem 7.2 (recurrences; the lockstep tower).**

    G_0 = 2,        G_{d+1} = C(G_d, 2) + 2;
    N_1 = 1,        N_{d+1} = N_d · G_{d−1} + C(N_d, 2)      (d ≥ 1),

with `N_d = G_d − G_{d−1}`.  Values (hand-computed):

    G_d (d = 0..6):  2, 3, 5, 12, 68, 2280, 2598062
    N_d (d = 1..6):  1, 2, 7, 56, 2212, 2595782

*Proof.*  By Prop 5.1, `{δ ≤ d+1} = G_{d+1}-set = atoms ∪ {pair{x,y} : x
≠ y ∈ G_d-set}`; the pairs are pairwise distinct and distinct from atoms
(T1, T2), and every composite already in the `G_d`-set is a pair of
`G_{d−1}`-elements ⊆ `G_d`-set, so the union is exhaustive and
`G_{d+1} = C(G_d, 2) + 2` exactly.  A composite of depth exactly `d+1`
has children of max-depth exactly `d`: either one child of depth `d` and
one of depth `< d` (`N_d · G_{d−1}` choices) or two distinct children of
depth `d` (`C(N_d, 2)`).  Injectivity (T1) makes these counts exact.  ∎

**Theorem 7.3 (classical identification of the counting sequences).**
All OEIS identifications below were verified against OEIS directly
(lookups on 2026-07-06); the recurrence-level claims are proved, not
pattern-matched.

(i) **By size** (trees with `λ = n`): the sequence
`t(n) = 2, 1, 2, 4, 10, 25, 68, 187, …` is **OEIS A063894** (unique OEIS
match; the entry's own description — binary trees over two atoms `x, y`
closed under pairing of *distinct* preceding terms — is exactly the
SPEC §1 carrier).  Proof-level anchor: our count satisfies A063894's
defining recurrence

    t(1) = 2,  t(n) = Σ_{i<j, i+j=n} t(i) t(j) + [n = 2k] C(t(k), 2),

by unordered-split counting with distinct children (T1 exactness), and
the values through `n = 8` are hand-checked (`25 = 2·10 + 1·4 + C(2,2)…`
— concretely: `t(6) = t(1)t(5) + t(2)t(4) + C(t(3),2)` = `20 + 4 + 1 =
25`; `t(7) = 2·25 + 1·10 + 2·4 = 68`; `t(8) = 2·68 + 25 + 20 + C(4,2) =
187`).

(ii) **By depth** (the height-layer widths): `N_d = 1, 2, 7, 56, 2212,
2595782, …` is **OEIS A103410** ("number of products of distinct
elements in generation n, starting with two elements" — again literally
this system: commutative pairing, self-pair excluded, two generators;
its posted formula is exactly the `N`-recurrence of Theorem 7.2)
**= OEIS A002658** (planted 3-trees of height `n`; free *one*-generator
commutative non-associative algebra, self-pair allowed, by height):
`N_d = A002658(d)` for `d ≥ 1`.

(iii) **The two-generator/one-generator coincidence in (ii) is a
theorem**, not numerology.  A002658 is defined by `a(0) = a(1) = 1`,
`a(n+1) = a(n)(a(0) + … + a(n−1)) + a(n)(a(n)+1)/2`.  Claim:
`N_d = a(d)` for `d ≥ 1`.  Induction with the auxiliary invariant
`G_{d−1} − 1 = Σ_{i=0}^{d−1} a(i)`: base `N_1 = 1 = a(1)`,
`G_0 − 1 = 1 = a(0)`; step:

    a(d+1) = a(d)·(Σ_{i<d} a(i)) + C(a(d), 2) + a(d)
           = N_d·(G_{d−1} − 1) + C(N_d, 2) + N_d
           = N_d·G_{d−1} + C(N_d, 2) = N_{d+1},

and `G_d − 1 = (G_{d−1} − 1) + N_d = Σ_{i≤d} a(i)`.  ∎  (Interpretation:
losing the second atom is exactly compensated by gaining the self-pair —
the one-generator algebra's `x·x` plays the role of the second atom's
pairings.  We record this as an observed structural coincidence with a
two-line proof; no deeper bijection is claimed.)

(iv) **Cumulative depth-census**: `G_d = A108225(d+1)`.  A108225 is
defined by `b(0) = 0, b(1) = 2`,
`b(n) = (b(n−1) + b(n−2))(b(n−1) − b(n−2) + 1)/2`.  Claim: with
`b(d+1) = G_d`, the two recurrences coincide along the orbit: writing
`g = G_d`, `p = G_{d−1}`,

    (g + p)(g − p + 1)/2 = C(g+1, 2) − C(p, 2) = [C(g,2) + g] − C(p,2),

and since `g = C(p, 2) + 2` (Theorem 7.2), `g − C(p,2) = 2`, so the
right side is `C(g, 2) + 2 = G_{d+1}`.  ✓  Base: `b(1) = 2 = G_0`,
`b(2) = (2+0)(2−0+1)/2 = 3 = G_1`.  ∎  (Verified against OEIS data
through `b(7) = 2598062 = G_6`.)

(v) **The wrong classical candidate, for the ledger**: the
Wedderburn–Etherington numbers **A001190** (unordered binary trees, one
atom, *equal children allowed*: recurrence with `C(t(k)+1, 2)` at even
sizes and `t(1) = 1`) differ from (i) on both defining counts — the SPEC
carrier has two distinguishable atoms (C2) and forbids self-pairs (C4:
`C(t(k), 2)`, not `C(t(k)+1, 2)`).  A001190 begins `1, 1, 1, 2, 3, 6,
11, 23`; ours begins `2, 1, 2, 4, 10, 25, 68, 187`.  The correct
classical anchors are A063894 (size) and A103410/A002658 (depth).

(vi) **Derived, not new**: the E3 node counts `|D_n| = 0, 2, 6, 14, 34 =
2 · Σ_{m=2}^{n} t(m)` (two events per composite) — a transform of
A063894, correctly reported by the enumerator as having no independent
OEIS entry.  The per-height width sequence itself,
`1, 1, 2, 2, 7, 7, 56, 56, …`, is the 2-fold repetition of A103410
(shifted); it has no separate OEIS entry (checked), and needs none given
(ii).  The enumerator's two remaining unmatched sequences (states per
`k`, runs per `k`) belong to the state-lattice, not to `D`'s layer
structure, and are outside this file's scope.

**Theorem 7.4 (growth: doubly exponential by depth, singly exponential
by size).**

(i) For `d ≥ 3`:  `4 · 3^{2^{d−3}} ≤ G_d ≤ 12^{2^{d−3}}`, hence
`log G_d = Θ(2^d)`; and `G_{d−1} ≤ 2√G_d`, so
`N_d = G_d − G_{d−1} = G_d (1 − o(1))`: the height-layer widths
`W_{2m} = N_{m+1}` are doubly exponential in the height.

(ii) For `n ≥ 2`:  `2^{n−2} ≤ t(n) ≤ 8^n`, so `log t(n) = Θ(n)`: the
size-layer widths are singly exponential.

(iii) Consequently the two strict ℕ-gradings `h` and `g_λ` of Corollary
5.5 are not even growth-compatible: no relabeling of layers matches a
doubly-exponential width profile to a singly-exponential one.  This is
the quantitative face of the fold divergence — and of Theorem 6.7(iii)'s
unbounded fibers.  Moreover the two layer systems interleave rather than
refine one another: the depth-3 layer meets the size-layers 4, 5 and 6,
and the size-6 layer meets the depth-layers 3, 4 and 5 — neither fold
factors through the other.  (Note: the naive "top of the λ-range at
depth `d` is the full binary tree with `2^d` leaves" is *false* in this
carrier — `((ab)(ab))` and its like are excluded by the distinct-children
constraint C4/T1; `2^d` remains a valid upper bound, but the maximum is
smaller, e.g. 3 at depth 2, 6 at depth 3, 11 at depth 4.)

*Proof.*  (i) For `g ≥ 2`: `g²/4 ≤ C(g,2) + 2 ≤ g²` (lower:
`2g² − 2g + 8 ≥ g² ⟺ (g−1)² + 7 ≥ 0`; upper: `g² + g − 4 ≥ 0` for
`g ≥ 2`).  With `G_3 = 12`: upper, `G_{d+1} ≤ G_d²` iterates to
`G_d ≤ 12^{2^{d−3}}`; lower, `G_{d+1}/4 ≥ (G_d/4)²` iterates to
`G_d/4 ≥ 3^{2^{d−3}}`.  From `G_d ≥ G_{d−1}²/4`: `G_{d−1} ≤ 2√G_d`.
(ii) Lower: the `2^{n−2}` combs of size `n` (Theorem 6.7(iii) with
`k = n − 1`).  Upper: the number of unordered trees with `n` leaves is at
most the number of ordered leaf-labeled binary trees,
`Catalan(n−1) · 2^n ≤ 4^{n−1} · 2^n < 8^n` — the map (unordered tree) ↦
(a fixed ordered representative with its leaf word) is injective.
(iii) The memberships: depth-3 trees of sizes 4, 5, 6 are, respectively,
the four combs `(x(y(ab)))`, the `2+3` splits `((ab)(a(ab)))`,
`((ab)(b(ab)))`, and the `3+3` split `((a(ab))(b(ab)))` (Theorems 5.3 and
4.2's case lists).  Size-6 trees of depths 3, 4, 5: the `3+3` split
(depth 3); `((ab)(x(y(ab))))` or `(z((ab)(a(ab))))` (depth 4); an atom
paired with a depth-4 comb (depth 5).  Depth-2 maximum: children distinct
with the deeper in `{(ab)}` and the other an atom, so `λ ≤ 3`; depth-3:
children among depth-≤2 trees, maximal distinct pair `(a(ab)), (b(ab))`,
`λ = 6`; depth-4: maximal pair `((a(ab))(b(ab)))` (the unique λ-6 depth-3
tree) with a λ-5 depth-≤3 tree, `λ = 11`.  ∎

**Remark 7.5 (reconciliation with ORIGIN_RAW §5).**  The lockstep tower
`|G_k| = 2, 3, 5, 12, 68, 2280, …` — the object-count the §5 procedure
would generate stage by stage — is exactly the cumulative census of the
height grading (Prop 5.1 + Theorem 7.2), confirmed against A108225.  So
the lockstep *cardinalities* are real (they are the width partial sums of
the invariant grading `h`); what is unreal is the lockstep's claim that
the stage structure is intrinsic — the stage function cannot be extended
to the events without either skipping (height, Theorem 6.5(ii)) or
contradiction (stratification, Theorem 3.5).  ORIGIN_RAW §6's suspicion
("the whole marching in lockstep" — a tension) is thereby made exact:
the foliation is consistent as a *count*, inconsistent as a *causal
stage assignment*, from λ = 5 onward.

---

## 8. Consolidated statement of the Q2/Q3 answers

**Q2 (as three theorems).**  On the causal poset `D` of the asynchronous
distinction system:

1. *Stratification* (unit steps along generators — the lockstep/§5
   semantics): exists on a downset iff it contains no skew link; unique
   `= c + h` where it exists; works on the level-≤2 zone `Z = D_3` (and
   `D_4`); **first failure** `ℓ* = link{(ab),(a(ab))}`, composite
   `((ab)(a(ab)))`, λ = 5 — the first event linking two composites, both
   of which are level-≤2 objects.  [Theorems 3.3, 3.5; Prop 3.4]
2. *Rank function* (unit steps along covers): **does not exist** on `D`;
   `D_n` graded iff `n ≤ 6`; first failure the four λ = 7
   skew-incomparable links, canonically `E* = link{(a(ab)),(a(b(ab)))}`,
   with saturated `⊥`-chains of lengths 4 and 6; the defect is unbounded.
   Height exists always, strictly monotone, pointwise-least, not a rank.
   [Theorems 4.1, 4.2; Prop 4.3]
3. *Fold divergence*: `gen = depth` identically; `depth, size` lock into
   the single ladder `λ = δ + 1` on all nine trees with `λ ≤ 4`
   (including the five level-≤2 objects) and **diverge at**
   `((ab)(a(ab)))` (λ = 5, δ = 3); they eventually order trees oppositely
   (`(a(a(a(ab))))` vs `((a(ab))(b(ab)))`), so no monotone rescaling
   reconciles them; at event level, `h` and `g_λ` are discordant strict
   ℕ-gradings agreeing (up to shift) on `D_4`.  [Prop 5.1–5.2, Theorems
   5.3–5.4, Cor 5.5]

**Q3 (as a computation).**  In the category of strict poset-valued
gradings of `D`: initial object `(D, id)`; no terminal object; the
chain-valued subcategory has neither initial nor terminal object; the
unit-step numeric subcategories are empty (on all of `D`) and inhabited
uniquely by height on the truncations `D_4`/`D_6`; the least ℕ-grading is
height, which is not initial and not a stratification; every chain
grading is a lossy fold or a symmetry-breaking gauge; the (depth, size)
multigrading is strict but non-separating with doubly-exponentially
growing fibers.  **Answer to §10: no number scale — the universal
grading is the causal order itself, and the theorems above are exactly
what make that answer contentful rather than tautological.**  Residual
open point: rigidity `Aut(D) = {id, σ}` (Conjecture 6.8).

---

## 9. Ledger entries (classical concepts relied on in this file)

| Internal term | Nearest classical object | Theorems imported / reproduced |
|---|---|---|
| height `h`, rank function, graded poset, saturated chain, cover vs chord | graded posets (Stanley, EC I §3.1); transitive reduction | "graded ⟺ all saturated ⊥-chains to each element equal-length" (reproved inline); rank forced along covers |
| stratification (Def 3.1) | potential/grading on a DAG; consistent labeling of a precedence graph | existence ⟺ all source-to-node path lengths equal (reproved as Thm 3.3 via minimal counterexample) |
| `Grad(D)`, initial/terminal object | coslice (under) category; universal properties | initiality of identity in a coslice (trivial; flagged); non-existence proofs are bespoke |
| natural labelings as gradings | linear extensions; order-preserving bijections to ω | imported from [OI] Thm 7.1(ii), Lemma 7.2 |
| `σ`-gauge dilemma (Lemma 6.6) | symmetry breaking; invariant maps constant on orbits | elementary group action on a poset |
| tree counts by size | OEIS **A063894** (two atoms, distinct unordered children); g.f. `A(x) = 1 − √(1 − 4x + A(x²))` (Somos) | recurrence proved from T1; values hand-checked to n = 8; OEIS unique match |
| tree counts by depth (layer widths) | OEIS **A103410** = **A002658** (planted 3-trees by height; one-generator free commutative magma) | `N`-recurrence proved; two-generator/one-generator equality proved by recurrence induction (Thm 7.3(iii)) |
| cumulative census | OEIS **A108225** | recurrence equivalence proved along the orbit (Thm 7.3(iv)) |
| rejected candidate | Wedderburn–Etherington **A001190** | differs on both defining counts (atoms, self-pair); recorded to preempt misidentification |
| doubly exponential growth | quadratic-map recurrences (Aho–Sloane 1973, "Some doubly exponential sequences") | sandwich `4·3^{2^{d−3}} ≤ G_d ≤ 12^{2^{d−3}}` proved inline |
| comb / caterpillar trees | path-like binary trees | `2^{k−1}` count; `λ = δ + 1` on combs |
| level = generation | breadth-first closure stages of an inductive datatype | `gen = depth` (Prop 5.1) |

Machine/data provenance: OEIS entries A063894, A108225, A103410, A002658,
A001190 fetched and checked 2026-07-06; the enumerator's E3/E4 tables were
re-derived by hand (§2.4, §7.1); no theorem in this file rests on
computation.

---

## 10. Proof status

Fully proved at referee bar (no gaps known to the author): Lemmas 2.1,
2.2, 2.4, 2.5, 6.6; Corollaries 2.3, 2.6, 5.5; Propositions 3.4, 4.3,
5.1, 5.2; Theorems 3.3, 3.5, 4.1, 4.2, 5.3, 5.4, 6.2, 6.3, 6.4, 6.5,
6.7, 7.1, 7.2, 7.3 (i)–(vi), 7.4; Remarks 4.4, 4.5, 7.5 (the remarks'
mathematical claims are proved where stated).

Flagged, not papered over:

1. **Conjecture 6.8** (`Aut(D) = {id, σ}`) is the only conjecture, and it
   is confined — per the task's rigor bar — to the full
   universal-property claim (rigidity of the universal object).  The
   ℕ-impossibility core (Theorems 3.5, 4.1, 4.2, 6.3, 6.4) is complete
   and does not use it.
2. **Category choice** (Definition 6.1) is a pinned design decision, with
   the (G0)/(G1)/(G2) alternatives analyzed and the robustness of the
   universal object under (G0) and under surjectivity restriction proved
   in §6.3(d).  A refuter who prefers a different morphism class should
   check Theorem 6.3's proofs, which use only: natural labelings exist,
   both orders of an incomparable pair are realized, and composition
   with monotone maps.
3. **Theorem 7.3(iii)**'s one/two-generator coincidence is proved as a
   recurrence identity; a bijective explanation is *not* claimed and
   would be a nice small further result.
4. **Not attempted here**: Lean mechanization (the intended interface:
   the height formula of Lemma 2.5 and the two saturated chains of
   Theorem 4.1 are finite objects, directly checkable; Theorem 3.3 and
   6.3 need the [OI] infrastructure first); the state-lattice sequences
   (E1 states/runs per `k`), which grade the *downset lattice*, not `D`,
   and belong to a separate deliverable.
