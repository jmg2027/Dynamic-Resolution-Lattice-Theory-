# F-ev — the event-primary formalization (design, task M2)

**Status**: design deliverable for SPEC §1 (F-ev) and question Q4.
**Inputs**: `rederive/SPEC.md`, `seed/ORIGIN_RAW.md` (§2, §3, §5–§8),
`seed/ORIGIN.md`, the program memo.  Nothing else from the repository.
Classical mathematics used freely; every classical concept relied on is
recorded in §12 for the bilingual ledger.

---

## 1. Requirements extracted from the raw text

From ORIGIN_RAW and SPEC §1 (F-ev paragraph), the design must satisfy:

- **R1 (events are the carrier).**  The inhabitants of the carrier are
  distinction-events, not "somethings".  (§2: "`a`, `b` … are not
  objects (objects are not defined yet); only the difference is.")
- **R2 (atoms are not elements).**  `a` and `b` must not be carrier
  inhabitants.  Whatever residue of them remains must be *sub-carrier*:
  a role inside the primordial contrast, not a thing alongside it.
- **R3 (the primordial element is the first distinction).**  The one
  element constructible with no prior event is the first distinction
  itself — the contrast that catches `a` against `b` (§2, §3).
- **R4 (points are derived).**  A "point" is a completed distinction
  playing the role of an operand for further distinctions (§8 Event 1:
  a line resolves into a point; SPEC §2 pins the point to *be* the
  reified contrast).
- **R5 (two event kinds, asynchronous).**  Exactly the two pure events
  of §8, with no global clock; a state must not smuggle staging (§6).
- **R6 (Lean-implementable, axiom-free, no quotients).**  Everything
  below must compile to Lean 4 core with `#print axioms` empty; in
  particular no `Quot`, no `propext`, no `Classical.choice`.  Unordered
  pairs must therefore be handled by canonical representatives, not by
  quotienting.

---

## 2. Candidate designs

### 2.1 Design E — distinctions-as-edges over a derived vertex set

Two mutually defined sorts: a vertex sort `V` and an edge sort `E`.

```
V ::= poleA | poleB | node (e : E)      -- node e = the reification of e
E ::= edge (u v : V), u ≠ v, unordered
```

The primordial edge is `edge poleA poleB`.  The dynamics is a growing
graph whose edge set is "primary".

*Assessment.*  This is F-obj in light disguise.  `V` is a genuine
first-class sort and the two poles are **elements of it** — R2 fails in
letter (atoms are elements of a carrier sort, merely a differently
named one).  The mutual definition also means neither sort is prior:
`E` mentions `V` and `V` mentions `E`, so the claimed primacy of events
is bookkeeping, not structure.  In Lean the mutual inductive plus a
mutual comparison function for canonicalization is heavier than
necessary.  The design would make Q4 nearly definitional and therefore
teach nothing: the translation `V ≅ Tree` is immediate, and no
asymmetry could surface because none was risked.

### 2.2 Design S — sides as operands (the pole-free attempt)

Push R2 to the limit: *no* pole constructors anywhere.  Operands of a
distinction are **sides of earlier distinctions**:

```
Operand ::= side (d : Ev) (s : Left | Right) | done (d : Ev)
Ev      ::= prim | mk (u v : Operand), u ≠ v, unordered
```

Here `a := side prim Left`, `b := side prim Right`; the carrier's only
ground element is `prim`, which takes no operands at all — R2 and R3
maximally satisfied.

*Assessment — this design dies without quotients.*  In F-obj, the tree
`a` occurs as a child of both `pair{a,b}` and `pair{a, pair{a,b}}` —
*the same* `a`.  In Design S, "the left side of `prim`" and "the
left-operand role inside `mk (side prim Left) (done prim)`" are
distinct term-occurrences; to make later distinctions take *the same*
`a` twice, the design must identify side-occurrences across terms.
That identification is exactly a quotient (occurrence-identity is an
equivalence relation on positions, not a subterm relation), and R6
forbids quotients.  The only quotient-free repair is to designate a
canonical occurrence — "`a` *is* the left side of `prim`" — which
reintroduces two distinguished global tags.  Those tags are poles.

> **Finding (first-class).**  Operand-identity across distinct
> distinction-terms is not derivable event-internally: any quotient-free
> event-primary formalization must carry the two-ness of the primordial
> contrast as *global tags* (poles).  The two-ness of `a`/`b` cannot be
> eliminated from the formalization; it can only be relocated from
> carrier elements (F-obj) to sub-carrier roles (F-ev).  Design S is
> the proof-by-failure.

### 2.3 Design P — distinction-terms over poles + earlier distinctions (chosen)

Single carrier of distinction-terms.  An operand is either one of two
formal **pole tags** (the two roles of the primordial contrast — tags,
not carrier elements) or an **earlier distinction** (a completed
distinction in operand position = R4's derived point).

```
Pole    ::= l | r                              -- tags, not a carrier
Operand ::= pole (p : Pole) | done (d : Ev)    -- defined sum, not a new sort
Ev      ::= ⟨u, v⟩ for u ≠ v, unordered        -- the carrier
prim    := ⟨pole l, pole r⟩                    -- the first distinction
```

*Assessment.*  R1: the only carrier is `Ev`.  R2: poles are constructor
tags of a *defined* auxiliary sum, never inhabitants of `Ev`; there is
no sort of points.  R3: `prim` is the unique element constructible with
no `Ev` operand (see §4.4).  R4: "point" is definable, not primitive
(§5.2).  R6: single first-order inductive, canonical representatives by
term ordering (§4.2).  Chosen.

### 2.4 Comparison table

| Criterion | E (edges/vertices) | S (sides) | P (poles + terms) |
|---|---|---|---|
| Atoms not carrier elements (R2) | fails (poles ∈ `V`) | holds | holds (tags only) |
| Single carrier (R1) | no (two mutual sorts) | yes | yes |
| Quotient-free (R6) | yes, heavier | **no** | yes |
| Primordial element = first distinction (R3) | edge, but `V` co-primary | yes | yes |
| Risk content for Q4 | none (F-obj relabeled) | n/a (dies) | genuine asymmetries (§9) |

**Design P is adopted.**  Design E is retained only as the comparison
strawman; Design S is retained as the negative finding above.

---

## 3. The carrier, precisely

To stay first-order (no nested inductive through a sum), the operand
sum is flattened into three constructors.  Raw terms first, canonical
subtype second (this is the standard quotient-free treatment of
unordered pairs: fix a total term order, keep sorted representatives).

**Raw terms.**

```
Pole ::= l | r
Ev   ::= pp (p q : Pole)        -- both operands are poles
       | pe (p : Pole) (e : Ev) -- one pole, one earlier distinction
       | ee (d e : Ev)          -- two earlier distinctions
```

**Term order.**  A total, decidable, structural order `cmp : Ev → Ev →
Ordering` (lexicographic on constructor tag then components, with
`l < r`).  Poles sort before distinctions; this is the F-ev counterpart
of whatever tie-break F-obj's canonical `Tree` uses.

**Canonicity (`canon : Ev → Bool`).**

- `pp p q` canonical iff `p = l ∧ q = r` — the *only* canonical
  pole-pole term is `prim`.  (Distinctness `p ≠ q` and unorderedness
  both collapse into this one clause.)
- `pe p e` canonical iff `canon e` — always sorted (pole first), and
  distinctness is automatic: a pole-operand never equals a
  distinction-operand.
- `ee d e` canonical iff `canon d ∧ canon e ∧ cmp d e = lt` — sorted
  and strict, so self-pair `⟨x,x⟩` has **no canonical term at all**.

**Carrier.**  `D := { e : Ev // canon e = true }` (a subtype, not a
quotient).  `prim := ⟨pp l r, rfl⟩ : D`.

**Operands (defined, not a sort).**  `Operand := Pole ⊕ D`, with the
smart constructor

```
pair : (u v : Operand) → u ≠ v → D
```

which sorts its arguments and lands in the matching constructor.
`pair` is commutative by construction (`pair u v h = pair v u h.symm`)
and injective as a function of the unordered pair `{u, v}`.

**Remark (C4 upgraded from side condition to non-existence).**  In
F-obj, "no self-pair" is a hypothesis on the `pair` constructor.  In
F-ev it is carrier-level: the canonical carrier simply *contains no
term* whose two operands coincide.  The prohibition became a
non-existence.

---

## 4. Basic structure theorems of the carrier

### 4.1 Operand recovery

`operands : D → Operand × Operand` returning the sorted operand pair;
`pair (operands d).1 (operands d).2 _ = d`.  Distinct canonical terms
have distinct operand pairs (the F-ev counterpart of F-obj's "the two
children are recoverable").

### 4.2 No quotients used

Everything above is a first-order inductive, a Bool-valued structural
recursion, and a subtype.  `Subtype` equality over a decidable
`Bool`-equation needs no `propext` (the proof component is an `Eq` in
`Prop`, handled by `Subtype.ext` which is axiom-free in Lean core).

### 4.3 Sizes and acyclicity

`size : D → Nat` (number of `Ev` nodes).  Operands of `d` have size
strictly less than `size d`.  Used for the causal poset's acyclicity
(§6).

### 4.4 The primordial element (R3 as a theorem)

Every leaf of every `Ev` term is a `pp` node, and canonicity forces
every `pp` leaf to be `pp l r`.  Hence:

> **`prim_subterm`** — for every `d : D`, `prim` is a subterm of `d`
> (equal or strictly below).  *Every distinction unfolds from the first
> distinction.*

Contrast F-obj: the corresponding statement is only "every tree has an
atom leaf" — there are two possible leaves, and no single tree is a
subterm of all trees.  In F-ev the primordial element is literally
unique and universal.  This is the event-primacy witness theorem.

---

## 5. The asynchronous system in F-ev language (SPEC §2 translated)

### 5.1 State = a status assignment

Because the line `{x,y}` and the point `pair{x,y}` are *one term* of
`D`, the F-obj state `(T, U)` collapses to a single classifier:

```
Status ::= absent < pending < completed        -- a 3-chain
State  ≈  σ : D → Status,  with σ ≠ absent on only finitely many d
```

Concretely (Lean, finite, computable): `State := (pending completed :
List D)` with well-formedness `WF s`: no duplicates, disjointness, and
*operand closure* — every `done`-operand of every listed distinction is
in `completed` … for members of `completed`, and is in `completed` for
members of `pending` as well.  `status s d` reads the classifier off
the two lists.

### 5.2 Points are derived (R4)

```
avail s : Operand → Bool
avail s (pole p)  = true
avail s (done d)  = (status s d == completed)
```

**Definition (point).**  A *point of the state `s`* is an operand
available in `s`: one of the two poles, or a completed distinction in
operand position.  There is no sort of points; "point" is a role that
a completed distinction plays toward later distinctions — plus the two
degenerate primordial roles.  (The poles are "points" that were never
events: exactly the residue R2 predicts cannot be eliminated, §2.2.)

### 5.3 The two event kinds (SPEC §2, ORIGIN_RAW §8)

Labels: `Label ::= link (d : D) | resolve (d : D)`.

- **`link d`** (Event 2, contrast, Pair → Line):
  *enabled* iff both operands of `d` are `avail` in `s` **and**
  `status s d = absent`;
  *effect*: `status d := pending` (append to `pending`).
  Reading: the distinction `d` **occurs** — the contrast is drawn.
- **`resolve d`** (Event 1, differentiation, Line → Point):
  *enabled* iff `status s d = pending`;
  *effect*: `status d := completed` (move to `completed`).
  Reading: the distinction **reifies** — it becomes available as an
  operand, i.e. becomes a point (§5.2).

Every event is one unit increment of one point of the classifier along
the 3-chain `absent → pending → completed`; the only guard is local
(the operands' fibers must be at the top).  Status is monotone along
every run — nothing ever descends.  This monotonicity is the
persistence half of Q1's commutation argument, visible by construction.

Note how the F-obj enabledness conditions fuse: F-obj `link {x,y}`
needs *two* separate negative conditions (`{x,y} ∉ U` and
`pair{x,y} ∉ T`); F-ev needs one (`status = absent`), because line and
point are the same term in different phases.  The SPEC §2 pinned
identification ("a line **is** the pair, the resolved point **is**
`pair{x,y}`") is not a pin here — it is definitional.  F-ev is the
formalization in which that identification costs nothing; conversely,
the equivalence theorem below is exactly the statement that the F-obj
pin is coherent.

### 5.4 Initial state, runs, fairness

Pinned initial state: `init := (pending = [], completed = [])` — the
empty classifier (everything absent).  In `init` exactly one label is
enabled: `link prim` (all other terms have a `done`-operand, and no
distinction is completed).  So the system opens with the primordial
contrast, forced.

Runs and weak fairness verbatim from SPEC §2: a run is a finite or
infinite sequence of labels, each enabled in the state its predecessors
produce; maximal = no forever-neglected enabled label.

*The initium choice-point, seen from F-ev* (SPEC §2 variant
`U₀ = {{a,b}}`): the F-ev counterpart is `initP := (pending = [prim],
completed = [])`.  Under the translation of §7, `init ↦ (T₀ = {a,b},
U₀ = ∅)` (the SPEC pin) and `initP ↦` the SPEC variant; they differ by
the single forced transition `link prim`.  The event-primary reading
mildly favors `initP` — "the primordial element is the first
distinction, so the system begins with it having occurred" — while the
pin `init` reads as "the poles are available but nothing has yet
happened", with pole-availability already encoding the latent contrast.
We pin `init` (matching SPEC's F-obj pin) and record: **the two initium
conventions are conjugate under the translation, offset by exactly one
forced event; the refuters' "expected immaterial" is, in F-ev, the
observation that a one-edge-shifted pointed graph is isomorphic past
its first vertex.**

---

## 6. The causal poset presentation (the design's main payoff)

Each carrier term `d : D` contributes exactly **two** occurrences:

```
Occ ::= linkOf (d : D) | resolveOf (d : D)
```

Generate a relation by two covering rules:

1. `linkOf d ⋖ resolveOf d` (a contrast must occur before it reifies);
2. `resolveOf e ⋖ linkOf d` whenever `e` is a `done`-operand of `d`
   (an operand must have reified before a distinction can use it).

Pole-operands contribute no generator (poles are unconditionally
available — they act as virtual bottom elements already completed).
By §4.3 (operands strictly smaller) the generated relation is
well-founded; its reflexive–transitive closure `≤` is a partial order
`ℙ = (Occ, ≤)`, locally finite (predecessors of an occurrence live in
the finite subterm closure).

**Observation (guards = covering predecessors).**  For a well-formed
state `s`, write `occSet s := {linkOf d | status d ≥ pending} ∪
{resolveOf d | status d = completed}`.  Then:

- `link d` enabled in `s` ⟺ `linkOf d ∉ occSet s` and every
  `≤`-predecessor of `linkOf d` is in `occSet s`;
- `resolve d` enabled ⟺ `resolveOf d ∉ occSet s` and every
  predecessor (namely `linkOf d`) is in `occSet s`.

That is: **the F-ev system is, definitionally, the downset-growth
process of the poset `ℙ`** — states ↔ finite downsets (order ideals),
events ↔ adding one minimal element of the complement, runs ↔
enumerations of downsets one element at a time, maximal fair runs ↔
linear extensions of `ℙ` (exhausting it, by local finiteness +
countability + weak fairness).

Consequences for the program:

- **Q1 in F-ev is near-definitional.**  Order-invariance (all maximal
  runs realize the same causal partial order and the same limit) is,
  for a downset-growth process, the classical statement "the runs are
  exactly the linear extensions of `ℙ`, and every linear extension of a
  countable locally-finite poset with finite principal downsets
  exhausts it under weak fairness".  The causal order **D** of Q1 *is*
  `ℙ`, produced by presentation rather than extracted by a commutation
  argument.
- **Recommended proof route for the program**: prove Q1 for F-ev
  (easy), prove the Q4 translation (§7–§8), transport Q1 to F-obj —
  rather than proving the diamond property twice.
- **C5 lands as a conclusion, as SPEC demands**: the true-concurrency
  object (a conflict-free elementary event structure, i.e. a plain
  poset) is *derived* — it is `ℙ` — not an input semantics.

*Caveat (kept honest).*  The three claims that need actual proofs, not
just the observation: (a) well-formed reachable states are exactly the
finite downsets; (b) the guard equivalence above, including that
transitive predecessors reduce to covering predecessors on downsets;
(c) fair exhaustion.  All three are routine but must be machine-checked
before Q1-via-F-ev is claimed.

---

## 7. Translations to and from F-obj

Assume the F-obj deliverable provides canonical `Tree` (atoms `A`, `B`;
`pairT : (x y : Tree) → x ≠ y → Tree` canonical-sorted; children
recoverable).  Write `Composite := {t : Tree // t ≠ A ∧ t ≠ B}`.

### 7.1 Term-level translation — the carrier shift

```
opToTree  : Operand → Tree            evToTree : D → Tree
opToTree (pole l)  = A                evToTree ⟨u,v⟩ = pairT (opToTree u) (opToTree v) _
opToTree (pole r)  = B
opToTree (done d)  = evToTree d

treeToOp  : Tree → Operand            treeToEv : Tree → Option D
treeToOp A          = pole l          treeToEv A = none,  treeToEv B = none
treeToOp B          = pole r          treeToEv (pairT x y _) =
treeToOp (pairT x y _) = done (pair (treeToOp x) (treeToOp y) _)   some (pair … )
```

**Theorem shape (`operand_tree_iso`).**  `opToTree` and `treeToOp` are
mutually inverse bijections `Operand ≅ Tree`; `evToTree` restricts this
to a bijection `D ≅ Composite`.

So the clean bijection is **F-obj carrier ≅ F-ev *operand* sort** — one
level shifted — and the carriers themselves are *not* isomorphic:
`Tree ≅ Pole ⊕ D`, an off-by-two defect, the two atoms/poles exactly.
This is asymmetry A1 (§9).

The side conditions correspond exactly: `u ≠ v` in `Operand` ⟺
`opToTree u ≠ opToTree v` in `Tree` (by injectivity), so C4 transports.

### 7.2 Label-level translation

```
β : Label_ev → Label_obj
β (link d)    = link    {opToTree u, opToTree v}   where (u,v) = operands d
β (resolve d) = resolve {opToTree u, opToTree v}
```

`β` is a **bijection** of label alphabets: every F-obj label carries an
unordered pair of distinct trees, and `treeToOp` + `pair` produce its
unique preimage.

### 7.3 State-level translation

```
Φ : State_ev → State_obj
Φ s = ( T = {A, B} ∪ evToTree '' (completed s),
        U = { {opToTree u, opToTree v} | d ∈ pending s, (u,v) = operands d } )

Ψ : State_obj → Option State_ev        -- partial on raw states, see §9 A5/A7
Ψ (T, U) = ( completed = treeToEv '' (T ∩ Composite),
             pending   = { pair (treeToOp x) (treeToOp y) _ | {x,y} ∈ U } )
    defined only when {A,B} ⊆ T, T ∋ children of its members,
    endpoints of U lie in T, and U-pairs are not already reified in T.
```

### 7.4 Simulation lemmas (intended theorem shapes)

- `Φ init = (T₀ = {A,B}, U₀ = ∅)` (the SPEC pin), `Φ initP = ` the
  SPEC variant.
- **Forward**: if `WF s` and `enabled s ℓ` then
  `objEnabled (Φ s) (β ℓ)` and `Φ (apply s ℓ) = objApply (Φ s) (β ℓ)`.
- **Backward (reflection)**: if `WF s` and `objEnabled (Φ s) m` then
  the unique `ℓ` with `β ℓ = m` satisfies `enabled s ℓ`.
- `Φ` is injective on well-formed states and surjective onto reachable
  F-obj states.

---

## 8. The equivalence conjecture (Q4), stated precisely

**What must be preserved.**  There is a hierarchy of candidate
invariants, strictly ordered in strength for these systems:

1. **limit only** — `T∞ ≅` (image of) `C∞`;
2. **causal partial order D** — isomorphism of the Q1 posets;
3. **pointed labelled transition graph over a label bijection** —
   graph isomorphism of reachable states commuting with initial state
   and labels.

Level 1 is **rejected** as the criterion: it would call the lockstep
foliation (choice point C3-alternative) equivalent too, erasing exactly
the content ORIGIN_RAW §6 insists on (the order structure, not the
inventory, is the system).  Level 3 is definitional today (no Q1
needed) and implies levels 2 and 1; after Q1 is proved, levels 2 and 3
coincide for these systems (the reachable graph is the downset lattice
of **D**, so each determines the other).  **We pin level 3**:

> **Conjecture (Q4-positive form).**  With `β` the label bijection of
> §7.2 and `Φ` the state translation of §7.3: `Φ` restricts to an
> isomorphism of pointed labelled transition systems
> `(Reach_ev, init) ≅ (Reach_obj, (T₀={A,B}, U₀=∅))` over `β`; that is,
> `Φ` is a bijection on reachable states, maps `init` to the F-obj
> initium, and `s →ℓ s′  ⟺  Φ s →β(ℓ) Φ s′` for all reachable `s`.
>
> Corollaries if it holds: bijection of runs preserving maximality /
> weak fairness; isomorphism of causal orders `D_ev ≅ D_obj` (level 2);
> limit correspondence `T∞ = {A,B} ⊔ evToTree '' C∞` (level 1, with
> the off-by-two defect explicit).

Confidence: high — §7.4's forward/backward lemmas are structural
inductions with no visible obstruction; the risk concentrates in the
well-formedness bookkeeping (operand closure vs child closure), which
is where any surprise would surface.

**And what is *not* preserved — where Q4 is answered "yes, but".**  The
conjecture deliberately does **not** ask for (i) a carrier bijection —
impossible, A1; (ii) initium coincidence without the convention
alignment — A2; (iii) preservation of sort structure or of the
"creation locus" — A3, A4.  These are the asymmetries; they are
results, catalogued next.

---

## 9. Asymmetry catalog (first-class results, not failures)

**A1 — carrier shift (off-by-two).**  The bijection is
`Tree ≅ Operand = Pole ⊕ D`, never `Tree ≅ D`.  The F-obj carrier
matches the F-ev *derived* sort; the two carriers differ by exactly the
two atoms/poles.  Event-primacy relocates the primordial two-ness below
the carrier (roles instead of elements) but cannot delete it — Design
S's failure (§2.2) shows the relocation is forced, not chosen.

**A2 — initium naturality flip.**  F-obj's natural initium is
`(T₀={A,B}, U₀=∅)` (SPEC pin); F-ev's philosophically natural initium
is `initP = {prim pending}` (SPEC's *variant*).  Both are expressible
on both sides, and they differ by one forced transition; but each
formalization makes a different convention read as "nothing has been
added".  The SPEC variant question is thereby answered structurally:
immaterial (one-edge offset), and the variant is exactly the
event-primary reading.

**A3 — sort collapse / expressivity gap.**  F-obj has two sorts (lines
in `P₂(T)`, points in `Tree`) identified by SPEC §2's pin; F-ev has one
term with a status.  Consequently F-ev **cannot even express** the
alternative individuations the pin excludes (e.g. "resolve creates a
fresh anonymous point not determined by its line"): in F-ev the
resolved point is the same term by typing, not by decree.  The pin is
a theorem-shaped cost on the F-obj side and free on the F-ev side; an
F-obj variant with anonymous reification would have *no* F-ev
counterpart.  Asymmetric expressivity in F-obj's favor, coherence in
F-ev's favor.

**A4 — creation-locus swap (a non-invariant question).**  In F-obj,
*resolve* creates (adds a new element to `T`) and link only records; in
F-ev, *link* creates (a term first acquires non-absent status) and
resolve only flips a status.  Since the two systems are conjectured
LTS-isomorphic over `β`, the question "which of the two event kinds is
the generative one?" is **not invariant under the equivalence** — by
the program's own criterion (only what survives translation is real),
it is not a property of the system but of the presentation.

**A5 — rule vs fact.**  Pole availability is an unconditional *rule*
in F-ev; atom presence is a stateful *fact* (`{A,B} ⊆ T`) in F-obj.
Raw F-obj states with an atom missing exist and have no F-ev
counterpart (`Ψ` is partial); reachability rescues the equivalence.
F-ev structurally forbids a state in which the primordial contrast is
"absent" — arguably the more faithful reading of ORIGIN_RAW §1
("by that alone, the chain reaction … has occurred").

**A6 — matched symmetry breaking (C2 hook).**  The pole swap `l ↔ r`
acts on `Ev` by recursion (re-sorting to stay canonical) and
corresponds under `Φ` to the atom swap `A ↔ B`.  Both formalizations
break the swap in the same place — the canonical order — so the C2
refutation-track question ("which theorems are swap-invariant?") can be
run once and transported.

**A7 — the status ladder hard-codes choice point C1.**  The 3-chain
`absent < pending < completed` *is* the pinned C1 ("a resolved line
persists as a joining; link never repeats"): monotone status makes
re-linking a completed distinction unstatable.  The C1-alternative
(lines vanish on resolve, re-link allowed) requires replacing `Status`
with two independent bits (`currently-pending`, `ever-completed`) —
representable, but the downset-lattice picture of §6 and the
one-term-two-phases identity are lost.  F-ev thus measures the *cost*
of the C1 alternative: it is exactly the loss of the causal-poset
presentation.  (Refutation track: build the two-bit variant and see
what survives; prediction: Q1 fails or weakens, since the same label
can fire twice and runs are no longer downset enumerations.)

---

## 10. Intended Lean 4 signatures (axiom-free, no quotients)

Fresh package under `rederive/lean/`, Lean core only.  `deriving`
clauses avoided where their generated instances are not certified
axiom-free; instances hand-written instead.

```lean
namespace Rederive.FEv

/-- The two roles of the primordial contrast.  Tags, not a carrier. -/
inductive Pole : Type where
  | l : Pole
  | r : Pole

def Pole.beq : Pole → Pole → Bool
instance : DecidableEq Pole

/-- Raw distinction-terms (operand sum flattened to stay first-order). -/
inductive Ev : Type where
  | pp : Pole → Pole → Ev
  | pe : Pole → Ev → Ev
  | ee : Ev → Ev → Ev

def Ev.beq : Ev → Ev → Bool
theorem Ev.beq_iff : ∀ d e : Ev, d.beq e = true ↔ d = e
instance : DecidableEq Ev

def Ev.cmp : Ev → Ev → Ordering                  -- total structural order
theorem Ev.cmp_eq_iff  : ∀ d e, d.cmp e = .eq ↔ d = e
theorem Ev.cmp_trans   : ∀ {d e f}, d.cmp e = .lt → e.cmp f = .lt → d.cmp f = .lt
theorem Ev.cmp_swap    : ∀ d e, (d.cmp e).swap = e.cmp d

def Ev.canon : Ev → Bool                         -- §3 clauses
def Ev.size  : Ev → Nat

/-- THE carrier: canonical distinction-terms. -/
abbrev D : Type := { e : Ev // e.canon = true }
def D.prim : D                                    -- ⟨.pp .l .r, rfl⟩

/-- Derived operand sort (a defined sum, not a new inductive). -/
abbrev Operand : Type := Sum Pole D

def D.pair : (u v : Operand) → u ≠ v → D          -- sorts; total
def D.operands : D → Operand × Operand
theorem D.pair_comm     : ∀ u v h, D.pair u v h = D.pair v u (Ne.symm h)
theorem D.pair_operands : ∀ d, D.pair d.operands.1 d.operands.2 _ = d
theorem D.pair_inj      : -- equal iff same unordered operand pair
theorem D.prim_subterm  : ∀ d : D, SubEv D.prim.val d.val ∨ d = D.prim

/-- ## Dynamics -/
inductive Status : Type where
  | absent | pending | completed

structure State : Type where
  pending   : List D
  completed : List D

def State.init  : State := ⟨[], []⟩               -- pinned initium
def State.initP : State := ⟨[D.prim], []⟩          -- SPEC-variant initium
def State.status : State → D → Status
def State.avail  : State → Operand → Bool
def State.WF     : State → Bool                    -- nodup, disjoint, operand-closed

inductive Label : Type where
  | link    : D → Label
  | resolve : D → Label

def enabled : State → Label → Bool                 -- §5.3 guards
def apply   : State → Label → State                -- total; unchanged if ¬enabled
theorem WF_preserved : ∀ s ℓ, s.WF → (apply s ℓ).WF
theorem status_monotone : -- along apply, no status ever decreases

/-- Runs: finite prefixes as lists; infinite runs as guarded streams. -/
def RunOk : State → List Label → Bool
def Run   : Type := Nat → Option Label             -- + validity predicate
def Fair  : Run → Prop                             -- weak fairness, SPEC §2

/-- ## Causal poset (§6) -/
inductive Occ : Type where
  | linkOf    : D → Occ
  | resolveOf : D → Occ

inductive Cov : Occ → Occ → Prop where
  | lr : ∀ d, Cov (.linkOf d) (.resolveOf d)
  | op : ∀ d e, e ∈ D.doneOperands d → Cov (.resolveOf e) (.linkOf d)

def CausalLE : Occ → Occ → Prop                    -- refl-trans closure (inductive)
theorem causal_po        : -- partial order, well-founded, locally finite
def   State.occList      : State → List Occ
theorem reachable_iff_downset :
  ∀ s, Reachable State.init s ↔ (s.WF ∧ IsDownset s.occList)
theorem runs_iff_linear_extensions : -- Q1 for F-ev, via §6

/-- ## Translation to F-obj (interface: canonical Tree from task M1) -/
def Operand.toTree : Operand → Tree
def D.toTree       : D → Tree
def Tree.toOperand : Tree → Operand
def Tree.toEv      : Tree → Option D
theorem operand_tree_iso :
  (∀ t, (Tree.toOperand t).toTree = t) ∧ (∀ u, u.toTree.toOperand = u)
theorem evToTree_composite : ∀ d : D, d.toTree ≠ Tree.A ∧ d.toTree ≠ Tree.B
theorem evToTree_inj : ∀ d e : D, d.toTree = e.toTree → d = e

def Label.toObj : Label → ObjLabel                 -- the bijection β
def State.toObj : State → ObjState                 -- Φ
theorem toObj_init : State.init.toObj = ObjState.init
theorem toObj_forward :
  ∀ s ℓ, s.WF → enabled s ℓ = true →
    objEnabled s.toObj ℓ.toObj = true ∧ (apply s ℓ).toObj = objApply s.toObj ℓ.toObj
theorem toObj_reflect :
  ∀ s m, s.WF → objEnabled s.toObj m = true →
    ∃ ℓ, ℓ.toObj = m ∧ enabled s ℓ = true
theorem toObj_inj_on_WF : -- Φ injective on well-formed states
theorem toObj_reach_surj : -- Φ surjective onto F-obj-reachable states

/-- Q4, packaged (the §8 conjecture). -/
theorem Q4_lts_iso :
  LTSIso (ReachableSub State.init) (ReachableSub ObjState.init) Label.toObj

end Rederive.FEv
```

Implementation notes: (a) all recursions are structural — no
well-founded recursion gymnastics expected; (b) `Prop`-valued
`Cov`/`CausalLE` are fine for the ∅-axiom contract (inductive `Prop`s
need no choice); Bool-valued mirrors kept where decidability is wanted
for the enumerator; (c) the F-obj interface must come from the M1
deliverable — the translation file imports both and nothing else.

---

## 11. Choice-point interactions (SPEC §2 table, revisited from F-ev)

| CP | In F-ev |
|---|---|
| C1 | Hard-coded by the `Status` 3-chain (monotone; re-link unstatable).  Alternative needs `Status := Bool × Bool`; costs the downset presentation (§9 A7). |
| C2 | Pole swap = recursion + re-sort; matched to atom swap under `Φ` (§9 A6). |
| C3 | Automatic: guards are stateless in history; a distinction over younger operands is enabled the moment they complete.  The generation-restricted alternative = restricting `ℙ`'s linear extensions to a foliation — visibly an *added* constraint in the downset picture. |
| C4 | Upgraded from side condition to carrier-level non-existence (§3, remark). |
| C5 | Discharged as a conclusion: the concurrency object is the derived poset `ℙ` (§6), not an input semantics. |

---

## 12. Ledger entries (classical concepts relied on)

| Internal term (F-ev) | Nearest classical object | Imported/used theorems |
|---|---|---|
| `Ev`, `D` | free term algebra / initial algebra of a polynomial functor | uniqueness of structural recursion, injectivity of constructors |
| `canon` + sorted pair | canonical representatives for unordered trees (sorted-children normal form) | existence/uniqueness of normal forms under a total term order |
| `cmp` | lexicographic path-style total order on terms | totality, transitivity |
| `Operand = Pole ⊕ D` | disjoint sum type | — |
| state/label/`enabled`/`apply` | labelled transition system (LTS) | — |
| `Φ`, `β`, forward/reflect lemmas | (bi)simulation, forward–backward simulation, LTS isomorphism (Milner; Lynch–Vaandrager style) | soundness of simulation for reachability transfer |
| `ℙ`, `occSet`, downsets | partially ordered sets, order ideals (downsets), linear extensions | linear extensions of countable locally finite posets exhaust under fairness; downset lattice (distributive) |
| downset-growth process | antimatroid / poset shelling; conflict-free (elementary) event structures (Winskel) | runs of ideal-growth = linear extensions |
| `Fair` | weak fairness (Manna–Pnueli style) | fair scheduling exhausts countable enabled sets |
| Design E | graph theory: vertex/edge two-sorted presentation | — |
| Design S failure | occurrence identification = quotient by positional equivalence | quotient constructions (rejected under R6) |

---

## 13. Claims summary

1. **(sketch)** Design P (§2.3, §3) satisfies R1–R6; carrier `D` is a
   single first-order inductive + Bool canonicity subtype,
   implementable in Lean 4 core with no quotients and empty axiom
   footprint.
2. **(sketch)** Design S (pole-free, sides-as-operands) is
   unimplementable without quotients; any quotient-free event-primary
   formalization must carry the primordial two-ness as global pole
   tags (§2.2).  The two-ness relocates; it does not vanish.
3. **(sketch)** `Tree ≅ Operand` and `D ≅ Composite`: the F-obj carrier
   matches the F-ev *operand* sort, one level shifted; the carriers
   differ by exactly the two atoms/poles (A1).
4. **(conjecture)** Q4-positive form (§8): `Φ` is a pointed-LTS
   isomorphism over the label bijection `β` between the reachable
   fragments; corollaries — causal-order isomorphism and the
   off-by-two limit correspondence.
5. **(sketch)** The reachable F-ev system is the downset-growth process
   of the explicit causal poset `ℙ` (§6); maximal fair runs = linear
   extensions; hence Q1 for F-ev reduces to classical order theory, and
   the recommended route is Q1(F-ev) + Q4-translation ⟹ Q1(F-obj).
6. **(sketch)** `prim_subterm`: every canonical distinction contains
   the primordial distinction as a subterm — R3 as a theorem, with no
   F-obj analogue of the same strength.
7. **(sketch)** Asymmetries A2–A5, A7: initium naturality flip (SPEC's
   `U₀` variant = the event-primary natural initium, offset one forced
   event); sort collapse making the SPEC §2 pin definitional and the
   anonymous-reification variant inexpressible; creation-locus swap
   showing "which event kind creates?" is not equivalence-invariant;
   pole availability as rule vs atom presence as fact; the `Status`
   3-chain as the exact formal content of choice point C1.
