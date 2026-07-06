# R5 — Refutation track: the F-obj / F-ev duality

**Target**: `rederive/theory/event_primary_design.md` (Design P, Q4, §9
asymmetry catalog).
**Inputs used**: `rederive/SPEC.md`, `seed/ORIGIN_RAW.md`, the target file.
Classical math from own knowledge.
**Verdict**: **WEAKENED**. The duality is not a pure relabeling (there is one
genuine natural F-ev question and a real guard-fusion), so the strongest
"F-obj relabeled" charge fails. But three load-bearing supporting claims break
under attack: (b1) the Design-S "dies without quotients" argument is a
non-sequitur; (b2) event-primacy over ORIGIN_RAW §2 is *circumvented*, not
honored — poles are constructionally **prior** to the difference; (a1) the A1
"carrier off-by-two" is a trivial repackaging (`Operand ≅ Tree` on the nose),
oversold as a first-class result; and (c1) the Q4 equivalence is an unproven
conjecture, and is equivalence to a **pinned, reachable-only** restriction of
F-obj, not to F-obj.

---

## 0. Hand recomputation (level ≤ 2), to anchor everything

**F-obj / Tree.** Atoms `A`, `B`. Composites buildable by level 2:
`pair{A,B}`, `pair{A, pair{A,B}}`, `pair{B, pair{A,B}}`. Total **5** (= 2
atoms + 3 composites). Matches ORIGIN_RAW §9 ("strata to level 2, 5 objects").

**F-ev / D (canonical `Ev`).** `prim = pp l r`. Next canonical terms:
`pe l prim`, `pe r prim`. No `ee` term yet (needs two *distinct* earlier
canonical distinctions; only `prim` exists). So `|D_{≤2}| = 3`: `{prim,
pe l prim, pe r prim}`.

**Operand = Pole ⊕ D** = `{pole l, pole r} ⊔ {prim, pe l prim, pe r prim}`,
cardinality **5**.

The bijection `Tree ≅ Operand`:

| Tree | Operand |
|---|---|
| `A` | `pole l` |
| `B` | `pole r` |
| `pair{A,B}` | `done prim` |
| `pair{A, pair{A,B}}` | `done (pe l prim)` |
| `pair{B, pair{A,B}}` | `done (pe r prim)` |

So `|Tree| = |Operand| = 5`, `|D| = |Composite| = 3`. **A1 checks out
numerically** — and this is exactly what exposes it (see §3).

**Guard-fusion check** (§5.3 claim). F-obj `link{x,y}` needs `{x,y}∉U ∧
pair{x,y}∉T`. F-ev `link d` needs `status d = absent`. With `pending ↔
{x,y}∈U`, `completed ↔ pair{x,y}∈T`, indeed `status = absent ⟺ {x,y}∉U ∧
pair{x,y}∉T`. **The fusion is real and correct.**

**Initium-offset check** (A2). In `init = ([],[])`: `prim`'s operands are
`pole l, pole r`, both `avail` unconditionally, and `status prim = absent`, so
`link prim` is enabled. Any `pe l prim` needs `done prim` avail, i.e.
`status prim = completed` — false in `init`. So **`link prim` is the unique
enabled label**, and `init --link prim--> ⟨[prim],[]⟩ = initP`. A2's "offset
by one forced event" is literally: `initP` is `init`'s only successor.

These four hand-checks show the design's *arithmetic* is honest. The attack is
on what the arithmetic is claimed to *mean*.

---

## 1. Attack (a): triviality — genuine dual, or F-obj relabeled?

### 1.1 The one place the design survives triviality

I could not reduce F-ev to "a carrier bijection with renamed constructors,"
because two things are genuinely non-trivial:

- **`prim_subterm` (§4.4).** In F-ev, `prim` is a subterm of *every* `d : D`
  (every canonical leaf is `pp l r = prim`). In F-obj the analogue is false:
  `A` is not a subterm of `B`, and no single Tree is a subterm of all. This is
  a real question F-ev makes natural and F-obj makes false. It is not
  relabeling.
- **Guard fusion (§0 above).** F-ev collapses two negative guards into one
  monotone classifier. Genuine ergonomic content.

So the blunt charge — "F-ev *is* F-obj with renamed constructors" — **fails**.
The carriers are genuinely not isomorphic (`|D| = 3 ≠ 5 = |Tree|`).

### 1.2 But the payoff is thinner than advertised, and possibly an artifact

`prim_subterm` holds **because F-ev collapsed the two atoms into one root
event**. That collapse is not obviously a *virtue*: ORIGIN_RAW §2/§3 insist
the primordial thing is a **two-sided contrast** (`b` is the minimal contrast
*for* `a`; "there must be at least two"). Making `prim` the unique universal
subterm reifies "everything descends from *one* first distinction," which reads
cleanly but buries the two-ness one level down (into `pole l/r`). So the one
genuinely-natural F-ev theorem is natural precisely to the degree that F-ev
*departs* from the raw text's "at least two" emphasis. The payoff is real but
double-edged; the design presents only the flattering edge.

**Sub-verdict (a): not trivial, but the non-trivial content is one theorem
(`prim_subterm`) plus one guard fusion — modest, and in tension with §2/§3, not
the rich "duality" the framing implies.**

---

## 2. Attack (b): R2 — atoms eliminated, or renamed "poles"?

### 2.1 The Design-S rejection is a non-sequitur (first-class finding)

§2.2 rejects the pole-free Design S with the headline "**this design dies
without quotients**." The argument:

> "the tree `a` occurs as a child of both `pair{a,b}` and
> `pair{a, pair{a,b}}` — the same `a`. In Design S, 'the left side of `prim`'
> and 'the left-operand role inside `mk (side prim Left) (done prim)`' are
> distinct term-occurrences; to make later distinctions take the same `a`
> twice, the design must identify side-occurrences across terms. That
> identification is exactly a quotient …"

This conflates **positions** with **values**. In Design S, `a := side prim
Left` is a *closed term* of sort `Operand`. Any later distinction that wants
operand `a` simply writes the same closed term `side prim Left`. Two
occurrences of `side prim Left` in two different big terms are equal *by
`rfl`* — inductive term equality is structural and decidable. There is no
"occurrence-identity relation on positions" to quotient by; nobody is
identifying positions. You reuse a value.

Concretely:
```
pair{a,b}            = mk (side prim Left) (side prim Right)
pair{a, pair{a,b}}   = mk (side prim Left) (done (mk (side prim Left) (side prim Right)))
```
The operand `side prim Left` in both is *one and the same* closed term. No
quotient is invoked or needed. **Design S does not die without quotients.**

The document itself, two sentences later, quietly concedes the real situation:
"The only quotient-free repair is to designate a canonical occurrence — '`a`
*is* the left side of `prim`' — which reintroduces two distinguished global
tags. Those tags are poles." That is the correct statement, and it is *not*
"dies without quotients" — it is "**Design S canonicalizes to Design P.**"
`side prim Left / side prim Right` *are* `pole l / pole r` spelled differently.

So the negative "Finding (first-class)" in §2.2 is reached by a broken
argument. Its stated **mechanism** (quotient necessity) is wrong. Its
**conclusion** — "two-ness must be carried as two global tags" — happens to
survive, but on a *different* ground: keeping the primordial contrast
genuinely two-sided while quotient-free (C2 pinned `a ≠ b`) forces two
*distinguishable* tags; you cannot merge them without the swap-quotient R6
forbids. The design should have argued *that*. As written, the flagship
proof-by-failure is invalid, which weakens the claim that Design P is *forced*
rather than merely *chosen*.

### 2.2 Poles are atoms relocated **and made prior** — §2 circumvented

R2 in letter: `Pole ∉ D`. Formally satisfied. But look at the *construction
order* in Design P:
```
Pole    ::= l | r                     -- defined first, DecidableEq, ground
Ev      ::= pp Pole Pole | …          -- uses Pole
prim    := ⟨pole l, pole r⟩           -- the "difference" is BUILT FROM poles
```
The poles are **constructionally prior** to `prim`. ORIGIN_RAW §2 says the
opposite: "`a`, `b` … are **not objects**; only the difference is," and §3:
`b` is "the minimal contrast required for `a` to be caught," i.e. `a`/`b` are
*roles inside* the difference, derivative of it. In Design P the difference
`prim` is a *derived* term over two *primitive givens* `l, r`. That inverts
§2's "only the difference is."

Ironically, the *rejected* Design S is **more** faithful here: it has `prim`
as a **nullary** constructor (primordial, built from nothing) and derives
`a := side prim Left`, `b := side prim Right` *from* `prim` — exactly "the two
are roles of the one difference." And, per §2.1, Design S is quotient-free.
The design discarded the more §2-faithful option using an invalid argument,
then adopted the option in which the atoms are *most* primitive.

**Sub-verdict (b): R2 is honored in letter and circumvented in spirit. The
poles are `a`/`b` renamed and promoted to constructional priority; atom-
primitives were not eliminated, only relocated — and relocated the wrong
direction relative to ORIGIN_RAW §2. The design concedes the relocation
("cannot delete it") but not the priority inversion, and it justifies the
choice with a broken lemma.**

---

## 3. Attack (a2)/(c): asymmetry catalog §9 and the level of equivalence

### 3.1 A1 is a trivial repackaging, oversold

A1 ("carrier off-by-two") states `Tree ≅ Operand = Pole ⊕ D`, "never
`Tree ≅ D`," billed as a "first-class result." But `Operand = Pole ⊕ D` means
the F-ev data is *exactly* `Tree`, merely partitioned into "two designated
points" ⊕ "the rest." My §0 table shows the partition explicitly: nothing is
added or lost, the 5 Trees are the 5 Operands. A genuine duality (Stone,
point-free vs points, …) yields a carrier **not reconstructible** as "the big
carrier minus two marked points." Here it is reconstructible on the nose. A1 is
a boundary-shift of the label "carrier," not a mathematical asymmetry. Calling
it a first-class result inflates a tautology.

### 3.2 A2, A4 are presentation artifacts

- **A2**: `init` and `initP` are not "conjugate conventions"; §0 shows `initP`
  is literally `init`'s unique successor under the forced `link prim`. The
  "naturality flip" is an aesthetic reading of two adjacent states, not a
  mathematical asymmetry.
- **A4** ("which event kind creates?"): the swap disappears once you compare
  like with like. The **point** is created at `resolve` in *both* systems
  (F-obj: enters `T`; F-ev: `avail (done d)` becomes true). The **line** is
  created at `link` in *both* (F-obj: enters `U`; F-ev: `status` leaves
  `absent`). A4's apparent swap comes from comparing F-ev's *full classifier
  support* (which includes pending terms) against F-obj's `T` (points only).
  Compare F-ev support against F-obj `T ∪ endpoints(U)` and the swap vanishes.
  A4's own punchline ("not invariant, hence a property of the presentation") is
  therefore *correct but self-undermining*: it is a presentation artifact
  dressed as a discovery. Modest, not first-class.

### 3.3 A3, A5, A7 are real — and they all cut the same way

- **A3** (sort collapse): genuine. F-ev cannot express anonymous reification.
- **A5** (rule vs fact): genuine. F-obj has junk states (atom missing) with no
  F-ev image; `Ψ` is partial.
- **A7** (`Status` 3-chain = C1): genuine. Monotone chain hard-codes C1.

These three are honest, but note their common direction: **the equivalence is
between F-ev and a *pinned, reachable-only, C1-fixed restriction* of F-obj**,
not F-obj itself. Without SPEC §2's identification pin, F-obj is strictly more
expressive (A3); with raw states, F-obj is strictly larger (A5); with the C1
alternative, the whole downset picture dies (A7). So "F-ev ≅ F-obj" is really
"F-ev ≅ F-obj|_{pinned, reachable, C1}". The duality is contingent on choices
external to both formalizations.

### 3.4 The equivalence level (attack c, direct)

Is equivalence claimed at causal-order level (Q4) or only carrier level? The
design pins **Level 3** (pointed LTS iso over `β`), *explicitly rejects*
Level 1, and derives Level 2 (causal poset iso) as a corollary. So the honest
answer to "only carrier level?" is **no** — it is pitched at the causal-order
level. That defends against the shallow version of attack (c).

**But**: Q4 is a **conjecture** ("Confidence: high"), not a theorem; §6 itself
lists *three* unproven load-bearing claims (reachable = downsets; guard =
covering-predecessors; fair exhaustion) needed even for Q1-via-F-ev. And per
§3.3 the target of the iso is the pinned/reachable restriction. So the
causal-order equivalence is **asserted at the right level but not established**,
and is narrower than "F-obj" unqualified. The strong reading ("the two systems
are the same causal order") is **not earned yet** — it is a well-motivated
conjecture with explicit unproven dependencies.

---

## 4. Recomputed adversarial case: does `prim_subterm` really have "no F-obj
analogue of the same strength"?

Claim 6 (§13) and §4.4 assert `prim_subterm` has "no F-obj analogue of the
same strength." Test the closest F-obj candidate: *"the pair `pair{A,B}` is a
subterm of every composite."* Level-2 composites: `pair{A,B}` (trivially
itself), `pair{A,pair{A,B}}` (contains `pair{A,B}` ✓), `pair{B,pair{A,B}}`
(contains `pair{A,B}` ✓). So on *composites* `pair{A,B}` is a common subterm —
an F-obj analogue exists! It fails only on the two atoms `A, B` (which are not
composites). Under the §0 bijection, the F-ev statement "prim ⊑ every `d : D`"
maps to "`pair{A,B}` ⊑ every `Composite`" — which is **true in F-obj**. So the
"strength gap" is exactly the off-by-two of A1 again: it is the two atoms, and
nothing else. `prim_subterm` is not a new phenomenon; it is A1 wearing a
subterm-relation costume. The design double-counts its one genuine structural
fact (the two-into-one root collapse) as two independent results (A1 +
`prim_subterm`).

This is my strongest single finding on triviality: **the design's two headline
"event-primacy witnesses" (A1 and `prim_subterm`) are the same fact** — that
F-ev merges the 2 atoms into 1 root — stated twice.

---

## 5. What survives, what breaks

**Survives (concede honestly):**
- F-ev is not a pure carrier bijection; carriers genuinely differ (`3 ≠ 5`).
- Guard fusion (`status = absent`) is real, correct content.
- Equivalence is pitched at causal-order level (Level 3 ⟹ 2), not carrier-only.
- §9 asymmetries are *honestly reported*, including A3/A5/A7 that cut against
  the design.

**Breaks / weakened:**
- (b1) "Design S dies without quotients" — **invalid**; Design S is
  quotient-free and canonicalizes to P. The flagship proof-by-failure fails.
- (b2) Event-primacy over ORIGIN_RAW §2 is **circumvented**: poles are
  constructionally prior to `prim`, inverting "only the difference is"; the
  more §2-faithful Design S was discarded via the invalid argument.
- (a1) A1 "off-by-two" is a **trivial repackaging** (`Operand ≅ Tree`), and
  `prim_subterm` is **the same fact restated** (§4), not two results.
- (c1) Q4 is an **unproven conjecture** with three explicit unproven
  dependencies, and its target is the **pinned/reachable/C1** restriction of
  F-obj, not F-obj.

---

## 6. Required fixes for the claim to reach "confirmed"

1. **Replace the Design-S argument.** Delete "dies without quotients." State
   the correct fact: Design S is quotient-free and *canonicalizes to Design P*;
   the genuine reason two tags are unavoidable is C2 (`a ≠ b`) + R6 (no
   swap-quotient), not occurrence-identity. Re-derive the negative Finding from
   *that*.
2. **Address the priority inversion.** Either (i) adopt an `Ev` in which `prim`
   is nullary and poles are *projected from* `prim` (Design-S-style), restoring
   ORIGIN_RAW §2's "only the difference is"; or (ii) explicitly argue why
   construction-order priority is immaterial and stop claiming §2 is "honored"
   in spirit.
3. **Demote A1 and merge with `prim_subterm`.** Present the two-into-one root
   collapse as **one** structural fact, and label A1 a partition/boundary-shift,
   not a duality asymmetry.
4. **Downgrade Q4 language** from a near-settled equivalence to a conjecture,
   and everywhere qualify the F-obj side as *pinned + reachable + C1-fixed*.
   Prove the three §6 dependencies before any "causal orders are isomorphic"
   claim is made.
5. **Recompute the "no F-obj analogue" claim** for `prim_subterm` with the
   composite-restricted analogue shown in §4; adjust the strength claim.

Absent 1–2, the "event-primary" framing is not established: the design is a
faithful but modest **reparametrization** of F-obj with one genuine ergonomic
payoff (guard fusion), a self-aware asymmetry catalog, and two headline
"primacy" results that reduce to a single off-by-two fact.
