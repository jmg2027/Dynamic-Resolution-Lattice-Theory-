# Lens Emergence Path — natural emergence of numbers and flat ontology

**Status**: working note.  Phase 1 of Option C *has already landed*
(see commit list); Options A, B, D, E remain open.  This is a
reflection on the path taken so far and the branches not taken.
**Date**: 2026-05-18  (`claude/move-tree-to-term-ring-DDom7` branch)
**Related commits this session**:
- `07f4fcde` — `Nat213.Raw` `zero` → `one` rename
- `01401d18` — `Int213.Raw` (inductive sum-type; **later superseded**)
- `3371fd14` — `Int213.Raw` rewritten lens-emergent (signedLens-derived)
- `b05c1f40` — `Int213.Raw` pairLens + factoring (`signedLens = npairToInt ∘ pairLens`)
- `ced56bef` — `Nat213/Core.lean` introduced (Phase 1 of Option C
  refactor — **already in tree**)

---

## 0. Purpose of this document

A consolidation of insights that accumulated during the conversation,
so that they sit in one place for later reflection rather than being
acted on piecemeal.  The reader is given a vocabulary (chart,
flat ontology, emergence path) and a decision-form catalog of options.

Status discipline: where the *codebase* has already moved (Phase 1 of
Option C), this is noted explicitly so the document does not pretend
that the choice is still open.  Where the document gestures beyond
what 213 currently proves (e.g. §2.6, §2.7, §3.3), this is flagged
inline.

---

## 1. Starting point — the Int213 detour

Initial intent: build ℤ from `Nat213.Peano.Nat213` by sign extension.
- Attempt 1: `inductive Int213 | ofPos Peano.Nat213 | zero | ofNeg Peano.Nat213` — depended on Peano.
- Attempt 2: switched carriers to `Raw` (`ofPos Raw | zero | ofNeg Raw`) — claimed "Raw-derived".

User's critique (verbatim, translated):

> "이게 진짜 Raw 만 가지고 만들어진 게 맞아?  Nat213 은 Raw 에
>  `(1, 1, +)` 라는 lens 를 가지고 만든 건데, Int213 은 Raw 의 어떤
>  lens 를 통해 봐서 만들 수 있는 건가?"
>
> "Is this actually built from Raw alone?  Nat213 was built by
>  applying the lens `(1, 1, +)` to Raw — through which lens of Raw is
>  Int213 supposed to be seen?"

That single question seeded all subsequent insights.

---

## 2. Core insights — by depth

### 2.1 Raw is the free commutative magma on {a, b}

213 axiom minimum:
- two atoms: `Raw.a`, `Raw.b`
- a binary operation `slash`, canonical-form symmetric
  (`slash x y = slash y x`)
- no further equation forced — the free magma

Every "derived structure" therefore arises by **imposing equations
on Raw** (taking a congruence), i.e. is emergent.

### 2.2 A lens is a chart, not a manifold

`LensCore`: `structure Lens α := (base_a, base_b, combine)` plus
`view : Raw → α`.

`Lens.leaves = ⟨1, 1, +⟩` is **one choice**, not a framework-mandated
one.  Alternative lenses:

| Lens | view Raw.a | view Raw.b | view (slash a b) | image |
|---|---|---|---|---|
| `⟨1, 1, +⟩` (leaves) | 1 | 1 | 2 | ℕ₊ |
| `⟨0, 0, fun a b => a+b+1⟩` (slashes) | 0 | 0 | 1 | ℕ (incl. 0) |
| `⟨1, -1, +⟩` (signed) | 1 | -1 | 0 | ℤ |
| `⟨1, 0, +⟩` (a-count) | 1 | 0 | 1 | ℕ |
| `⟨(1,0), (0,1), pairwise+⟩` (pair) | (1,0) | (0,1) | (1,1) | ℕ×ℕ |

→ each lens yields a *different* emergent type.

The statement "Raw.a equals 1" is not framework-forced; it is a
consequence of choosing `Lens.leaves`.

### 2.3 Raw.a and Raw.b are chart-local labels

User's note (verbatim, translated):

> "어떤 Raw a 를 골라도 대응하는 c 가 있기 때문.  a 도 무언가 Raw
>  둘을 구분하는 애일텐데 이건 못 본다.  왜냐하면 기준점이 a 이기
>  때문."
>
> "For any Raw `a` you pick, there is a corresponding `c`.  `a` is
>  itself something that distinguishes two other Raws, but we cannot
>  see *that* — because `a` is our reference point."

`Raw.a` and `Raw.b` are *some* two distinct Raw nominated as
reference.  Under a different reference, those two would be at the
atom position; the current atoms would themselves be a slash of
(two deeper) Raws.

The Lean definition `inductive Tree | a | b | slash` hardcodes **one
chart**.

### 2.4 Raw is not a tree shape — operation and object are not separated

User's note (verbatim, translated):

> "모든 Raw 는 연산이기도 하고 객체이기도 하기 때문 — 즉 애초에
>  연산과 객체도 정의되지 않은 상태이다."
>
> "Every Raw is both an operation and an object — meaning that the
>  distinction between operation and object is itself not given."

```
a, b are atoms
slash a b → c       ← c is the result of slashing a and b (object)
slash a c → d       ← simultaneously c participates as an argument of d (operation)
slash b c → e
slash a d → ...
```

`c` is simultaneously:
- an **object** built from `a` and `b`
- an **operator-part** of the construction of `d`, `e`

**Every Raw is at once node and arrow.**  Lean's `inductive Tree`
forces a node/arrow separation — chart artifact.

The real Raw is a **self-referential cascade**: for an internal
observer to define itself it needs another object; the boundary
between those two is itself an object; the boundary of that boundary
is an object, and so on.  A finite chart of this infinite cascade is
what we call Raw.

### 2.5 Flat ontology — everything is bundles of Raw

| Unit | Element | predicate form |
|---|---|---|
| object (1st-order) | r ∈ Raw | Raw → Bool |
| object (n-th order) | (r₁,…,rₙ) ∈ Rawⁿ | Rawⁿ → Bool |
| type | a subset of Rawⁿ | predicate |
| relation | a subset of Raw² | predicate |
| function | a functional subset of Raw² | predicate + uniqueness |
| Lens | (labelled) predicate | (Raw → α, with α also Raw-encodable) |

**One dimension.**  Types, objects, and relations share a single
universe (the predicate space).

**Caveat (cross-ref §6.7).**  Reading "predicate" as `Set Rawⁿ` (a
`Prop`-valued function) requires `propext` / `Classical` to do most
useful work — which violates the ∅-axiom standard.  The strict
∅-axiom reading uses `Rawⁿ → Bool` (decidable predicates).  The
table above is therefore best read as a *picture* of the flat
ontology; the strict translation lives in §6.7.

Self-referential closure: predicates themselves can be Raw-encoded
(Gödel — see `Lens/Cardinality/Godel.lean`).

### 2.6 Internal vs External representation

**External (current codebase)**:
- `Lens.equiv L x y := L.view x = L.view y` — uses equality in an
  external α
- introduction of a new type α (`Nat`, `Int`, …) is required

**Internal (potential)**:
- an *algebraic congruence* on Raw, expressed by a set of generator
  equations
- candidate: `ℕ₊ = Raw / (a ≡ b ∧ associativity-of-slash)`
- candidate: `ℤ  = Raw / (associativity ∧ [slash a b] ≡ identity)`
- zero dependence on external types

**Caveat.**  The two candidates above are *conjectural*.  In the
current 213, `slash` is canonical-form symmetric (`Raw.slash_comm`,
`lean/E213/Theory/Raw/Slash.lean:32`), but **no `slash_assoc`
theorem exists** — associativity is not derivable from the current
axiom set and would constitute an additional commitment (verified
by `grep` in this session: zero hits for `slash_assoc` across
`lean/E213/Theory/` and `lean/E213/Term/`).  Whether either
candidate congruence quotients Raw onto ℕ₊ / ℤ is therefore an
open question, not a fact.

Were associativity to hold (or were a weaker generator to suffice),
external and internal would be equivalent: agreement of α-values
under the external lens ⟺ same congruence class under the Raw
equations.  This equivalence is asserted here, not proved.

### 2.7 Syntactic internalization (the far end)

User's note (verbatim, translated):

> "{a, b, a/b} 의 모든 글자 자체가 객체 — {, /, , (쉼표), 심지어
>  띄어쓰기도 — 모두 Raw."
>
> "Every glyph in `{a, b, a/b}` is itself an object — `{`, `/`, `,`
>  (comma), even whitespace — all are Raw."

Gödel encoding one step further: not only **referent Raws**
(`Raw.a`, `slash`, …) but also **notation glyphs** (`{`, `}`, `,`,
`/`, …) are each Raw.  An expression becomes a sequence-Raw of
glyph-Raws.

"Meaningless punctuation" is then merely an *external convention*,
not essential; every glyph carries meaning.

**Status: gestural, not formal.**  213's *no exterior* principle
(`seed/AXIOM/07_self_reference.md` §8.1) is suggestive of this
extension, and the meta-meta-…-language cascade is expected to halt
in a finite chart at the resolution limit.  The halting itself is
asserted here, not constructed.  Treat §2.7 as conjecture pending a
minimal prototype.

---

## 3. The natural emergence path for numbers

### 3.1 The most natural path

**Distinction iteration**:
```
pick a reference Raw r₀                            ← "1"
pick another Raw r' with r₀ ≠ r'                   ← new distinguishing marker
slash r₀ r' = r₁                                   ← "2"
slash r₁ r' = r₂                                   ← "3"
...
```

Each chain element `rₙ ∈ Raw` is a Raw-representation of a natural
number in ℕ₊.

Convention (Method A): `r₀ = Raw.a`, `r' = Raw.b`.  Any pair of
distinct Raws would do.

ℕ ⊂ Raw — *type as a subset of Raw* (a direct instance of the
flat ontology of §2.5).

### 3.2 Multi-representation

Each natural number `n` corresponds to *multiple* Raws:

```
leaves count = 1: {Raw.a, Raw.b}             ← two "1"s
leaves count = 2: {slash a b}                ← one "2"
leaves count = 3: {slash a (slash a b),      ← two "3"s
                   slash b (slash a b)}
leaves count = n: roughly (n+1)/2 representations
```

→ "one '1' might be one Raw or many Raws (and even for the same
natural number!)" — exactly this.

Each `n` is one equivalence class of `Lens.leaves.equiv`.

### 3.3 Extending to other number systems — same pattern

- **ℤ**: bidirectional extension of the chain.  `Raw.swap` plays
  the role of a `(-1)` multiplier.  `signedLens = ⟨1, -1, +⟩`.
- **ℚ⁺**: a pair of chains (numerator / denominator), ratio
  quotient.  `Tower/NatPairToQPos`.
- **ℝ**: a Cauchy sequence over ℚ chains (a sequence of chains).
  `Lib/Math/Real213/Cauchy/*`.

Each stage bundles the chains of the previous stage by one
dimension.  **Recursive chain cascade.**

**Caveat for ℝ (must be cross-read with `seed/RESOLUTION_LIMIT_SPEC
.md` §1).**  Under the strict ∅-axiom regime, the Cauchy trajectory
object and the "exact value" object live at *different types* — the
quotient by Cauchy equivalence requires `propext` / `Quot.sound`,
which 213 does not admit.  Consequently the Real213 marathon
operates **on the trajectory side**, proving Cauchy completeness
without claiming `limit = exact value`.  Calling ℝ "emergent via
Cauchy sequence" is convenient shorthand; the literal statement is
that Real213 emerges as the *trajectory* type, with structural
inequality to any putative exact-value type preserved.  Do not
import the ZFC reading by reflex.

### 3.4 Practical consequence

Without going all the way to syntactic decomposition, ℕ, ℤ, ℚ, ℝ
are all emergent.  "Once a natural emergence path for numbers is
fixed, practical mathematical research is possible" — correct.

The codebase *already* realises this partially:
- `Nat213.Raw.numeral, succ, add, mul` (Method A chain + arithmetic)
- `Int213.Raw` (signedLens + `Raw.swap` negation + factoring)
- `Tower/NatPairToQPos, NatPairToInt, NatTripleToZ2` (chain pairs)
- `Lib/Math/Real213/Cauchy/*` (Cauchy sequence, trajectory side
  per §3.3 caveat)

What is missing is *framing*: the existing definitions are written
as "ad-hoc Lean constructions" rather than as instances of natural
emergence.

---

## 4. Current codebase — re-evaluated through the emergence lens

### 4.1 Lens-strict (✓)

| File | Assessment |
|---|---|
| `Lens/LensCore.lean` | core framework, definitions are clean |
| `Lens/Number/Int213/Raw.lean` (post-3371fd14) | signedLens, pairLens, factoring — lens-strict |
| `Lens/Number/Nat213/Core.lean` (post-ced56bef) | `Nat213 := {n // 1 ≤ n}` + `Lens.leaves` view |

### 4.2 Ad-hoc / chart-imposed (⚠ — needs reconsideration)

| File | Issue |
|---|---|
| `Lens/Number/Nat213/Raw.lean` | `add, mul, numeral, succ, addAux, mulAux` defined by direct pattern-match on Tree — bypasses Lens.  `value : Raw → Nat := Raw.fold 1 1 (·+·)` duplicates `Lens.leaves.view`. |
| `Lens/Number/Nat213/Peano.lean` | `inductive Nat213 \| one \| succ` — a parallel inductive type, not Lens-derived. |
| `Lens/Number/Nat213/Bridge.lean` | Peano ↔ Raw isomorphism.  Because Peano is not Lens-derived, the bridge itself is ad-hoc. |
| `Lens/Number/Nat213/NumberingSystem.lean` | numbering patterns beyond Method A, but the chart-relativity meaning is not made explicit. |

### 4.3 Coherence of the "Nat213" name

Currently:
- `Lens.leaves : Lens Nat` (LensCore)
- `Nat213.Raw.value : Raw → Nat`  (= `Lens.leaves.view`, duplicated)
- `Nat213.Peano.Nat213 : Type`  (separate inductive type)
- `Nat213.Core.Nat213 : Type := {n // 1 ≤ n}`  (Phase 1, Lens-image subtype)
- `Nat213.Peano.toNat : Peano.Nat213 → Nat`  (yet another view)

→ "Nat213" is split across 4–5 meanings.  Coherence is needed.

---

## 5. Options — where to go

### Option A: Lightweight reframing (no code change)

- add a docstring to `Nat213/Raw.lean` etc. naming it "Method A
  distinction-iteration chain; the emergent path of `Lens.leaves`"
- add a new note under `seed/AXIOM/` covering chart-relativity,
  flat ontology, syntactic internalization
- do not touch the code; only realign framing

**Pro**: zero risk, lightest.
**Con**: the chart-imposed feel of the code remains.

### Option B: Predicate-based Raw subtype

- define `IsMethodAChain : Raw → Prop` ("this Raw is an element of
  the chain")
- introduce `Nat213.Chain := { r : Raw // IsMethodAChain r }`
- arithmetic closed over Chain
- keep existing `Nat213.Raw.{add, mul, ...}`, optionally deprecate
  or redefine via Chain

**Pro**: Raw-native, arithmetic closed within Raw.
**Con**: adds a new layer, runs in parallel with existing code.

### Option C: Full lens-strict refactor (Phase 1 has already landed)

- delete the ad-hoc arithmetic in `Nat213.Raw.lean`
  (`add, mul, numeral, succ, addAux, mulAux`)
- move all arithmetic to the codomain (`Nat`); the Raw side keeps
  only `value` and lens theorems
- remove `Nat213.Peano.lean` (or isolate it as ergonomic parallel)
- rewrite `Bridge.lean`, update Tower files, audit downstream
  `Lib/Physics`

**Pro**: maximal coherence, lens-strict.
**Con**: multi-file refactor (9+ files), large work.

**Status**: `Nat213/Core.lean` (commit `ced56bef`) is Phase 1 of this
option.  Phases 2–7 remain.

### Option D: Chart-explicit framework

- expose the fact that `Nat213.Raw`'s `one` / `succ` are *an
  arbitrary chart choice*
- add a parameterised definition such as
  `Nat213.RawFromChart (r₀ r' : Raw) (h : r₀ ≠ r')`
- prove that other charts are equally valid (chart-invariance
  theorem)
- the current `Raw.a`, `Raw.b` is then "the default chart"

**Pro**: philosophy and code line up; chart-relativity made
explicit.
**Con**: largest scope, affects all downstream.

### Option E: Internal congruence (algebraic equations)

- inductively define `Eqv : Raw → Raw → Prop` from a set of
  generator equations
- represent equivalence by `Eqv` directly, without taking a quotient
  (preserves ∅-axiom)
- the meaning of each lens is determined by its generator set

**Pro**: internal representation, most axiom-pure.
**Con**: new abstraction layer, all lens theorems re-proved.

**Reminder**: Option E depends on §2.6 — the candidate generators
(e.g. associativity) are not yet established as derivable.

---

## 6. Open questions — to be settled before action

1. **Which option (A–E)?**  Single?  Combined?  Recommendation:
   **A + B + (Option C Phase 1 preserved)** as the most balanced,
   but see §7 for the post-hoc note.

2. **Canonical definition of `Nat213`?**
   - `{n : Nat // 1 ≤ n}` (Nat subtype, current Phase 1)
   - `{r : Raw // IsMethodAChain r}` (Raw subtype)
   - both (linked by iso)

3. **ℕ vs ℕ₊?**
   - `Lens.leaves` forces ℕ₊
   - slash-count lens `⟨0, 0, fun a b => a+b+1⟩` gives ℕ (incl. 0)
   - which is "the default"?  Expose both?

4. **Canonicality of the Method A chain?**
   - a single canonical chain?  Or an atlas?
   - do we state "any chart is valid" as a theorem?

5. **Status of `Peano.lean`?**
   - delete?  Keep only the isomorphism with the Lens-derived form?
   - "ergonomic parallel" with an explicit `Lens.leaves` bridge?

6. **Syntactic internalization — how far?**
   - L1 (referent Gödel) only: current codebase
   - L2 (glyph → Raw mapping): minimal prototype is feasible
   - L3+ (full meta-circular): large project

7. **Flat ontology in Lean?**
   - `Set Raw`, `Set (Raw × Raw)` — depend on propext / classical
   - `Raw → Bool` (decidable predicates) — ∅-axiom-clean
   - how far is "enough"?

---

## 7. Recommendation — a balanced path

Honest note: Option C Phase 1 has *already* landed in commit
`ced56bef`.  The recommendation below is therefore partly post-hoc
rationalisation of the path already taken; Steps 2–3 remain genuinely
open.

### Step 1 (short term, light):

- commit this document (`research-notes/2026-05-18_lens_emergence_path
  .md`)
- add a one-page note under `seed/AXIOM/` covering *chart-freeness +
  flat ontology + syntactic internalization* (slot 08?)
- add a one- or two-line docstring to `Nat213/Raw.lean` and
  `Nat213/Peano.lean` framing them as *one representation along an
  emergence path; chart-local*
- zero code change

### Step 2 (medium term, safe addition):

- Option B: define `IsMethodAChain : Raw → Prop` and expose
  `Nat213.Chain` subtype
- leave existing `Nat213.Raw.{add, mul, numeral, succ}` as-is
  (not deprecated)
- add closed-Raw arithmetic theorems on the Chain subtype
- the emergent framing becomes code-visible without breaking
  existing code

### Step 3 (long term, big cleanup):

- continue Phases 2–7 of Option C from the Phase 1 base
  (`Nat213/Core.lean`)
- multi-file refactor, coherence including downstream
- only after sufficient reflection following Step 2

### Step 0 (self-reflection):

This document is itself one chart — the view we currently take.  A
re-read months later may surface additional insight.  Keeping it as
a working note has its own value.

---

## 8. One-line summary

> Starting from the 213 minimum (Raw + slash), the choice of *how to
> bundle* — that is, which lens / chart to pick — generates every
> derived structure.  Numbers (ℕ, ℤ, ℚ, ℝ) are a chain-iteration
> cascade — distinction iterating on itself.  The current codebase
> is one Lean encoding of one representation of one chart of that
> cascade; some non-essential chart artifact is mixed in.  Honouring
> the original meaning of the Lens framework lets the whole thing
> close inside the self-referential cascade.

---

## 9. Next action — commit this?

The lightest start: commit this document as the first step, then
proceed with the other Step 1 actions (a `seed/` note, the
one-line docstrings).

Alternatively, keep this as working notes only and skip the commit.

Decision rests with the user.
