# Lens Emergence Path — natural emergence of numbers and flat ontology

**Status**: completed.  All recommendations of this note have been
realised on the `claude/review-lens-emergence-path-ZtS3A` branch
(2026-05-18).  See `HANDOFF.md` for the result summary.
**Date**: 2026-05-18.

This note is now a *record of the reasoning* that motivated the
work, kept for posterity.  The §2–§3 insights remain the
substantive content; the original §4–§9 (options catalogue, open
questions, recommendation, next-action) have been removed since
they are fully resolved.

---

## 0. Purpose of this document

A consolidation of the insights that accumulated during the
conversation.  The reader is given a vocabulary (chart, flat
ontology, emergence path) and the natural emergence paths for
ℕ, ℤ, ℚ, ℝ.

The original §5–§7 (options catalogue, open questions,
recommendation) and §9 (next action) have been deleted — every
recommendation has been carried out on the
`claude/review-lens-emergence-path-ZtS3A` branch.  See
`HANDOFF.md` for the result summary.  The §1–§3 insights remain
as the substantive content.

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

**Caveat — and a 2026-05-18 correction (Mingu Jeong).**  The two
candidates above are *not just conjectural — the framing is wrong*.

In the 213 axiom set, `slash` is canonical-form symmetric
(`Raw.slash_comm`, `lean/E213/Theory/Raw/Slash.lean:32`) and that
is *all* the equational structure on Raw.  In particular,
**`slash_assoc` does not hold and *should not* hold**:
`Raw.slash (Raw.slash x y h₁) z h₂` and `Raw.slash x (Raw.slash y z
h₃) h₄` build *different Tree shapes* with the same multiset of
leaves.  Those two Raws are *legitimately distinct* — the
parenthesisation (= tree shape) is itself Raw-internal structure,
not meta-language artifact.  Forcing associativity via a generator
quotient would *erase* Raw-internal information; that is
information-loss, not normalisation.

(Even the source-text parentheses are themselves Raw-encodable per
§2.7 — meta-syntax and Raw-structure converge in the
self-referential reading.)

Concrete witness:
`lean/E213/Theory/Raw/ParenthesizationDistinct.lean` —
kernel-evaluated counter-example showing
`(a/b)/(b/(a/b)) ≠ a/(b/(b/(a/b)))` as Raws.

**Therefore**: ℕ₊ is **not a quotient of Raw**.  It is the
*projection-image* of `Lens.leaves.view : Raw → Nat`.  The
projection is many-to-one (different Raws → same leaves count) and
that *is* the structure.  Option C of the refactor (commit
`9efd8263`) realised this picture: `Raw` carries the chart
representative, `Nat` carries the abstract number, the projection
makes the bridge.

The `Eqv`-quotient approach (Option E) remains useful as a
*generic* construction (`Theory.Raw.Congruence` +
`Lens.Congruence`), and yields a clean
"`Eqv L.equiv ↔ L.equiv` for any lens".  But the specific §2.6
candidates `ℕ₊ = Raw / (a ≡ b ∧ slash_assoc)` and
`ℤ = Raw / (assoc ∧ [slash a b] ≡ identity)` are abandoned — they
ask for an equivalence that throws away content.

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
(`seed/AXIOM/05_no_exterior.md` §5.1) is suggestive of this
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

## 4. One-line summary

> Starting from the 213 minimum (Raw + slash), the choice of *how to
> bundle* — that is, which lens / chart to pick — generates every
> derived structure.  Numbers (ℕ, ℤ, ℚ, ℝ) are a chain-iteration
> cascade — distinction iterating on itself.  The current codebase
> is one Lean encoding of one representation of one chart of that
> cascade; some non-essential chart artifact is mixed in.  Honouring
> the original meaning of the Lens framework lets the whole thing
> close inside the self-referential cascade.

---

