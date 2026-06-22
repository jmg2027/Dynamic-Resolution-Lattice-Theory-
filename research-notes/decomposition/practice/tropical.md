# Decomposition: tropical mathematics / idempotent semirings

*213-decomposition of the tropical (max,+) / (min,+) semiring, tropicalization, the
Maslov dequantization limit, and tropical polynomials/curves, per `../README.md` (model
v7.1). The bar is **PREDICTION/REVELATION, consolidating five prior entries**:
`exponential.md` (the `×↦+` character arrow), `entropy.md` (the `weight∘log`-character,
`log₂(2^n)=n` on the dyadic substrate), `convex_duality.md` (Legendre–Fenchel = `clo`),
`free_corner.md`/README v6 (the **iteration-character** axis: nilpotent `∂` / idempotent
`clo` / growing `S`), and `galois.md`/`adjunction.md` (the `clo` closure / the max-lattice
sup). Hypothesis: the tropical semiring is **not a new field** — it is the `×↦+` character
arrow pushed to its **idempotent `T→0` limit**, where `max` IS the idempotent (`clo`-flavoured)
pole of the iteration-character axis the calculus already built.*

This entry is split into a **grounded core** (the max/min lattice operations, the idempotency
`max(a,a)=a` — with the load-bearing find that the repo's own docstring already reads it as
the iteration-character's idempotent pole — and the `×↦+` log-character it degenerates) and a
**flagged conceptual leg** (the actual tropical *semiring object*, the tropicalization map, the
dequantization `t·log(e^{a/t}+e^{b/t})→max`, and tropical polynomials — all **absent**, located
precisely like `knots.md` and `convex_duality.md` located their missing primitives).

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the same `(ℝ∪{±∞}, ·)`-style construction whose elements are
  `Real213` **cuts**: numbers built as descending/ascending Bool-tests `Nat → Nat → Bool`
  (`CutMaxMin.lean`), carrying the additive `+`-structure (`cutMul`/`cutSum` imports) and a
  **fold-height** sub-structure (README model v4). Nothing new is constructed for "tropical":
  it reads the *same* number-construction at a degenerate resolution.

- **Reading `L = the `×↦+` log-character at its `T→0` idempotent limit`** — the central
  claim, in two stages:
  1. **The log-character `×↦+`** (`exponential.md`/`entropy.md`'s arrow): `vp_mul`
     (`Meta/Nat/VpMul.lean:165`) is the homomorphism `× ↦ +`; on the dyadic substrate
     `surprise_dyadic_eq_depth` (`Entropy.lean:55`) realizes `log₂(1/2^k)=k` as `rfl`, with
     `surprise_additive` (`Entropy.lean:90`) the `log(ab)=log a+log b` homomorphism. The
     classical dequantization `x⊕y := lim_{t→0} t·log(e^{x/t}+e^{y/t}) = max(x,y)` is
     **this very `×↦+` character** (`log`-of-a-`+`) pushed to the `t→0` resolution, where the
     softmax `t·log Σ e^{·/t}` collapses to the hard `max` and the product `×` collapses to `+`.
  2. **The idempotent collapse** — at `T→0` the additive `+` of the semiring becomes `max`,
     and `max` is **idempotent**: `max(a,a)=a`. This is the iteration-character axis's
     idempotent pole (README v6: nilpotent `∂` / idempotent `clo` / growing `S`), the literal
     `clo`-flavoured `T²=T` reading. The repo proves the idempotency directly: `max_idem`
     (`Meta/Nat/Iterate213.lean:235`, `Nat.max a (Nat.max a x) = Nat.max a x`), and — the
     load-bearing find — its **own docstring already reads it as the iteration-character**:
     *"`a∪a=a`: the diagonal climb is multiplicative only where the rung-operator is **not**
     idempotent — `max`/`∪` builds no tower"* (`Iterate213.lean:241-245`,
     `max_iter_trivial`). The tropical sum is therefore the **`clo`-idempotent pole** of the
     same axis whose **growing pole** is `succ_not_idempotent` (`MuNuMirror.lean:80`, whose
     docstring names it the "mirror of `clo_idempotent`" on the iteration-character axis).

  As a lattice reading the tropical `⊕=max` / `⊗=+` is `galois.md`'s order structure made into
  an algebra: `cutMax` (`CutMaxMin.lean:23`, `cx m k && cy m k` = the join/sup of cuts) and
  `cutMin` (`:27`, `cx m k || cy m k` = the meet), commutative + associative
  (`cutMax_comm`/`cutMax_assoc`, `:56`/`:66`), with abstract idempotency of join/meet
  `idem_sup`/`idem_inf` (`BooleanAlgebra.lean:40`/`:31`, `sup a a=a` / `inf a a=a`). `max` IS
  the lattice sup `CutMaxMin` builds.

- **Residue** — tagged **`q=+1` (converging/closure pole)**, two faces:
  1. the **dequantization residue**: the parameter `t` is a *resolution* dial
     (`derivative.md`'s resolution axis), and `t→0` is the limit that is *reached by none, only
     bracketed* — the same `e`/`log₂e` residue as `exponential.md`/`entropy.md`
     (`chebyshev_constant_interval`, `ChebyshevLower.lean:387`, `log₂e ∈ [(m+1)/(2(m+2)),6]`).
     "Tropical" is the residue at the `t→0` end of the softmax-resolution dial, never the dial's
     operand.
  2. the **Legendre/closure residue**: the tropical product of *polynomials* = the infimal
     convolution = the Legendre-dual of addition, which is `convex_duality.md`'s `clo=G∘F`
     closure (`clo_idempotent`, `GaloisConnection.lean:126`); the tropical idempotency
     `a⊕a=a` is the *settled* (`q=+1`) closure, not the Cantor `q=−1` escape.

## Re-seeing — `⟨C | L⟩ ⊕ Residue`

```
   log-character (×↦+)        =  vp p (m·n)=vp p m+vp p n                       (vp_mul)            × ↦ +
   dyadic realization         =  surpriseBitsDyadic k = k  (log₂(1/2^k)=k)      (surprise_dyadic_eq_depth, rfl)
   dequantization a⊕b         =  lim_{t→0} t·log(e^{a/t}+e^{b/t}) = max(a,b)     [CONCEPTUAL: the t→0 collapse]
   tropical sum ⊕ = max        =  the lattice sup                                (cutMax = cx&&cy, CutMaxMin:23)
   ★ idempotency a⊕a=a        =  Nat.max a (Nat.max a x) = Nat.max a x           (max_idem, Iterate213:235)
   "max builds no tower"      =  iter (max a) (n+1) x = max a x                  (max_iter_trivial, :246)  ← idempotent pole
       its growing mirror     =  S(S r) ≠ S r                                    (succ_not_idempotent, MuNuMirror:80) ← growing pole
   abstract join idempotent   =  sup a a = a                                     (idem_sup, BooleanAlgebra:40)
   tropical product ⊗ = +      =  the surviving additive structure of C
   tropical(poly) = Legendre   =  f** = clo(f) = the closed (convex) hull        (clo_idempotent, GaloisConnection:126)  [object CONCEPTUAL]
   t→0 residue                 =  the resolution dial's reached-by-none end       (chebyshev_constant_interval, log₂e bracket)
```

**(1) Tropical `⊕=max` IS the `×↦+` character at its idempotent limit.** The dequantization
`x⊕y = t·log(e^{x/t}+e^{y/t})` is, term for term, the **log-character of a sum** — the
`×↦+`/`log` arrow of `exponential.md` (`vp_mul`) and `entropy.md` (`surprise_additive`). At
`t→0` the softmax `t·log Σ e^{·/t}` hardens to `max` and the multiplication degenerates to `+`.
So tropical is not a new operation: it is the **`T→0` degenerate reading of the one character
arrow** the calculus runs through parity / valuation / det / entropy / Noether / Fourier / ζ —
its eighth instance, read at the resolution where the character collapses `+↦max` and `×↦+`.

**(2) Idempotency `a⊕a=a` is the iteration-character's idempotent (`clo`-flavoured) pole — and
the repo already says so.** This is the leverage moment. The iteration-character axis (README v6,
`free_corner.md`) has three poles: nilpotent `∂` (`∂²=0`), idempotent `clo` (`T²=T`), growing `S`
(`Tⁿ` ascends). The tropical sum's defining law `a⊕a=a` is **exactly the idempotent pole** —
`max_idem` (`Iterate213:235`) is `T²=T` for the rung-operator `max a`. The decisive datum: the
repo's own docstrings, written before any tropical decomposition, already classify `max` this way
— `max_iter_trivial`'s comment "`max`/`∪` builds no tower … the diagonal climb is multiplicative
only where the rung-operator is **not** idempotent" (`:241-245`) is the iteration-character axis
stated negatively, and `succ_not_idempotent`'s docstring (`MuNuMirror:80`) names `max`'s mirror —
the *growing* pole — as "the exact mirror of `clo_idempotent` (`T²=T`) … the two values of the
decomposition calculus's iteration-character axis." So `max` was *already* identified as the
idempotent pole opposite the growing successor; tropicalization is just that pole armed with a `⊗`.

**(3) Tropical product of polynomials = the Legendre dual = `convex_duality.md`'s closure.** The
tropical product of tropical polynomials (piecewise-linear functions) is the **infimal
convolution** `(f□g)(x)=inf_{u+v=x}(f(u)+g(v))`, the Legendre-dual of addition:
`(f□g)* = f*+g*`. This is `convex_duality.md`'s `f**=clo(f)` closure on the function lattice
(`clo_idempotent`, `GaloisConnection:126`) — tropical polynomials live on the **`q=+1`
convex/closed locus**, where the Legendre transform is an involution and the closure is the
identity. Tropicalizing a polynomial = taking its Newton-polygon/Legendre dual = the closure of
`convex_duality.md`, read on the (max,+)-piecewise-linear functions.

## LEVERAGE — does the tropical semiring fall out as the `×↦+` character's idempotent `T→0` limit?

**Verdict: PREDICTION (a five-entry consolidation) — with one real PARTIAL, the tropical
*semiring/tropicalization/dequantization object itself* absent, located precisely.** Tropical
mathematics is not a new field; it is the **single `×↦+` character arrow read at its idempotent
`T→0` resolution-limit**, tying together five prior entries that were not previously known to be
one. Four legs, honestly graded.

**(A) `⊕=max` = the `×↦+` character at `T→0`; `⊗=+` the surviving structure — PREDICTED,
the character grounded, the dequantization map conceptual.** The character `×↦+` is built and
certified (`vp_mul`, `surprise_additive`, `surprise_dyadic_eq_depth`). The claim "tropical `⊕`
is this character pushed to `t→0`" is structurally exact — `t·log(e^{x/t}+e^{y/t})` is the
log-of-a-sum, the character's defining shape. *Conceptual leg:* the **softmax/dequantization map
`(x,y)↦t·log(e^{x/t}+e^{y/t})` and its `t→0` limit object are not built** — there is no
`tropicalize`, `dequantize`, `softmax`, or `tLog` in the repo (grep: zero hits; the only
`max-plus`/`tropical` strings are *comments* — `RawDagSize.lean:12` labels the depth-fold
"max-plus algebra", `DiscreteGeometry.lean:111` calls shortest paths "a tropical/min-plus
structure" — neither a semiring object). The character it degenerates *from* is certified; the
degeneration *map* is conceptual.

**(B) Idempotency `a⊕a=a` = the iteration-character's idempotent pole — PREDICTED AND GROUNDED
(the surprise, the leg I expected weakest is strongest).** `max_idem` (`Iterate213:235`) is a real
∅-axiom theorem `Nat.max a (Nat.max a x) = Nat.max a x` — literally `T²=T` for `max a`. Better: the
repo's *own* docstrings already place it on the iteration-character axis (`max_iter_trivial`'s "max
builds no tower"; `succ_not_idempotent`'s "mirror of `clo_idempotent`"). The abstract join
idempotency `idem_sup` (`BooleanAlgebra:40`, `sup a a=a`) and the cut-lattice sup `cutMax`
(`CutMaxMin:23`) ground the lattice reading. **The defining law of the tropical semiring — the one
fact that makes it "tropical" rather than a ring — is the iteration-character's idempotent pole, and
the repo built and named that pole independently.** This is the entry's strongest grounding.

**(C) Tropical product of polynomials = Legendre dual = the `clo` closure — PREDICTED, the closure
grounded, the transform object conceptual (inherited from `convex_duality.md`).** The infimal-
convolution/Legendre structure is `convex_duality.md`'s `clo=G∘F` (`clo_idempotent`,
`clo_extensive`, `GaloisConnection:104-126`), all ∅-axiom. The tropical product = inf-convolution =
the Legendre dual of `+` sits on the `q=+1` convex-closed locus where this closure is exact.
*Conceptual leg:* the **Legendre transform object `f*` itself is absent** — exactly the missing leg
`convex_duality.md` located (no `convexConjugate`/`biconjugate`/`infConvolution` in the repo). The
closure *machine* is present; the (max,+)-function-lattice *instance* is unwritten.

**(D) Dequantization `t→0` = the resolution-limit residue — PREDICTED, the residue-as-bracket
grounded.** The softmax parameter `t` is a resolution dial (`derivative.md`/`continuity.md`'s
resolution axis); `t→0` is the limit reached by none, bracketed by a modulus — the *same* status as
`e`/`log₂e` (`chebyshev_constant_interval`, `ChebyshevLower:387`). Tropical geometry =
algebraic geometry at the `t→0` resolution residue is the structural prediction; the residue-as-
narrowing-interval status is grounded, the `t→0` limit *object* is the conceptual leg (B's softmax).

**Net.** Not collapse-only (it **predicts** the form of tropical algebra from five prior entries and
*derives why*: `⊕=max` is the character at `T→0`, `a⊕a=a` is the idempotent pole, `⊗`-on-polynomials
is the Legendre closure, `t→0` is the resolution residue). Not a miss (the `×↦+` character, the
idempotency `max_idem` *named on the iteration-character axis by the repo itself*, the lattice sup
`cutMax`, the `clo` closure, and the `log₂e` resolution residue are **all ∅-axiom theorems**). It is
a **prediction whose every structural leg is grounded and whose missing legs are *named objects*
(the tropicalization/softmax map, the `t→0` dequantization limit, the Legendre transform `f*`), not
missing structure** — the structure they inhabit (the character arrow, the idempotent pole, the
`clo` closure, the resolution dial) is wholly present.

## Revelation

**Tropical mathematics is ONE `(C,L)` — the `×↦+` character arrow read at its idempotent `T→0`
resolution-limit — and `max` IS the iteration-character's idempotent pole the repo built and named
independently.** This is a **collapse + forcing + residue-surfaced**, three at once:

1. **Collapse — tropical is the eighth face of the one character arrow.** The dequantization
   `x⊕y = t·log(e^{x/t}+e^{y/t}) → max` is the `×↦+`/`log`-character (`vp_mul`,
   `surprise_additive`) read at `t→0`. So the tropical semiring is **not a new structure** — it is
   parity `L₂` / valuation `vp_mul` / det / entropy / Noether / Fourier / ζ's *same arrow* at the
   degenerate resolution where `+↦max` and `×↦+`. The five "different" things — the (max,+) sum, the
   idempotency, the tropical product, dequantization, and the convex/Legendre dual — are **one
   `(C,L)`**: the character at `T→0`, with its idempotent pole, its `clo` closure, and its resolution
   residue.

2. **Forcing — `max` is forced as the idempotent pole, not chosen.** Idempotency `a⊕a=a` is *not an
   arbitrary axiom* distinguishing tropical algebra: it is the iteration-character axis's **idempotent
   `clo`-flavoured pole** (`max_idem` = `T²=T`), the exact mirror of the growing successor
   (`succ_not_idempotent`, whose docstring names the mirror). The decisive datum is that the repo
   *already* read `max` this way — "`max` builds no tower … multiplicative only where the rung is not
   idempotent" (`max_iter_trivial`) — **before** any tropical decomposition. The thing that makes a
   semiring "tropical" (idempotent `+`) is forced by the calculus's pre-existing iteration-character
   axis: tropical = the algebra you get when the iteration-character's idempotent pole becomes the
   `⊕`.

3. **Residue surfaced — `t→0` is the resolution residue, not a god above the finite.** Classical
   accounts present tropicalization as a limit *into* a new realm; the calculus re-sees `t` as a
   **resolution dial** (`derivative.md`) whose `t→0` end is the residue reached by none, bracketed by
   a modulus — the *same* `log₂e`/`e` residue (`chebyshev_constant_interval`), `q=+1` (settles,
   converges to the hard max). Tropical geometry = algebraic geometry at this resolution residue.

**THE CONSOLIDATION (the brief's central question):** tropical mathematics is the meeting point of the
notebook's two load-bearing invariants — the **`×↦+` character arrow** (`exponential`/`entropy`) and
the **iteration-character's idempotent pole** (`free_corner`/`galois`/`adjunction`'s `clo`) — read
through the **resolution dial** at `T→0`:

| pillar | 213 reading | prior entry | Lean status |
|---|---|---|---|
| tropical sum `⊕ = max` | the `×↦+` log-character at `t→0`; the lattice sup | `exponential`/`entropy`; `galois` | character **built** (`vp_mul`, `surprise_additive`); sup **built** (`cutMax`); softmax map conceptual |
| **idempotency `a⊕a=a`** | the iteration-character's **idempotent pole** `T²=T` | `free_corner`/README v6 | **built** (`max_idem`), *named on the axis by the repo* (`max_iter_trivial`, `succ_not_idempotent`) |
| tropical product `⊗ = +`, on polys = inf-conv | the surviving `+`; the Legendre dual = `clo` closure | `convex_duality` | closure **built** (`clo_idempotent`); transform object `f*` conceptual |
| dequantization `t→0` | the resolution dial's reached-by-none end, `q=+1` | `derivative`/`exponential` | residue-bracket **built** (`chebyshev_constant_interval`); `t→0` limit object conceptual |

So **YES** — the tropical `(max,+)` semiring falls out as the `×↦+` character arrow at its idempotent
`T→0` limit: **`max` = the `clo`-idempotent pole** the repo built and named on the iteration-character
axis (`max_idem`, mirror of `succ_not_idempotent`), **the tropical product = the Legendre/infimal-
convolution dual** = `convex_duality.md`'s `clo` closure, and **dequantization = the resolution-limit
residue** (`derivative.md`'s dial at `t→0`, the `e`/`log₂e` bracket). Tropical mathematics consolidates
`exponential` + `entropy` + the idempotent iteration-character + `convex_duality` + the max-lattice
with **no new axis**.

## Note for the technique — does tropical force a new construct?

**Verdict: EXTEND by consolidation — no new primitive.** Every slot tropical uses already exists:
- **the `×↦+` character arrow** (`exponential`/`entropy`'s `vp_mul`/`surprise_additive`) — the tropical
  `⊕` is its `T→0` degenerate reading;
- **the iteration-character's idempotent pole** (`free_corner`/README v6's `clo`-flavoured `T²=T`,
  `max_idem`) — the tropical `a⊕a=a`, *the* defining tropical law;
- **the lattice sup** (`galois`/`CutMaxMin`'s `cutMax`, `idem_sup`) — `max` as join;
- **the `clo` closure** (`convex_duality`/`adjunction`'s `clo_idempotent`) — the tropical product /
  Legendre dual on the `q=+1` convex-closed locus;
- **the resolution dial** (`derivative`/`continuity`) — the dequantization parameter `t`, `t→0` its
  reached-by-none residue.

The one sharpening: **tropicalization is the calculus's first explicit "character-at-a-resolution-
limit" reading** — it composes the character-mode (`×↦+`) with the resolution dial (`t→0`) and lands
exactly on the iteration-character's idempotent pole. Previously the character-mode and the resolution
dial were separate `L`-parameters; tropical shows that **dialing the character's resolution to its
degenerate limit selects an iteration-character pole** (here idempotent). That cross-tie — *resolution
limit of the character ⇄ iteration-character pole* — is the structural lesson, recorded as an
EXTEND, not a new axis.

## Verified Lean anchors (file:theorem:line — all grep/Read-verified; purity per file imports, no Mathlib)

| Leg | Theorem (file : name : line) | Status |
|---|---|---|
| ★ **idempotency `a⊕a=a` = the iteration-character's idempotent pole `T²=T`** | `Meta/Nat/Iterate213.lean : max_idem : 235` (`Nat.max a (Nat.max a x) = Nat.max a x`); `max_unfold : 229`; `max_iter_trivial : 246` ("max builds no tower") | ∅-axiom ✓ (decidable case-split, no `propext`/`Classical`) |
| ★ **the growing-pole mirror** (the iteration-character axis, repo-named) | `Theory/Raw/MuNuMirror.lean : succ_not_idempotent : 80` (`S(S r) ≠ S r`; docstring: "mirror of `clo_idempotent`, the calculus's iteration-character axis") | ∅-axiom ✓ |
| **tropical sum `⊕ = max` = the lattice sup** | `Lib/Math/NumberSystems/Real213/Lattice/CutMaxMin.lean : cutMax : 23` (`cx m k && cy m k`), `cutMin : 27` (`||`), `cutMax_comm : 56`, `cutMax_assoc : 66`, `cutMin_comm : 46`, `cutMin_assoc : 76` | ∅-axiom ✓ (Bool combinators, `rfl`/`cases`) |
| **abstract join/meet idempotency** (lattice sup/inf) | `Lib/Math/Order/BooleanAlgebra.lean : idem_sup : 40` (`sup a a = a`), `idem_inf : 31` (`inf a a = a`) | ∅-axiom ✓ (parametrized, from absorption) |
| min/max base order | `Meta/Nat/Max213.lean : le_max_left : 39`, `le_max_right : 51`, `max_eq_left : 25` | ∅-axiom ✓ |
| **the `×↦+` log-character** (tropical `⊕` degenerates from this) | `Meta/Nat/VpMul.lean : vp_mul : 165` (`vp p (m·n)=vp p m+vp p n`), `vp_pow : 183`, `vp_self_pow : 204` | ∅-axiom ✓ |
| **dyadic log realization** (`log₂(1/2^k)=k`) | `Lib/Math/Probability/Information/Entropy.lean : surprise_dyadic_eq_depth : 55`, `surprise_additive : 90` (`log(ab)=log a+log b`) | ∅-axiom ✓ (`rfl`) |
| **tropical product / Legendre dual = the `clo` closure** | `Lib/Math/Order/GaloisConnection.lean : clo : 104`, `clo_idempotent : 126` (`T²=T`), `clo_extensive : 107`, `clo_monotone : 114` | ∅-axiom ✓ (15 pure / 0 dirty) |
| **dequantization `t→0` = resolution residue** (`e`/`log₂e` bracket) | `Lens/Number/Nat213/ChebyshevLower.lean : chebyshev_constant_interval : 387` (`log₂e ∈ [(m+1)/(2(m+2)),6]`) | ∅-axiom ✓ (prior, `exponential.md`/`entropy.md`) |
| `e` as residue cut (the transcendental status of the `t→0` limit) | `Lib/Math/NumberSystems/Real213/ExpLog/EulerCut.lean : eulerCut_in_8_3_to_3 : 85`; `cutLog`/`cutExp` (`ExpLog/CutLogSeries.lean:49`, `CutExpSeries.lean:58`) | ∅-axiom ✓ |

## Conceptual-only legs (honest — NOT grounded in repo Lean; the located missing primitives)

- **The tropical semiring *object* `(ℝ∪{±∞}, max, +)` itself** — **absent.** No `TropicalSemiring`,
  `MaxPlus`, `MinPlus`, or idempotent-semiring structure in the repo. The only `tropical`/`max-plus`
  strings are *comments*: `Lib/Math/Foundations/UniverseChain/RawDagSize.lean:12` labels the depth-fold
  "max-plus algebra" (a naming convention on `Raw.fold`, not a semiring), and
  `Cohomology/HodgeConjecture/Bridge/DiscreteGeometry.lean:111` calls graph shortest-paths "a
  tropical/min-plus structure" (a conceptual remark). The *ingredients* (`max`, `+`, idempotency) are
  all built and ∅-axiom; the *semiring bundling them as a tropical algebra* is unwritten — the precise
  missing leg, parallel to `convex_duality.md`'s missing transform object and `knots.md`'s located
  boundary.
- **The tropicalization / dequantization map** `(x,y) ↦ t·log(e^{x/t}+e^{y/t})` and its `t→0` limit
  — **absent.** No `tropicalize`, `dequantize`, `softmax`, `tLog`, or `t→0` semiring-degeneration object
  (grep: zero hits). This is **the central missing leg the brief asked for**: the character arrow it
  degenerates *from* (`vp_mul`/`surprise_additive`) and the idempotent pole it lands *on* (`max_idem`)
  are both grounded ∅-axiom, but the **degeneration map welding them — the Maslov dequantization limit
  — is conceptual.** The one weld that would promote this entry: define `softmax_t (x y) := t·cutLog(cutExp(x/t)+cutExp(y/t))`
  on the `Real213` cuts, show it is the `×↦+` character (via `cutLog`/`cutExp`), and prove its `t→0`
  resolution-residue is `cutMax` — instantiating the resolution dial at the idempotent pole.
- **Tropical polynomials / tropical curves / the Newton polygon** — **absent.** No `NewtonPolygon`,
  `piecewiseLinear`, `infConvolution`, or tropical-polynomial object. The Legendre/inf-convolution
  structure they would use is `convex_duality.md`'s `clo` closure (present and certified), but the
  transform object `f*(p)=sup_x(px−f x)` is itself the leg `convex_duality.md` already located as
  absent — so tropical polynomials inherit that exact missing primitive.
- **The `min-plus` ⇄ `max-plus` duality as a built negation/order-reversal** — the abstract order-
  reversal is in `galois.md`'s `clo=Inv∘Fix`, but no `tropical` instance pairs `cutMax`/`cutMin` as the
  two semiring additions via a sign/negation reading (the `ℤ`-style direction toggle of `integers.md`).

## Verdict: PREDICTION (consolidating exponential + entropy + iteration-character + convex_duality + max-lattice), one PARTIAL

Tropical mathematics **predicts and consolidates** — it does not break the model and adds no axis. The
load-bearing claims are all grounded ∅-axiom: the **`×↦+` character** the tropical `⊕` degenerates from
(`vp_mul`, `surprise_additive`), the **idempotent pole** that is the defining tropical law — *named on
the iteration-character axis by the repo's own docstrings* (`max_idem`, mirror of `succ_not_idempotent`)
— the **lattice sup** (`cutMax`, `idem_sup`), the **`clo` closure** the tropical product / Legendre dual
inhabit (`clo_idempotent`), and the **`t→0` resolution residue** (`chebyshev_constant_interval`). The one
PARTIAL is the **tropical semiring / tropicalization / dequantization-limit object itself** (with tropical
polynomials and the Legendre transform `f*`) — absent, located precisely: the character it degenerates
from, the idempotent pole it lands on, the closure it inhabits, and the resolution dial it rides are all
present and certified; only the **dequantization map welding them (`t·log(Σe^{·/t})→max`) and the semiring
that bundles `max`/`+`** are unwritten.

> **Open Lean target the calculus names precisely:** define the softmax dequantization
> `softmax_t (x y) := t · cutLog (cutExp (x/t) + cutExp (y/t))` on the `Real213` cut-construction
> (`ExpLog/CutLogSeries`, `CutExpSeries`), prove it is the `×↦+` character, and show its `t→0`
> resolution-residue (the `derivative.md` dial) is `cutMax` — i.e. **instantiate the resolution dial at
> the iteration-character's idempotent pole `max_idem`**. Then bundle `(cutMax as ⊕, cutAdd as ⊗)` as an
> idempotent semiring (idempotency from `max_idem`/`idem_sup`, associativity/commutativity from
> `cutMax_assoc`/`cutMax_comm`). This is the one weld that would promote the entry from PREDICTION+PARTIAL
> to a closed derivation — the tropical semiring as the `×↦+` character at the idempotent `T→0` limit,
> parallel to `ConvolveRescaleContraction` welding the Banach engine to the CLT.
