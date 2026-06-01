# G160 — depth-arc E status + the CDDoubleFlexible cross-pair attack

**Date**: 2026-06-01. **Status**: scoping + concrete attack scaffolding (NOT closed).
Tier-1 scratch for the two genuinely-open items the depth arc surfaced once A–D and
the B general theorem closed.

## What closed this arc (durable; see HANDOFF / `completeness_without_completeness.md`)

  - **A** `DepthFloorDetOne` — depth-0 floor = det P = 1 (P-orbit invariant).
  - **B** `DepthPRecursiveInstances` — `newton_polyDepth`: *every* degree-`d` discrete
    polynomial (Newton form, 213-native `binom`) has `polyDepth d`; e fully closed;
    π recurrences + `polyDepth 2` step coefficient.
  - **C** `DepthOmegaTower` — depth-`r` tower coordinate is an ordinal `< ω^r`; the
    `ω^ω` ladder, each layer ×`ω`.
  - **D** `DepthLiouvilleCoord` — `k!` gets a finite recursion coordinate.

## E (GRA-tower ↔ CD-tower duality) — open conjecture, NOT a short theorem

The conceptual claim (level-`n` property loss ↔ level-`5−n` Reading-iso gain; both
towers bottoming at the `5 = NS+NT` floor) is **Conjecture 5.3.1** in
`theory/math/gra_book.md` §5.3 / "Open frontier" in `theory/essays/tower_atlas.md`.
Three separate PURE bricks exist but are **not** linkable into the duality without
foundational work:

  1. depth-0 floor = det P = 1 (`Cauchy/DepthFloorDetOne`).
  2. all (2,3)-GRA models share `depth n = ⌈n/3⌉` (`GRA/DepthFunctor.depth_const`).
  3. `5 = NS + NT = disc P` (`Mobius213SignatureAxisCatalog.axis_nt_five_prime` +
     `Mobius213.mobius_213_discriminant`).

Missing for the duality: (a) a formal `GRATowerLevel : Nat → Prop` (the
Reading-iso-count tower is narrative only — the per-domain isos are scattered
theorems, not tallied); (b) a proof that each Reading gains an iso *exactly when* a
CD property is lost; (c) the CD flexibility characterization (below).  **Bundling
the three `5`-facts into one theorem is forbidden** — it would import meaning-by-
analogy (the framework refuses suggestive numeric coincidence as content; the
duality must be an earned formal correspondence or nothing).

## The CDDoubleFlexible cross-pair — concrete attack scaffolding

`Meta/Algebra213/CDDoubleFlexible.lean` has all foundation lemmas PURE
(`conj_eq`, `left_assoc_conj`, `right_assoc_conj`, `conj_sandwich`, `moufang_mid`,
`flex_polar`).  The one open crux blocking `cd_flexible` (and hence the
Cayley/Sedenion flexibility instances) is the **cross-pair**:

```
(conj d · b) · a + conj b · (d · a) = a · (conj b · d) + (a · conj d) · b
```

Two attack routes, both reduce it to a base-algebra (conjugate-free) identity:

### Route 1 — trace substitution (`conj_eq` on both conjugates)

Write `conj b = T_b − b`, `conj d = T_d − d` with `T_x := ofInt (trace x) = x + conj x`
(scalar, central + nuclear via `ofInt_nuc_{l,m,r}`, `ofInt_central`).  Distributing
and pulling the scalars out with the nuclearity lemmas collapses the cross-pair to

```
−T_d·[a,b] − T_b·[a,d] + [a, b·d] + [a, d·b] = 0        ([x,y] := x·y − y·x)
```

So the cross-pair is equivalent to a **trace-weighted commutator identity** — the
"double-trace bookkeeping".  Closing it needs the commutators `[a, b·d] + [a, d·b]`
related to `T_b·[a,d] + T_d·[a,b]` via alternativity (`alt_left`/`alt_right`) — this
is the unfinished step; it did not close by inspection.

### Route 2 — four `flex_polar` instances

Each cross-pair term is a `flex_polar` summand:

  - `flex_polar (conj d) b a` : `(conj d·b)·a + (a·b)·conj d = conj d·(b·a) + a·(b·conj d)`
  - `flex_polar (conj b) d a` : `(conj b·d)·a + (a·d)·conj b = conj b·(d·a) + a·(d·conj b)`
  - `flex_polar a (conj b) d` : `(a·conj b)·d + (d·conj b)·a = a·(conj b·d) + d·(conj b·a)`
  - `flex_polar a (conj d) b` : `(a·conj d)·b + (b·conj d)·a = a·(conj d·b) + b·(conj d·a)`

Adding/subtracting these (a linear puzzle over the 16 product terms) plus
`conj_sandwich` / `moufang_mid` to discharge the conjugate-sandwich residues is the
second path.  The bookkeeping is intricate; not closed here.

**Assessment**: a genuinely open non-associative-algebra identity (the originator's
flagged crux), not a quick win.  Route 1's trace-commutator form is the most
promising single target for a focused future attempt.

## π's degree-4 ratio polyDepth (B residual) — CLOSED

The PURE nonlinear-`Nat` kit got built (`Meta/Nat/PolyNat`, a reflection `ring`:
reify → Horner normal form → equal lists by `rfl`), and with it the π quartic is
mechanical: `Cauchy/DepthPiQuartic.piRatio_polyDepth` proves the full degree-4
cross-det ratio `4(n+1)²(2n+1)(2n+3)` has `polyDepth 4` (four exact differences →
const `384`, each `f(n+1) = f(n)+g(n)` discharged by `poly_id`).  Depth-arc B is now
fully closed (general theorem + e + π).  `PolyNat` is reusable for the repo's other
hand-rolled `Nat` expansions.
