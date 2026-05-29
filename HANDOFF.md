# Session handoff

Branch: `claude/moufang-polarization-conditions-X9f2p`

## Non-associative Moufang layer via polarization — COMPLETE

Closed the L3/L4 **non-associative** alt layer of the Cayley-Dickson
towers: `MoufangIntegerNormed213` instances for **Cayley** (Type A L3,
integer octonions), **ZOmegaQuad** (Type C L4, M_24 Chein loop), and
**L4T** (Type B L4) — the CDDouble of a *non-commutative* associative
base, where the Moufang norm-collapse is the genuine degree-4 Hurwitz
identity (no `mul_assoc` shortcut).

### The polarization condition (the session's core idea)

Task question: *what cancels the residue when doubling a
non-commutative associative base?*  Answer: the **trace form**, the
linear/polarization companion of the quadratic norm form.

New class `TraceNormed213` (in `Meta/Algebra213/Core.lean`):
```
class TraceNormed213 α extends IntegerNormed213 α where
  trace         : α → Int
  self_add_conj : ∀ a, a + conj a = ofInt (trace a)
```
Where `self_mul_conj` (`a·conj a = ofInt(normSq a)`) is the quadratic
coefficient, `self_add_conj` is the linear one — together the two
coefficients of a Hurwitz integer's minimal polynomial.

### Where the residue cancels

`Meta/Algebra213/CDDoubleMoufang.lean` (all strict ∅-axiom):
  - `diag_collapse` — the four *diagonal* terms of the Hurwitz
    expansion collapse to central `ofInt` scalars via `self_mul_conj`.
  - `cross_zero` — the four *cross* terms cancel pairwise: the
    non-commutative residue `conj a·conj w − conj w·conj a = a·w − w·a`
    is killed because `a + conj a` is central (`self_add_conj`).
  - `hurwitz_norm_re` — the full degree-4 identity assembled.
  - `cd_normSq_mul` — Hurwitz norm composition `|u·v|² = |u|²·|v|²`
    for `CDDouble α` over a non-comm base, derived from
    `hurwitz_norm_re` (NOT from Moufang → no circularity).
  - `cd_moufang_norm` + `instMoufangIntegerNormed213CDDouble` — the
    abstract `MoufangIntegerNormed213 (CDDouble α)` instance for any
    `[TraceNormed213 α]`.

### Concrete layers (each bridges via `toCDDouble`)

| Layer | File | base TraceNormed213 |
|---|---|---|
| Cayley (A L3) | `Levels/CayleyMoufang.lean` | Lipschitz (trace `2·re`) |
| ZOmegaQuad (C L4) | `Integer/ZOmegaQuadAlgebra213.lean` §4 | ZOmegaDouble (Eisenstein `2re−im`) |
| L4T (B L4) | `Integer/ZSqrtMinus2Algebra213.lean` §7 | L3T (trace `2·re`) |

Each yields `normSq_mul` (Hurwitz composition) via the generic
`MoufangIntegerNormed213.normSq_mul`, verified `#print axioms` →
"does not depend on any axioms".  This **replaces** the
`hurwitz_ring` 32-Int-var brute force (`maxHeartbeats 4000000` in
`CayleyHeavy.normSq_mul`) with one structural lemma reused across all
three towers.

## Follow-up marathon (this session, after the core layer)

  - **#1 done** — `CayleyHeavy.normSq_mul` now bridges to
    `cd_normSq_mul` (PURE); the `hurwitz_ring` + `maxHeartbeats 4000000`
    proof is gone.  `TraceNormed213 Lipschitz` relocated to
    `LipschitzAlgebra213` (cycle-free).
  - **#5 done** — `CayleyDickson/INDEX.md`, theory chapter
    `theory/math/cayley_dickson/algebra_tower.md` (new norm-composition
    section), methodology Pattern #21 (polarization), falsifier-roster
    composition-boundary entry.
  - **#2 done (partial)** — new reusable `NonAssocRing213` /
    `NonAssocStarRing213` generic-lemma layer (Ring213 proofs port
    verbatim, no `mul_assoc`).  `SedenionHeavy.conj_mul_anti` now PURE
    (was 8M-heartbeat `hurwitz_ring`).
  - **#3 done** — `Levels/SedenionZeroDivisor.lean`: explicit zero
    divisor `(e₁+e₁₀)(e₄−e₁₅)=0` + `normSq` non-multiplicativity,
    marking the composition boundary (decide, ∅-axiom).
  - **octonion alternativity done** — `Meta/Algebra213/CDDoubleAlternative.lean`:
    `cd_alt_left` (hard component identity via the same norm-central +
    trace-polarization + assoc reductions), `cd_alt_right` (conj
    anti-automorphism of alt_left), `cd_flexible` (linearization).
    `CayleyHeavy.{alt_left,alt_right,flexible}` bridge to it — **CayleyHeavy
    is now entirely `hurwitz_ring`-free** (and its `HurwitzRing` import +
    `maxHeartbeats` are gone).

## Open / next

  - `SedenionHeavy.flexible` + `TrigintaduoionionHeavy` are the last
    `hurwitz_ring` users.  These are **flexibility over a non-associative
    base** (Sedenion = CDDouble Cayley); the associative `cd_flexible`
    does not apply (its reassociations need an associative base).  Needs
    a fresh `cd_flexible_nonassoc` (cubic component proof using the base's
    own flexible/alternative laws + norm/trace centrality) — a distinct
    derivation, scoped but sizeable.  `Sedenion` `alt_left`/`alt_right`
    genuinely *fail* (zero divisors), so only flexibility is in play.
  - `CayleyHeavy.no_zero_div`'s residual `[propext, Quot.sound]` comes
    from `normSq_eq_zero_iff`'s `↔`/decidability machinery (Int), not
    the polynomial brute force.
