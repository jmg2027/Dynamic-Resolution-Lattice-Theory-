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
    does not apply.  `Sedenion` `alt_left`/`alt_right` genuinely *fail*
    (zero divisors), so only flexibility is in play.

    **Precisely scoped** (verified numerically, `/tmp` Python during the
    session — re-derive before coding):
      · flexibility of `CDDouble α` needs only **base-flexible** (NOT
        base-alternative): trigintaduonion = CDDouble of the
        flexible-but-non-alternative sedenion is itself flexible.
      · So the target is `cd_flexible_nonassoc` over a base class bundling
        `NonAssocStarRing213` + `flexible` + `self_mul_conj`/`conj_mul_self`
        (norm central) + `self_add_conj` (trace central).  Cayley and
        Sedenion are instances (Cayley flexible = `CayleyHeavy.flexible`).
      · `.re` term grouping (a=u.re,b=u.im,c=v.re,d=v.im, conj=base):
        `(a*c)*a = a*(c*a)` (base flexible);
        `conj b*(b*conj c) = (conj c*conj b)*b` (call it `L4=R3`);
        `-(conj d*b)*a - conj b*(d*a) = -a*(conj b*d) - (a*conj d)*b`
        (trace pair `L2+L3=R2+R4`).  `.im` is analogous.
      · Key reusable base lemma: `(conj b*y)*b = conj b*(y*b)`
        (`moufang_mid`) holds from **flexible + trace**: substitute
        `conj b = ofInt(trace b) - b`, the trace term is central, the
        remainder is `[b,y,b] = 0` (base flexible).  This is the lever for
        the cross-terms; `L4=R3` reduces similarly via flexible + norm
        (`conj b*b = ofInt(normSq b)` central) + trace.
      · Effort: ~cd_alt_left scale ×(both components) + base sub-lemmas +
        typeclass + Cayley/Sedenion instance bridges.  Sizeable; warrants
        its own session.

    **Foundation built (`Meta/Algebra213/CDDoubleFlexible.lean`, all PURE):**
      · class `FlexAlt213` (= `MoufangIntegerNormed213` + `trace`/
        `self_add_conj` + `conj_mul_self` + scalar nuclearity
        `ofInt_nuc_{l,m,r}` + `alt_left`/`alt_right`/`flexible`).  [Note:
        the file uses the *alternative* base form — `alt_left`/`alt_right`
        are included; flexibility-only would drop them but then `L4=R3`
        needs a different reduction.  Cayley satisfies alt, so this
        covers Sedenion; Trigintaduonion (base Sedenion, non-alt) would
        need the flexibility-only variant.]
      · DONE lemmas: `conj_eq`; `left_assoc_conj` (`[conj b,b,X]=0`);
        `right_assoc_conj` (`[X,conj b,b]=0`); `conj_sandwich` (gives
        `L4=R3`); `moufang_mid`.
      · **Remaining crux = the cross-pair**
        `(conj d·b)·a + conj b·(d·a) = a·(conj b·d) + (a·conj d)·b`.
        Verified to hold (numerically) but not yet reduced.  Lead:
        derive `flex_polar` (linearized flexibility,
        `(x·y)·z + (z·y)·x = x·(y·z) + z·(y·x)` — same expand+cancel
        shape as `cd_flexible`'s linearization) and combine with
        `moufang_mid` + scalar nuclearity + `self_add_conj` (both `b`
        and `d` traces).  Then `cd_flexible.re` = `flexible`(L1=R1) +
        `conj_sandwich`(L4=R3) + cross-pair; `.im` analogous; then
        register `Cayley`/`Sedenion : FlexAlt213` (Cayley needs trace +
        conj_mul_self + scalar-nuclearity proofs — real-scalar nuclearity
        is the fiddly one) and bridge `Sedenion.flexible`.
  - `CayleyHeavy.no_zero_div`'s residual `[propext, Quot.sound]` comes
    from `normSq_eq_zero_iff`'s `↔`/decidability machinery (Int), not
    the polynomial brute force.
