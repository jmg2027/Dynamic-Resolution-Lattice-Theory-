# Decomposition: domain theory / denotational semantics (CPOs, Scott-continuity, lfp = ⊔fⁿ(⊥), D≅[D→D])

*A FRESH decomposition per `../README.md` (model v7.1) and `../SYNTHESIS.md` (two invariants, the q=±1
spine, the resolution/iteration axis). The order-completion companion to the metric-completion fixed-point
work: `golden_ratio.md`/`martingales.md`/`differential_equations.md` (the q=+1 converging fixed point on a
metric/number-pair/vector-field), `curry_howard.md` (KEY — recursion = the fixed point of an unfolding;
the Lambek q=+1 well-founded floor = strong normalization), `cut_elimination.md` (normalization = the
fold), and `cardinality.md` (the q=−1 escaping diagonal `object1`/Lawvere — the reflexive domain
D≅[D→D] is that diagonal TAMED). Honest verdict: PREDICTION — the least fixed point lfp f = ⊔ₙ fⁿ(⊥) is
the q=+1 converging fixed point reached as an ORDER-colimit (a CPO order-completion) rather than a
metric-completion, the iteration ascending to a supremum; Scott-continuity = the reading commutes with
directed colimits (the resolution axis); D≅[D→D] = Lawvere's diagonal made consistent by ⊥/partiality.
The Knaster–Tarski lfp (the glb-of-pre-fixed-points construction of the least fixed point) is **BUILT and
PURE** (`Order/KnasterTarski.lean`, 19/0); the named CPO / Scott-continuous / Kleene-`⊔fⁿ(⊥)` /
reflexive-`D≅[D→D]` objects are ABSENT (grep-confirmed). The decomposition's NEW datum: the lfp the
calculus already uses as a *metric* completion (`banach_fixed_point_modulated`) is the *order* completion
when the resolution axis ascends to a directed supremum instead of contracting to a Cauchy limit.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — distinguishing, iterated, read out with its **fold-height** and **direction**
  sub-structures (the same `C` as everywhere). The domain-theoretic content is a *partial order* on
  constructions: `x ≤ y` = "`y` refines / is more-defined-than `x`", with a least element `⊥` =
  the empty/undefined construction (the atomic floor, `terminal_iff_atom`). The order-completion is the
  resolution axis read **upward**: a directed/ascending chain `⊥ ≤ f(⊥) ≤ f²(⊥) ≤ …` of ever-more-defined
  constructions, whose **supremum `⊔`** is the colimit. A CPO is `C` equipped with this order plus all
  directed sups; `⊥` is the count/fold-height-zero floor. This is the *order-theoretic* face of the same
  iteration the metric-completion notes (`golden_ratio.md`, `gaussian_clt.md`) run as a Cauchy chain.

- **Reading `L`** — a **Scott-continuous reading**: a reading `L` that **commutes with directed colimits**,
  `L(⊔ xᵢ) = ⊔ L(xᵢ)`. This is the resolution-axis-compatibility condition (`continuity.md`'s dial promoted
  to a *condition*, here on the *order* resolution rather than the metric one): a continuous map is one
  whose value at the limit is the limit of its values. The three derived readings:
  - **a Scott-continuous function `f : D → D`** = the reading whose value at a directed sup is the sup of
    its values (resolution-axis-compatible, the order analogue of `IsContinuousModulus`).
  - **the least-fixed-point reading `lfp f`** = the reading that takes `f` to its q=+1 converging fixed
    point. Two constructions of the *same* lfp:
    - **Kleene** — `lfp f = ⊔ₙ fⁿ(⊥)`: the supremum of the iteration chain; needs `f` Scott-continuous.
      The iteration ascends and the colimit is the fixed point — the **iteration index `n` is the modulus**
      (the exact role the chain index plays in `banach_fixed_point_modulated`'s `picard_cauchy`).
    - **Knaster–Tarski** — `lfp f = glb {x | f x ≤ x}` (the greatest-lower-bound of pre-fixed points);
      needs only `f` monotone, lives on a complete lattice. **This one is BUILT and PURE**
      (`Order/KnasterTarski.lean`).
  - **the denotational-meaning-of-recursion reading** = `⟦rec g⟧ = lfp (λφ. unfold g φ)`: recursion is the
    lfp of its unfolding functional — the same "the fixed point of the unfolding" the calculus reads on φ
    (φ = the fixed point of `x ↦ 1+1/x`) and on Picard (`y = y₀ + ∫f` the fixed point of the integral
    operator, `differential_equations.md`).

- **Residue** — the lfp reading's self-application surplus, splitting at the two q=±1 poles, with the
  **reflexive domain D≅[D→D]** the load-bearing new datum on the q=+1 side:
  - **q=+1 (converge / fixed point reached) — the lfp ITSELF and the TAMED reflexive domain.** The
    iteration `⊥ ≤ f(⊥) ≤ f²(⊥) ≤ …` ascends to its supremum, the q=+1 converging fixed point
    (`ResidueTag` `converge`, `converge_residue_fixed`, delegating to `banach_fixed_point_modulated` — the
    *same* engine as φ via `golden_is_converge`, on an order-completion instead of a metric-completion).
    And the reflexive domain **D≅[D→D]** (Scott's model of the untyped λ-calculus, a domain isomorphic to
    its own function space) is **Lawvere's diagonal made CONSISTENT**: `OneDiagonal.lawvere_fixed_point`
    says a point-surjective `f : A → (A → B)` forces **every** modifier `t : B → B` a fixed point. On
    *total* functions with `t = not` (no fixed point in `Bool`) this is the impossibility that drives
    Cantor (`cantor_via_lawvere`, q=−1 escape). But on a CPO **every** Scott-continuous `t` *has* a fixed
    point (its own lfp) — so the Lawvere construction's conclusion is *satisfiable*, and a `D` surjecting
    onto `[D→D]` is consistent. **Partiality/⊥ is exactly what supplies the fixed point the diagonal
    demands** — the q=−1 escape is defused into the q=+1 fixed-point pole.
  - **q=−1 (escape / reached-by-none) — the diagonal on TOTAL maps and non-termination.** The *same*
    self-cover, on total functions or with a fixed-point-free modifier (`!` on `Bool`,
    `bool_not_fixedPointFree`), is the escaping diagonal `object1_not_surjective` /
    `no_surjection_of_fixedpointfree` (`cardinality.md`'s Cantor, `godel.md`'s incompleteness). The
    bottomless (non-CPO) self-application is the q=−1 pole; ⊥ is what moves it to q=+1.

## Re-seeing — ⟨C | L⟩

```
   a CPO D                  =  ⟨ C ordered by refinement, with ⊥ = floor + all directed sups ⊔ ⟩   (C)
   ⊥ (bottom)               =  the atomic/undefined floor (fold-height 0, terminal_iff_atom)        (C)
   the iteration chain      =  ⊥ ≤ f(⊥) ≤ f²(⊥) ≤ …  (the resolution axis read UPWARD)              (C)
   Scott-continuous f       =  a reading commuting with directed colimits  L(⊔xᵢ)=⊔L(xᵢ)            (L)
                              (the resolution-axis-compatibility condition, order version)
   lfp f = ⊔ₙ fⁿ(⊥)  (Kleene) =  Residue(lfp-reading, C) at q=+1 = the colimit of the iteration       (⊕Residue, q=+1)
                              (n = the modulus, the same role as picard_cauchy's chain index)
   lfp f = glb{x|f x≤x} (K–T)  =  the same lfp as the glb of pre-fixed points  [BUILT: lfp_fixed/lfp_least]
   ⟦recursion⟧              =  lfp (λφ. unfold φ) = the fixed point of the unfolding (q=+1)
                              (the SAME "fixed point of an unfolding" as φ / Picard / martingale)
   D ≅ [D→D]  (untyped λ)   =  Lawvere's diagonal (cardinality.md) TAMED by ⊥:
                              every Scott-continuous t has a fixed point (its own lfp), so the
                              lawvere_fixed_point conclusion is SATISFIABLE → self-application consistent
   Cantor / Gödel           =  the SAME diagonal on TOTAL maps (t=not, no fixed point) = q=−1 escape
   DOMAIN THEORY            =  (lfp = ⊔fⁿ(⊥), q=+1 order-colimit) + (Scott-cont = resolution-compat)
                              + (D≅[D→D] = the q=−1 diagonal defused to q=+1 by partiality)
```

So domain theory is the calculus's q=+1 fixed-point engine reached as an **order-colimit** (a CPO directed
supremum) instead of a **metric-completion** (a Cauchy limit), with the reflexive-domain self-reference made
consistent by ⊥. No new primitive: it is `golden_ratio.md`'s converging fixed point + `continuity.md`'s
resolution-compatibility + `cardinality.md`'s diagonal, the diagonal flipped from escape to fixed point by
the bottom element.

## THE REVELATION — lfp = ⊔fⁿ(⊥) is the q=+1 fixed point on an ORDER-completion; Scott-continuity is the resolution axis; D≅[D→D] is the q=−1 diagonal TAMED by ⊥

The decomposition's payoff is two collapses and one forcing, each load-bearing and distinct from the
metric-completion notes it neighbors:

- **★ COLLAPSE 1 — metric-completion and order-completion are ONE q=+1 fixed point, differing only in
  which way the resolution axis runs.** `golden_ratio.md`/`gaussian_clt.md`/`differential_equations.md`
  reach the q=+1 fixed point as a **Cauchy limit**: a contracting sequence whose modulus shrinks the
  distance (`banach_fixed_point_modulated`'s `picard_cauchy`). Domain theory reaches the *same* q=+1 fixed
  point as a **directed supremum**: an **ascending** chain `⊥ ≤ f(⊥) ≤ f²(⊥) ≤ …` whose colimit IS the
  fixed point (Kleene). Both are `ResidueTag` `converge` with the iteration index as the modulus — the
  *only* difference is that the metric version contracts (distance ↓ 0) while the order version ascends
  (definedness ↑ ⊔). `converge_residue_fixed` already delegates both to `banach_fixed_point_modulated`. So
  "completion" is one operation read at two resolutions of the SAME axis: metric (contract to a Cauchy
  limit) and order (ascend to a directed sup). This is the resolution axis (`continuity.md`,
  `SYNTHESIS.md` row 3) made literal on a partial order — the genuinely new datum, not a re-skin of the
  metric notes.

- **★ COLLAPSE 2 — the two lfp constructions (Kleene ⊔fⁿ(⊥) vs Knaster–Tarski glb of pre-fixed points)
  are one lfp; the K–T one is BUILT.** `Order/KnasterTarski.lean` (19/0 PURE) builds the least fixed point
  as `lfp = glb {x | f x ≤ x}` with `lfp_fixed` (`f lfp = lfp`), `lfp_least` (`lfp ≤` every fixed point),
  and `lfp_least_prefixed` (`lfp ≤` every pre-fixed point) — a pure order-chase, parametrized over an
  explicit `(le, glb)` complete lattice, **no Mathlib, no Classical, no `funext`**. This is the
  *impredicative* (monotone-only) construction of the very lfp domain theory's denotational semantics
  needs; Kleene's `⊔fⁿ(⊥)` is the *predicative* (Scott-continuous) construction of the *same* least fixed
  point, and the two agree when `f` is continuous. So the load-bearing object — "recursion = its lfp" — is
  already a PURE theorem in the repo; only its *Kleene/iteration* presentation (and the CPO it lives on) is
  absent.

- **★ FORCING — D≅[D→D] is Lawvere's diagonal forced into the q=+1 pole by ⊥.** This is the deepest find
  and the cleanest tie to `cardinality.md`. `OneDiagonal.lawvere_fixed_point` (`:43`, PURE): for a
  point-surjective `f : A → (A → B)`, **every** `t : B → B` has a fixed point. The two readings of this one
  theorem are the two poles:
  - **q=−1 (Cantor/Gödel):** at `B = Bool`, `t = !` (`bool_not_fixedPointFree`, no fixed point), the
    conclusion is *false*, so the hypothesis is *impossible* — there is **no** surjection `A → (A→Bool)`
    (`no_surjection_of_fixedpointfree`, `cantor_via_lawvere`). Total functions escape.
  - **q=+1 (Scott/D≅[D→D]):** on a CPO, **every** Scott-continuous `t : D → D` *has* a fixed point (its own
    lfp, the q=+1 colimit). So Lawvere's conclusion is *satisfiable*, and a `D` (point-)surjecting onto its
    own continuous-function space `[D→D]` is **consistent**. The untyped λ-calculus's self-application
    `(λx.xx)` — which is exactly the diagonal `f a a` — is well-defined because partiality supplies the
    fixed point the diagonal demands.
  So D≅[D→D] is NOT a new construction defeating Cantor; it is `cardinality.md`'s *one diagonal* read at the
  q=+1 pole, with ⊥/partiality the operator that moves the modifier `t` from fixed-point-free (`!`) to
  fixed-point-having (Scott-continuous, `lfp t`). The q=±1 multiplier bit (`multiplier_unimodular`) is the
  literal switch: total/escape (q=−1) vs partial/converge (q=+1) on the SAME self-cover. This passes the
  re-skin guard as a *forcing*: the consistency of self-application is forced by the existence of fixed
  points, which is forced by ⊥, which is the q=+1 pole.

**Net revelation:** domain theory consolidates three prior decompositions under the two invariants with no
new axis. It is `golden_ratio.md`/`differential_equations.md`'s q=+1 converging fixed point (now reached as
an *order*-colimit `⊔fⁿ(⊥)` instead of a *metric* one), `continuity.md`'s resolution-axis-compatibility
(now the *order* "commutes with directed colimits" = Scott-continuity), and `cardinality.md`'s q=−1
diagonal (now *defused to q=+1* by ⊥ — the reflexive domain). The lfp the calculus uses as a metric
completion is the order completion; the diagonal that escapes on total maps converges on partial ones. The
one genuinely-built load-bearing object is the Knaster–Tarski lfp (`lfp_fixed`/`lfp_least`, 19/0 PURE).

## The precise missing legs (located, like `curry_howard.md` / `model_theory.md`)

The **engines are PURE**; only the *named CPO / Scott / Kleene / reflexive-domain objects* are ABSENT
(all grep-confirmed below). Concretely the repo has **no**:
1. a **CPO / `CompletePartialOrder` / ω-CPO** structure (a partial order with a designated `⊥` and all
   directed/ω-chain suprema). The order machinery exists — `Order/KnasterTarski.lean` (complete lattice via
   explicit `(le, glb/lub)`), `Order/GaloisConnection.lean`, `Order/BooleanAlgebra.lean` — but no
   *directed-sup / ⊥-pointed* CPO object. (`KnasterTarski` uses a *complete lattice* glb, not a
   *directed*-sup CPO; the directedness condition is the missing piece.)
2. a **`ScottContinuous` predicate** `L(⊔xᵢ) = ⊔L(xᵢ)`. The resolution-axis-compatibility condition is
   built for the *metric* dial (`ContinuityOpenSet`, `IsContinuousModulus`, `uniform_limit_continuous`) and
   for the *cut/grade* resolution (`ResolutionShift.IsResolutionShift`); the **order** version
   (commutes-with-directed-colimits) is the absent leg.
3. the **Kleene lfp `lfp f = ⊔ₙ fⁿ(⊥)`** as an iteration-colimit theorem (Scott-continuous `f`). The lfp
   exists as the *Knaster–Tarski glb* (`lfp_fixed`/`lfp_least`, BUILT, PURE) but NOT as the
   ascending-iteration supremum; the bridge "K–T glb = Kleene ⊔fⁿ(⊥) for continuous `f`" is absent.
4. a **named denotational-semantics object** (a syntax `Term`/`Expr`, a `⟦·⟧` semantic function into a CPO,
   `⟦rec g⟧ = lfp …`). As in `curry_howard.md`, the calculus has `Raw`/`Lens.view = Raw.fold` (the
   recursor) and the lfp theorem, but no *named* term-language-with-denotation object wiring them.
5. the **reflexive domain `D ≅ [D→D]`** as a built isomorphism (Scott's `D∞` inverse-limit / the untyped-λ
   model). The *taming mechanism* is PURE (`lawvere_fixed_point` + the q=+1 fixed-point existence), but the
   *named* `D∞`/`[D→D]`-isomorphism object is absent — the order-completion twin of the metric `D∞`
   inverse limit, the same shape as the absent typed-λ object in `curry_howard.md`.

This is the *exact* analogue of `curry_howard.md`'s located missing leg (a named typed λ-calculus /
cut-elimination object): the engine (the lfp, the q=±1 diagonal, the resolution axis) is real and PURE; the
*named domain-theoretic instance* (CPO, Scott-continuity, Kleene `⊔fⁿ(⊥)`, `D≅[D→D]`) is the missing
primitive. It is not a break of the model (no new axis) — it is the absent order-completion instance, the
denotational dual of `curry_howard.md`'s absent operational/typed instance.

## Note for the technique

**No new primitive; a resolution-axis consolidation that pays by collapse + forcing.** Domain theory does
not extend model v7.1 — it confirms the resolution axis is **bidirectional** in a second sense (orthogonal
to fold-height's bidirectionality): the *metric* dial contracts to a Cauchy limit, the *order* dial ascends
to a directed supremum, and **both reach the same q=+1 fixed point** (`converge_residue_fixed` →
`banach_fixed_point_modulated`). The model's robustness datum: the q=+1 fixed-point engine that already
spans φ / Gaussian / ODE / martingales now also covers denotational recursion, on an order-completion, with
the *only* change being the direction the resolution axis runs. And the q=±1 diagonal gains its sharpest
"taming" instance: ⊥/partiality is the operator that moves Lawvere's self-cover from the q=−1 escape (total
maps, `t=!` fixed-point-free) to the q=+1 fixed point (Scott-continuous `t`, fixed point = `lfp t`) — the
multiplier bit `±1` realized as total-vs-partial on one self-application. The honest edge — a named CPO /
Scott-continuous / Kleene-`⊔fⁿ(⊥)` / `D≅[D→D]` object — is the located missing leg, the denotational dual
of `curry_howard.md`'s absent typed λ-calculus, with the lfp itself (Knaster–Tarski) already PURE-built.

---

## Verified Lean anchors (grep/Read-verified file:line; purity freshly scanned via `tools/scan_axioms.py` this session)

| Leg | Theorem / def (file:line : name) | Status |
|---|---|---|
| **lfp = the LEAST fixed point** (glb of pre-fixed points; `f lfp = lfp`) — Knaster–Tarski, the order-theoretic lfp recursion's denotation needs | `Lib/Math/Order/KnasterTarski.lean:31 lfp` (def `glb {x | le (f x) x}`); `:60 lfp_fixed` (`f lfp = lfp`); `:39 lfp_prefixed` | ∅-axiom PURE ✓ (19/0) |
| **lfp ≤ every (pre-)fixed point** — the LEAST-ness, the denotational "smallest solution of the recursion" | `Lib/Math/Order/KnasterTarski.lean:89 lfp_least`; `:78 lfp_least_prefixed`; smoke `:197 unit_lfp_fixed`, `:203 unit_lfp_least` | ∅-axiom PURE ✓ |
| dual greatest fixed point (gfp = lub of post-fixed points) — the q=−1/co-recursion companion | `Lib/Math/Order/KnasterTarski.lean:114 gfp`; `:132 gfp_fixed`; `:148 gfp_greatest` | ∅-axiom PURE ✓ |
| **the q=+1 converging fixed point** (the lfp's tag; same engine for metric AND order completion) | `Lib/Math/Foundations/ResidueTag.lean:160 converge_residue_fixed`; `:180 golden_is_converge` (q=+1 = φ Cassini); `:86 multiplier_unimodular`; `:228 residue_tag_two_poles` | ∅-axiom PURE ✓ (55/0) |
| **the converge ENGINE** the order-colimit shares with the metric-completion (n = the iteration modulus) | `Lib/Math/Analysis/BanachFixedPointModulated.lean:111 banach_fixed_point_modulated` (`#print axioms` → "does not depend on any axioms", verified this session); `:101` docstring | ∅-axiom PURE ✓ |
| **the resolution axis** (iteration index = grade; compose adds grades) — the order-colimit's ascent dial | `Lib/Math/Analysis/ResolutionShift.lean:73 IsResolutionShift`; `:130 IsResolutionShift_compose`; `:179 IsResolutionShift_cutHalfIter`; `:226 IsResolutionShift_grade_unique` | ∅-axiom PURE ✓ (17/0) |
| **⊥ = the atomic floor; the iteration ascends from it** (well-founded; no infinite descent) | `Theory/Raw/Lambek.lean:199 isPart_wf`; `:273 no_infinite_descent`; `:308 terminal_iff_atom` (the floor = the atoms); `:178 no_part_of_atom` | ∅-axiom PURE ✓ (22/0) |
| the iteration ascends unboundedly (the directed chain has no top — the colimit is reached-by-none) | `Theory/Raw/MuNuMirror.lean:50 ascent_unbounded`; `:105 ascent_total_descent_partial`; `:118 descent_wf_ascent_unbounded` | ∅-axiom PURE ✓ (8/0) |
| residue re-enters as its own operand (the iteration = the residue iterated, never closing = q=−1) | `Lens/Foundations/ResidueReentry.lean:85 residue_perpetually_reenters`; `:63 residue_reentry_never_closes` | ∅-axiom PURE ✓ (14/0) |
| **D≅[D→D] = Lawvere's diagonal; q=+1 (tamed) iff t has a fixed point** | `Lens/Foundations/OneDiagonal.lean:43 lawvere_fixed_point` (point-surjective `f:A→A→B` ⟹ every `t:B→B` has a fixed point) | ∅-axiom PURE ✓ (11/0) |
| **q=−1 escape** — diagonal on TOTAL maps (t=! fixed-point-free) = Cantor/Gödel, the un-tamed pole | `Lens/Foundations/OneDiagonal.lean:51 no_surjection_of_fixedpointfree`; `:61 cantor_via_lawvere`; `:87 russell_liar_no_surjection`; `Lens/Foundations/FlatOntologyClosure.lean:61 object1_not_surjective`; `:47 object1_injective`; `:69 self_covering_closure` | ∅-axiom PURE ✓ (FOC 7/0) |

**Fresh purity scan (this session, `tools/scan_axioms.py` from repo root):**
`E213.Lib.Math.Order.KnasterTarski` — **19 pure / 0 dirty** (`lfp`, `lfp_fixed`, `lfp_least`,
`lfp_prefixed`, `lfp_least_prefixed`, `gfp`, `gfp_fixed`, `gfp_greatest`, all PURE).
`E213.Lib.Math.Foundations.ResidueTag` — **55 pure / 0 dirty** (`converge_residue_fixed`,
`golden_is_converge`, `multiplier_unimodular`, `residue_tag_two_poles`, `escape_residue_outside` PURE).
`E213.Lib.Math.Analysis.ResolutionShift` — **17 pure / 0 dirty** (`IsResolutionShift_compose` etc.).
`E213.Theory.Raw.Lambek` — **22 pure / 0 dirty** (`isPart_wf`, `no_infinite_descent`, `terminal_iff_atom`).
`E213.Theory.Raw.MuNuMirror` — **8 pure / 0 dirty** (`ascent_unbounded`, `descent_wf_ascent_unbounded`).
`E213.Lens.Foundations.FlatOntologyClosure` — **7 pure / 0 dirty** (`object1_not_surjective`,
`object1_injective`, `self_covering_closure`).
`E213.Lens.Foundations.OneDiagonal` — **11 pure / 0 dirty** (`lawvere_fixed_point`,
`no_surjection_of_fixedpointfree`, `cantor_via_lawvere`, `russell_liar_no_surjection`).
`E213.Lens.Foundations.ResidueReentry` — **14 pure / 0 dirty** (`residue_perpetually_reenters`,
`residue_reentry_never_closes`).
`banach_fixed_point_modulated` — `#print axioms` ⟹ **"does not depend on any axioms"** (probed directly
this session under namespace `…BanachFixedPoint.CompleteMetricModulusMod`).

## Dropped / flagged (honest — NOT grounded in repo Lean)

- **A CPO / `CompletePartialOrder` / ω-CPO with ⊥ and directed sups — ABSENT (grep-confirmed).** The grep
  for `cpo|CPO|ScottContinuous|directed|CompletePartialOrder|omegaCPO` over `lean/E213/` returned no such
  object; the `lfp`/`Domain`/`lattice` hits are `Order/KnasterTarski.lean` (a *complete lattice* via
  explicit `glb`/`lub`, not a *directed-sup* CPO), `Order.lean`, `KnasterTarski`, and unrelated
  `ParadigmDomain*` / `CrossDomainUnification` files (no domain-theory content). KnasterTarski's lattice is
  the nearest object; the directed/⊥-pointed CPO is the missing leg.
- **`ScottContinuous` (commutes with directed colimits) — ABSENT.** The resolution-compatibility condition
  is built for the metric dial (`ContinuityOpenSet`, `IsContinuousModulus`) and the cut/grade resolution
  (`IsResolutionShift`), never for order-directed colimits. The "Scott-continuity = the resolution axis"
  identification is the decomposition's framing on those built dials, not a built Scott-continuity predicate.
- **Kleene `lfp f = ⊔ₙ fⁿ(⊥)` (iteration-colimit lfp) — ABSENT.** The lfp is built as the *Knaster–Tarski
  glb* (`lfp_fixed`/`lfp_least`, PURE); the *ascending-iteration supremum* presentation and the bridge
  "glb = ⊔fⁿ(⊥) for Scott-continuous `f`" are not built. "lfp = the q=+1 order-colimit reached as ⊔fⁿ(⊥)
  with n the modulus" is conceptual framing on `converge_residue_fixed` + `KnasterTarski.lfp`.
- **A denotational-semantics object (`⟦·⟧ : Term → D`, `⟦rec g⟧ = lfp …`) — ABSENT.** As in
  `curry_howard.md`: `Raw`/`Lens.view = Raw.fold` (the recursor) and the lfp theorem exist; no named
  term-language-with-CPO-denotation object wires them.
- **The reflexive domain `D ≅ [D→D]` (Scott `D∞`) as a built isomorphism — ABSENT.** The *taming
  mechanism* is PURE (`lawvere_fixed_point` + q=+1 fixed-point existence); the *named* `D∞`/`[D→D]`-iso is
  absent — the order-completion twin of the metric inverse-limit, same shape as `curry_howard.md`'s absent
  typed-λ object.

### Verified buildable witness (named, like the README's `Ext¹`/nonzero-Betti targets)

A **Kleene-style lfp via the built K–T lfp** is buildable ∅-axiom with no new primitive: on
`Order/KnasterTarski.lean`'s parametrized complete lattice, instantiate `lfp` and prove the
iteration-monotonicity lemma `fⁿ(⊥) ≤ fⁿ⁺¹(⊥)` (by induction from `⊥ ≤ f(⊥)` via the supplied `mono`),
exhibiting the ascending chain whose sup the existing `lfp_fixed`/`lfp_least` pin as the least fixed point.
This would weld the order-colimit ascent (`MuNuMirror.ascent_unbounded` shape) to the built K–T lfp,
delivering the "lfp = ⊔fⁿ(⊥)" collapse at the *abstract-lattice* level (the full Scott-continuous CPO with
directed sups remains the named open object). I have NOT built or asserted this as done — it is named as
the buildable next step, the lfp analogue of the README's nonzero-`Ext¹` buildable target. (I propose no
`decide` witness; all claims above are `#print axioms`/grep-checked.)

## Cross-frame

`golden_ratio.md` / `gaussian_clt.md` / `differential_equations.md` / `martingales.md` (the q=+1
converging fixed point as a *metric* completion — domain theory is the *order* completion of the same
`converge_residue_fixed`/`banach_fixed_point_modulated` engine); `curry_howard.md` (recursion = the fixed
point of an unfolding; strong normalization = `Lambek.no_infinite_descent`'s q=+1 floor = ⊥; the absent
typed-λ object is the operational dual of the absent CPO/`D≅[D→D]`); `cut_elimination.md` (normalization =
the fold = `view=fold` initiality, the lfp's syntactic twin); `cardinality.md` (the q=−1 escaping diagonal
`object1`/`lawvere_fixed_point` — D≅[D→D] is that diagonal TAMED to q=+1 by ⊥/partiality); `continuity.md`
(the resolution-axis-compatibility condition — Scott-continuity is its order version); `SYNTHESIS.md` §3
(the q=±1 spine — domain theory sits on both poles at once: lfp = q=+1 converge, the un-tamed total-map
diagonal = q=−1 escape). **VERDICT: PREDICTION** — domain theory = the q=+1 fixed point built as an
order-colimit (lfp = ⊔fⁿ(⊥), the iteration ascending to ⊔, n = the modulus) + Scott-continuity = the
resolution axis (commutes with directed colimits) + D≅[D→D] = Lawvere's diagonal made consistent by ⊥; no
new primitive. The load-bearing lfp is **BUILT PURE** (`KnasterTarski.lfp_fixed`/`lfp_least`, 19/0); the
named CPO / Scott-continuous / Kleene-`⊔fⁿ(⊥)` / `D∞≅[D→D]` objects are the located missing legs, the
denotational dual of `curry_howard.md`'s absent typed λ-calculus.
