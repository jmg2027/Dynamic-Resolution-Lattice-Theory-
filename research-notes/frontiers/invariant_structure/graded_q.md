# Is invariant B (`q=±1`) the order-2 truncation of a GRADED invariant?

**Status**: frontier `invariant_structure` Q1, first pass (2026-06-23). **Tier**: 1.
Parent: `research-notes/frontiers/invariant_structure.md` Open direction 1.
Anchor: `research-notes/decomposition/SYNTHESIS.md` §2 finding (i)/(iii), §3 (the q=±1 spine).

## The question, sharpened

Invariant B is the binary residue tag `ResidueTag = escape | converge`, with
`multiplier : ResidueTag → Int` valued `∓1` and `multiplier_unimodular : q² = 1`
(`Lib/Math/Foundations/ResidueTag.lean`). The two poles are
`residue_tag_two_poles`. The question: does the **binary** escape/converge tag
refine to a **graded** order/depth/rate, of which `q=±1` is the `k=2` slice?

Two candidate gradings live in the corpus:

- **(a) Multiplicative** — `qᵏ=1` roots of unity (character orthogonality at
  orders 2/3/4/6 and all orders mod p). The ±1 tag is the `k=2` slice of a
  *cyclic order grading*.
- **(b) Graded depth/order** — a ℕ-graded pole-order / nilpotency degree /
  valuation (`ε²=0`, difference-depth, `vp`). The ±1 tag is the `order≤2` /
  `degree-2` slice of an *additive depth grading*.

The honest finding (verdict below): **(a) and (b) are two genuinely distinct
refinements, not one graded invariant; and neither grading subsumes B as stated.**
B's binary bit factors *into* a magnitude × a sign-order whose order **is** the
small-order slice of (a) — but the *content* of B (which pole) is **not** what
either grading grades.

---

## Candidate (a): the multiplicative `qᵏ=1` order grading

### What grounds it (grep-verified, scanned PURE this pass)

The ±1 tag's multiplier `−1` is a root of unity of **order exactly 2**, and the
order is a genuine grading index realised concretely at orders 2/3/4/6 and (in
the finite-field direction) at every order `n ∣ p−1`.

| order `k` | Lean anchor (file:name) | statement | scan |
|---|---|---|---|
| 2 | `Lib/Math/Algebra/CassiniUnimodular.lean:188` `multiplier_unit_magnitude_sign_order_NT` | `qpow (-1) NT = 1 ∧ qpow (-1) 1 ≠ 1 ∧ NT = 2` — `−1` has order **exactly 2** | PURE (68/0, file) |
| 2 | `…/NumberTheory/ModArith/CharacterOrthogonality` `quadratic_orthogonality` | order-2 `Σ(−1)ᵏ = 0` (the Legendre/`±1` slice) | (cited in census, §4a) |
| 3 | `Lib/Math/Algebra/CayleyDickson/Integer/RootOfUnityOrthogonality.lean:206` `omega_orthogonality` | `geomSum Omega 3 = 0` (`1+ω+ω²=0`) | PURE (38/0, file) |
| 4 | `Lib/Math/Algebra/CayleyDickson/Integer/GaussianOrthogonality.lean:219` `i_orthogonality` | `gsum one I 4 = 0` (Gaussian, order 4) | (named object, §4a) |
| 6 | `…/Integer/RootOfUnityOrthogonality.lean:210` `zeta6_orthogonality` | `geomSum Zeta6 6 = 0` | PURE (38/0, file) |
| any `n ∣ p−1` | `…/ModArith/CyclicCharacterOrthogonality.lean:254` `cyclic_orthogonality_modp` | `Σ_{k<n} (g^{(p−1)/n})^k ≡ 0 (mod p)` | PURE (38/0 across the pair) |

The single engine across all orders is the **geometric telescope**
`(ζ−1)·Σ_{k<n} ζᵏ = ζⁿ−1` (`RootOfUnityOrthogonality.geomSum_telescope:190`,
PURE; ℕ-version `CyclicCharacterOrthogonality.geomNat_telescope:106`, PURE). The
order-2 `+1,−1` pair cancellation is its `n=2` instance — i.e. the ±1 tag **is**
literally the `k=2` slice of this one engine, as SYNTHESIS §2(i) already records.

### Scan tallies (this pass, run from repo root)

- `RootOfUnityOrthogonality` + `CyclicCharacterOrthogonality`: **38 PURE / 0 DIRTY**.
- `CassiniUnimodular` (carries `qpow`, the order-`NT` factorization): **part of 68 PURE / 0 DIRTY** (scanned with `ResidueTag`).

### What (a) actually grades — and the gap

`CassiniUnimodular.multiplier_unit_magnitude_sign_order_NT` is the load-bearing
bridge: the unimodular multiplier `q=±1` factors as **(unit magnitude, order-`NT`
sign)** — `q=+1` is the unit (`qpow 1 n = 1`, order 1), `q=−1` returns to the unit
only after `NT=2` steps (order 2). So **B's two poles ARE the two smallest cyclic
orders** of the multiplier: `converge ↦ order-1` root, `escape ↦ order-2` root.

This is real and PURE. But it does **not** make B the `k=2` truncation of a
`qᵏ=1` grading, for a precise reason:

> The order grading `k=1,2,3,4,6,…` grades the *multiplier of a single converging
> orbit* (the Cassini determinant scales by `q` each step). It is a grading
> **within the `q=+1`/converge world** — every `ζ` with `ζⁿ=1` is a converging
> unimodular multiplier; orders 3,4,6 are all "the orbit comes back," i.e. all on
> the `converge` side of B's dichotomy. The order-2 root `−1` is the **only** order
> that B reads as `escape` (alternation/non-fixed). Orders 3,4,6 do **not** give
> new *values of B*; they give finer structure inside one pole.

So (a) refines the *multiplier* (a `q=+1`-world object), not the *tag*. B's
`escape` pole (`object1_not_surjective`, fixed-point-free, the Cantor diagonal) has
**no `qᵏ=1` reading at all** — the escape consequence is a universal negation, not
a root of unity (`ResidueTag` docstring §"honest shape", and `escape_residue_outside`
delegates to `no_surjection_of_fixedpointfree`, not to any cyclic group). The
`qᵏ` grading is defined only where a multiplier exists; B is defined also where it
does not (the character-free/foundational world, SYNTHESIS §2(iv) "independent").

**Verdict on (a): B is NOT the order-2 truncation of the `qᵏ=1` grading.** The
`k=2` slice of (a) reproduces B's *multiplier* `−1`, but the grading lives entirely
inside B's `q=+1`/converge pole and never reaches B's `escape` pole. (a) is a
graded refinement *of the converge multiplier*, transverse to B's binary split.

---

## Candidate (b): the ℕ-graded depth/order (pole-order / nilpotency / valuation)

### What grounds it (grep-verified, scanned PURE this pass)

| grading | Lean anchor (file:name) | statement | scan |
|---|---|---|---|
| nilpotency degree (`ε²=0`) | `Lib/Math/Algebra/CayleyDickson/Tower/F2CDTower.lean:86` `F2D.eps_sq_is_zero` | `ε·ε = 0` in 𝔽₂[ε]/(ε²); `eps_has_no_inverse:122` | PURE (17/0, file) |
| `q`-adic valuation | `Meta/Nat/Valuation.lean` `vp`, `vp_not_dvd_succ:18`, `le_vp_iff` | `vp q n` = largest `k` with `qᵏ∣n`; exactness | PURE (32/0 incl. F2CDTower) |
| difference-depth = pole-order = growth-degree | `research-notes/frontiers/simplicial_operation_tower.md` §L3‴ (lines 318–355); anchors `MultSystem.diff_drops_rung`, `totalCount_eq` (= `×(1−x)⁻¹`), `monoCount_le_succ_pow` | three equivalent ℕ-graded handles on "dimension"; `×` = pole at `x=1` = `ζ` | (anchors cited PURE in L3‴; not re-scanned this pass — see ABSENT note) |

### Scan tallies (this pass)

- `F2CDTower` + `Valuation`: **32 PURE / 0 DIRTY** (run from repo root).
- The L3‴ difference-depth/pole-order anchors (`diff_drops_rung`, `totalCount_eq`,
  `monoCount_*`) are recorded PURE in `simplicial_operation_tower.md` but were
  **not re-scanned in this pass** — marked accordingly below.

### What (b) actually grades — and the gap

(b) is a real ℕ-grading: `vp` assigns `0,1,2,3,…`; `ε²=0` is the truncation of the
nilpotency tower at degree 2; L3‴'s difference-depth/pole-order is a genuine
ℕ-graded "dimension without ∞." These are load-bearing in the corpus.

But (b) grades a **different axis** than B. In the SYNTHESIS §2 frame and the
"read-off axes" table (SYNTHESIS §2 "The frame"), this is explicit:

- the `q=±1` swap-bit is the **direction / antisymmetry** axis
  (`bracket_antisymm`, `dsq_zero_universal_delta4`);
- pole-order / nilpotency / `∂`-degree is the **fold-height (bidirectional)** axis
  (`isPart_wf`, `dsq_zero_universal_delta4`, "dimension, degree, pole-order, ∂/d").

These are listed as **two distinct rows** of the frame. The `∂²=0` of homology
carries *both*: a sign-bit (`q=±1`, which is B) **and** a degree `n` (the
fold-height, which is (b)). They co-occur on one object (a chain complex) but are
**orthogonal coordinates** — `Ext^n`/`Tor_n` is graded by `n` (b) *and* tagged
`q=±1` (B) independently (SYNTHESIS §2 "the reflexive deepening"). The nilpotency
`ε²=0` is degree-2 in (b)'s grading, but its `q` is not thereby fixed — degree and
sign are read off separately.

**Verdict on (b): B is NOT the order-2 truncation of the depth grading either.**
(b) grades fold-height/degree; B is the sign/direction bit. `ε²=0` being a
"degree-2 truncation" is a truncation of the *height* axis, not of B. They are the
two independent coordinates of a graded-signed object, not one grading with B as
its low slice.

---

## Are (a) and (b) one invariant or two?

**Two.** They differ in the most basic way a grading can:

- (a) is **multiplicative / cyclic**: the index `k` is the *order* of a root of
  unity (`ζᵏ=1`), grading is **mod-`k` cyclic**, and the group is `ℤ/k`. Composition
  multiplies. Engine: `geomSum_telescope`.
- (b) is **additive / linear**: the index `n` is a *count* (valuation, pole-order,
  nilpotency degree, difference-depth), grading is **ℕ (free, non-cyclic)**, the
  monoid is `(ℕ,+)`. Composition adds (`vp_mul`: `vp(ab)=vp a + vp b`;
  `IsResolutionShift_compose`: grades add). Engine: differencing `×(1−x)`.

This is exactly the corpus's own **Invariant A character dichotomy** `×↦·` vs
`×↦+` (SYNTHESIS §2 Invariant A) reappearing one level up: (a) is the `×↦·`
(cyclic/multiplicative) grading, (b) is the `×↦+` (additive/log) grading. They are
related by the `exp`/`log` wall (CLAUDE.md "`^`-wall"), not by being two faces of
one ℕ-grading. There is **no corpus theorem** unifying a `qᵏ=1` order with a `vp`
depth into a single graded object — and there should not be, because cyclic order
and free additive depth are the two sides of the multiplicative/additive split the
calculus already names as irreducible (Invariant A).

A tempting false merge: "the order of `−1` is 2, and `ε²=0` truncates at 2, so both
are 'the number 2.'" This is the **count-Lens-import-as-Raw** failure mode
(CLAUDE.md): the `2` in (a) is a *cyclic order* (`ℤ/2`, sign-swap period), the `2`
in (b) is a *free degree* (`ℕ`, nilpotency exponent). Same numeral, different Lens —
not the same grading.

---

## Overall verdict

**B is the order-2 truncation of NEITHER (a) nor (b), and (a)/(b) are two distinct
refinements, not one graded invariant.** What is true and PURE-anchored:

1. B's *multiplier* `−1` is the order-exactly-2 root of unity
   (`multiplier_unit_magnitude_sign_order_NT`), so the `k=2` slice of (a)
   reproduces B's multiplier. But (a)'s higher orders (3,4,6,…) live **inside**
   B's `q=+1`/converge pole and give finer multiplicative structure there — they
   never produce new *values of B*, and B's `escape` pole has no `qᵏ=1` reading at
   all (it is a universal negation, `no_surjection_of_fixedpointfree`). So (a)
   grades the converge-world multiplier, **transverse** to B's binary split, not
   below it.
2. (b) grades fold-height/degree (`vp`, `ε²=0`, pole-order), an axis the SYNTHESIS
   frame lists **separately** from the `q=±1` swap-bit. `∂²=0` carries both a sign
   (B) and a degree (b) as **independent** coordinates; (b) is not B-with-a-grade.
3. (a) and (b) are the multiplicative (`ℤ/k`, cyclic) vs additive (`ℕ`, free)
   gradings — the Invariant-A `×↦·`/`×↦+` dichotomy one level up — separated by the
   `exp`/`log` wall, with no unifying theorem and no expectation of one.

The honest one-line answer: **the binary B does not refine to a graded invariant
of which it is the order-2 truncation. B is a sign/direction bit; the gradings
that exist (cyclic order, additive depth) grade the multiplier's order and the
fold-height respectively — two distinct axes, both orthogonal to B's escape/converge
content.** This is a calibrated NEGATIVE: no forcible unification was found, and the
structure of the failure (B is transverse to both gradings, which are themselves the
two sides of the multiplicative/additive split) is itself the result.

---

## Honest ABSENT / not-built ledger

- **A graded `ResidueTag`** (`ResidueTag` indexed by ℕ or `ℤ/k`, with `q=±1` as a
  slice): **ABSENT.** No such object exists; `ResidueTag` is a bare two-constructor
  inductive. Predicted by the question, not built — and the analysis above argues it
  *should not* be built as a single object (the two gradings are distinct axes).
- **A theorem linking `qpow`-order to `vp`-grading** (unifying (a) and (b)):
  **ABSENT and not expected.** Searched (`grep` over `research-notes/`, `theory/`):
  no witness. The `exp`/`log` wall (CLAUDE.md) is the structural reason.
- **L3‴ depth anchors re-scan**: the `diff_drops_rung` / `totalCount_eq` /
  `monoCount_*` theorems are recorded PURE in `simplicial_operation_tower.md` but
  were **NOT re-scanned in this pass**; only `F2CDTower` (17/0) and `Valuation`
  (32/0 with F2CDTower) were freshly scanned for (b). Treat the L3‴ PURE status as
  inherited, not re-verified here.
- **The `escape` pole as a root of unity**: structurally **ABSENT** (and the
  analysis says it cannot exist — escape is a universal negation, not a cyclic
  element). No false witness asserted.

## Scan summary (this pass, `tools/scan_axioms.py`, repo root)

| modules scanned together | PURE / DIRTY |
|---|---|
| `ResidueTag` + `CassiniUnimodular` | 68 / 0 |
| `RootOfUnityOrthogonality` + `CyclicCharacterOrthogonality` | 38 / 0 |
| `F2CDTower` + `Valuation` | 32 / 0 |

All cited Lean anchors grep-verified to exist at the line numbers given.
