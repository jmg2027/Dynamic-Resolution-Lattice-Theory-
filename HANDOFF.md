# Session Handoff — 2026-06-24 (autonomous research: Nat213 order discipline)

## Branch
`claude/continuation-5yvjwq` — working tree clean, pushed. **Full `lake build
E213` passes clean (463/463).** All new theorems ∅-axiom (`#print axioms`
empty, verified individually). Started from `main` after the previous
grounded-FTA + Leg-1 marathon merged.

## What Was Done This Session (autonomous-research, fifteen iterations)

Fifteen focused iterations on the **descent-leg discipline** over `Nat213` (the
Raw-generated ℕ₊, `Lens/Number/Nat213/`) — building the **complete** leg-2
elementary number theory chain on the generated carrier, then **promoting it to a
`theory/` chapter**: order → divisibility → gcd → coprimality → well-ordering →
exponentiation → **p-adic valuation** (both forms, exactness + uniqueness), all
∅-axiom.

### Iteration 15: the readout bridge generalized — `ToNatReadout.lean` (PURE ✓)
Extracted the carrier-readout API (from `Valuation`) into a reusable file and
generalized from `Dvd` to the whole order/divisibility structure: `lt_toNat_iff`,
`le_toNat_iff`, `dvd_toNat_iff` (each direction, ⟸ via `toNat_surj`), `toNat_powNat`,
capstone **`toNat_faithful`** — `toNat` transports `lt`/`le`/`Dvd` exactly and is
surjective onto ℕ₊, i.e. the essay's "faithful homomorphism" made a theorem for the
whole structure. `Valuation` now imports it; `vp_eq_vpSub` unchanged.

### Iteration 14: the carrier weld as a proven equation (PURE ✓)
`Valuation.vp_eq_vpSub` — for a prime `p` (`p ≠ one`), `vp p n = vpSub p.toNat
n.toNat`: the generated `p`-adic valuation over `Nat213` equals the native
`subMod`-grounded `vpSub` (`Meta/Nat/VpSub213`) of the depth readouts. Both are
"the largest dividing exponent" (`le_vp_iff` / `le_vpSub_iff`), matched by the
carrier bridge `dvd_toNat_iff` (`Dvd a b ⟺ a.toNat ∣ b.toNat`, ⟸ via `toNat`
surjectivity onto ℕ₊) + `toNat_powNat`, closed by `Nat.le_antisymm`. Carries the
prose weld (essay #112) to a proven equation — closes #103's frontier in Lean.
Purity craft: `.mp`/`.mpr` application, NOT `rw` on iff lemmas (`rw` iff→eq pulls
`propext`).

### Iteration 13: cross-domain essay — the carrier-gap weld
`theory/essays/synthesis/two_carriers_one_count.md` (essay #112) closes essay
#103's open frontier: `toNat` is a faithful (injective) `+`/`×` homomorphism
(`Peano.toNat_{add,mul,injective}`, image ℕ₊) welding the `Nat213` discipline to
the native-`Nat` corpus — agreement = functoriality of the count-Lens, native
`Nat` = the readout plus the `0` the spine forbids. Open frontier kept: the
valuation-specific cross-carrier identity `vp = vpNative ∘ toNat` (not yet a Lean
theorem) — the concrete next deposit.

### Iteration 12: promotion to a theory/ chapter (PROMOTION_CRITERIA met)
The closed leg-2 cone (H1 ∅-axiom ✓, H2 build clean ✓, S1 categorically closed)
promoted to **`theory/math/numbertheory/number_theory_over_the_spine.md`** — a
mirror chapter organized by the discipline chain, sibling to the carrier chapter
`naturals_from_the_spine.md` (cross-linked both ways), complementing the
native-`Nat` `grounded_fundamental_theorem.md`. Registered in `theory/math/INDEX.md`
(+ the previously-missing `grounded_fundamental_theorem`); promotion #111 logged.
The conceptual residue (Legs 1 & 3) stays open in `frontiers/the_descent_leg.md`
(cited in the chapter's Open frontier).

### Iterations 10–11: p-adic valuation, both forms, closed (PURE ✓) — Valuation.lean
After a design memo on the no-zero snag (a valuation counts, and the count can be
zero, but `Nat213` has no zero), implemented **both** agreed forms and closed both
frontier follow-ups:
- **A (readout into ℕ):** `Peano.powNat` (Nat-exponent power, `powNat a 0 = one`),
  with `powNat_add` + the bridge `pow_eq_powNat_toNat`. `Valuation.vp :
  Nat213→Nat213→Nat` (multiplicity reads OUT into ℕ where 0 lives), `vpSearch`
  (downward search on `decDvd`, no Classical), `pow_vp_dvd`, and **exactness
  `le_vp_iff`** (`p^k ∣ n ⟺ k ≤ vp p n` for `p ≠ one` — `vp` is the largest
  dividing exponent).
- **B (native):** `padic_factorization` (`p∣n → n = p^k·m`, `¬p∣m`) + **uniqueness
  `padic_factorization_unique`** (the `(k,m)` is unique — welds B's native exponent
  to A's `vp`). Fully native, no readout.
The leg-2 `Nat213` cone is now a complete ∅-axiom elementary-number-theory
discipline on the generated carrier.

### Iteration 9: prime divides a power ⟹ divides the base (PURE ✓)
- **`Divisibility.self_dvd_pow`** — `a ∣ a^n` (always; no zero exponent).
- **`Prime.irreducible_dvd_pow`** — `Irreducible p`, `p∣a^n ⟹ p∣a` (Euclid
  iterated by induction on `n`).
- **`Prime.irreducible_dvd_pow_iff`** — `Irreducible p → (p∣a^n ↔ p∣a)`.

### Iteration 8: the Prime↔Coprime bridge (PURE ✓)
`Coprime` gains the named form of the lemma `euclid` computes internally:
- **`coprime_of_irreducible_not_dvd`** — `Irreducible p`, `¬ p∣a ⟹ Coprime p a`.
- **`not_dvd_of_irreducible_coprime`** — the converse.
- **`irreducible_coprime_iff`** — `Irreducible p → (Coprime p a ↔ ¬ p∣a)`.

### Iteration 7: pow order/divisibility facts (PURE ✓)
- **`Order.lt_mul_right`** (companion to `lt_mul_left`) + **`Order.pow_lt_pow_base`**
  (`a<b → a^n<b^n`, strict monotonicity in the base).
- **`Divisibility.dvd_pow_self`** (`a ∣ a^(n+1)`) + **`Divisibility.pow_dvd_pow`**
  (`m ≤ n → a^m ∣ a^n`, via `pow_add`).

### Iteration 6: exponentiation + power-coprimality (PURE ✓)
- **`Peano.pow`** — `a^n` recursing on the exponent (`a^1=a` base, no zero
  exponent since `Nat213` has no zero), with `pow_one`, `pow_succ`, `one_pow`,
  `pow_add` (`a^(m+n)=a^m·a^n`), `pow_mul` (`a^(m·n)=(a^m)^n`), `mul_pow`
  (`(a·b)^n=a^n·b^n`).
- **`Coprime.coprime_pow`** — `Coprime a b → Coprime (a^m) (b^n)`, via
  `coprime_pow_right`/`left` (induction over `coprime_mul`).

### Iteration 5: well-ordering `WellOrder.lean` (PURE ✓) — NEW FILE
`Factorization.wf_lt` (`WellFounded lt`, by structural `acc_lt`) exposed as a
named API:
- **`strong_induction`** — the ergonomic named form of `wf_lt.induction`.
- **`well_ordering`** — every inhabited *decidable* predicate has a `lt`-minimal
  witness; strong induction on the witness, deciding at each step (via
  `decBoundedExists`) whether a smaller `P`-element exists. Decidable-`P` only
  (general `Prop` form needs excluded middle); fully constructive, no `Classical`.
- Wired into the aggregator (now 462 modules).

### Iteration 4: coprimality `Coprime.lean` (PURE ✓) — NEW FILE
Built on `Gcd`: `Coprime a b := IsGcd a b one` (gcd is the divisibility bottom).
- **`coprime_dvd_mul`** (headline) — `gcd(a,b)=1` and `a ∣ b·c ⟹ a ∣ c`, the
  `EuclidUnique.euclid` scaling trick packaged generically from
  `Gcd.isGcd_mul_left` (scale `gcd(b,a)=1` by `c` → `gcd(c·b,c·a)=c`).
- **`coprime_mul`/`mul_coprime`** — multiplicative closure: coprime to each factor
  ⟹ coprime to the product (a common divisor of `a` and `b·c` is coprime to `b`,
  so divides `c`, and being coprime to `c` divides `one`).
- `coprime_comm`, `coprime_one_{left,right}`, `coprime_self_imp` (only the unit is
  self-coprime), `coprime_of_dvd_{left,right}` (descent to divisors).
- Wired into the aggregator (now 461 modules).

### Iteration 3: the gcd discipline `Gcd.lean` (PURE ✓) — NEW FILE
`EuclidUnique.gcd_exists_mul` had proved subtractive-gcd existence with the
*scaled* multiplicative spec in one well-founded induction (no zero, no
subtraction operator). Extracted the clean discipline:
- **`IsGcd a b d`** — the greatest lower bound of `a`, `b` in the `Dvd` partial
  order. **`isGcd_exists`** (from the algorithm), **`isGcd_unique`** (via
  `dvd_antisymm` — "the" gcd justified), `isGcd_comm`, projections, `isGcd_self`,
  `isGcd_one_{left,right}`, `isGcd_of_dvd`.
- **`isGcd_mul_left`/`isGcd_mul_right`** — the multiplicative law
  `gcd(c·a,c·b)=c·gcd(a,b)` (Euclid's Bézout substitute), from scaled existence +
  uniqueness.
- **`gcd_meet_semilattice`** — capstone: divisibility over `Nat213` is a
  meet-semilattice. Wired into the aggregator (now 460 modules).

### Iteration 2: the non-strict order `le` + cross-discipline bridge (PURE ✓)
- **`Nat213.Order.le`** — promoted the non-strict order from a buried local
  helper in `Factorization.lean` (which had only `le_refl`/`le_succ_of_le`) to a
  full **total partial order**: `le_refl`, `le_of_lt`, `le_succ_of_le`,
  `le_trans`, `le_antisymm`, `le_total`, and the `le_total_order` capstone (the
  non-strict twin of `lt_strict_total_order`). Also promoted `lt_succ_self` and
  `lt_of_succ_lt_succ`. `Factorization` now keeps only the *decidability*
  (`decLt`, `decBoundedExists`) and reuses Order's primitives; `EuclidUnique`'s
  `lt_trans` redirected from Factorization to Order.
- **`Divisibility.dvd_imp_le`** — `a ∣ t → a ≤ t` (divisibility refines the
  additive order), one line via `dvd_imp_eq_or_lt` read through `Order.le`. The
  bridge between the multiplicative (`Dvd`) and additive (`le`) disciplines.

### Iteration 1: the strict order completed + INDEX refresh (PURE ✓)
A focused iteration tightening the native order and fixing badly-stale docs.

### 1. `Nat213.Order`: completed the native strict order (PURE ✓)
`Order.lean` proved trichotomy, multiplicative monotonicity, and cancellation
but was missing transitivity, asymmetry, and additive monotonicity.
- **`lt_trans`** — *promoted* from a `private lt_trans'` that lived inside
  `Divisibility.lean` (a dedup smell, repo org rules 7/8). Now public in
  `Order`; `Divisibility` reuses it and its private duplicate is gone.
- **`lt_asymm`** — `a < b → ¬ b < a` (trans + irrefl).
- **`lt_strict_total_order`** — capstone bundling irrefl + trans + trichotomy
  (the additive twin of `Divisibility.divisibility_preorder_with_bottom`).
- **`lt_add_right`** (`a < a + b`), **`add_lt_add_left`**, **`add_lt_add_right`**
  — additive monotonicity, from `add_assoc`/`add_comm` only. The additive
  counterpart of the multiplicative `lt_mul_left`/`lt_mul_self` already present.
All over `Nat213` — no `toNat`, no Lean `Nat` order lemma.

### 2. `Nat213/INDEX.md` refresh (doc hygiene)
The INDEX was stale at "Files (12) / five representations" while the directory
had grown to **25 + Tower/5**. The entire leg-2 number-theory discipline
(Order, Divisibility, Irreducible, EuclidUnique, Prime, Factorization, FTA,
Infinitude, ChebyshevLower), the generation layer (Generation, Forcing), the
multiplicative system (MultSystem, MultSystemValue, SignatureMaps), and the two
new Tower completion files were unlisted. Reorganised by role with accurate
one-line descriptions and a current count.

## Commits this session
```
4c4c8d1 Nat213.ToNatReadout: the depth readout is a faithful ordered-semiring embedding
a54b3e7 Nat213.Valuation: the carrier weld vp_eq_vpSub — generated vp = native vpSub of readouts
d913cc7 Essay: "Two carriers, one count" — the depth-readout welds the number theory
b11dc2c Promote: leg-2 number-theory discipline over Nat213 → theory/ chapter
ea8184d Nat213.Valuation: exactness le_vp_iff — vp is the largest dividing exponent
8e7408c Nat213.Valuation: uniqueness of the p-adic factorization (welds B's k)
cc00261 Nat213: p-adic valuation — both forms (powNat + vp readout, padic_factorization)
734ea5d Nat213.Prime: a prime dividing a power divides the base (irreducible_dvd_pow)
bce6f45 Nat213.Coprime: the Prime↔Coprime bridge (irreducible_coprime_iff)
c9f198f Nat213: pow order/divisibility facts (pow_lt_pow_base, dvd_pow_self, pow_dvd_pow)
68c4732 Nat213: exponentiation on Peano + coprime_pow
c4c35e8 Nat213.WellOrder: well-foundedness as a named API (strong_induction, well_ordering)
2e9a270 Nat213.Coprime: multiplicative closure (coprime_mul, mul_coprime)
4b27642 Nat213.Coprime: coprimality + Euclid's coprime-division law
8ff4416 Nat213.Gcd: the gcd discipline — divisibility is a meet-semilattice
81dc3d1 Nat213.Divisibility: dvd_imp_le — divisibility refines the additive order
5674cf4 Nat213.Order: promote the non-strict order `le` to a total partial order
14b855d Nat213.Order: additive monotonicity (lt_add_right, add_lt_add_{left,right})
7fcf196 Nat213 INDEX: refresh for the descent-leg discipline (12 → 30 files)
b3c9da1 Nat213.Order: promote lt_trans, add lt_asymm + strict-total-order capstone
```

## Current Precision Results (0 free parameters)
**No physics touched this session** (pure math/order-theory + docs). The DRLT
precision table is unchanged — see `catalogs/physics-constants.md` (canonical).

## Open Problems (Priority Order)
Unchanged from the prior handoff — the deep items are conceptual residue:

### 1. Leg 3 residue — "suffices by breadth, not proven unique"
Four rival primitive classes are formally excluded, but no proof that *no*
conceivable primitive generates equal richness. Deepest open item, likely not
fully closable. `frontiers/the_descent_leg.md` (Leg-3) + `frontiers/the_one_act.md`.

### 2. Leg 1 final residue — the kernel `inductive` itself
`Nat213`/`RawNat` still borrow the kernel's `inductive` to *have* `Raw`, and
`Nat` as the `depth` readout (conceded). `frontiers/the_descent_leg.md` §5.

### 3. Further leg-2 disciplines over `Nat213`
The `Nat213` elementary-number-theory cone is now a **coherent chain**: order
(strict `lt` + non-strict `le`, both total; monotonicity; Dvd↔le bridge) →
divisibility → gcd (`Gcd.lean`: meet-semilattice) → coprimality (`Coprime.lean`:
coprime-division law + descent + mult. + power closure) → well-ordering
(`WellOrder.lean`: strong induction + decidable well-ordering), with `pow` on the
`Peano` arithmetic base, with the full `pow` API and the Prime↔Coprime bridge.
Remaining natural deposits, low-risk:
- **prime-power valuation** over `Nat213` (`vp`-style) — NOTE the snag: a valuation
  counts *how many times* and can be **zero**, but `Nat213` has no zero. A native
  `vp : Nat213 → Nat213 → Nat` would read OUT into ℕ (a count-Lens readout, the
  legitimate direction) and need a Nat-exponent `pow` variant (`powNat p 0 = one`),
  duplicating machinery. Cleaner framing: the **p-adic factorization** `n = p^k · m`
  with `¬ p ∣ m` stated only for `p ∣ n` (so `k ≥ 1`, expressible in `Nat213`).
  Deferred — needs design (decide readout-into-ℕ vs. p∣n-restricted form first).
- an `lcm` as the dual join (harder — needs a bound; defer).
- consider whether `acc_lt`/`wf_lt` should *move* from `Factorization` to
  `WellOrder` (their natural home) — deferred as an org pass; would touch
  `Factorization`/`EuclidUnique` opens. Clean, low-risk, build-verifiable.

## Next
The `Nat213` leg-2 number-theory cone is **complete and promoted** (chapter
`theory/math/numbertheory/number_theory_over_the_spine.md`). The remaining
descent-leg work is **conceptual** (Legs 1 & 3 — generation-vs-borrowing,
forcing-vs-matching; research-grade, `frontiers/the_descent_leg.md`). Recommended
next moves:
- A fresh campaign regrounding another field on `subMod`/structural descent (the
  prior handoff's thick target) — e.g. modular arithmetic or a divisor theory over
  `Nat213`, extending the now-promoted cone.
- The carrier weld (`vp_eq_vpSub`) and the general readout bridge
  (`ToNatReadout.toNat_faithful`: `lt`/`le`/`Dvd` all read exactly + surjectivity)
  are closed. A remaining concrete readout deposit: a **generated `gcd`'s readout =
  the grounded native `SubGcd213.gcdSub`** (the gcd analogue of `vp_eq_vpSub`,
  using `dvd_toNat_iff` + the gcd specs) — low-risk if `SubGcd213` exposes a
  divides-both+greatest characterization; check first.
- Minor leftover: an `lcm` dual join (needs an upper bound; deferred).
- Or a fresh campaign regrounding another field on `subMod`/structural descent.
The deep conceptual residue (Open Problems 1–2) needs a specific new rival model
and is research-grade.

## Three-tier state
- No promotions this session (incremental theorem deposits + doc fix; the
  Nat213 cone is already promoted at `theory/math/numbersystems/naturals_from_the_spine.md`).
- **Active scratchpad**: `research-notes/frontiers/the_descent_leg.md` (Leg-1/Leg-3 residue).

## File Map (touched this session)
```
lean/E213/Lens/Number/Nat213/ToNatReadout.lean   ← NEW: faithful readout bridge (lt/le/dvd_toNat_iff, toNat_faithful)
lean/E213/Lens/Number/Nat213/Valuation.lean      ← NEW: p-adic valuation (vp readout + padic_factorization + vp_eq_vpSub weld)
lean/E213/Lens/Number/Nat213/Peano.lean          ← +pow + pow laws; +powNat (Nat-exponent power) + bridge
lean/E213/Lens/Number/Nat213/Order.lean          ← +lt_mul_right, pow_lt_pow_base
lean/E213/Lens/Number/Nat213/Divisibility.lean   ← +dvd_pow_self, pow_dvd_pow, self_dvd_pow
lean/E213/Lens/Number/Nat213/Prime.lean          ← +irreducible_dvd_pow, irreducible_dvd_pow_iff
lean/E213/Lens/Number/Nat213/WellOrder.lean      ← NEW: strong_induction + decidable well_ordering
lean/E213/Lens/Number/Nat213/Coprime.lean        ← NEW: coprimality; +coprime_pow; +Prime↔Coprime bridge
lean/E213/Lens/Number/Nat213/Gcd.lean            ← NEW: gcd discipline (meet-semilattice, mult. law)
lean/E213/Lens/Number/Nat213/Order.lean          ← +lt_trans/lt_asymm/lt_strict_total_order/additive monotonicity/le total partial order
lean/E213/Lens/Number/Nat213/Divisibility.lean   ← reuse Order.lt_trans (private dup removed); +dvd_imp_le
lean/E213/Lens/Number/Nat213/Factorization.lean  ← order primitives moved to Order; keeps decidability + bounded search
lean/E213/Lens/Number/Nat213/EuclidUnique.lean   ← lt_trans redirected to Order
lean/E213/Lens/Number/Nat213.lean                ← +import Gcd (aggregator, 460 modules)
lean/E213/Lens/Number/Nat213/INDEX.md            ← refreshed (12 → 31 files, role-organised; Order/Divisibility/EuclidUnique/Gcd lines)
```
</content>
