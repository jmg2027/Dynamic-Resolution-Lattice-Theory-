# The descent leg — wire the act to the unfolding (the central open frontier)

**Core open problem.** The corrected 진의 (`the_substance_test.md` §CORRECTION) is that *mathematics
is the forced unfolding of the one primitive act of distinguishing*. A 3-agent panel (2026-06-22)
established **mechanically** that this is **not yet instantiated in the Lean**:

> Of 1571 files in `lean/E213/Lib/Math`, **1512 (96%) import neither `E213.Theory.Raw` nor
> `E213.Lens`.** The disciplines are built directly on Lean's native `Nat`/`Int`. Even
> `Theory/Raw` reads *out* into native `Nat` (`Raw.leaves : Nat`, `Raw.depth` via `Nat.add_comm`) —
> it **borrows** ℕ, it does not **generate** it.

So the generative chain the thesis needs — `Raw (slash) → Lens-reading → discipline` — is **severed**:
the act (`Theory/Raw/*`) and the unfolding (`Lib/Math/*`) are two adjacent codebases that share a
build target, not a derivation. Most of the corpus is excellent ∅-axiom **re-derivation** of classical
mathematics over native carriers; it is not **generation from the primitive**. (This is not a defect of
the theorems — they are real and PURE — but of the *claim* the originator now makes about them.)

## What "closing the descent leg" requires (the falsifiable target)

A worked case where a classical result is **re-obtained as a Lens reading of a `Raw` construction**,
with the chain load-bearing *in the proof*, not just the prose:

1. **Generate ℕ from `Raw`.** Promote `Raw.depth` / `Raw.leaves` / the `RawRecurrence` spine
   (`|S_n| = 2 + C(|S_{n-1}|,2)` → 2,3,5,12,68, the originator's discovered recurrence) into a
   *naturals object* `Nat₂₁₃` defined from the distinguishing, with its `succ`/`+`/`*` as
   Lens-readings of `slash`-operations — **not** Lean's `Nat`. The honest bar (skeptic's Attack 1):
   account for what is borrowed from the kernel (inductive, Pi, `Bool`) vs. generated.
2. **Re-derive one discipline over `Nat₂₁₃`.** Take a single downstream classical theorem already
   PURE over native `Nat` — candidates: `φ = μ ∗ id`, σ_m multiplicativity, or a figurate identity —
   and re-state + re-prove it over `Nat₂₁₃` via the Lens-arrow, ∅-axiom. This is the first genuine
   "discipline = the distinguishing's reading" demonstration.
3. **Forcing, not matching.** Strengthen the initiality story (`Lens/Foundations/Initiality`, `raw_initial`) so a
   *specific* classical structure is the **unique** distinguishing-preserving reading, not merely *a*
   reading that happens to match (skeptic's Attack 2: the primitive must be shown non-interchangeable
   with rivals — negation-first, relation-first).

## UPDATE (2026-06-22, later): generation headline closed; leg-2 discipline progressing

- **Generation headline — CLOSED** (`Lens/Number/Nat213/Generation.lean`, 4 PURE): ℕ₊ is the
  *canonical* leaves-Lens reading of iterated distinguishing, as theorems (not comments):
  `value_eq_leaves` (`value = Lens.leaves.view`, the `⟨1,1,(·+·)⟩` catamorphism),
  `succ_is_distinguishing` (`succ n = slashOrSelf n Raw.b` — `+1` IS a slash event),
  `generation_capstone` (`Lens.leaves.view (numeral n) = n+1`). So "ℕ₊ = the count-Lens reading of
  iterated self-distinguishing" is now a theorem routed through the canonical Lens — leg-1 is closed
  for ℕ₊ (the "ergonomic parallel" caveat is dissolved: the count is the canonical Lens).
- **Leg-2 discipline — progressing** (`Divisibility.lean`, 13 PURE, all over `Nat213`): divisibility
  is a **partial order** (`dvd_antisymm` + `mul_eq_one`), **order-refining** (`dvd_imp_eq_or_lt`:
  divisor ≤ dividend), **bounded below** (`one_dvd`) and **open above** (`dvd_no_top` — no top,
  forced by the primitive's non-closure). A discipline computed entirely on the distinguishing's ℕ₊.
- **Leg-3 — BRACKETED at the arithmetic level** (`Generation.lean`, 8 PURE):
  - *forced* (`count_reading_forced`): any `g` with atom↦1, slash↦+ is identically the leaf-count
    (initiality with teeth) — the reading is forced given the interpretation.
  - *necessary* (`distinguishing_necessary` + `deg_view_one`): a distinguishing-blind reading (constant
    combine ignoring the `slash`) collapses all numerals to one value, while the count separates them —
    the distinguishing structure is load-bearing, not decorative.
  Together: at the arithmetic level the unfolding is **forced AND the distinguishing is necessary** — a
  genuine partial answer to the skeptic's Attack 2.
- **Remaining (the genuinely hard part):**
  - leg-2 *depth* — a deeper discipline (primality / unique factorisation) over `Nat213`.
  - leg-3 *full rival-PRIMITIVE exclusion* — **two corners closed**:
    - *degenerate corner* (`OneDiagonal` §6, `no_distinguishing_on_subsingleton` +
      `raw_has_distinguishing`): the distinguishing is in the *type* of `Raw.slash (x y) (h : x≠y)`,
      so a non-distinguishing (subsingleton) rival cannot fire the slash even once — generates
      nothing; Raw meets the precondition (`a ≠ b`).
    - *unary / negation-first corner* (`UniverseChain.RivalArity`, 4 PURE): a unary rival's graded
      count is **linear** (`unaryCount n = n+1`), while the binary slash obeys the **super-linear**
      `2 + C(·,2)` recurrence (`rawCount_ge`: `n+2 ≤ rawCount n` ∀n; `binary_non_interchangeable_with_unary`:
      constant `+1` step vs `C(·,2)` step, strict domination). A negation-first rival cannot
      reproduce 213's graded structure — too slow, no branching.
    - *relation-first / non-distinctness corner* (`RivalArity` §2, 12 PURE total): a binary op
      *without* distinctness (allowing `op x x`) counts pairs *with repetition*
      (`relCount`, step `2 + choose2(·) + (·)`), so it **strictly exceeds** 213's distinct-only count
      at every level ≥ 1 (`nondistinct_rival_exceeds`); `distinctness_removes_self_combination` is the
      capstone — **213's distinguishing = the unrestricted binary rival minus the self-combinations**,
      the unique primitive forbidding `op x x`.
    - **All three formalized rival corners are now closed** (degenerate / unary / non-distinctness):
      the distinguishing primitive is non-interchangeable with each, ∅-axiom. *Honest residual*: no
      *finite* enumeration of rival classes is exhaustive — "the distinguishing is THE primitive
      against ALL conceivable rivals" is not a finitely-checkable statement (it would itself be a
      §5.1 universality claim). The three corners are strong evidence, not a closed totality.

## CORRECTION (2026-06-22): leg 1 is ~80% done — the gap is leg 2

A direct read of `Lens/Number/Nat213/` revises Agent B's import-count diagnosis. The Raw-native ℕ
**already exists with its own arithmetic**, not as a thin wrapper:

- `Nat213/Raw.lean` — the Method-A Raw chain: **`one := Raw.a`, `succ n := slashOrSelf n Raw.b`**
  (the successor *is* a `slash`/distinguishing operation against `b`). So ℕ₊ is literally the
  iterated self-distinguishing of the atom. `numeral_succ`, `value_succ_of_ne` PURE.
- `Nat213/Peano.lean` — an inductive ℕ₊ (`| one | succ`) with its **own** `add`/`mul` (defined on
  `Nat213`, *not* Lean's `Nat`) and the full commutative-semiring-minus-zero law set proven by
  induction over `Nat213`, ∅-axiom: `add_comm/assoc`, `mul_comm/assoc`, `add_mul`/`mul_add`,
  `add_left_cancel`, `mul_left_cancel`. **Plus the forcing theorems** — `no_additive_identity_at_one`,
  `no_closed_subtraction`, `no_absorbing_element`: the no-zero / no-subtraction / no-absorption shape
  is *forced* by the primitive (Raw has ≥1 atom), not chosen. **This is the "distinguishing forces the
  structure" content the skeptic (Attack 2) demanded** — a rival "ℕ-with-0" primitive is provably
  foreign here.
- `Nat213/Bridge.lean` — the iso: `toRaw : Peano → Raw`, `value_toRaw`, `toRaw_injective` (PURE).

So leg 1 (ℕ generated from the distinguishing, with forced structure) is **substantially present**.
What remains:

- **The real gap (leg 2):** per the Bridge's "Option C", the *abstract number-theoretic operations
  live on Lean `Nat`*; the Raw side "carries only the chart representative." So every **discipline**
  (φ=μ∗id, σ_m, LTE, …) is proven over Lean `Nat` and bridged — **none is computed over
  `Nat213.Peano` using its own `add`/`mul`.** The first genuine descent-leg deposit: take one
  classical theorem and prove it **over `Nat213.Peano`** (its operations), ∅-axiom, with no detour
  through Lean `Nat` in the statement. Candidates that fit a zero-free ℕ₊: a distributive/factoring
  identity, a divisibility fact, or a figurate identity rephrased without 0.
- **Leg 3 (forcing/uniqueness):** the Peano file is still flagged "ergonomic parallel, not
  lens-derived" though `Bridge` makes it iso to the lens-derived chain. Upgrade: show the `Peano`
  `succ`/`add` *are* the Lens-readings of the `Raw` `slash`-operations (not merely iso at the
  `value`/`toNat` level), and strengthen `Lens/Foundations/Initiality` so this reading is the **unique**
  distinguishing-preserving one (rules out rival primitives).

## UPDATE (2026-06-22, marathon) — the toNat-cone bet: PRE-REGISTERED, WON

A 4-agent panel (CT/HoTT positioning; 진의 re-inference; adversarial skeptic; marathon strategist)
re-ran the substance inference. The skeptic's sharpest *internal* discriminator, verified against the
Lean rather than the prose:

> The divisibility discipline's *statements* are Nat-free, but a load-bearing lemma in its **proof
> cone** — `Peano.mul_left_cancel` — laundered through Lean `Nat`: `congrArg toNat` → cancel in `Nat`
> via `NatHelper.mul_left_cancel_pos` → pull back through `toNat_injective` (76 `toNat` uses in
> `Peano.lean`). And `Order.add_ne_self` (used by `lt_irrefl`, itself in the cone via `dvd_no_top`)
> did the same. So "computed over `Nat213` with no detour through Lean `Nat`" held for the *types* but
> **not for the proofs** — "looks generated, is parasitic on `Nat`."

**Pre-registered falsifiable bet (G206 template).** *Every lemma in the `Nat213.Divisibility`
dependency cone can be re-proven by `Nat213`-induction with **zero `toNat` and zero Lean-`Nat`
lemmas**.* WIN = generation all the way down for one discipline; NULL = the generation was parasitic
on `Nat` (an honest datapoint against the thesis, exactly as designed).

**Result: WON.** The cancellation was re-derived natively, mirroring the file's own `mul_self_inj`
template (trichotomy + strict monotonicity from distributivity + `lt_ne`), with **no order or `toNat`
machinery imported**:
- `Peano.add_ne_self` (NEW, native): `add a c ≠ a` by structural induction (`add one c = succ c ≠ one`;
  `succ`-step via `succ.inj`) — replaces the `toNat`-laundered `Order.add_ne_self`, which is deleted.
- `Order.lt_mul_left` (NEW): `b < c ⟹ a·b < a·c` from left-distributivity (`mul_add`) alone.
- `Order.mul_left_cancel` / `mul_right_cancel` (NEW, native): trichotomy + `lt_mul_left` + `lt_ne`.
  `Divisibility` now opens cancellation from `Order`, not `Peano`.
- Bonus: `Peano.no_absorbing_element` (a flagship *forcing* theorem cited by `Divisibility`) de-laundered
  to native — `mul z 2 = add z z` (`mul_two`) so `mul z n = z` forces `add z z = z`, impossible by
  `add_ne_self`; the laundering helper `mul_two_grows` is deleted.

**Verification (the bet's mechanical gate).** `lake build E213` clean (439/439); `scan_axioms`
`Order` 10/0, `Divisibility` 13/0 (all PURE); `grep -E 'toNat|Nat\.|NatHelper'` over `Order.lean`
and `Divisibility.lean` returns **comments/docstrings only — zero code hits**; every Peano lemma in
the cone (`mul_one/comm/assoc`, `add_*`, `mul_add`, `add_mul`, `succ_ne_one`, `add_ne_self`) is
`toNat`-free. So the **first elementary discipline (divisibility) over the Raw-generated ℕ₊ now stands
on `Nat213` all the way down — proofs included.** This converts the skeptic's "looks generated" into
"is generated," for one discipline.

**M1 DONE (same marathon) — irreducibility over `Nat213`.** On the now-`toNat`-free foundation,
`Lens/Number/Nat213/Irreducible.lean` (18 PURE): `Irreducible p := p ≠ one ∧ ∀ a b, p = mul a b →
a = one ∨ b = one` (no Lean `Nat`); `two/three/five_irreducible`, `four_not_irreducible`,
`irreducible_divisors`. `five_irreducible` is genuine elementary number theory — proper divisors
enumerated by a **native `lt_succ_iff`** + a **native cofactor bound** (`cofactor_lt`: `a ≠ 1 ∧ p =
a·c ⟹ c < p`, from `lt_right_mul`), then the finite `(a,c)` grid refuted by structural `decide`
(PURE on `Nat213`'s `DecidableEq`). Whole cone `toNat`-free. This is rung 1 of the FTA-generated
capstone (M1→M6). Next: M2 (factorization existence, needs native well-founded recursion on
`Order.lt`) → M3 (Euclid + uniqueness via native descent gcd).

**M2 DONE (same marathon) — factorization existence over `Nat213`.** `Factorization.lean` (18 PURE):
`exists_factorization : ∀ n, ∃ l, (∀ p ∈ l, Irreducible p) ∧ prod l = n`. Both scouted pins (below)
were honoured *constructively*: native `acc_lt`/`wf_lt` (structural recursion, no `Nat` measure) +
`decBoundedExists` (decides `∃ c ≤ k, P c` for decidable `P`), giving decidable `lt`/`Dvd` (cofactor
`≤` dividend) and the *decided* dichotomy `irreducible_or_properDiv` — no `Classical.em`. Native
`mem_append_pure`/`not_mem_nil` avoid the propext-carrying core `List.mem_append`/`not_mem_nil`. Rung
2 of the FTA-generated capstone. Next: M3 (uniqueness — Euclid's lemma `p ∣ ab → p ∣ a ∨ p ∣ b` via a
native descent gcd / Bézout over `Nat213`, then list-permutation uniqueness of the factorization).

**M3 DONE (same marathon) — Euclid's lemma / primality over `Nat213`.** `EuclidUnique.lean` (7 PURE):
`euclid` (`p` irreducible, `p ∣ a·b → p ∣ a ∨ p ∣ b`) + `prime_dvd_prod` (`p ∣ ∏ L → p ∈ L`). The
no-zero/no-subtraction wall I anticipated (Bézout needs ℤ; division-with-remainder needs a zero
remainder) was **dissolved by an internal handle** (§5.4 guard, looked for before declaring a wall):
a *subtractive* Euclidean gcd — every step subtracts smaller from larger, the difference being the
`lt`-witness (`a<b ⟺ ∃k, a+k=b`), so it lives in ℕ₊ with no zero. gcd existence AND the multiplicative
law `gcd(c·a,c·b)=c·gcd(a,b)` (the Bézout substitute Euclid needs) are proved in **one** well-founded
induction on `a+b` (`gcd_exists_mul`, spec quantified over the scaling `c`). Rung 3 of the FTA-generated
capstone. Next: M4 — uniqueness up to permutation (needs a native, propext-free `List` permutation /
`erase` + `prod_erase`, then induction using `prime_dvd_prod` + `mul_left_cancel`).

**M2 advance scouting (the two pins, both now discharged above):**
- *Native well-foundedness is in hand* — `Acc lt` is provable over `Nat213` with **no `toNat`**, by
  structural recursion:
  `acc_lt : ∀ n, Acc lt n | one => Acc.intro _ (fun y h => absurd h (not_lt_one y)) | succ n =>
  Acc.intro _ (fun y h => (lt_succ_iff.mp h).elim (· ▸ acc_lt n) ((acc_lt n).inv ·))`.
  So `WellFounded lt := ⟨acc_lt⟩` is ∅-axiom — the descent recursion needs no `Nat` measure.
- *The case split must be CONSTRUCTIVE, not `by_cases (Irreducible n)`.* `Classical.em` is forbidden,
  and `Irreducible n` (a `∀` over `Nat213 × Nat213`) is not obviously decidable. Branch instead on a
  **bounded divisor search**: `Decidable (∃ a, lt one a ∧ lt a n ∧ Dvd a n)` via enumeration of
  `a < n` (with `Dvd a n` decidable through the cofactor bound `c < n`). Build that bounded
  decidability first; then the WF recursion splits on its result (proper divisor → recurse on the two
  `< n` factors and append; none → `n` irreducible).

**Honest residual (the next bet, not yet run).** Peano still has a `toNat`-laundered
`mul_left_cancel`/`mul_right_cancel` — retained because the **ℚ₊ Tower** cone
(`Tower/NatPairToQPos`, `Tower/PairCompletion`) still consumes them. That cone is the next
pre-registered target: de-launder the Tower (route its `mul_right_cancel` through `Order`'s native
one). The bridge lemmas `toNat`, `toNat_add/mul`, `toNat_injective` legitimately *are about* `toNat`
(homomorphism characterisations), not laundering, and stay. And the deepest gap (leg-2 *depth*) is
unchanged: irreducibility / unique factorisation over `Nat213` (strategist's milestones M1–M3) — now
on a genuinely `toNat`-free foundation, which is the right ground to build them on.

## Other seeds

- `Lib/Math/Foundations/UniverseChain/RawRecurrence.lean` — the `Raw → count` recurrence
  (`|S_n| = 2 + C(|S_{n-1}|,2)`, → 2,3,5,12,68); consumed by one file. The combinatorial spine.
- `Lens/Foundations/Initiality.lean`, `Theory/Raw/Lambek.lean`, `Theory/Raw/MuNuMirror.lean` — initiality/μF-νF
  apparatus for leg 3.

## Why this is the central frontier (not peripheral)

Per the correction, *this is the work*: without the descent leg, the breadth of ∅-axiom re-derivations
witnesses **constructivity per domain** (real, the census artifact) and Line A witnesses **unity across
some domains via shared engines** (`genSwap`, `det2_mul`, `lcm`-meet) — but *neither* witnesses
**generation from the act**. The descent leg is the only thing that would make "mathematics is the
distinguishing's unfolding" a demonstrated theorem-chain rather than an asserted slogan.

## Honest risk

This is large and may not close cleanly: reconstructing ℕ from `Raw` without silently re-importing the
kernel's inductive ℕ is exactly where the skeptic's circularity attack (Attack 1) bites. The
deliverable may end up being a *precise accounting* of what is genuinely generated vs. borrowed — which
is itself valuable (it converts the slogan into a measured claim), even if full generation is out of
reach. Time-box and report honestly, win or lose (the G206 template).

## Pointers
- Diagnosis + corrected 진의: `the_substance_test.md` §CORRECTION (2026-06-22).
- Generation already deposited (the *other* prong): `Lens/Foundations/OneDiagonal.lean` (the residue as the
  engine of the limitative theorems), `theory/essays/foundations/the_one_diagonal.md`.
