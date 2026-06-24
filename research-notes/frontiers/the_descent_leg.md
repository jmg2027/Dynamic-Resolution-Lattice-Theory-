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
capstone.

**M4 DONE (same marathon) — THE FTA CAPSTONE CLOSED.** `FTA.lean` (11 PURE): `fta` =
existence (`exists_factorization`) + uniqueness up to permutation (`factorization_unique`), generated
over `Nat213`. A native propext-free `Perm` inductive + native `erase`/`prod_erase`/`cons_erase_perm`
(the core `List.Perm` lemmas import `propext`), then structural induction using `prime_dvd_prod` to
locate the head in the second list and `mul_left_cancel` to descend. **The arithmetic-generation half
of the descent leg is achieved**: the Fundamental Theorem of Arithmetic is now *computed on the
Raw-generated carrier* — "math is the distinguishing's unfolding" instantiated for arithmetic, not
asserted. Remaining: the *forcing* half (M5 rival-exclusion: a distinguishing-blind reading cannot
carry factorization; M6 `DStr`-dichotomy merge), and the §5.1 verdict-wall (a clean capstone proves
coherence+forcing, not "not a re-skin") → Line B exposure is the only external test.

**M5 DONE (same marathon) — the FTA carrier forced by the distinguishing.** `Forcing.lean` (3 PURE):
`peano_succ_is_distinguishing` (under `Bridge.toRaw`, Peano's `succ` *is* `Raw.succ = slashOrSelf ·
Raw.b`, the distinguishing op) + `factorization_forced_by_distinguishing` (`five` irreducible, `four`
not; the distinguishing-blind `Generation.degLens` collapses both Raw images to `1`, while the count
reading `Raw.value` — which uses the distinguishing via `+` — separates `4 ≠ 5`). So a reading blind
to the act cannot carry the prime/composite distinction the FTA rests on. **Honest boundary stated in
the file**: `Peano.Nat213` is an *ergonomic parallel* inductive, not literally `Raw`; the link is the
*injective* bridge, so the earned claim is **recognition, not genesis** (the marathon's wall #1). M6
(`DStr`-dichotomy merge — every rival `≅ Raw` or fails a named clause, via `UniversalDistinguishing`)
remains.

**M6 DONE (negative arm; positive arm = the open existence leg).** `Forcing.lean` extended (now 6
PURE): `forcing_dichotomy` lifts M5's single `degLens` instance to the schema level —
*positive side* the FTA carrier's home `Raw` is the free `DStr` (`rawDStr_generated`) and `Nat213`
embeds injectively (`Bridge.toRaw_injective`); *negative side* any distinguishing-blind (subsingleton)
carrier neither hosts the FTA carrier (`subsingleton_cannot_host_fta`: `four ≠ five` can't collapse)
nor is even a `DStr` (`no_DStr_on_subsingleton`, fails named clause D1 `e_ne`). **The one remaining
gap is honest and explicit**: that *every* `Generated DStr` is `≅ Raw` (so carries the FTA by
transport) is the **open `DStr` existence leg** (`the_distinguishing_schema.md`; only the uniqueness
half `dhom_unique_pointwise` is proven). The forcing half of the descent leg is otherwise closed.

**Applied (same marathon) — Euclid's theorem over `Nat213`.** `Infinitude.lean` (3 PURE):
`infinitude_of_irreducibles` — no finite list of irreducibles is complete, generated over the
Raw-derived carrier from the FTA (native: `succ (prod L)` has an irreducible factor `q`; `q ∈ L` ⟹
`q ∣ prod L` and `q ∣ succ (prod L)` ⟹ `q ∣ 1` ⟹ `q = 1`, impossible). A *second* discipline-defining
theorem after the FTA — primacy as breadth (§7.1), the residue-as-`Nat213` reproducing another
classical result with no Lean `Nat`.

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

## UPDATE (2026-06-24): the descent ENGINE now grounds in `isPart_wf` (PURE ✓)

The named bar — "factorisation/FTA descent must terminate via **Raw's own descent** `isPart_wf`, not
borrowed `Nat.strongRecOn`" — is now **cleared at the induction-engine level**
(`Lib/Math/Foundations/IsPartGroundedInduction.lean`, 6 PURE, all ∅-axiom):

- `nat_lt_wf_via_isPart : WellFounded (· < ·)` — `Nat`'s `<` is well-founded **because the
  distinguishing's descent is**: `m < n` embeds into `TransGen IsPart (rawTower m) (rawTower n)`
  (`tower_lt_transGen`, one rung per `+1`), and WF transports along `InvImage`/`Subrelation` from
  `transGen_wf isPart_wf`.
- `strongInduction_grounded`, `measureInduction_grounded` — strong/measure induction on ℕ powered by
  this WF (the `Ω`-descent shape FTA existence needs).

**Decisive check (direct kernel-closure walk on `strongInduction_grounded`):**
`isPart_wf : true`, `rawTower : true`, `Acc.rec : true` (powered by `isPart_wf`) — and crucially
`Nat.lt_wfRel : false`, `Nat.strongRecOn : false`. So the well-founded engine is Raw's, not Nat's.
This is exactly the criterion `the_genesis_seam.md` found FTA-over-`Nat213` *failing*. (cic_footprint.py
mis-resolved the target and returned a spurious "no Acc / Nat-free" reading; the direct closure walk —
325 consts, `isPart_wf` present, `Nat.lt_wfRel` absent — is authoritative.)

**Honest scope.** This clears the bar for the *engine*. The embedding lemma `tower_lt_transGen` still
uses `Nat` structural recursion to prove an *inequality* (bookkeeping, not the descent). And FTA
existence itself is **not yet rebuilt** on this engine — the next step is to re-prove
`mul_factorization_exists` via `measureInduction_grounded` (Ω-measure) **and** audit that `minFac`/`Ω`
definitions in its cone don't re-introduce `Nat.strongRecOn`. Until that, the deep discipline's
descent is groundable but not yet grounded. The engine is the reusable keystone; wiring FTA onto it is
the remaining concrete step.

### UPDATE (2026-06-24, cont.): FTA descent re-routed onto the engine — measured PARTIAL, blocker named

Applied the engine to FTA existence (`NumberTheory/MulDescentGrounded.mul_factorization_exists_grounded`,
PURE): the descent now goes through `measureInduction_grounded` (peel `n ↦ n/minFac n`, `id`-measure).
Direct closure walk, grounded vs old:

| | `isPart_wf` | `Nat.strongRecOn` | `Nat.lt_wfRel` |
|---|---|---|---|
| old `mul_factorization_exists` | false | true | true |
| grounded (this file) | **true** | **true** (still) | true |

**Honest verdict: the FTA bar is NOT yet cleared.** Re-routing the descent *added* `isPart_wf` (real
progress — the recursion now terminates on `Raw`'s descent) but did **not remove** `Nat.strongRecOn`:
a reused supporting lemma carries it, traced precisely to `minFac_spec` → **`leastFactorFrom_spec`**
(the least-factor search's correctness proof uses strong recursion). So swapping the descent is
necessary-not-sufficient; the **`minFac`/`leastFactorFrom` specification chain must be rebuilt on
structural-fuel induction** as the next concrete step. `Nat.lt_wfRel` remains from `Nat.div` (separate
borrowed primitive). The deliverable is the *measured accounting*: engine clean, descent grounded,
remaining blocker isolated to one named lemma — the "win or lose, report honestly" the note asks for.

### UPDATE (2026-06-24, cont. 2): FTA existence — descent-leg bar CLEARED (PURE ✓)

Pushed through. `mul_factorization_exists_grounded` now measures (direct closure walk + `#print axioms`):

| | `isPart_wf` | `Nat.strongRecOn` | `Nat.lt_wfRel` | axioms |
|---|---|---|---|---|
| grounded FTA (final) | **true** | **false** | true | **none (∅-axiom)** |

The bar — *factorisation terminates via `Raw`'s own descent, not borrowed `Nat.strongRecOn`* — is
**cleared for FTA existence**. The remaining-blocker hunt bottomed out at a **single point** and a
two-step fix cleared the whole chain:

1. **`AddMod213.div_add_mod`** (`n = b·(a/b) + a%b`) was the sole source of `Nat.strongRecOn` for the
   entire `minFac`/`leastFactorFrom` chain — its proof used `Nat.strongRecOn` for the `a ↦ a-b`
   descent. Rebuilt on **structural fuel recursion** (`Nat.rec` on a bound): `strongRecOn` gone from
   `div_add_mod`, `minFac_spec`, `minFac_prime`, and everything above. (Kept ∅-axiom: the new zero
   case avoided `Nat.zero_mod`, which leaks `propext`.)
2. In `mul_factorization_exists_grounded`, the two core div lemmas `Nat.div_lt_self` (carries
   `strongRecOn`) and `Nat.mul_div_cancel'` (carries `propext`) were replaced by `div_lt_self'` and a
   `div_add_mod`+`mod_zero_of_dvd` cancellation — both built from the now-clean `div_add_mod`.

**Honest residual.** `Nat.lt_wfRel` remains, isolated to `Nat.div`/`Nat.mod` (kernel WF-recursion) —
division as a borrowed *arithmetic primitive*, a separate frontier from the *descent* (the deep
carrier-rebuild, `the_genesis_seam.md`). So: the factorisation **descent** is grounded in the
distinguishing; **division** is still a borrowed op. That is the precise, measured generated-vs-borrowed
boundary for the multiplicative discipline — the descent leg's first deep-discipline clearance.

**Bonus**: the `div_add_mod` fuel-rewrite removes `Nat.strongRecOn` from *every* downstream user of
`minFac`/`leastFactorFrom`, not just FTA (Meta.Nat builds clean, 108 modules).

### UPDATE (2026-06-24, cont. 3): division rebuilt structurally — the divisibility primitive (PURE ✓)

Toward removing the residual `Nat.lt_wfRel` (from `Nat.div`/`Nat.mod`, kernel WF-recursion).  The
divisibility test is the load-bearing use of `Nat.mod` in `minFac`/`leastFactorFrom`.  Rebuilt it
**structurally from subtraction** (`Meta/Nat/SubMod213.lean`, 3★ + helpers, all ∅-axiom):

- `subMod fuel a b` — `a mod b` by repeated `Nat.sub` (structural `Nat.rec` on fuel);
- `subMod_eq` — `a = b·q + subMod fuel a b`; `subMod_lt` — remainder `< b` when fuel ample;
- `subMod_zero_iff_dvd` — `subMod a a b = 0 ↔ b ∣ a` (both directions): the `Nat.mod`-free
  divisibility decision.

**Verified clean**: closure walk shows `lt_wfRel=false, strongRecOn=false, Nat.mod=false,
Nat.div=false`, and `#print axioms` empty (∅-axiom).  `Nat.sub` is structural and clean, so the whole
primitive is.  (Integrity notes: a first draft leaked `propext` via `Nat.add_sub_cancel'`,
`Nat.zero_mod`-style core lemmas, and `Nat.le_of_add_le_add_left` — all replaced by the repo's clean
`NatHelper.sub_add_cancel` and a hand-proved `le_add_cancel_left`; caught by `#print axioms`.)

**Remaining (mechanical)**: rewire `leastFactorFrom`/`minFac` to branch on `subMod n n k` instead of
`n % k`, reprove `minFac_spec` via `subMod_zero_iff_dvd`, and run FTA existence on the **divisibility
witness `q`** (from `minFac n ∣ n`) instead of `n / minFac n` — which removes `Nat.div` too.  Then the
whole FTA chain is `lt_wfRel`-free: division fully rebuilt from the distinguishing's subtraction.  The
hard reusable part (the clean primitive) is done; the rewire is copy-and-swap.

### UPDATE (2026-06-24, cont. 4): FTA existence FULLY lt_wfRel-free — division generated (PURE ✓✓)

The mechanical rewire is done. `MulDescentGroundedNoDiv.mul_factorization_exists_nodiv` measures
(direct closure walk + `#print axioms`):

| | isPart_wf | strongRecOn | lt_wfRel | Nat.div | Nat.mod | axioms |
|---|---|---|---|---|---|---|
| **no-div FTA** | **true** | **false** | **false** | **false** | **false** | **none (∅-axiom)** |

So FTA existence now uses **no borrowed `Nat` well-founded machinery at all**: `minFac'` tests
divisibility by `subMod` (structural subtraction, no `Nat.mod`); the recursion is on the divisibility
**witness `q`** with `n = minFac' n * q` (no `Nat.div`); the descent is `measureInduction_grounded`
(grounded in `isPart_wf`). The only `Nat` primitives left are `succ`/`+`/`*`/`-` (all structural) and
the structural recursors.

**Division and remainder are rebuilt from the distinguishing's subtraction; the descent from the
distinguishing's own well-foundedness.** This is the descent leg's first *complete* deep-discipline
clearance: the multiplicative existence theorem (FTA, the branch's namesake) generated end-to-end
without `Nat.div`/`Nat.mod`/`Nat.strongRecOn`/`Nat.lt_wfRel`. (`minFac'`/`leastFactorFrom'`/spec/prime
all rebuilt on `subMod`; `Nat.mul_assoc` — which leaks propext in core — swapped for the repo's clean
`NatHelper.mul_assoc`; caught by `#print axioms`.)

Remaining (deeper): `Nat.sub`/`succ`/`*` themselves are kernel inductive recursion (Tree/Nat W-type,
`the_trusted_base.md`) — the irreducible CIC floor, not borrowed *WF*. That is a different frontier
(the W-type itself), not the descent-grounding one, which is now closed for FTA existence.

### UPDATE (2026-06-24, cont. 5): Euclid's infinitude of primes — second grounded discipline (PURE ✓)

To show the `Nat.div`/`Nat.mod`-free grounding generalises beyond FTA existence:
`EuclidPrimesGrounded.infinitude_of_primes` — for any list `L` of primes there is a prime not in `L`
(`minFac' (prodL L + 1)`).  Measures: `strongRecOn=false, lt_wfRel=false, Nat.div=false,
Nat.mod=false`, `#print axioms` empty (∅-axiom).  (No `isPart_wf` — Euclid is a *one-shot*
construction via `minFac'`, no descent, so no borrowed WF at all.)  Reuses the clean `minFac'`; the
`Nat.dvd_sub`/`Nat.dvd_trans`/`Nat.add_sub_cancel`/`Nat.le_of_add_le_add_left`/`Nat.mul_assoc` propext
leaks were all replaced by clean inline witnesses + `SubMod213.le_add_cancel_left` (made public) +
`NatHelper.mul_assoc`.  Two classical multiplicative theorems (FTA existence, Euclid) now generated
without borrowed `Nat` division or well-foundedness.

### UPDATE (2026-06-24, cont. 6): structural quotient — division complete, `vp` prerequisite (PURE ✓)

Toward grounding FTA *uniqueness* (which needs a structural `vp`/valuation that peels `n ↦ n/p`).
Completed the structural division in `SubMod213` (∅-axiom): `subDiv` (quotient by counting the
repeated subtractions, mirroring `subMod`), `subDivMod_eq` (`b·subDiv + subMod = a`, the division
algorithm by `Nat.rec`), and `subDiv_lt_of_dvd` (the quotient strictly descends when `2 ≤ b ∣ a`, the
descent `vp` needs). So both quotient and remainder are now structural / `Nat.div`-`Nat.mod`-free.
Remaining for uniqueness: a structural `vp` (via `measureInduction_grounded` + `subDiv`), its
multiplicativity, and `vp q (prodL l) = countOcc q l` — the larger next step.

### UPDATE (2026-06-24, cont. 7): FTA uniqueness is a multi-session wall — scoped precisely

Honest scoping (not a quick win).  FTA *uniqueness* needs **Euclid's lemma** (`p` prime, `p ∣ a·b →
p∣a ∨ p∣b`) — both the `vp`-multiplicativity route and the multiset-cancellation route require it, and
Euclid's lemma needs gcd/Bézout (or unique factorisation, circular).  The repo *has* `prime_dvd_mul`
(`PrimeValuation:66`), but it routes through `Gcd213.gcd213`, which uses **`Nat.mod`** (verified:
`gcd213_dvd_left` has `lt_wfRel=true, Nat.mod=true`).  So grounding uniqueness means **regrounding the
whole `Gcd213` chain (~600 lines) onto `subMod`**: structural gcd → its dvd/greatest properties →
coprime/Bézout → `prime_dvd_mul` → `vp_mul` (or direct cancellation) → uniqueness.  This is a genuine
multi-session sub-project, not a turn.

**First brick deposited** (`Meta/Nat/SubGcd213.lean`, ∅-axiom): `gcdSub` (Euclidean algorithm with the
remainder from `subMod`, no `Nat.mod`) + base/recursion lemmas (`gcdSub_zero_right`, `gcdSub_succ`).
The remaining bricks: the `subMod` analogue of `Nat.mod_eq_sub_mod` (the fuel-aware mod-subtraction
step), `gcdSub_dvd_both`/`gcdSub_greatest` (mirror `Gcd213.gcdFuel_dvd_both`, ~70 lines), then the
coprime/Bézout/Euclid's-lemma stack.  Whoever continues starts from `gcdSub`.

**State of the grounded multiplicative discipline**: FTA *existence* and Euclid's infinitude are
*fully* grounded (no `Nat.div`/`Nat.mod`/`strongRecOn`/`lt_wfRel`, ∅-axiom); structural division
(quotient+remainder) is complete; FTA *uniqueness* awaits the gcd-chain regrounding above.

### UPDATE (2026-06-24, cont. 8): grounded gcd — divisibility + prime-coprimality (PURE ✓)

Bricks 2 + 3 of the `SubGcd213` chain land (∅-axiom; closure-walked: `lt_wfRel`/`strongRecOn`/`Nat.div`/`Nat.mod`/`propext`/`Acc.rec`/`WellFounded.fix` all absent — 233-const closure, zero forbidden hits).

- **Brick 2** — `g_dvd_of_dvd_subMod` (`g ∣ a → g ∣ (b mod a) → g ∣ b`, immediate from `subMod_eq`, much shorter than the `Nat.mod` analogue `Gcd213.g_dvd_b_via_mod`) and `gcdSub_dvd_both` (`gcdSub n a b ∣ a ∧ ∣ b`, fuel `n ≥ b` the Euclidean monovariant, inductive step `(a, b'+1) → (b'+1, a mod (b'+1))` lifted via brick 2). The `subMod_eq` identity `b = a·q + (b mod a)` trivialises the divisibility lift that the mod-recursion version has to grind out.
- **Brick 3** — `gcdW a b := gcdSub (a+b) a b` (fuel discharged, `b ≤ a+b` ample), `gcdW_dvd_left`/`gcdW_dvd_right`, and `gcd_eq_one_of_prime_not_dvd`: for `p` with only divisors `1, p` and `p ∤ a`, `gcd(p,a)=1`. This is the half of Euclid's lemma that needs **no Bézout** — `gcdW p a ∣ p` so it is `1` or `p`, and `p` is excluded because `gcdW p a ∣ a` would force `p ∣ a`.

**Remaining wall (unchanged)**: the *other* half — `gcd(p,a)=1 → p ∣ a·b → p ∣ b` — is exactly where **Bézout** (a `g = a·x − b·y` witness, structural) is unavoidable, and that is the hard regrounding still ahead before `prime_dvd_mul` → `vp_mul` → FTA uniqueness. Coprimality is now a clean PURE primitive to build Bézout against; the descent of the extended-Euclid coefficients is the next genuine piece of work.

### UPDATE (2026-06-24, cont. 9): the Bézout wall is CLEARED — Euclid's lemma grounded (PURE ✓)

The wall scoped in cont.7 ("FTA uniqueness is a multi-session wall") is down.  Two deposits, both
∅-axiom, both closure-walked clean (no `Nat.lt_wfRel`/`strongRecOn`/`Nat.div`/`Nat.mod`/`propext`/
`Acc.rec`/`WellFounded.fix`/`Gcd213.gcd213`):

- **`Meta/Nat/SubBezout213.lean`** — *structural Bézout*, the piece I'd called "the hard remaining
  work".  `egcd` is the extended Euclidean recursion threading a coefficient quadruple `(g,x,y,s)`
  with `s : Bool` a **sign flag**, so the Bézout identity stays in `Nat` — **no `Int`/signed
  integers**:
    - `s = true  → a·x = b·y + g`
    - `s = false → b·y = a·x + g`
  The Euclidean step `a = b·q + r` (`subDivMod_eq`, *no Nat-subtraction in the algebra*) forces the
  uniform update `xₙ = y'`, `yₙ = x' + q·y'`, `s` flips — proved by distribution + IH (`egcd_bezout`,
  `Nat.rec` on fuel).  `egcd_fst` ties the `g`-component to `gcdSub`, and `bezout_one_of_coprime`
  reads off `gcd(a,b)=1 → ∃ x y, a·x = b·y+1 ∨ b·y = a·x+1`.
- **`Lib/Math/NumberTheory/EuclidLemmaGrounded.lean`** — *Euclid's lemma*, `prime_dvd_mul`:
  `p` prime, `p ∣ a·b → p∣a ∨ p∣b`.  Regrounds the repo's `PrimeValuation.prime_dvd_mul` (which goes
  through `Gcd213.gcd213` = `Nat.mod`) onto the `subMod` Bézout.  Closure 288, **zero** bad hits.
  Key craft: case on `gcd(p,a) ∈ {1,p}` (from primality + `gcdW_dvd_left`) **instead of**
  `by_cases p ∣ a` — the latter's `Decidable (p∣a)` instance computes via `Nat.mod` and would
  re-import the dirt.  Multiply the Bézout identity by `b`, fold in `p ∣ a·b`, get `p·c₁ = p·c₂ + b`,
  whence `p ∣ b` (`dvd_of_pmul_eq`, clean right-cancel + `subMod`-style `sub_add_cancel`).

**State of the grounded multiplicative discipline (revised)**: FTA *existence*, Euclid's *infinitude*,
structural *division* (quotient+remainder), structural *gcd* + prime-coprimality, structural *Bézout*,
and *Euclid's lemma* — all ∅-axiom, none borrowing `Nat.div`/`Nat.mod`/`strongRecOn`/`lt_wfRel`.  FTA
*uniqueness* now reduces to `vp`-multiplicativity (`vp_mul`) on top of grounded `prime_dvd_mul`, which
is mechanical (the conceptual content was Euclid's lemma).  The descent leg's hardest number-theory
wall is behind us.
