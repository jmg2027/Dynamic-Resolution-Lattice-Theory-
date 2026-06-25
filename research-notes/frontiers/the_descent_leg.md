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

## PROMOTED — multiplicative chain closed (2026-06-24)

The multiplicative-discipline grounding marathon that ran in this note (FTA existence + uniqueness, and
every gear between — structural division, gcd, Bézout, Euclid's lemma, the `p`-adic valuation, its
multiplicativity) is **closed** and promoted to a permanent chapter:

> **`theory/math/numbertheory/grounded_fundamental_theorem.md`**

The Fundamental Theorem of Arithmetic, both halves, is reconstructed with no theorem in the chain
depending on `Nat.div`/`Nat.mod`/`Nat.strongRecOn`/`Nat.lt_wfRel` — verified by transitive
kernel-closure walk (`factorization_unique`: 485-constant closure, zero forbidden hits).  The Lean
source of truth is `Meta/Nat/{SubMod213,SubGcd213,SubBezout213,VpSub213}` +
`Lib/Math/NumberTheory/{EuclidLemmaGrounded,VpMulGrounded,FTAUniquenessGrounded,
MulDescentGroundedNoDiv,EuclidPrimesGrounded}`.

### UPDATE (2026-06-24, cont. 12): Leg 1 first brick — ℕ as a reading of the Raw spine (PURE ✓)

`Theory/Raw/RawNat.lean` (∅-axiom): the naturals object **generated** on `Raw`'s own
`slash`-successor spine, not borrowed.

- carrier `RawNat = { r : Raw // ∃ n, rawTower n = r }` — the `slash`-successor thread;
- `succ = slashOrSelf Raw.a` (point once more with `a`) — the *same* `slash` `rawTower` iterates, so a
  step IS one more distinguishing;
- **Peano** proved from `Raw`'s combinatorics: `succ_inj`, `succ_ne_zero`, `rec` (induction) — derived
  from depth-injectivity of the spine (`rawTower_depth`), not from `Nat`'s Peano;
- **arithmetic generated**: `add` iterates `succ` (`depth y` times), `mul (x y) = mulNat x (depth y)`
  iterates `add`; the `depth` Lens is a **semiring homomorphism** onto `ℕ` (`toNat_add`, `toNat_mul`),
  so `+`/`·` *read as* `Nat`'s.
- **the discipline closed**: `RawNat` is an **ordered commutative semiring** — `add_{comm,assoc}`,
  `zero_add`, `add_zero`, `mul_{comm,assoc}`, `one_mul`, `mul_one`, `zero_mul`, `mul_zero`,
  `left_distrib`, `right_distrib`, plus the order `le x y := ∃ z, add x z = y` (additive reachability,
  proved `↔ toNat x ≤ toNat y` — `le_refl/trans/antisymm/total`, `add_le_add_left`) — every law
  transported through `toNat_inj` from `ℕ`'s, the homomorphism load-bearing (no law re-proved on `Raw`).  `mul_assoc`/`right_distrib` route through `NatHelper.mul_assoc`/`add_mul`
  (core `Nat.mul_assoc`/`Nat.add_mul` leak propext); `succ_inj`/`succ_ne_zero` via
  `Nat.succ.inj`/`Nat.noConfusion`.  This is the **leg-1 step-2 demonstration**: a classical discipline
  (commutative-semiring arithmetic) realised as a reading of the distinguishing's spine, ∅-axiom.
- **PROMOTED**: the closed Leg-1 generation (carrier, Peano, ordered semiring, grounded recursion) +
  the count-spine + the rival forcing are now a permanent chapter,
  `theory/math/numbersystems/naturals_from_the_spine.md`.  The conceptual residue below stays open.

**§4 — recursion engine grounded in `isPart_wf` (the borrowed-WF caveat retired).**  The Peano
induction is re-derived *intrinsically*: `strongRec_isPart` recurses on `Raw`'s `slash`-peel relation
`IsPart`, well-founded by the Theory-ring theorem `isPart_wf` (0 `Nat` constants in its cone), and
`rec_grounded` discharges the per-step descent with `tower_ascent_isPart` (each rung is a part of the
next).  Closure probe of `rec_grounded` (∅-axiom): `isPart_wf` **present**, `Nat.lt_wfRel` and
`Nat.strongRecOn` **absent** — the natural-number recursion *descent* runs on the distinguishing's own
peel, not `Nat`'s order.  (Residual `Nat.rec`/`Acc.rec` are structural recursors: the `∃ n` carrier-
index case-split and the legitimate `Acc` well-founded mechanism — not borrowed `Nat` well-foundedness.)

**§5 — the carrier defined *without* `Nat` (the carrier-borrow retired).**  `IsRawNat : Raw → Prop` is
the inductive closure of the seed `b` under the `slash`-successor `rawSucc` (`base`, `step`) — the
naturals with **no `Nat` in the definition**.  Its own recursor is natural-number induction:
`rawNat_induction` (∅-axiom) has a **125-constant closure containing only `IsRawNat`/`IsRawNat.rec` —
no `Nat`, `Nat.rec`, `Nat.lt_wfRel`, `Acc.rec`, `WellFounded.fix`, or `isPart_wf` at all**.  Structural
induction over "closure of the first distinguishing under point-once-more-with-`a`", borrowing nothing.
And `isRawNat_iff` proves this `Nat`-free carrier coincides exactly with the `∃ n` tower carrier, so
`RawNat` *could* be carried by `IsRawNat` with the `∃ n` form demoted to its tower reading.

**Honest scope** (what Leg 1 now is): *generated / borrowing nothing but the kernel `inductive`* — the
carrier (`IsRawNat`), the natural-number induction (`rawNat_induction`, `IsRawNat.rec`), the zero +
`slash`-successor, the Peano laws, and the commutative-semiring discipline.  *Still borrowed*: the
kernel's `inductive` mechanism itself (to have `Raw`/`IsRawNat` — the distinguishing *is* an inductive
act, conceded in Attack 1), and `Nat` as the `depth` **readout** type (a Lens reading *out*, the
legitimate direction).  **Update**: the carrier is now *actually* flipped — `RawNat = { r : Raw // IsRawNat r }`, a
`Nat`-free type; `succ = ⟨rawSucc x.val, x.2.step⟩`, `toNat_succ` is `Nat`-free via `rawSucc_depth`
(the `slash` fires as `a/r`, `a ≠ r`, adding one level), and `add`'s carrier witness is
`isRawNat_addRaw`.  The `∃ n` tower index survives only as a *derived reading* (`tower_of_isRawNat`),
used inside `ofNat_toNat`/`toNat_add`/`zero_or_succ` to bridge to `depth` facts.

**Count-spine reading done** (`Lib/.../UniverseChain/RawNatCensus.lean`, ∅-axiom): the `RawRecurrence`
population `2,3,5,12,68,…` (`rawCount n = 2 + C(rawCount (n−1), 2)`, Mingu's recurrence — canonical
`Raw`s of depth ≤ n) is tied to the spine as `census x = rawCount (toNat x)`, with the recurrence
re-indexed by `RawNat`'s **own** successor (`census_succ : census (succ x) = 2 + choose2 (census x)`).
`two_readings` exhibits the *same* spine read two ways — `depth`/`toNat` linear (`…,2,…`) vs `census`
population (`…,5,…`) at the depth-2 rung — the "second, wider reading of the same object".  (It lives in
`Lib`, not `Theory`, since `rawCount` sits above the `Theory` ring.)

**Leg 3 — forcing bracket extended (both arity sides + distinctness now closed).**
`Lib/.../UniverseChain/RivalArity.lean` already excluded the unary (negation-first) rival as too weak
(linear `unaryCount` vs super-linear `rawCount`) and the non-distinct binary rival as over-generating
(`relCount > rawCount` = the self-combinations distinctness removes).  Added the **higher-arity** corner
(§3) and a **both-sides bracket capstone** (§4), ∅-axiom:

- `ternCount_sterile` — a *ternary-distinct* rival is **sterile on the two-atom seed**: the first
  distinguishing yields exactly `2`, and three distinct args cannot be drawn from two (`choose3 2 = 0`),
  so `ternCount n = 2` forever; `ternary_sterile_below` puts it strictly below 213.
- `arity_distinctness_forcing` — the squeeze: arity `1` too weak, arity `3` sterile on the seed, arity
  `2` without distinctness over-generates, arity `2` *with* distinctness = 213's branching recurrence.

So the **(arity, distinctness) design space is closed**: the binary-distinct distinguishing is forced
along both dimensions.

**Relation-first corner addressed** (§5, ∅-axiom): `relation_outputs_le_two` — a binary *relation*
`R : α → α → Bool` has codomain `Bool`, not the carrier, so it takes ≤ 2 values (`Bool` pigeonhole:
among any three applications two agree) and **produces no carrier element**.  A relation qua
`Bool`-codomain is non-generative — it cannot supply the unbounded fresh inhabitants the `2,3,5,12,…`
recurrence consumes (`slash`'s codomain is the carrier, image unbounded).  The distinguishing's
relational face *is* `Object1 r = (·=r)`, the same act read `Bool`-valued; to *generate*, a relation
must be functionalised to a carrier-valued operation, collapsing to operation-first (then forced to
arity-2-distinct).  Honest framing: not "no relation could matter", but "a relation generates nothing
the operation does not, and collapses to it when made generative".

**Honest residue** (Leg 3 still not *fully* closed): the formalized rival classes — unary, ternary,
non-distinct binary, relation-first — are all excluded, but this is not a proof that *no* conceivable
primitive (a differently-seeded or genuinely exotic one) could generate equal richness.  That residue
stays the open middle of `the_one_act.md` ("suffices by breadth, not proven unique", per the
failure-mode row "Sufficiency read as uniqueness").

### What remains open here (the conceptual frontier, unchanged)

This note stays as the record of the *still-open* descent-leg frontier — the part neither the closed
multiplicative chain nor the Leg-1 first brick settles:

- **Leg 1 — generate ℕ from `Raw`.** The grounded chain still recurses on the kernel's *structural*
  `Nat` (`Nat.rec`, fuel), not a distinguishing-generated `Nat₂₁₃` (promote the `RawRecurrence` spine
  per the leg-1 target above).  Structural-but-borrowed is weaker than generated.
- **Leg 3 — forcing, not matching.** No proof that the distinguishing primitive is non-interchangeable
  with rivals (negation-first, relation-first); that is the open middle of `frontiers/the_one_act.md`.

The `isPart_wf` engine (above) grounds the *existence* descent in the distinguishing's own descent; the
uniqueness chain grounds in structural fuel.  Both clear the "no borrowed non-structural WF" bar, but
leg 1's "generated, not borrowed" bar is stronger and stays open.

### Leg-2 discipline build-out over `Nat213` — status + remaining (2026-06-25)

The leg-2 elementary-number-theory cone is now a coherent chain, all ∅-axiom over the Raw-generated
`Nat213`: order (`lt`+`le`, both total; mono; cancellation) → divisibility (partial order, `pow`
facts) → gcd (`Gcd`: meet-semilattice, mult. law) → coprimality (`Coprime`: coprime-division law,
mult./power closure, Prime↔Coprime bridge) → well-ordering (`WellOrder`: strong induction + decidable
well-ordering) → exponentiation (`Peano.pow`/`powNat`) → `p`-adic structure (`Valuation`).

**`p`-adic valuation, both forms landed + closed** (`Valuation.lean`, all ∅-axiom):
- **A (readout):** `vp : Nat213 → Nat213 → Nat` via `powNat`; `pow_vp_dvd` (`p^(vp p n) ∣ n`);
  **exactness `le_vp_iff`** (`p^k ∣ n ⟺ k ≤ vp p n` for `p ≠ one` — `vp` is the largest dividing
  exponent). ✓ CLOSED.
- **B (native):** `padic_factorization` (`p∣n → n = p^k·m ∧ ¬p∣m`) + **`padic_factorization_unique`**
  (the `(k,m)` is unique — welds B's native exponent `k` to A's `vp`). ✓ CLOSED.

The leg-2 `Nat213` cone (order → divisibility → gcd → coprimality → well-ordering → pow → p-adic
valuation) is now a complete ∅-axiom elementary-number-theory discipline on the generated carrier,
**promoted** to `theory/math/numbertheory/number_theory_over_the_spine.md`.

**Carrier weld — CLOSED** (`Valuation.vp_eq_vpSub`): the generated valuation reads onto the native one,
`vp p n = vpSub p.toNat n.toNat` (via `dvd_toNat_iff` + `toNat_powNat`), so the discipline over
`Nat213` and the native-`Nat` corpus are one count at two resolutions welded by the depth-readout
`toNat` (essay `two_carriers_one_count`, closing #103).

**Carrier-readout weld — CLOSED across the discipline**: `ToNatReadout.toNat_faithful` (lt/le/Dvd
read exactly + `toNat` surjective onto ℕ₊), `Valuation.vp_eq_vpSub` (valuation, value-level),
`Gcd.isGcd_toNat`/`isGcd_toNat_eq` (gcd, spec- and value-level; required `SubGcd213.gcdW_greatest`,
the previously-missing greatest property). The generated discipline reads onto the native corpus
across order, divisibility, gcd, and valuation.

**Remaining is conceptual, not arithmetic** — see Legs 1 & 3 above (generation vs. borrowing, forcing
vs. matching).  Minor: an `lcm` dual join (needs an upper bound; deferred). The carrier-readout
pattern (`dvd_toNat_iff` + `toNat_*` + propext-free Nat craft) is now a reusable toolkit for
regrounding another field on `subMod`/structural descent.
