# G185 — the Morse–Hedlund dense axis: aperiodic ⟹ no autonomous finite-state machine

**Tier 1 (volatile).**  The genuinely-heavy ∅-axiom target that remained after `G184` (where the
Garrabrant–Pak mod-2 axis turned out subsumed for its witnesses).  Now closed: the **dense**
non-holonomicity axis — sequences with *no long runs* (Thue–Morse, Sturmian) escaping every
autonomous finite-state machine, via the Morse–Hedlund argument.

## What was built (∅-axiom, `Cauchy/MorseHedlund.lean` 14 PURE + witness)

  - **Phase A — binary window encoding** (reusable): `binEnc k f = Σ_{t<k} b2n(f t)·2^t`,
    `binEnc_lt` (`< 2^k`), `binEnc_inj` (equal codes ⟹ equal windows).  Built from pure
    mod/div + binary bit recovery — no general binary-representation-uniqueness library.
  - **Phase B — `kStepDet_periodic`** (the Morse–Hedlund bounded direction): a `Bool`-sequence
    whose next value is determined by its length-`k` window (`kStepDet`) is **eventually
    periodic** — finitely many windows, deterministic shift, `ForwardPeriodicity.pigeonhole_collision`,
    forward propagation (`window_propagate`).
  - **Phase C — `aperiodic_not_autoRec`**: `AutoRec` over the `{0,1}`-embedding ⟹ `kStepDet` ⟹
    `EvPeriodic`; contrapositive (clean modus tollens, no `∃`-from-`¬∀`) — **any
    non-eventually-periodic `Bool`-sequence escapes every autonomous finite-state machine**,
    *including dense ones with no long runs*.  Now closed to an **iff**
    (`bool_autoRec_iff_evPeriodic`, 16 PURE): the converse `bool_evPeriodic_autoRec` builds the
    machine outright — period `p` + threshold `N` ⟹ window length `N+p`, single-slot rule
    `F w = w N` (since `a(n+N+p)=a(n+N)`).  Escaping `AutoRec` ⟺ aperiodic, no slack.
  - **Phase D — `isPow2_morse_not_autoRec`**: a concrete bounded aperiodic witness (the
    powers-of-two indicator is not eventually periodic — a gap-length-`p` window would force
    `false` forever — hence `¬ AutoRec`).  `ZeroRunNonHolonomicWitness` now 24 PURE.

## Why this is the dense companion

The sparse route (`zero_run_not_homogRec`, `χ`) needs *arbitrarily long zero-runs*; the
two-continuation route needs an explicit repeated window.  **Morse–Hedlund needs neither**: mere
aperiodicity (for a bounded sequence) already forces, for every memory `k`, two equal windows
with different continuations — so the autonomous-machine class is escaped *by any bounded
aperiodic sequence whatever*.  This is exactly the class the sparse route misses: dense,
bounded-run-length, aperiodic (Thue–Morse run-length ≤ 2, Sturmian complexity `n+1`).

## Phase E — Thue–Morse: the genuinely-dense witness (∅-axiom, `Cauchy/ThueMorseAperiodic.lean` 42 PURE)

The dense axis is now non-vacuous on the canonical example.  **Thue–Morse** (`tm`, run-length
`≤ 2`, no long runs) is defined by its self-similar recurrence via *fuel-structural* recursion
(well-founded recursion leaks `propext`), with a fuel-irrelevance lemma (`tmF_canon`, strong
induction on a fuel bound) pinning the canonical fuel `= n`.  The recurrence reads off as
`tm_even : tm(2n)=tm(n)`, `tm_odd : tm(2n+1)=¬tm(n)`, hence `tm_pair_differ : tm(2n+1)≠tm(2n)`
(never constant).  **Aperiodicity** (`tm_not_evPeriodic`) is the self-similar **period-descent**:

  - `even_descent` — a period `2q` halves to period `q` through `tm(2m)=tm(m)`;
  - `odd_descent` — a period `2r+1` drops to the even period `2r` (the auxiliary `tm(m+r)=¬tm(m)`
    via `tm_odd`+`tm_even`, applied twice cancels the negation);
  - strong induction on the period: even halves, odd drops-by-one to even, and period `1`
    contradicts `tm_pair_differ`.

`tm_morse_not_autoRec := aperiodic_not_autoRec tm tm_not_evPeriodic` — a concrete *dense*
inhabitant of the Morse–Hedlund escape, not the long-run `isPow2`.

### Run-length `≤ 2` — `tm_run_le_two`

The density is now a theorem, not a citation: `tm_run_le_two` proves Thue–Morse has **no three
consecutive equal values** (in any length-`3` window an adjacent differing pair already sits — at
an even start `(tm k, ¬tm k)`, at an odd start `(tm(k+1), ¬tm(k+1))`).  This is exactly what
makes Thue–Morse the *genuinely-dense* witness: the sparse `zero_run_not_homogRec` route needs
arbitrarily long constant runs, which `tm_run_le_two` forbids — so Thue–Morse escapes the
finite-state class **only** through the dense Morse–Hedlund route, not the sparse one.

**Location, sharply.**  `χ` escapes *both* machine classes (`chi_not_finiteRecurrence`) on the
back of its long zero-runs.  Thue–Morse escapes `AutoRec` only; whether it escapes `HomogRec`
(P-recursive) is **not** ∅-axiom-closable here, and not by accident — `tm_run_le_two` removes the
very zero-runs the cheap `HomogRec` certificate needs, so the only route to `¬ HomogRec` for a
no-long-run sequence is the deep *automatic ∧ aperiodic ⟹ non-holonomic* theorem
(Cobham/Christol), which has no constructive shadow.  Thue–Morse's P-recursive escape thus shares
π's open status: density is not a *strengthening* of the sparse witness but the regime where the
cheap certificate is structurally unavailable.

### The automatic structure — `tm_eq_popParity`

The companion fact: Thue–Morse *lacks* term-window memory (`AutoRec`) but *has* digit memory.
`tm_eq_popParity : tm n = decide (s2 n % 2 = 1)` proves `tm n` = parity of the binary digit-sum
`popcount(n)` — a two-state base-`2` automaton.  `s2` (fuel-structural `popcount`, `s2_even`,
`s2_odd`, `succ_parity` parity-flip).  This pins the exact divergence of the two finite-state
notions: finite memory *in the digits of the index* (automatic — Thue–Morse has it) vs *in the
previous terms* (window-recurrence — Thue–Morse lacks it).  Classically: automatic ∧ aperiodic
⟹ non-holonomic (Cobham/Christol); here both hypotheses are ∅-axiom, the term-window escape is
the elementary shadow.

### Dyadic self-similarity / complement fold — `tm_shift_pow`

`tm(2^k + n) = ¬tm(n)` for `n < 2^k` (`tm_shift_pow`): on `[2^k, 2^{k+1})` Thue–Morse is the
bitwise complement of `[0, 2^k)`.  The disjoint high bit adds one to the digit-sum and flips the
parity — `s2_add_pow : s2(2^k+n) = s2 n + 1` (induction on `k` with the parity split of `n`), then
`succ_parity`.  This is the self-similar doubling fold that *is* the 2-automaton: the next dyadic
block is the current one negated.

### Sparse and dense witnesses are one automaton — `isPow2_eq_s2_one`

`χ`/`isPow2` and `tm` are the *same* 2-automatic digit-sum `s2 = popcount` with different output
maps: `isPow2 n = decide (s2 n = 1)` (`isPow2_eq_s2_one`, via `s2_eq_one_iff : s2 n = 1 ↔
∃ j, 2^j = n` bridged to the existing `pow2aux` characterization `isPow2_true_iff`) and
`tm n = decide (s2 n % 2 = 1)` (`tm_eq_popParity`).  Supporting Nat number-theory:
`s2_two_pow : s2(2^j)=1`, `s2_eq_zero_imp : s2 n = 0 → n = 0`, `s2_eq_one_imp : s2 n = 1 →
∃ j, 2^j = n`.  (propext landmine: `Nat.succ_ne_zero` is propext-dirty — replaced by
`Nat.noConfusion`.)  The conceptual payoff: their differing holonomic status (sparse `χ` escapes
both machine classes, dense `tm` only the autonomous one) lives in the **output map**, not the
automaticity — the automaton is shared.

### Realised as an actual continued fraction — `tmCF`

The dense axis is no longer abstract.  `tmCF n = b2n(tm n) + 1` is the `{1,2}`-valued Thue–Morse
partial-quotient sequence — a valid CF (`tmCF_ge_one : 1 ≤ aₙ`, `tmCF_mem : aₙ ∈ {1,2}`), bounded,
dense (`tm_run_le_two`), aperiodic (`tm_not_evPeriodic`), generated by no autonomous machine
(`tmCF_not_autoRec`).  The bridge is `autoRec_shift` (a constant shift `a ↦ a+c` preserves
`AutoRec`, compose the window-rule with the shift), so `tm_morse_not_autoRec` transports to the
shifted `{1,2}` sequence.  This is the marathon's subject — a continued fraction on the dense
non-holonomic axis — made concrete (autonomous escape; `HomogRec`/π-core stays open).

### The digit counter escapes the ring — `s2_not_eventually_monotone`

The companion at the *other* end: the digit counter `s2 = popcount` (unbounded, `s2_unbounded` via
`s2_ones : s2(ones k)=k`) returns to its minimum `1` at every power of two (`s2_pw2 : s2(2^k)=1`),
so it is **not eventually monotone** (`s2_not_eventually_monotone`; subtraction-free `ones`/`pw2`
families, `ones_ge`/`pw2_gt`).  A finite-Δ-depth integer sequence is eventually a polynomial, hence
eventually monotone — so `popcount` has no finite difference-depth: it sits *outside* the
`FiniteDepthAlgebra`/`NewtonGregory` generating ring while its bounded `{0,1}` readout `tm` is the
dense non-holonomic witness.  One structure, two ends: the readout escapes the *machine*, the
counter escapes the *ring*.

**Lean status: CLOSED.**  `s2_not_eventually_monotone` (213-native) + the bridge now give the full
theorem `ThueMorseRingEscape.s2Z_not_polyDepthZ : ¬ ∃ d, polyDepthZ d s2Z` (∅-axiom).  Built in
three files:

  - **`Meta/Int213/Order.lean`** (33 PURE) — the `Int` ordering layer the repo lacked (Lean-core
    `Int.le_trans`/`lt_trichotomy` carry `propext`): `le_trans`/`lt_trans`/`lt_of_le_of_lt`,
    `lt_irrefl` (contradiction engine), `add_le_add_*`, sign trichotomy `pos_zero_or_neg`,
    negation-reverses-order, the `ofNat` embedding — all from the inductive `Int.NonNeg` +
    `ring_intZ`.
  - **`Cauchy/PolyDepthMonotone.lean`** (11 PURE) — `polyDepthZ_evMono`: **every finite-Δ-depth
    integer sequence is eventually monotone** (non-decreasing or non-increasing).  LPO-free via
    the constant-top-difference sign trichotomy: `c>0` ⟹ eventual strict increase
    (`posTop_evStrictMonoZ`, the faithful-`Int` port of `positive_floor`'s descent, using the
    eventual-positivity telescope `evStrictMonoZ_eventually_pos`), `c<0` ⟹ negation
    (`liftKZ_negS_apply`, pointwise to avoid `funext`'s `Quot.sound`), `c=0` ⟹ genuine depth-drop
    (faithful `Int` difference, no `ℕ` truncation — exactly the branch the `ℕ` version could not
    close).
  - **`Cauchy/ThueMorseRingEscape.lean`** (4 PURE) — `s2Z_not_polyDepthZ`: `MonoFromZ` contradicts
    `s2_not_eventually_monotone`; `AntiFromZ` ⟹ bounded ⟹ contradicts `s2_unbounded` (via
    `s2 (ones k) = k`).

The earlier worry — that the vanishing-top-difference branch was the obstruction — was right about
`ℕ` (truncated `diff` only gives non-increasing) and is dissolved over `Int`: faithful `diffZ` makes
`liftKZ(e+1)s ≡ 0` give `liftKZ e s` *genuinely constant* ⟹ `polyDepthZ e s`, the clean recursion.

## Honest scope

  - The earlier *formalized witness* (`isPow2`) happens also to have long runs (so the sparse
    route would catch it too); **Thue–Morse** (`ThueMorseAperiodic`, run-length `≤ 2`) closes the
    genuinely-dense gap — `aperiodic_not_autoRec` now has a dense inhabitant proven ∅-axiom.
    Sturmian (complexity `n+1`) remains the next dense instance, awaiting its own aperiodicity.
  - This closes the *autonomous* (time-invariant) machine class on the dense side.  It does
    **not** touch the time-varying P-recursive class (that is `HomogRec`/zero-runs) nor π (π's CF
    non-holonomicity remains classically open; even π's aperiodicity-as-a-CF is not the relevant
    statement — π's *partial quotients* are unbounded, a different object).

## The ∅-axiom non-holonomicity map, now

| machine class | escape criterion | witnesses |
|---|---|---|
| time-varying homogeneous P-recursive (`HomogRec`) | `zero_run_not_homogRec` (long zero-runs) | `(n!)ⁿ`, `χ`, Champernowne |
| time-invariant autonomous, *sparse* (`AutoRec`) | `two_continuations_not_autoRec` / `distinct_next_equal_window_not_autoRec` | `χ`, Champernowne |
| time-invariant autonomous, *dense* (`AutoRec`) | `aperiodic_not_autoRec` (Morse–Hedlund) | any bounded aperiodic — **Thue–Morse** (formalised, `tm_morse_not_autoRec`), `isPow2`; Sturmian next |

`χ` escapes the union `FiniteRecurrence = HomogRec ∨ AutoRec` (`chi_not_finiteRecurrence`).  The
three criteria together cover both machine classes across both densities — the full elementary
∅-axiom reach.  π stays the open core (no constructive shadow of the FGS analytic obstruction).

## The autonomous axis, closed to an iff

With `bool_autoRec_iff_evPeriodic` the `AutoRec` column is no longer a one-way escape: over the
`{0,1}`-embedding, `AutoRec ⟺ EvPeriodic` *exactly*.  So the entire content of "escapes the
autonomous machine" **is** "aperiodic" — the three escape criteria above are the only ways to
*exhibit* aperiodicity ∅-axiom (long zero-runs, a repeated window with two continuations, or the
Morse–Hedlund pigeonhole), but the class boundary itself is now a clean equivalence.  Dense
witnesses are not a stronger escape; they are the aperiodic sequences for which the first two
*cheap* exhibition routes are unavailable, leaving only Morse–Hedlund.

## Verdict — dense `HomogRec` concluded as one classical theorem

The dense `HomogRec` question is now *concluded* (located, not forced).  The bounded `{0,1}` picture:

  - `AutoRec ⟺ EvPeriodic` — both ∅-axiom (`bool_autoRec_iff_evPeriodic`).
  - `EvPeriodic ⟹ HomogRec` — **now ∅-axiom** (`HomogRecPeriodic.evPeriodic_homogRec`, 1 PURE):
    order `k = p`, prefix `< N` killed by an `if`-guarded `lead`/`R` (the repo's `HomogRec` admits
    arbitrary `lead`/`R`, so no polynomial-product is needed).
  - `HomogRec a ∧ bounded a ⟹ EvPeriodic a` — the **bounded-P-recursive theorem**; its
    contrapositive *is* the dense escape `aperiodic ∧ bounded ⟹ ¬ HomogRec`.

So the entire residual content of the conjecture is exactly this one classical theorem, and it is
**not** ∅-axiom-elementary for a precise reason: `HomogRec` is *time-varying*, so the state vector
evolves by an `n`-dependent transition `M(n)`; a bounded integer sequence's finitely-many states
recur by pigeonhole but at *different* transitions, so equal states at `n₁ ≠ n₂` yield no
periodicity — exactly the step the time-invariant `AutoRec` iff could take and this cannot.  The
only elementary handle on `HomogRec` is the `zero_run` cascade, needing run-length `→ ∞`; a
bounded-run-length witness (`tm_run_le_two`, run `≤ 2`) defeats `HomogRec` only up to order `2` (its
`00` windows), never all orders.

**Conclusion.**  Dense `HomogRec` escape ≡ the bounded-P-recursive theorem.  Elementary half
∅-axiom-closed; hard half identified and outside elementary reach — it is π's neighbour, not a gap
in the elementary program.  (Falsification handle, were it ever to move: an ∅-axiom certificate `C`
obstructing a polynomial-coefficient recurrence without a constant-window cascade — a genuinely new
mechanism; absent it, Thue–Morse's `¬ HomogRec` sits at exactly π's status.)

## Verdict — π concluded as the open core

π's CF non-holonomicity is **classically open** and provably **not ∅-axiom-closable**, now a settled
boundary statement: the FGS analytic obstruction is irreducibly analytic (Fuchs–Frobenius + Stokes
summability + Tauberian transfer, no constructive shadow) and bottoms at the unproven Gauss–Kuzmin
normality of π — even "π's partial quotients unbounded" is itself open.  The marathon's deliverable
is the **map**: the escape is ∅-axiom-certified for constructed witnesses on every elementary axis
(growth `(n!)ⁿ`, sparse `χ`, dense Thue–Morse with automatic structure + ring-escape + the concrete
CF `tmCF`), and the two cores it cannot reach are pinned to named classical theorems.  π is reached
by no elementary pointing; the witnesses converge to the same boundary from inside — the residue's
own signature (`spineL_escapes`, `object1_not_surjective`).  See
`theory/essays/non_holonomicity_as_finite_state_escape.md` "The verdict on the two cores".
