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

## Phase E — Thue–Morse: the genuinely-dense witness (∅-axiom, `Cauchy/ThueMorseAperiodic.lean` 21 PURE)

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
