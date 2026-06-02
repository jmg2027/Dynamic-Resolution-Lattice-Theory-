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
    *including dense ones with no long runs*.
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

## Honest scope

  - The *formalized witness* (`isPow2`) happens also to have long runs (so the sparse route would
    catch it too); the **theorem** `aperiodic_not_autoRec` is the general result, and applies to
    genuinely dense witnesses — Thue–Morse, Sturmian — whose only missing input is their own
    aperiodicity (the repo has Thue–Morse with finite-period aperiodicity witnesses only, not the
    full overlap-free aperiodicity; supplying it would give a dense instance directly).
  - This closes the *autonomous* (time-invariant) machine class on the dense side.  It does
    **not** touch the time-varying P-recursive class (that is `HomogRec`/zero-runs) nor π (π's CF
    non-holonomicity remains classically open; even π's aperiodicity-as-a-CF is not the relevant
    statement — π's *partial quotients* are unbounded, a different object).

## The ∅-axiom non-holonomicity map, now

| machine class | escape criterion | witnesses |
|---|---|---|
| time-varying homogeneous P-recursive (`HomogRec`) | `zero_run_not_homogRec` (long zero-runs) | `(n!)ⁿ`, `χ`, Champernowne |
| time-invariant autonomous, *sparse* (`AutoRec`) | `two_continuations_not_autoRec` / `distinct_next_equal_window_not_autoRec` | `χ`, Champernowne |
| time-invariant autonomous, *dense* (`AutoRec`) | `aperiodic_not_autoRec` (Morse–Hedlund) | any bounded aperiodic — Thue–Morse, Sturmian, `isPow2` |

`χ` escapes the union `FiniteRecurrence = HomogRec ∨ AutoRec` (`chi_not_finiteRecurrence`).  The
three criteria together cover both machine classes across both densities — the full elementary
∅-axiom reach.  π stays the open core (no constructive shadow of the FGS analytic obstruction).
