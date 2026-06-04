# The residue unit's odometer — the arithmetic face of the `+1`

The third companion in the residue triptych.  `the_residue_as_primitive.md` builds the residue's
two fixed points (µF = Raw, νF = the escape) as a coalgebra; `the_frontier_has_a_form.md` shows
the escape carries a definite, populated, symmetric form.  This essay reads the **arithmetic** face
of the same residue: the unit `+1` — the act of pointing, the glue `det P = NS − NT = 1`, the
ascent and descent step — is an **odometer** (the `+1` adding machine) on the residue's escape
space, and its dynamics (carry, injectivity, invertibility, reversibility, continuity) are the
arithmetic shadow of no-exterior.

The triggering question: *what is the `+1` of 213, dynamically?*  The shared unit `1`
(`unit_bridges_dynamics_and_readings`) is one value across the readings; here it is one **map** —
the successor — and the residue's escape space is the `2`-adic integers `ℤ₂` under it.

## Lean source

- `lean/E213/Theory/Raw/Odometer.lean` (41 PURE, 0 DIRTY) — the binary `+1` odometer on the
  bit-stream space `Nat → Bool` (the residue's escape carrier, `CoResidue`).
- `lean/E213/Theory/Raw/OdometerValue.lean` (16 PURE, 0 DIRTY) — the profinite value `bval`, the
  carry-explicit `+1 mod 2ᵏ` identity (`bval_odo`), and **freeness** of the `ℤ`-action (`odo_free`).
- `lean/E213/Lib/Math/NumberSystems/Real213/ZeckendorfCarry.lean` (7 PURE, 0 DIRTY) — the golden
  (Fibonacci-base) carry, the residue's own variable base.
- Built on `Theory/Raw/CoResidue` (`spineL`, `boolSpine`), `Mobius213/Px/FibonacciAtomicLock`
  (`fib`), `Lens/Number/SharedUnitAcrossReadings` (the shared unit).

## Narrative

The residue's escape space is the bit-stream carrier `Nat → Bool` (the `CoResidue` co-trees read
as label sequences).  Two maps act on it: the **descent** (shift `σ`, drop the low bit) and the
**ascent unit** (odometer `+1`, with carry).  The odometer's `carry f` starts at the unit
(`carry_zero`, the `+1`) and survives a step only through a `1` (`carry_succ`); the output bit is
`odo f n = (f n) xor (carry f n)`.

### The µF/νF mirror at the odometer scale

The carry **terminates iff the stream has a floor** — `carry_dies_iff_has_false`: a `0` somewhere
absorbs the carry (µF, the `+1` resolving locally, the descent bottoming out at an atom,
`Lambek.terminal_iff_atom`); the **all-`true`** stream has the carry running *forever*
(`allTrue_carry_forever`, the νF face, the `+1` escaping to a new rung,
`MuNuMirror.ascent_unbounded`).  And the all-`true` stream is exactly the seed of the canonical
escape `spineL` (`CoResidue.spineL_eq_boolSpine_true`), so the residue's canonical escape **is**
the odometer's non-terminating overflow (`spineL_seed_is_odo_overflow`): "the escape" and "the
carry that never lands" are one object (`odometer_mu_nu_mirror`).

### The successor dynamics — injective, interlocking with the descent

The `+1` is **injective** (`odo_injective`): it never sends two streams to one — the
odometer-scale `tower_no_cycle` (`MuNuMirror`), no-exterior read on the unit (the act of adding
the unit never returns).  It interlocks with the descent by the **adding-machine recursion**
(`shift_odo`): `σ (odo f) = odo (σ f)` gated by the low bit — the `+1` and the shift commute
exactly through the carry (`carry_shift`: `carry f (n+1) = f 0 && carry (σ f) n`).  Bundle:
`successor_dynamics`.

### The `ℤ`-action — the `+1` is invertible

The `+1` has an inverse: the **predecessor `−1`** (`dec`), the *borrow* machine dual to the carry
(the borrow survives through leading `0`s as the carry survives through leading `1`s).  They are
mutually inverse — `dec_odo` (`(f+1)−1 = f`), `odo_dec` (`(f−1)+1 = f`) — via the identity
`borrow (odo f) = carry f` (`borrow_odo`: subtracting `1` from `f+1` borrows exactly where adding
`1` to `f` carried).  So the residue unit is **invertible**: it generates a `ℤ`-action `(±1)` on
the escape space (`odo_unit_action`), the `+1`/`−1` the difference-Lens generators
(`integers_as_difference_lens.md`).  No-exterior (`tower_no_cycle`) is now a *group action* —
never collapsing, always undoable.

### The reversibility asymmetry — descent forgets, the ascent unit remembers

The two faces split by *reversibility* (`descent_forgets_ascent_remembers`).  The descent (shift)
is **surjective** (`shift_surjective`, every stream is a tail) but **not injective**
(`shift_not_injective`, distinct streams agreeing from position `1` collapse — the dropped low bit
is lost): a forgetful quotient, the µF face grounding *irreversibly*.  The ascent unit (odo) is
**bijective**: the νF unit escaping *reversibly*.  Reversibility is the operational µF/νF
signature — grounding forgets, the unit remembers.

### The `ℤ₂`-successor homeomorphism

Under the Cantor (product) topology the bit-stream space is `ℤ₂ = lim ℤ/2ᵏ`, and the odometer is a
**homeomorphism** (`odo_homeomorphism`): bijective (above) and **continuous**
(`odo_prefix_determined`, each output bit `n` determined by the input prefix `[0, n]` — the carry
reaches no further than it has seen).  So the residue's `+1` is the `ℤ₂`-successor as a
topological-group automorphism: the escape space carries the `2`-adic integer structure, generated
by the act of pointing.

### The profinite value — the `+1` is `+1 mod 2ᵏ` (quantitatively)

The qualitative homeomorphism is sharpened to an arithmetic identity (`Theory/Raw/OdometerValue`).
Read the first `k` bits as a number, LSB-first (`bval k f`, with `bval (k+1) f = bit (f 0) + 2·bval
k (σf)`).  Then the odometer is literally the successor on that truncation, carry-explicit:
`bval k (odo f) + carryVal k f = bval k f + 1` (`bval_odo`), where `carryVal k f` is `2ᵏ` if the
increment overflowed the `k`-bit window and `0` otherwise — i.e. `odo = (+1 mod 2ᵏ)` without
division.  So `ℤ₂ = lim ℤ/2ᵏ` is not just the topological shape of the escape space but its
arithmetic: the residue's `+1` is the `2`-adic successor on every finite truncation.  A first
consequence is **fixed-point-freeness** (`odo_no_fixpoint`): `odo f 0 = ¬(f 0) ≠ f 0`, so the `+1`
fixes no stream — the act of pointing always changes something.  Iterating `bval_odo` gives the
full **freeness** (`odo_free`): `odoʲ f = f → j = 0` — the value advances by `j` up to whole wraps
(`bval_odoIter`: `∃ c, bval k (odoʲ f) + c·2ᵏ = bval k f + j`), so a period at `k = j` forces
`c·2ʲ = j` with `j < 2ʲ`, hence `j = 0`.  The `+1`, iterated, **never returns** — the full
no-exterior / `tower_no_cycle` at the odometer scale (`ℤ₂` is torsion-free).  The arithmetic here
is pure `Nat` (no `omega` / `Nat.add_left_cancel`, which are propext-tainted).

### The residue's own base — the golden / Zeckendorf carry

The binary base is not privileged; the residue's *own* base is the Fibonacci spiral (the `P`-orbit,
§"count" of `phi_self_similarity.md`).  The **golden / Zeckendorf adic** (= Ostrowski(φ)) carries
`011 → 100` via the Fibonacci recurrence — `zeck_carry_weight`: `fib (i+2) + fib (i+3) = fib (i+4)`
(the `+1` lifting one spiral rung, ground instance `1 + 2 = 3`) — and the carry is
**value-preserving** on Fibonacci-base digit lists (`fibValFrom_carry`).  Its admissibility law
(no two consecutive `1`s) is the Cassini `W = ±1` / `det P = 1` digit law
(`FibCassiniNat.fib_cassini_norm`).  Bundle: `golden_adic_carry`.  Same residue unit `+1`, now in
the residue's own spiral base.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `odometer_mu_nu_mirror` | `Theory/Raw/Odometer` | carry terminates iff floor (µF) / runs forever on the escape (νF) |
| `spineL_seed_is_odo_overflow` | `Theory/Raw/Odometer` | the canonical escape `spineL` is the odometer overflow |
| `successor_dynamics` | `Theory/Raw/Odometer` | the `+1` is injective + interlocks with the descent (adding-machine recursion) |
| `odo_unit_action` | `Theory/Raw/Odometer` | the `+1` is invertible (`−1` = borrow); the unit generates a `ℤ`-action |
| `descent_forgets_ascent_remembers` | `Theory/Raw/Odometer` | descent surjective-not-injective (forgets), ascent unit bijective (reversible) |
| `odo_homeomorphism` | `Theory/Raw/Odometer` | the `+1` is the `ℤ₂`-successor homeomorphism (bijective + continuous) |
| `carry_profile` | `Theory/Raw/Odometer` | the carry is the leading run of `1`s (`carry_eq_true_iff`) and a step function (`carry_monotone`) — its depth = the floor distance |
| `bval_odo` | `Theory/Raw/OdometerValue` | the profinite successor: `bval k (odo f) + carryOut·2ᵏ = bval k f + 1` — `odo = (+1 mod 2ᵏ)` on each finite truncation |
| `odo_no_fixpoint` | `Theory/Raw/OdometerValue` | the `+1` is fixed-point-free (`odo f 0 ≠ f 0`) — the act of pointing always changes something |
| `odo_free` | `Theory/Raw/OdometerValue` | the `ℤ`-action is **free**: `odoʲ f = f → j = 0` — the `+1`, iterated, never returns (no nonzero period) |
| `golden_adic_carry` | `Real213/ZeckendorfCarry` | the golden/Zeckendorf carry `011→100` = Fibonacci recurrence, value-preserving; admissibility = Cassini |

## Honest scope (what this is and is not)

The mathematics is the **`2`-adic odometer** (the adding machine / Vershik–Bratteli `+1`) and
**Ostrowski(φ) = Zeckendorf** — both known objects.  The 213 content is the *reading*, ∅-axiom: the
odometer's `+1` IS the self-pointing act; its carry IS the residue unit (`SharedUnitAcrossReadings`);
its overflow IS the νF escape (`spineL`); its injectivity IS `tower_no_cycle` (no-exterior); its
reversibility distinguishes µF (forgetful grounding) from νF (the unit's group action).  213 would
be **falsified** by an exterior object; finding `X₂₁₃ = X_known` (here: the odometer, Zeckendorf) is
the prediction, the relabeling layer (`the_frontier_has_a_form.md` "nothing new").

## Constructive accessibility (the syntactic landing object)

The essay lands on `odo_homeomorphism` — a ∅-axiom term asserting the residue's `+1` is the
`ℤ₂`-successor homeomorphism.  "The arithmetic face of the residue unit" is not a slogan: it is the
statement that the escape space is `ℤ₂` and the act of pointing is its topological-group `+1`,
witnessed by a term that type-checks with no axioms.

## Open frontier

The three frontiers this essay opened are all addressed:

  - **The profinite value** — *closed*: `bval_odo` proves `odo = (+1 mod 2ᵏ)` carry-explicitly,
    pinning the escape space as `ℤ₂ = lim ℤ/2ᵏ` quantitatively (pure `Nat`, no `omega`).
  - **Freeness of the `ℤ`-action** — *closed*: `odo_free` (`odoʲ f = f → j = 0`) — the `+1`,
    iterated, never returns (`ℤ₂` torsion-free; full no-exterior at the odometer scale).
  - **Carry-depth** — *characterised + honest ceiling*: `carry_profile` pins the carry as the
    leading run of `1`s, a step function whose depth is the floor distance.  A fully *decidable*
    µF/νF classification from the stream is **constructively obstructed** — membership "is `f` the
    escape?" is `∀ k, f k = true`, and `¬(∀ k, f k = true) ↔ ∃ k, f k = false` is not
    constructive (it is the `object1_not_surjective` non-decidability at the bit-stream scale, not
    a gap).  So the carry-depth is the *coordinate*; the classification it indexes is exactly as
    accessible as the escape itself — no more, by no-exterior.

## How to verify

```bash
cd lean && lake build E213.Theory.Raw.Odometer E213.Lib.Math.NumberSystems.Real213.ZeckendorfCarry
python3 tools/scan_axioms.py E213.Theory.Raw.Odometer
python3 tools/scan_axioms.py E213.Theory.Raw.OdometerValue
python3 tools/scan_axioms.py E213.Lib.Math.NumberSystems.Real213.ZeckendorfCarry
```

## Self-check (failure-mode discipline)

  - *Overclaim of novelty?*  Explicitly inverted: the `2`-adic odometer and Zeckendorf are known;
    the content is the residue reading + ∅-axiom formalisation (the relabeling-layer prediction).
  - *Universe-constant framing?*  The `+1` is the *unit* (a Lens-output unit shared across readings),
    not a privileged universe constant; the bit-stream carrier is one Lens-presentation of the
    escape, not "the" residue.
  - *Forcible map?*  The descent/ascent-unit interlock (`shift_odo`) and the `±1` inverse are
    proven Bool identities, not an imposed correspondence; the golden carry's value-preservation is
    the Fibonacci recurrence, not a fitted analogy.

## One line

> **The residue unit `+1` is an odometer: the act of pointing is the `ℤ₂`-successor on the escape
> space — injective (never returns), invertible (a `ℤ`-action), reversible where the descent
> forgets, continuous (a homeomorphism), and carrying in the residue's own golden base.  The
> arithmetic face of no-exterior.**
