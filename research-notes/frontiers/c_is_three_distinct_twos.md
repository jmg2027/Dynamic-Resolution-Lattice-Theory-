# What `c` properly is in 213: three distinct 2's, not one

**Status: research finding (triangulated, ∅-axiom-grounded).**  Answers the
challenge: *the old `c` (Lorentz-anisotropy ratio) does not go into
`K_{3,2}^{(c)}`, and the recent "presentation parameter / fifth-Lens-reading"
framing is itself mistaken — so what does `c` properly become when derived
from 213?*

Three independent investigations (combinatorial-cohomology / signature-physics
/ adversarial red-team) converged on the same answer, the red-team **failing to
refute** it after genuine effort:

> The single label **`c`** has been carrying **three structurally distinct
> "2"s**.  Two are genuinely forced (in *different* roles); the third — the
> `K_{3,2}^{(c)}` edge multiplicity — is a *selected re-presentation*, not a
> forced primitive.  Disentangling them is the whole content; the proper
> 213 shape has **no fourth atomic parameter `c`** at all.

---

## The three 2's

### (S) Signature-2 — the *order/exponent* (this is the old `c`)

The recovered pre-seed reading
(`research-notes/archive/c_multiplicity/original_lorentz_anisotropy_reading.md`)
defines `c = d_S/d_T` via information distance `d := −ln(overlap)`:

  · temporal edge = ONE correlated (unitary) step → `W_T = 1/d` → `d_T = ln d`;
  · spatial edge = TWO independent objects → `W_S = 1/d² = W_T²` → `d_S = 2 ln d`;
  · `c = d_S/d_T = 2`, **exactly, for every `d`**.

This "2" is the **square in `W_S = W_T²` read through `−ln`** — an exponent /
order count (how many `1/d` factors), not a count of parallel objects.  Its
`d`-independence is the decisive tell: a multiplicity carries graph data
(`b_1 = 6c−4` is a line *in* `c`), this 2 carries none.

It traces to **one forced object seen three ways**:

  · **`NT = 2`** — forced atom (`Theory/Atomicity/{PairForcing,ArityForcing}`);
  · **the period-2 difference-Lens sign** — `Int213.neg_subNatNat`,
    `−(−x) = x` (`seed/AXIOM/06_lens_readings.md` §6.7); `|ℤ/2| = 2`;
  · **the Cayley–Dickson first doubling `i`** — `i² = −1`, order-2 unit;
    `ℤ[i]^× = C₄`, selected by `d = 5` (`theory/physics/cp_phase.md`).

And it **manifests as the metric signature** `(−,+,+,+)`: the single negative
grade is `⋆² = −1` at the simplex dimension `n = d − 1 = 4`
(`Mixing/CPHodgeStructure`: `star_sq_minus_one_at_1_3`, with `parity_wall_at_n5`
showing the odd vertex-count dimension `n=5` collapses every sign to `+1`).
The chain is uniform and every link is **order/period/sign-2**:

```
NT = 2  =  period-2 sign (Int213.neg_subNatNat)  =  CD unit i (i² = −1)
       =  ⋆² = −1 at grade n = d−1 = 4  =  the lone minus of (−,+,+,+)
       =  W_S = W_T² (the square)  =  the old  c = d_S/d_T = 2.
```

This is **genuine, forced physics** (the signature), and it is *the* content
the originating "time twice as short" reading was pointing at.  Its proper
213 home is the **signed Hodge complex structure on `Δ⁴`** — currently a PURE
*parity skeleton* (`CPHodgeStructure`); the signed-`ℤ` Hodge star that would
make `(−,+,+,+)` a ∅-axiom theorem (rather than a narrative reading) is the
concrete **open construction** this finding promotes.

### (M) Cover-2 — the `K_{3,2}^{(c)}` edge multiplicity (a *re-presentation*)

`c` = number of parallel edge-layers per `(s,t)` incidence; `|E| = c·NS·NT = 12`
at `c = 2`.  Its only structural job is to make the graph cycle space
reproduce the octet:

  · `b_1(K_{3,2}^{(c)}) = 6c − 4` is a strictly increasing **line in `c`**
    (`Cup/K32Projection.lean §7`: `k32_b1_32_is_line`, `k32_b1_32_strict_mono`);
  · the target `NS² − 1 = 8` is **constant in `c`**;
  · they coincide at the **unique crossing** `c = 2`
    (`k32_b1_32_crosses_adjoint_only_at_2`).

A `c`-varying space and a `c`-constant target cannot be naturally isomorphic;
`c = 2` is therefore **selected to hit the target, not forced**.  And the octet
exists without it: `SpectrumComplete.alpha_3_channel := NS*NS − 1 = 8`, straight
from the forced `NS = 3`.  Falsifiers are entirely `c`-free
(`FalsifierRosterForced`: every measurable falsifier is a polynomial in
`(NS,NT,d)`; `N_gen = C(3,2) = 3`, muon `(NS²−1)(d²−1) = 192`, …).  Where `c`
*does* appear in precision (the `60/24/12` α_em / Δm_np prefactors, routed
through `c·NS·NT`), it is a **role-distinct re-encoding** whose value `2` is
plugged in, not derived (`AlphaEM/AssignmentForcing`:
`increments_distinguish_c_from_nt` distinguishes the *slot's role*, never the
*value*).

### (N) Count-2 — `NT` and arity (forced atoms, no controversy)

`NT = 2` (temporal slot count, forced with `(NS,NT)=(3,2)`) and arity `= 2`
(the binary slash, `CombinatorialArity`) are the genuine "atomic 2".
`AssignmentForcing.c_and_nt_equal_value_distinct_role`: `c` and `NT` are
**equal value, distinct role, distinct source**.

---

## Why the three are distinct (not "one number, several Lenses")

The previous "multiplicity-doctrine" reconciliation
(`c_counter_as_layer_count.md`, since corrected) framed (S) as a *Lens reading
of the same `c`* as (M).  **That is too generous and is the mistake the
challenge names.**  (S) and (M) are different *quantities*, and the repo's own
∅-axiom theorems prove it:

  · **Orthogonality (the bridge-killer).**
    `V32Betti.mult_parity_orthogonal_to_cup_orientation` (PURE): every
    sheet-pair `(2k, 2k+1)` shares its endpoints yet differs in `e % 2`.  The
    sign/`i` ℤ/2 (which carries (S)) is a **function of endpoints**; the
    multiplicity ℤ/2 (which is (M)) **preserves endpoints and flips only the
    multiplicity bit**.  The two ℤ/2's act on **orthogonal data** — they
    *cannot* be identified.  This severs the only non-numerical bridge.
  · **`d`-independence.**  (S) `= 2` for every `d` (no `K`-content); (M) lives
    in the `c`-line `6c−4` (all `K`-content).  A quantity with no graph data
    cannot *be* the graph multiplicity.
  · **The Euler "bridge" is a value-coincidence.**  `χ(Δ⁴)+χ(K_{3,2}^{(c=2)})
    = +1 + (−7) = −6 = −NS·NT` holds **only at `c=2`** (the `−7 = 5−12` has
    `12 = c·NS·NT` baked in; at `c=1` the sum is `0`, at `c=3` it is `−13`).
    `χ(Δ⁴) = +1` is pure `binom 5 k` — no `c`, no `d_S/d_T`, no signature.  The
    anisotropy never enters the computation.

So identifying (S) with (M) is the **"coincidence of two structurally-distinct
2's"** pattern the corpus catalogs — here made precise: an *order/signature*
2 versus a *cover/count* 2, provably orthogonal.

---

## The proper 213 shape of `c`

**`c` is not a thing.**  When derived honestly from 213 the label dissolves:

1. **The forced data is `(NS, NT, d) = (3, 2, 5)`.**  No fourth primitive.
2. **The octet is `NS² − 1`** directly from `NS = 3` (SU(3) adjoint) — no
   graph, no multiplicity.  `K_{3,2}^{(c=2)}` is a *cohomological
   re-presentation* of that number; its `c = 2` is the bookkeeping multiplier
   (`12 = 2·NS·NT`, equally `2(d+1)`) chosen so the cycle space lands on 8.
   It is a valid **secondary reading**, not a source — and must not be carried
   as a forced atom.
3. **The genuine "2" is the binary distinguishing** — `NT` = arity =
   difference-Lens sign = `i`.  In the **metric** this 2 is the **Lorentz
   signature**: the order-2 gap between the *correlated / self-pointing* axis
   (time, `−`, where successive pointings feed each other — the recursion of
   §1.2) and the *independent / distinguished* axes (space, `+++`).  The
   `−/+` split is the **recursion-vs-distinction split** — deeply 213-native,
   and the real content the old `c` reading captured.  Its axis count is
   `4 = NS + (NT−1) = 3 space + 1 time` (G121 `deployment_M2_partial_capstone`;
   the spare `NT` axis is the chart-invisible self-pointing residue) — **not**
   "3 space + 2 time".

In one line:

> 213 forces `(3,2,5)` and the octet `NS²−1`.  The old `c` is the **signature**
> (an order-2 property of the metric, sourced in `NT`/`i`); the K32 `c` is a
> **re-presentation multiplier** (selected, removable).  They share the value
> 2 and nothing else.  There is no fourth atomic `c`.

---

## Open construction (the genuine next step)

Make the signature a ∅-axiom theorem rather than a narrative reading: build the
**signed-`ℤ` Hodge star on `Δ⁴`** so `⋆² = −1` at grades `1,3` is a real
operator identity (currently `CPHodgeStructure` is a PURE *parity skeleton*
with the signed star named-unbuilt), and read `(−,+,+,+)` off the one negative
grade.  This is the same `d = 5` cohomology that hosts `1/α_em` and the CP
phase — the signature, the imaginary unit, and the fine-structure constant
share one home, and that home is the order-2 `i`, **not** the edge multiplicity.

## Corpus corrections this finding triggers

  · `theory/essays/cohomology/c_counter_as_layer_count.md` — the "Physical
    (anisotropy)" reading must be demoted from *"a Lens reading of the same
    `c`"* to *"a distinct (signature) quantity that shares the value 2"*; the
    "one number, two Lenses" line is wrong (orthogonality theorem).
  · `research-notes/archive/c_multiplicity/original_lorentz_anisotropy_reading.md`
    — its "bridge to current form" likewise overstates the identification;
    sharpen to "distinct quantities, orthogonal ℤ/2's".
  · `research-notes/frontiers/atomic_c_multiplicity_forcing.md` — already
    "3 forced + 1 posited"; add the positive identification that the *posited*
    `c` is removable and the genuinely-forced order-2 lives in the signature,
    not the graph.

## Cross-references

  · `research-notes/archive/c_multiplicity/original_lorentz_anisotropy_reading.md`
  · `research-notes/frontiers/atomic_c_multiplicity_forcing.md`
  · `theory/essays/cohomology/c_counter_as_layer_count.md`
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V32Betti.lean`
    (`mult_parity_orthogonal_to_cup_orientation`)
  · `lean/E213/Lib/Math/Cohomology/Cup/K32Projection.lean` §7 (c-line crossing)
  · `lean/E213/Lib/Physics/Foundations/FalsifierRosterForced.lean` (c-free falsifiers)
  · `lean/E213/Lib/Physics/Mixing/CPHodgeStructure.lean` (⋆²=−1 parity skeleton)
  · `lean/E213/Lib/Physics/Couplings/SpectrumComplete.lean` (octet = NS²−1 directly)
