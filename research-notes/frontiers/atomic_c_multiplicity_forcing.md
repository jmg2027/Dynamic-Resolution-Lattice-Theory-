# Atomic multiplicity `c = 2` — is it axiom-internally forced?

**Status: open.**  Of the four atomic numbers `(NS, NT, c, d) = (3, 2, 2, 5)`,
**arity = 2** (the slash is binary) and the **pair `(NS, NT) = (3, 2)`** are
genuinely forced, ∅-axiom (`Theory/Atomicity/ArityForcing`,
`CombinatorialArity`, `PairForcing`, `Five.atomic_iff_five`).  The **cup /
edge multiplicity `c = 2`** is **not** — it is currently *selected to hit a
physics target*, and the candidate axiom-internal routes fail.  This note
pins the exact missing step so it is attackable rather than dressed as
closed.

## What `c` is

`c` = number of parallel edges per `(s, t)` pair in the canonical lattice
`K_{NS,NT}^{(c)}`.  The framework works with `K_{3,2}^{(c=2)}` (12 edges =
`NS·NT·c`).

## The razor-sharp pinch (where `c = 2` actually enters)

The Betti computation (`Lib/Math/Cohomology/Bipartite/V32Betti.lean:17-18`):

```
dim C¹ = NS·NT·c            (= 12 at c=2)
dim im δ₀ = dim C⁰ − dim ker δ₀ = (NS+NT) − 1   (= 4)
b₁ = dim C¹ − dim im δ₀ = NS·NT·c − (NS+NT−1) = 6c − 4
```

The anchor `b₁ = NS² − 1 = 8` (the photon-kernel / `1/α₃` confined-coupling
count) holds **iff `6c − 4 = 8`, i.e. `c = 2`**.  But:

- `b1_eq_NS_sq_minus_1` (`V32Betti.lean:64`) is `decide` on `8 = 3·3 − 1` —
  a numerical match, **not a structural isomorphism**.
- The edge count `dim C¹ = 12` is built **with `c = 2` already baked in**
  (`CochE = Fin 12`).  So the cohomology reads `b₁ = 8` back out of a graph
  whose multiplicity was already chosen.
- The whole c-counter cohomology programme is **parametric in `c` by
  design** ("no level privileged"; `codim ≥ c` proven for all `c`,
  `theory/essays/cohomology/c_counter_programme_closure.md`).  It forces
  "codim grows with `c`", never `c = 2`.

So `c = 2` enters **only** by demanding `b₁` equal the imported target
`NS² − 1 = 8`.  That is the physics destination, assumed.

## Why the candidate axiom-internal routes fail

1. **`c = NT` (the most promising handle).**  Asserted at
   `Lib/Math/Cohomology/Bipartite/V32LocalSignature.lean:86-93` and
   `Lib/Math/Foundations/C2DoublingDerivation.lean` (`c_multiplicity_eq_NT`),
   but both *observe* `c = NT` by `decide`/`rfl` after independently fixing
   both numbers to 2.  The intuitive picture "each `(s,t)` edge carries the
   2-leaf alphabet `{a,b}`, so `c = |{a,b}| = NT`" **conflates two
   structurally distinct 2's**: the leaf alphabet `Fin 2` is the
   *arity-base* (and is exactly what forces arity = 2), whereas `NT` is the
   *q-slot of the partition `d = 5 = 2·1 + 3·1`*, an entire Lens-tower
   above Raw.  They both equal 2, but no theorem identifies them — and one
   should not, because the same argument would give `c = NS = 3`.

2. **Orientation / direction-freedom.**  Clause 3 (`a/b = b/a`) *quotients
   out* the two orientations of a pair rather than recording both, so this
   route yields `c = 1`, not 2.  Structurally closed against `c = 2`.

3. **The `10/5` pentagonal route** (`C2DoublingDerivation`): `P⁵ ≡ −I`,
   `P¹⁰ ≡ +I (mod 5) ⟹ c = 10/5 = 2`.  A real derivation, but it routes
   `c` through `d = 5` (which already presupposes the atom pair); the
   final `= NT` step is again `decide` coincidence, not structure.

## The exact missing lemma (what a genuine closure needs)

A non-circular, drawable forcing of `c = 2` requires a **structural
isomorphism**

```
H¹(K_{NS,NT}^{(c)})  ≅  (the S-side pairwise-distinguishing lattice, dim NS² − 1)
```

from which `NS·NT·c − (NS+NT−1) = NS² − 1` follows **without already naming
`NS²−1 = 8` as the target**.  With `(NS,NT) = (3,2)` forced, this is
`6c − 4 = 8 ⟺ c = 2`.

### This route is now proven NON-forcing (∅-axiom)

The proposed isomorphism **cannot exist as a c-natural map**, and the
obstruction is clean: `b₁(K_{3,2}^{(c)}) = 6c − 4` is **strictly increasing
in `c`** (each multiplicity layer adds `NS·NT = 6` independent cycles),
while `dim(su(NS) adjoint) = NS² − 1 = 8` is **constant in `c`**.  A
c-varying space and a c-constant space cannot be naturally isomorphic; they
coincide in dimension at *one* `c` only (`c = 2`), and there the "iso" is a
non-canonical equality of two 8-dim spaces — no forcing content.  Every
numerical match en route (`NS·NT = NS(NS−1) = 6`; the 2 geometric cycles =
rank 2) is itself a `NT = NS−1` coincidence, not a canonical correspondence.

Formalized ∅-axiom in `Lib/Math/Cohomology/Cup/K32Projection.lean` §7:
- `k32_b1_32_is_line` — `b₁(K_{3,2}^{(c)}) = 6c − 4` (a line in `c`).
- `k32_b1_32_strict_mono` — strictly increasing (`+6` per multiplicity).
- `k32_b1_32_crosses_adjoint_only_at_2` — `b₁ = NS²−1 ⟺ c = 2` (unique crossing).

So `c = 2` is **selected** (crossing point of a c-line with a c-constant
target), not **forced**, via the cohomology-dimension route.

### What remains

A genuine forcing must come from **outside** the cohomology-dimension route
(now closed-negative).  Candidate directions: (i) a reason the *multiplicity
structure itself* must be binary — i.e. the same arity-2 / NT-2 forcing
acting on edges, made into a real identity rather than the `decide`
coincidence of two distinct 2's; (ii) a minimality principle ("smallest `c`
activating the multiplicity-cycle dimension") with an axiom-internal reason
`c > 1` is required that does not route through the `b₁ = 8` target.  Neither
is proven.

### Candidate (i) examined — also fails (and the reason is clean)

"Multiplicity binary-ness = the arity-2 forcing acting on edges" **does not
work**, for a precise reason: **edge multiplicity is not an arity.**  The
arity-2 forcing (`CombinatorialArity`) is a pigeonhole argument over the
2-element distinguishing base — it bounds how many *inputs* a relation can
take.  It says nothing about how many *parallel copies* of an incidence
exist.  So the genuinely-forced "2" (base size / arity) has no channel by
which it becomes the edge multiplicity.

The other independent route, the **Möbius-period derivation**
(`Lib/Math/Foundations/C2DoublingDerivation.lean`), is also non-forcing on
inspection:
- `half_period := 5` and `full_period := 10` are **literals**
  (`C2DoublingDerivation.lean:60,64`), not computed minimal periods — the
  docstring says "smallest k such that P^k ≡ ±I" but the Lean posits 5, 10.
- `c := full_period / half_period = 2` is then `decide` on `10/5`.
- The ratio `= 2` is the **trivial** fact `(−I)² = I`: if `P^k ≡ −I` then
  `P^{2k} ≡ I`, so full/half = 2 for *any* sign-flipping half-period —
  no `P`-specific or `5`-specific content; it just re-expresses
  `|{+1,−1}| = 2`.
- `c := full/half` identifies edge multiplicity with the period ratio by
  **definition**, with no structural reason the two are the same 2.

So every route (cohomology, Möbius-period, the `(NT,1,NS)` local signature)
ties `c` to an already-forced 2 (`NT`, the sign group, the base) **by
positing the identification**, a coincidence of numerically-equal but
structurally-distinct 2's.  `C2DoublingDerivation.lean:46` states the
monism outright ("all of these are the **same atomic 2 = NT**").

The monism does not rescue the forcing: "what the number 2 *is*" (one
atomic 2, fine) is a different question from "which *quantity* must equal 2
rather than 1 or 3."  `c = 1` (the bare simple graph `K_{3,2}`, `b₁ = 2`) is
equally expressible in the framework; `c = 2` is the value the **gauge
target** (8 gluon channels = `NS²−1`) selects.

### Honest status: 3 forced + 1 posited

`(NS, NT)` are forced (`PairForcing`), `d = NS + NT` is definitional, and
**`c` is posited** via `c = NT` (the edge-multiplicity-equals-T-axis
identification, asserted in `V32LocalSignature` / `C2DoublingDerivation`,
never derived).  The `(3,2,2,5)` headline should read as **three forced
atomic numbers plus one posited multiplicity**, with `c = 2` selected so the
cohomology reproduces the SU(3) gauge content.  A genuine forcing of `c`
would need an axiom-internal principle picking `c = NT` (or `c > 1`) that
does not name the gauge target — none exists.

## Multi-agent debate (fiber / resolution / Raw-explosion reframing)

Seed (originator): *"c is like a fiber → the coefficient of Raw's explosion
→ then it could be resolution."*  A continuous multi-agent debate (3 framings
× 1 round + proponent/red-team × 1 round) developed and stress-tested this.
Outcome: **the gap survives every 213-native reframing, but is now maximally
sharpened to a single posit, and one tempting wrong intuition is refuted.**

**Refuted (a correction worth keeping).**  "c=1 is degenerate (trivial,
`Fin 1`, nothing there)" is **false**: `parametric_c_independent_h2_classes`
gives a genuine non-coboundary H²-class already at `c = 1`, and
`primary_cup_span_soundness_c1` + `joint_psi_kernel_subset_primary_c1` (51
PURE) span a full dim-8 ψ-kernel at `c = 1`.  So `c = 1` is the
**non-degenerate base case**, not a degenerate point — any "minimal
*non-degenerate* resolution = 2" argument is dead on arrival.

**The sharpened gap (what `c = 1` actually lacks).**  `c = 1` is not
degenerate but **pre-distinguishing on the multiplicity axis**: the layer
index runs over `Fin 1`, so the layer signature
`psi_layer c m' (e_face_layer c m) = decide (m.val = m'.val)`
(`V33EnrichedParametric.lean:167`) has no off-diagonal — it is constantly
`true`, the cross-layer distinguishing does not yet exist.  `c = 2` is the
**first `c` with `∃ m m' : Fin c, m ≠ m'`** — the first multiplicity at which
the layer axis itself distinguishes.

**The conditional closure (genuine salvage).**  The debate converged (all
three framings independently) on a `ℤ/2` sign/orientation structure, giving:

> **IF** the multiplicity axis is required to be a genuine distinguishing (an
> orientation/sign Lens, hence `≥ 2` levels), **THEN** 213's minimal-residue
> reading forces `c = 2`, and that `2` is provably `|ℤ/2|` — the order of the
> sign/swap involution (`Int213.neg_subNatNat`, the difference-Lens sign;
> Bool-style `not∘not = id`, `05_no_exterior.md §5.2`).

Under the antecedent the `2` is the **same structurally-forced 2 as the
difference-Lens sign**, NOT a renamed multiplicity — this answers the
"c is just relabelled multiplicity" objection and is the debate's real gain.

**Why it does not close (the single remaining posit, P3).**  The antecedent
— *the physical/cohomological multiplicity axis must be an orientation
distinguishing* — is **posited, not derived**:
- The only axiom-level treatment of orientation is clause 3 (`a/b = b/a`),
  which *quotients* orientation → would give `c = 1`.  "Retain the
  orientation" is chosen against that grain.
- Its only motivation is imported physics (SU(3) roots come in `±` pairs, so
  the gauge reading wants the signed resolution) — an **exterior**, which
  no-exterior (§5.1) forbids using to *derive*.
- Pinning `c = 2` exactly (not just `≥ 2`) invokes minimality as a
  **selection rule on a strict-mono level axis** — structurally the same
  move the repo *deleted* `5²⁵ = N_U` for ("no level privileged").  Cannot
  privilege `c = 2` by the move that retired `N_U`.

**Net.**  The gap is now one clean conditional: `c = 2` is forced **iff** the
multiplicity axis must carry the sign/orientation Lens (P3).  P3 is not a
theorem; its motivation is the gauge target (exterior) and its "minimal"
selection is the banned level-privileging.  Status stands: **3 forced + 1
posited**, with the posit now pinpointed to P3 and the forced-given-P3 value
identified as `|ℤ/2|`.  A genuine closure must derive P3 axiom-internally
(why must the canonical lattice be read at the *signed* resolution?) without
naming the gauge target — still open.

## Secondary symptom: the `C2b` label collision

The same gap shows up as a documentation inconsistency — "C2b" names two
**different** equations across the two canonical files:

- `theory/physics/foundations/atomic_constants.md:14`:
  C2b = `2mn = m² + m + n − 2` (cohomology-loss).
- `Lib/Physics/Foundations/AtomicConstantsUnique.lean:56`:
  C2b = `(m²−1)(n²−1) = (m+n)²−1` (adjoint-product); the cohomology-loss
  equation is there called **C2a**.

Both C2a (cohomology-loss) and C2b (adjoint-product) are read off
adjoint-rank identifications — i.e. the physics target.  The label
confusion is the tell that the `c = 2` selection is not held as one clear
picture.

## Honest bottom line

`c = 2` is **formalized, not forced**.  Closing it = constructing the
`H¹ ≅ S-distinguishing-lattice` isomorphism above (so `b₁ = NS²−1` becomes
structural, not `decide`d).  Until then the `(3,2,2,5)` headline overstates:
two of the four numbers are forced, `d = 5 = NS+NT` is definitional, and
`c = 2` is the open one.

Companion gap (same flavour, already on the board):
`gram_d2_prefactor.md` — the `/d²` prefactor's `(a) full End V` vs
`(b) symmetric Gram` modeling commitment.
