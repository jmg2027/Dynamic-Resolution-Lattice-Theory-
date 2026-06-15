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
