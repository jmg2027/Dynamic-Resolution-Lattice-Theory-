# Holonomy of the lattice — the dynamic read as a loop, and why ℕ⁺ has none

**Status**: Closed.  Source of truth:
`lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean` (25 PURE / 0
DIRTY).  Anchor: `seed/AXIOM/06_lens_readings.md` §6.6 (state-transition = state)
+ §5.7 (frozen/dynamic) + `theory/essays/analysis/the_modular_group_from_two_folds.md`.

## The bridge: where state and state-transition have the same representation

"Dynamic" is a Lens reading, not a property of the residue (§5.7).  Without an
external time axis an internal observer cannot separate *state at a moment* from
*transition between moments* — both are readings of one residue (§6.6).  A `2×2`
integer matrix `M` is exactly that non-separation made into a single object:

  - **frozen** — `M` is a configuration, a lattice point, four counts;
  - **dynamic** — `M` is the map `x ↦ M·x`, a transition.

The **modular / Möbius matrix is the representation in which the two readings
coincide**: the operator is an object *of the same kind* it operates on.  That
coincidence is what lets a *loop of transitions compose to a state*.  The
composite state is the **holonomy** of the loop.

A *path* is a list of state-transitions `w : List Mat2`; its holonomy is the
ordered fold-product

  `holonomy [g₀, …, gₙ] = g₀ · g₁ · … · gₙ · I`.

This is genuinely a holonomy — parallel transport of a connection around a path —
in three ∅-axiom facts.

### 1. Functoriality — the path-composition law

`holonomy (p ++ q) = holonomy p · holonomy q` (`holonomy_append`).  Concatenating
paths composes their holonomies: holonomy is a monoid homomorphism from the free
monoid of paths `(List Mat2, ++, [])` into the matrix monoid `(Mat2, ·, I)`.  The
codomain is *states* — transport around a path lands on an object of the same
kind it transported, the §6.6 collapse made computational.  The proof is the
associativity of `Mat2` (`Mat2Assoc.mul_assoc`) plus the left identity
(`one_mul`); nothing more is needed, because "transition composes" is exactly
"the monoid is associative."

### 2. Flatness — `det = 1` is the conserved holonomy invariant

`det` is multiplicative (`det_mul`, Cauchy–Binet for `2×2`), so if every step has
`det = 1` the holonomy has `det = 1` around the *whole* loop
(`det_holonomy_eq_one`).  `det = 1 = NS − NT` is the founding shared unit
(`FoundingDynamicBridge.founding_swap_is_elliptic_floor`); it is the conserved
invariant of transport — the discrete **flat connection** whose curvature `det`
is preserved.  This is the same invariant the `Mobius213` cross-determinant reads
as the constant `−1` on the convergent pair
(`mobius_213_pell_unit_invariant_forall`): the area `2`-form preserved by the
`SL₂` action, here read as the holonomy that does not depend on the loop.

### 3. The ℕ⁺ sector has no holonomy — and holonomy is born from the fold

The Stern–Brocot / Calkin–Wilf generators `L = [[1,0],[1,1]]`, `R = [[1,1],[0,1]]`
have entries in ℕ — the **ℕ⁺ sector** — and `det = 1`.  Every positive rational is
reached by a unique word in `L, R` (the Stern–Brocot tree).  A tree is simply
connected: it has no non-trivial loop.  This is a theorem here, not a picture.

Define the entry-sum length functional `entrySum M = a + b + c + d`
(`entrySum I = 2`).  On the positive interior `Pos M` (diagonal `≥ 1`,
off-diagonal `≥ 0`) — which `I` satisfies and which `L`, `R` preserve under
left-multiplication (`pos_mul_L`, `pos_mul_R`) — the entry-sum *strictly grows* at
every step (`entrySum_lt_L`, `entrySum_lt_R`).  Hence every non-empty positive
word has `entrySum (holonomy w) > 2` (`positiveWord_entrySum_gt_two`), so it can
never return to `I`:

> **`positive_loop_trivial`** *(∅-axiom)*.  No non-empty word in `⟨L, R⟩` returns
> to the identity.  The positive monoid is free — a tree — so the count-Lens
> (ℕ⁺) sees only trivial holonomy.

The first non-trivial loop appears **exactly when the negation-fold composite
`S = N·R = z ↦ −1/z` is admitted** (`first_loop_is_the_fold`).  `S` carries the
entry `S.b = −1` that the ℕ⁺ sector excludes, and

  `holonomy [S, S] = −I ≠ I`,    `holonomy [S, S, S, S] = I`

— the first closed loop returns to the central element `−I` and closes at order
4, the elliptic Gaussian period.  A length-2 *positive* loop `[L, R]` does not
close at all.

## The thesis

Holonomy is the residue-internal signature of the fold that turns ℕ⁺ into ℤ.  The
count-Lens (ℕ⁺) is loop-free: "dynamic," read as a lattice of positive-integer
transitions, has *trivial* holonomy — a tree, no monodromy.  The difference-Lens
(ℤ, the sign fold of §6.7) is what creates a loop: admitting the swap `(a,b) ↦
(b,a)` that the projection reads as negation (the `S = N·R` of the founding
bridge) gives the first closed path with non-trivial transport.  So the modular
group's holonomy is not imported — it is born at the exact step where the founding
sign-fold enters, and the elliptic order 4 of that first loop is the period the
finite-order spectrum `{1,2,3,4,6}` already pins
(`the_modular_group_from_two_folds.md`).

## Cross-frame

Classically: holonomy is parallel transport around a closed loop of a connection;
a flat connection has holonomy depending only on the homotopy class of the loop;
the holonomy group of `SL₂(ℤ)` acting on the modular tessellation is generated by
the elliptic/parabolic loops around the orbifold points.  Each statement is
recovered, but read on the **founding folds**: the flat connection is `det = 1 =
NS − NT`; the simply-connected sheet is the ℕ⁺ Stern–Brocot tree; the first
non-trivial holonomy is the negation fold `S`, order 4.

## Self-check

  - *Is "dynamic" a property of the residue?*  No (§5.7) — it is a Lens reading;
    holonomy is what that reading produces on a loop, and the frozen reading
    (the composite matrix) is the same object.
  - *Is `SL₂(ℤ)` / the modular group imported to define holonomy?*  No — holonomy
    is the fold-product of an arbitrary path; the generators `L, R, S` are
    residue-internal (count-Lens entries and the sign-fold composite).
  - *Is the ℕ⁺-loop-free claim a picture or a theorem?*  A theorem
    (`positive_loop_trivial`), via the strictly-growing entry-sum — no appeal to
    "the tree is obviously simply connected."

---

**Lean**: `Real213/HolonomyLattice` (all ∅-axiom).
**Anchors**: `seed/AXIOM/06_lens_readings.md` §6.6 + §6.7; §5.7;
`theory/essays/analysis/the_modular_group_from_two_folds.md`;
`lean/E213/Lens/Number/FoundingDynamicBridge.lean`.
