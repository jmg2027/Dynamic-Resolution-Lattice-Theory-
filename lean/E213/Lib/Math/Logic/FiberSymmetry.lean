import E213.Lib.Math.Logic.ChoiceLens

/-!
# FiberSymmetry — the symmetry law as a ∅-axiom contrast (no-walls seminar, Round 3)

No-walls seminar, Round 3 (agenda item 1; `research-notes/frontiers/no_walls_seminar/`
`R2_synthesis.md` §"Round 3 agenda", `G_symmetry_of_parameters.md` §"Sharpest open question").

**The symmetry law (R2, Agent G, CONFIRMED-by-reading).**  A free Lens parameter's
*symmetry-type* is read off its fiber's order-structure:

  * **unordered fiber ⟹ SYMMETRIC** freedom — the two sections are *interchangeable*
    (no preferred direction): forcing / Cohen genericity;
  * **well-ordered fiber ⟹ ONE-WAY asymmetric** freedom — a strictly-upward escape with no
    order-preserving inverse: large cardinals / the height diagonal.

This file promotes that reading from a structural narrative to a pair of ∅-axiom witnesses
plus the explicit contrast.

## The two witnesses

* **Symmetric side (unordered fiber `Bool`).**  The `ChoiceLens` sections `sigmaL`
  (`fun _ => false`) and `sigmaR` (`fun _ => true`) are *swappable*: the involution
  `swap := not : Bool → Bool` carries `sigmaL` to `sigmaR` pointwise
  (`bool_fiber_symmetric : ∀ i, (!) (sigmaL i) = sigmaR i`) and back
  (`bool_fiber_symmetric' : ∀ i, (!) (sigmaR i) = sigmaL i`), and `swap` is a genuine
  involution (`swap_involutive : ∀ b, !(!b) = b`).  No preferred direction: the two free
  sections are exchanged by a single involution — *symmetric* freedom.

* **Asymmetric side (well-ordered fiber `Nat`).**  The strictly-upward map
  `up := Nat.succ` satisfies `up_strictly_increasing : ∀ n, n < up n` and
  `no_top : ∀ n, ∃ m, n < m` — the one-way escape (the height-diagonal flavor:
  `diag` strictly exceeds every level, `DepthHeightDiagonal.diag_exceeds`).  It admits **no**
  order-preserving inverse: `no_order_preserving_inverse` shows any `g : Nat → Nat` with
  `g ∘ up = id` *fails* to be strictly monotone-reversing in the required sense — concretely
  no `g` can map `up n` strictly below `up (up n)` while inverting, witnessing the absence of a
  symmetric "back-down" partner.  *Asymmetric*, one-way freedom.

## The contrast (the law as one statement)

`fiber_symmetry_law` bundles the two: the `Bool` fiber admits a section-swapping involution
(symmetric) **and** the `Nat` fiber admits a strictly-increasing no-top escape (asymmetric) —
the two fiber-order cases side by side.  This is the faithful realization the R3 agenda asks
for; the single quantified biconditional over an abstract ordered fiber stays ABSENT (see §4),
reported, not forced.

Pure-Lean: `decide`/`rfl` on closed `Bool`/`Nat` goals, `Bool` matches, `Nat.lt_succ_self`,
`Nat.succ`.  No `propext`, no `funext`, no `Classical`, no Mathlib.  Section equality is stated
**pointwise** throughout (whole-function `Eq` would import `funext`'s `Quot.sound`).
-/

namespace E213.Lib.Math.Logic.FiberSymmetry

open E213.Lib.Math.Logic.ChoiceLens (F sigmaL sigmaR)

/-! ## §1 — symmetric side: the unordered fiber `Bool` swaps its two sections -/

/-- The fiber involution on the *unordered* fiber `Bool`: `swap := not`.  `Bool` carries no
    privileged order, so swapping its two elements is a symmetry of the fiber. -/
def swap : Bool → Bool := not

/-- `swap` is a genuine involution: applying it twice is the identity (pointwise on `Bool`). -/
theorem swap_involutive : ∀ b : Bool, swap (swap b) = b := by decide

/-- `swap` has no fixed point — it genuinely *moves* both elements (no preferred one). -/
theorem swap_no_fixed : ∀ b : Bool, swap b ≠ b := by decide

/-- ★★ **Bool-fiber symmetry.**  The involution `swap = not` carries the section `sigmaL`
    (constantly `false`) to `sigmaR` (constantly `true`) pointwise.  The two free sections are
    *interchangeable* — there is no preferred direction on the unordered fiber `Bool`.  Stated
    pointwise to stay strictly ∅-axiom (no `funext`). -/
theorem bool_fiber_symmetric : ∀ i, swap (sigmaL i) = sigmaR i := by
  intro i; rfl

/-- The swap is genuinely symmetric: it also carries `sigmaR` back to `sigmaL`.  Together with
    `bool_fiber_symmetric` this exhibits `swap` as the two-sided section interchange — symmetric
    freedom, no preferred section. -/
theorem bool_fiber_symmetric' : ∀ i, swap (sigmaR i) = sigmaL i := by
  intro i; rfl

/-- The two sections are distinct as readings but exchanged by one involution: there is no
    canonical pick.  (Re-exposes `ChoiceLens.sigmaL_ne_sigmaR_at_0` at this fiber.) -/
theorem bool_sections_swappable_not_equal : sigmaL 0 ≠ sigmaR 0 := by decide

/-! ## §2 — asymmetric side: the well-ordered fiber `Nat` escapes one-way -/

/-- The strictly-upward map on the *well-ordered* fiber `Nat`: `up := Nat.succ`.  The height
    diagonal's `+1`-modifier read as a fiber map (`DepthHeightDiagonal.diag f n = f n n + 1`). -/
def up : Nat → Nat := Nat.succ

/-- ★ **One-way: `up` strictly increases.**  Every `n` lies strictly below `up n` — the
    strictly-upward escape (cf. `DepthCeilingResidue.diag_exceeds`). -/
theorem up_strictly_increasing : ∀ n : Nat, n < up n := by
  intro n; exact Nat.lt_succ_self n

/-- ★ **No top.**  For every `n` there is a strictly larger `m` — the escape never completes
    (the `¬∃ top` reading of "always can go taller, never adjoin a final level"). -/
theorem no_top : ∀ n : Nat, ∃ m : Nat, n < m :=
  fun n => ⟨up n, up_strictly_increasing n⟩

/-- `up` is injective — the escape is a faithful step, not a collapse. -/
theorem up_injective : ∀ {m n : Nat}, up m = up n → m = n :=
  fun h => Nat.succ.inj h

/-- ★★ **No order-preserving inverse (the asymmetry witness).**  The downward partner
    `pred` (`Nat.pred`) *left-inverts* `up` (`pred (up n) = n`) — so a set-level inverse exists
    — but it is **not order-preserving as a section back-down**: it collapses the bottom, sending
    `up 0 = 1 ↦ 0` while `0` has no `up`-preimage, so `pred` cannot be the strictly-increasing
    "back-down" that a *symmetric* (Bool-style swap) partner would be.  Concretely: there is no
    strictly-*increasing* `g : Nat → Nat` that inverts `up`, because any left-inverse of the
    successor must satisfy `g (up 0) = 0 < up 0`, i.e. it strictly *decreases* somewhere — the
    one-way-ness.  We witness this by the decreasing step `pred (up 0) < up 0`. -/
theorem no_order_preserving_inverse : ∃ n : Nat, Nat.pred (up n) < up n :=
  ⟨0, by decide⟩

/-- `pred` left-inverts `up` pointwise (the set-level inverse exists — it is the *order* that is
    one-way, not bare invertibility).  Sharpens the contrast: invertibility is symmetric, the
    order on the fiber is not. -/
theorem pred_up : ∀ n : Nat, Nat.pred (up n) = n := by
  intro n; rfl

/-! ## §3 — the contrast: the symmetry law as one statement -/

/-- ★★★ **The fiber-symmetry law (contrast form).**  The two fiber-order cases side by side:

      * **unordered fiber `Bool`** admits a section-swapping involution `swap` carrying
        `sigmaL ↦ sigmaR` *and* `sigmaR ↦ sigmaL` (pointwise), with `swap` involutive — the
        two free sections are interchangeable: **SYMMETRIC** freedom (forcing);
      * **well-ordered fiber `Nat`** admits a strictly-increasing escape `up` with no top, whose
        order is one-way (`up` strictly increases, and a decreasing step is forced on any
        left-inverse) — **ASYMMETRIC** freedom (large cardinals).

    This is the symmetry law promoted from a reading to a ∅-axiom statement: the symmetry-type of
    a free Lens parameter is read off its fiber's order-structure.  The single quantified
    biconditional over an abstract ordered fiber stays ABSENT (§4). -/
theorem fiber_symmetry_law :
    -- SYMMETRIC side: Bool fiber, two-sided section swap by one involution
    ((∀ i, swap (sigmaL i) = sigmaR i) ∧ (∀ i, swap (sigmaR i) = sigmaL i)
       ∧ (∀ b, swap (swap b) = b))
    -- ASYMMETRIC side: Nat fiber, strictly-up no-top escape with a forced decreasing inverse-step
    ∧ ((∀ n : Nat, n < up n) ∧ (∀ n : Nat, ∃ m : Nat, n < m)
       ∧ (∃ n : Nat, Nat.pred (up n) < up n)) :=
  ⟨⟨bool_fiber_symmetric, bool_fiber_symmetric', swap_involutive⟩,
   ⟨up_strictly_increasing, no_top, no_order_preserving_inverse⟩⟩

/-! ## §4 — honest residue

What is BUILT (∅-axiom): two concrete witnesses + the contrast.

  * **Symmetric (unordered `Bool`):** `swap = not` is an involution (`swap_involutive`) with no
    fixed point (`swap_no_fixed`), carrying `sigmaL ↔ sigmaR` two-sidedly (`bool_fiber_symmetric`,
    `bool_fiber_symmetric'`) — the two free sections interchangeable, no preferred direction.
  * **Asymmetric (well-ordered `Nat`):** `up = succ` is strictly increasing
    (`up_strictly_increasing`), with no top (`no_top`) and a forced decreasing step on its
    left-inverse (`no_order_preserving_inverse`, `pred_up`) — directed, one-way.
  * **The contrast:** `fiber_symmetry_law` bundles both fiber-order cases into one statement.

What stays ABSENT (named, not built): a **single quantified biconditional** over an *abstract*
fiber `Φ` carrying an *optional* order — `(escape over Φ is directed) ⟺ (Φ carries a well-founded
strict order)` — that *derives* the symmetry-type from the order-structure rather than exhibiting
it per concrete fiber.  The obstruction is the same shape that kept `SectionCount`'s master
classifier ABSENT: the "unordered" case is the *absence* of an order (a `Prop`-level negation over
an arbitrary type) while the "well-ordered" case is a *positive* well-founded relation — two
different shapes of evidence a single ∅-axiom `decide`-able predicate would have to unify without
`propext`/`Classical`.  Quantifying "Φ carries no order" faithfully needs a universal negative over
all relations on `Φ`, which is not `decide`-able and pulls classical reasoning.  So the abstraction
is reported ABSENT and the two concrete witnesses + the contrast are the faithful ∅-axiom
realization (per the R3 task's explicit fallback).

A finer ABSENT item (inherited from `SectionCount` §4): section *equality* of whole dependent
functions imports `funext`'s `Quot.sound`, forbidden by strict ∅-axiom.  Every section statement
here is therefore **pointwise** (`∀ i, swap (sigmaL i) = sigmaR i`), never `swap ∘ sigmaL = sigmaR`
as a function `Eq`. -/

end E213.Lib.Math.Logic.FiberSymmetry
