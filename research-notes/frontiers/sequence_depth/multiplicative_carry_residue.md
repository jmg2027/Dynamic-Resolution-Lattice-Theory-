# Frontier — the multiplicative carry as a νF inhabitant (the residue of ×)

Status: **core CLOSED** (`lean/E213/Lib/Math/NumberSystems/Padic/NuEscape.lean`); only the
Lens-reading refinement (item 3) remains soft-open.

## The frontier question — answered YES

*Is the multiplicative carry itself a νF inhabitant?*  **Yes.**  `gspine` is generic over the leaf
alphabet (CoResidue §20), so the carry stream `mulCarry : Nat → Nat` is `gspine (mulCarry …) :
GCoShape Nat` — a consistent, anti-reflexive co-tree reached by no finite Raw (`carry_is_nu_escape`,
`gspine_escapes` at `L = Nat`).  And it is a *genuine* (unbounded) escape:

- `neg_one_sq_eq_one` — `(-1)² = 1`: the **result** is the trivial µF element `1`.
- `mulCarry_unbounded` — the carry is unbounded, the exact dual of `add_carry_le_one` (carry `≤ 1`).
- `mul_carry_nu_residue` — capstone: result `= 1`, carry is a νF escape, carry unbounded.

So **finite-state-ness is a property of the pointing (the carry), not the number (the result `1`)**:
the same real `1` is reached, while the multiplication-carry escapes the finite the way `spineL`
does — the ring-operation image of `Real213/PresentationDependence` ("holonomicity is a property of
the pointing, not the real").  The supporting helper `AddMod213.div_le_div_right_pure` (pure
monotone div) was added to `Meta/Nat`.

## What is closed

The carrier-arithmetic split between `+` and `×` is now precise, ∅-axiom:

- `+` is **finite-state**: `add_carry_le_one` — `Zp.add`'s carry is always a single bit (the
  odometer unit, `Theory/Raw/Odometer`).
- `×` is **native corecursive but not finite-state**:
  - corecursive — `mul_corecursive` (head `residue_mul` `(x·y)₀=x₀·y₀`, tail `mulRaw_tail`
    `(x·y)'=x₀·y'+x'·y`, emit/advance `mul_digit_carry_step`): `Zp.mul` is a coalgebra morphism for
    the carrier shift (CoResidue §21), the Cauchy product's behavioural differential equation;
  - not finite-state — `mulRaw_negOne_negOne` (`mulRaw (-1)(-1) k = (k+1)(p-1)²`) + `mulRaw_unbounded`,
    the exact dual of `add_carry_le_one`.

So the earlier "× is non-native by design" was wrong: `×` is native (corecursive); only *bounded
state* fails.  The unbounded carry is the **multiplicative residue** — the part of `×` that escapes
every finite-state machine.

## Closed (was the open frontier)

1. ✅ `mulCarry (-1)(-1)` unbounded — `mulCarry_unbounded` (the carry itself, not just `mulRaw`),
   the dual of `add_carry_le_one`.
2. ✅ The carry stream `gspine (mulCarry …) : GCoShape Nat` is reached by no finite Raw —
   `carry_is_nu_escape` (`gspine_escapes` at `L = Nat`): "the multiplicative residue is a νF escape"
   is now a *theorem*, the ring-operation image of `spineL_escapes` / `object1_not_surjective`.

## Still soft-open

3. The Lens reading: addition's carry is the difference-Lens **unit** (§6.7, the ±1 odometer);
   multiplication's carry is a **higher** count-Lens reading whose value itself escapes finite state.
   The shared invariant (the carry — one object, read at two depths: unit vs residue) is *named* in
   `mul_carry_nu_residue` and `the_one_carrier.md`; a Lens-level theorem (the carry as an explicit
   §6.7 readout) would close it fully.  An explicit linear lower bound `mulCarry ≥ c·k` (via
   `PositiveFloorUnbounded.positive_linear_exact`) would also sharpen item 1's witness from
   "unbounded" to "exactly linear".

## Cross-links

- `theory/essays/foundations/the_one_carrier.md` (the corrected narrative).
- `theory/essays/analysis/non_holonomicity_as_finite_state_escape.md` (the same escape, sequence scale).
- `research-notes/frontiers/sequence_depth/G188_multiplicative_conv_design.md` (the Hadamard/conv
  irreducibility — the coefficient-level mirror of "× is structurally heavier than +").
- `theory/essays/foundations/the_residue_unit_odometer.md` (addition's carry = the residue unit).
