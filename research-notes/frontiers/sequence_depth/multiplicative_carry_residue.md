# Frontier — the multiplicative carry as a νF inhabitant (the residue of ×)

Status: **open** (the closed part is in `lean/E213/Lib/Math/NumberSystems/Padic/NuEscape.lean`).

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

## The open frontier

The multiplicative residue is currently characterized *negatively* (`mulRaw_unbounded`: no constant
bounds the carry).  The conjecture: the carry stream itself is a **νF inhabitant** — reached by no
finite Raw — exactly as `spineL` is, with `Zp.mulCarry`'s linear growth the arithmetic image of the
odometer overflow `allTrue_carry_forever` / `odo_allTrue` (`Theory/Raw/Odometer`).

Concretely, candidate theorems:
1. `mulCarry (-1)(-1)` is monotone-and-unbounded with an explicit lower bound (e.g. `≥ c·k`),
   tightening `mulRaw_unbounded` from "the convolution" to "the carry" itself.  (The
   `PositiveFloorUnbounded.positive_linear_exact` engine — positive constant difference ⟹ exact
   linear formula — is the likely tool, since `mulRaw(k+1)−mulRaw(k) = (p-1)²`.)
2. The carry stream `fun k => Zp.mulCarry p x y k`, spined via `boolSpine`/`gspine`, is reached by
   no finite Raw — making "the multiplicative residue is a νF escape" a *theorem*, the ring-operation
   image of `spineL_escapes` / `object1_not_surjective`.
3. The Lens reading: addition's carry is the difference-Lens **unit** (§6.7, the ±1 odometer);
   multiplication's carry is a **higher** count-Lens reading whose value itself escapes finite state.
   Name the shared invariant precisely (the carry — one object, read at two depths: unit vs residue),
   not a bare `+`/`×` analogy.

## Cross-links

- `theory/essays/foundations/the_one_carrier.md` (the corrected narrative).
- `theory/essays/analysis/non_holonomicity_as_finite_state_escape.md` (the same escape, sequence scale).
- `research-notes/frontiers/sequence_depth/G188_multiplicative_conv_design.md` (the Hadamard/conv
  irreducibility — the coefficient-level mirror of "× is structurally heavier than +").
- `theory/essays/foundations/the_residue_unit_odometer.md` (addition's carry = the residue unit).
