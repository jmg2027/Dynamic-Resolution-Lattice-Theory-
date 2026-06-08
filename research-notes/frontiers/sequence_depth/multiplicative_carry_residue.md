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

3. ✅ **The "one schema" question** (is there a single ∅-axiom term with `gspine_escapes` /
   `carry_is_nu_escape` / `object1_not_surjective` as instances-by-parameter?) — **answered, with
   an honest limit.**  `CoResidue.escape_by_invariant` (§22) is the schema: an inhabitant lacking a
   property `P` that every cover-image has is in the image of none.  The number- and operation-carry
   escapes are *literally* this schema (`gspine_escapes_via_schema`, cover `gToShape a b`, `P` =
   "all-`false` path hits a leaf"), at alphabets `Fin p` / `Nat`.  **Cantor (`object1_not_surjective`)
   is the *sibling*, not an instance** — it is the diagonal-flip flavor (escapee differs pointwise,
   no single `P`).  So scale-invariance is a theorem across the invariant-escapes and a *twinning*
   with the diagonal-flip; a single term subsuming *both* flavors does not exist (the two
   non-surjection flavors are genuinely distinct) — which is itself the honest residue of the
   unification act.

## Still soft-open

4. The Lens reading: addition's carry is the difference-Lens **unit** (§6.7); multiplication's carry
   a **higher** reading that escapes finite state.  A Lens-level §6.7 readout theorem would name it
   fully.  Explicit linear lower bound: `mulCarry (-1)(-1) (k+1) ≥ (k+1)(p-1)²/p` is immediate from
   `mulCarry_ge_mulRaw_div` + `mulRaw_negOne_negOne` (the carry post-`/p` is not constant-difference,
   so `positive_linear_exact` applies to `mulRaw`, not directly to `mulCarry`).

## Note — ℝ is *not* a clean not-finite-state theorem (Advance-A correction)

Investigated: ℝ's cut decision is **not** cleanly "not finite-state" the way `×` is.  `cutBits r N =
orderProj 1 (N+1) (view (r.xs N))` reads only `r.xs N` (so the "agree on the prefix, differ at N"
statement is satisfied even by a *memoryless* transducer — it does not capture not-finite-state),
and for a fixed positive real `1/(N+1) → 0` makes `cutBits r` *eventually constant*.  ℝ's
"transport-only / presentation-dependent / order-based" status is an honest *structural* observation
(kept as prose in `the_one_carrier.md`), **not** a `mulCarry_unbounded`-style theorem.  A genuine
ℝ not-finite-state result would need a transducer/unbounded-modulus framework — a larger frontier,
not a quick theorem.

## Cross-links

- `theory/essays/foundations/the_one_carrier.md` (the corrected narrative).
- `theory/essays/analysis/non_holonomicity_as_finite_state_escape.md` (the same escape, sequence scale).
- `research-notes/frontiers/sequence_depth/G188_multiplicative_conv_design.md` (the Hadamard/conv
  irreducibility — the coefficient-level mirror of "× is structurally heavier than +").
- `theory/essays/foundations/the_residue_unit_odometer.md` (addition's carry = the residue unit).
