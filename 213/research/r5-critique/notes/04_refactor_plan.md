# 04 — Architecture refactor plan (B option)

After user's architectural advice:
- `private inductive` causes elaboration explosion when all
  proofs accumulate in one file (Raw.lean took 1+ hour).
- Solution: `@[eliminator] def Raw.rec` exposes a clean
  Raw induction principle so consumers can write their own
  induction proofs without touching Tree.

## Current state (this session)

✓ **Spec/Impl typeclass hierarchy** (`Meta/SelfRecognising.lean`):
- `R12Codomain` (R1+R2: combine + commutativity)
- `R3Codomain extends R12Codomain` (no zero divisors)
- `R4Codomain extends R3Codomain` (conj swap-matching)
- Generic `specLens`, `specLens_nonVanishing`,
  `specLens_swapMatching` proved once per tier.

✓ **ZI / Z2 instances** updated to `R4Codomain` (single
14-line instance, all R3+R4 theorems inherited).

✗ **Tree internalisation attempt failed.** De-privatising
Tree triggers elaboration mismatch in `Tree.cmp_eq_iff`'s
`Ordering.noConfusion` invocation — Lean 4 changes
how `noConfusion` is synthesised when Tree is no longer
private.  Reverted.

## Next-session plan (B option)

**Keep `private inductive Tree` in Raw.lean** but add
`@[eliminator] def Raw.rec` so external consumers write
their own Raw induction without Tree access.  The
`@[eliminator]` attribute makes `induction r` and `match r`
use `Raw.rec` instead of `Tree.rec`.

```lean
-- Sketch (inside Raw.lean, after Raw.fold)
@[eliminator]
def Raw.rec {motive : Raw → Sort u}
    (a_case : motive Raw.a)
    (b_case : motive Raw.b)
    (slash_case : ∀ (x y : Raw) (h : x ≠ y),
                  motive x → motive y →
                  motive (Raw.slash x y h)) :
    ∀ r, motive r := by
  intro r
  obtain ⟨t, hcanon⟩ := r
  induction t with
  | a => exact a_case
  | b => exact b_case
  | slash x y ihx ihy =>
      -- decompose hcanon, show ⟨.slash x y, _⟩ = Raw.slash x' y' h
      sorry  -- subtype-induction subtleties to resolve
```

## Once Raw.rec is in place

- Move `Raw.fold_signed_swap` and `Raw.fold_swap_hom` from
  `Firmware/Raw.lean` to `Meta/FoldSwapHom.lean` — they only
  need Raw.rec, not Tree.
- Firmware shrinks; Meta absorbs use-case-specific helpers.
- New use cases (e.g. ZOmega's `fold_omega_swap`) can be
  added in their own modules without touching firmware.

## Why this matters for E1–E3

ZIInstance / Z2Instance currently work via the existing
`Raw.fold_swap_hom`.  This will continue to work.  But further
extensions (general field-extension family parameterised on
`D` such that `K = ℤ[√-D]`) would hit pattern repetition.
Raw.rec + the spec class let any future codomain plug in
cleanly.

## Estimated work

- Raw.rec definition: ~30 lines, ~1 hour to debug
  (subtype-induction subtleties).
- Move signed_swap / swap_hom to Meta: ~50 lines, trivial.
- Verification needs full Raw build (~1 hour on this host).

Best done in dedicated session with longer timeout window.
