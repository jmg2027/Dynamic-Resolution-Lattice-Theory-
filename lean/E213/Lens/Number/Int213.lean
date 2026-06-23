import E213.Lens.Number.Int213.Raw

/-! Spec-as-code entry point for `E213.Lens.Number.Int213`.

  Int213 — ℤ seen from the `⟨1, -1, +⟩` lens view of Raw.

  **The point**: if Nat213.Raw is the `Lens.leaves = ⟨1, 1, +⟩` view of Raw,
  then Int213.Raw is the `signedLens = ⟨1, -1, +⟩` view of the same Raw.  Same
  Raw, different lens — no new type is introduced.

  ## Sub-modules

    * `Raw` — definition of signedLens `⟨1, -1, +⟩ : Lens Int` + view (`value`),
              negation (`Raw.swap`, `value_neg`), lens-induced equivalence
              (`equiv`).  Canonical minimal-leaves representatives:
              `zero = slash a b`, `one = Raw.a`, `negOne = Raw.b`.

  ## The precise reason ℤ is lens-emergent

  Assigning a sign of ±1 to the two atoms (a, b) of Raw + slash acting as
  addition + Raw.swap acting automatically as a (-1)-multiplier (already proved
  by `Raw.fold_signed_swap`).  No extra quotient, no extra sum-type, and nothing
  added to the axiom set is needed — the Lens framework handles the quotient
  meaning automatically.

  ## Multiple Raws → same ℤ (the lens is many-to-one)

  There are infinitely many Raws with `value r = 0` (slash a b, slash a (slash b
  (slash a b)), ...).  This is not a problem but *the essence of the lens* — for
  Nat213.Raw too there are several Raws with the same leaves count, handled by
  `Lens.equiv` (Lens-induced equality).  The quotient of ℤ is likewise handled
  by `signedLens.equiv`.

  ## Parallel ℤ-constructions (this codebase)

    * `Lens.Number.Nat213.Tower.NatPairToInt` — ℕ × ℕ diagonal
      quotient (framing).  A pair-and-quotient construction.
    * `Lens.Number.Int213.Raw` (this file) — the direct lens-view of Raw.
      ℤ emerges naturally from atom-level sign assignment.

  All theorems ∅-axiom.
-/
