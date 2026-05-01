import E213.Firmware.Raw

/-!
# Research.RawDecEq: DecidableEq Raw

Since `Tree` has `deriving DecidableEq` and `Raw` is
`{t : Tree // canonicalBy t = true}`, equality on `Raw` is also
decidable.  Explicit formalization of the 1-line claim in PAPER1 §2.3.

## Significance

The precondition `x ≠ y` of `Raw.slash` is *constructive* —
the elaborator can produce a witness.  Decidability is carried as
data; no external LEM.
-/

namespace E213.Firmware.Raw.DecEq

open E213.Firmware

/-- Equality on `Raw` is decidable. -/
instance : DecidableEq Raw := by
  intro x y
  match h : decEq x.val y.val with
  | isTrue heq => exact isTrue (Subtype.ext heq)
  | isFalse hne => exact isFalse (fun heq => hne (congrArg Subtype.val heq))

end E213.Firmware.Raw.DecEq
