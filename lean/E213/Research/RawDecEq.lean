import E213.Firmware.Raw

/-!
# Research.RawDecEq: DecidableEq Raw

`Tree` 가 `deriving DecidableEq` 이고 `Raw` 가 `{t : Tree //
canonicalBy t = true}` 이므로, `Raw` 의 equality 도 decidable.
PAPER1 §2.3 의 1-line claim 의 explicit formalization.

## 의의

`Raw.slash` 의 precondition `x ≠ y` 가 *constructive* —
elaborator 가 witness 를 produce 가능.  Decidability 가
data 로 carry, 외부 LEM 부재.
-/

namespace E213.Research.RawDecEq

open E213.Firmware

/-- `Raw` 의 equality 가 decidable. -/
instance : DecidableEq Raw := by
  intro x y
  match h : decEq x.val y.val with
  | isTrue heq => exact isTrue (Subtype.ext heq)
  | isFalse hne => exact isFalse (fun heq => hne (congrArg Subtype.val heq))

end E213.Research.RawDecEq
