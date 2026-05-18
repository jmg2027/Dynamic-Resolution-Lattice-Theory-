import E213.Lens.Bool213.Raw
import E213.Lens.Bool213.System

/-! Spec-as-code entry point for `E213.Lens.Bool213`.

  213-native Boolean — Raw-encoded closed-universe Bool.  Two
  modules:

    * `Raw`     — Method A 카타모피즘 (T = Raw.a, F = Raw.b).
                  `booleanProj := Raw.fold T F and` 의 closed-Raw
                  codomain catamorphism — Raw-internal vertical
                  projection onto the two-element form {T, F}.
                  not / and / boolValue / fixed-point 특성화.
                  (Post-Option-C: 이 패턴은 Bool213 / RawCut /
                  CauchyCutSeq 에서 살아 있고, Nat213 은 Nat 측
                  projection 으로 옮겨감.)
    * `System`  — 메타 (T, F) 패턴.  임의의 distinct Raw 쌍이
                  valid system; system 간 iso 가 not / and 보존.
                  Nat213 의 `NumberingSystem` 과 평행.

  Migrated 2026-05-14 from `Theory.Closed.{Bool213, Bool213System}`
  — Raw + 카타모피즘 = Lens 레이어 산물 (Nat213 이전과 동일 원칙).

  All theorems ∅-axiom.
-/
