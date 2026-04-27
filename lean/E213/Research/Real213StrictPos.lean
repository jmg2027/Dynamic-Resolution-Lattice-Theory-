import E213.Research.Real213
import E213.Research.PellSeq
import E213.Research.DiagonalHasModulus

/-!
# Research.Real213StrictPos: addition-friendly subtype (E2 의 해 결책 (i))

`E2_phase_b_obstruction.md` 의 obstruction 해 결: Real213 의
sequence 가 *모든 i 에 서* view (a, b) with a, b ≥ 1.

이 subtype 위 에 서 는 addition 의 sum view = (a*b' + a'*b, b*b')
가 항상 ≥ (2, 1) → abLens_witness 로 lift 가능.

## 정의

```
structure Real213StrictPos extends Real213 where
  view_pos : ∀ i, 1 ≤ (abLens.view (xs i)).1 ∧ 1 ≤ (abLens.view (xs i)).2
```

## 의의

- Real213 의 *engineering refinement* (axiom 추가 부재).
- Phase B (arithmetic) 가 이 subtype 위 에 서 작업.
- Real213 ↔ StrictPos 의 cut-equivalence 호환 은 별 도 작업
  (모든 Real213 이 StrictPos 의 *equivalent* 가 짐 — 가능 하 지 만
  proof 는 sequence reshuffling).
-/

namespace E213.Research.Real213

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- Real213 with all sequence views strictly positive ((a, b) with a, b ≥ 1). -/
structure Real213StrictPos extends Real213 where
  view_pos : ∀ i, 1 ≤ (abLens.view (xs i)).1 ∧ 1 ≤ (abLens.view (xs i)).2

end E213.Research.Real213

namespace E213.Research.Real213

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- Diagonal sequence: xs n = Raw with view (n+1, n+1) via abLens_witness. -/
def diagonalRaw (n : Nat) : Raw :=
  (E213.Research.PellSeq.abLens_witness ((n+1) + (n+1)) (n+1) (n+1)
    rfl (Nat.succ_le_succ (Nat.zero_le _))
    (Nat.succ_le_succ (Nat.zero_le _))).1

theorem diagonalRaw_view (n : Nat) :
    abLens.view (diagonalRaw n) = (n+1, n+1) :=
  (E213.Research.PellSeq.abLens_witness ((n+1) + (n+1)) (n+1) (n+1)
    rfl (Nat.succ_le_succ (Nat.zero_le _))
    (Nat.succ_le_succ (Nat.zero_le _))).2

/-- Diagonal sequence 가 Real213StrictPos instance — concrete inhabitance. -/
def diagonalReal : Real213StrictPos where
  xs := diagonalRaw
  modulus := E213.Research.DiagonalHasModulus.diagonalHasModulus diagonalRaw diagonalRaw_view
  view_pos := by
    intro n
    rw [diagonalRaw_view]
    exact ⟨Nat.succ_le_succ (Nat.zero_le _),
           Nat.succ_le_succ (Nat.zero_le _)⟩

end E213.Research.Real213
