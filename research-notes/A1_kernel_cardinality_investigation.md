# A1 — Lens-kernel cardinality: investigation log (2026-04-26)

## 문제

PAPER1 §5.4 의 open question: Lens-kernel space 의 cardinality
의 uncountable lower bound.

## 시도 한 angle 들

### A.1 leavesModNat-intersection family
For each f : Nat → Bool, define
  E_f := λ r r'. ∀ n, f n = false ∨
                       leavesModNat (n+2) view r = view r'.

**관찰**: E_f 는 slash-congruence (intersection of
slash-congruences).

**문제**: intersection of {leavesModNat m : m ∈ S} =
leavesModNat (lcm S).  서로 다른 S 가 같은 lcm 을 줄 수
있음 ({2,3,6} 와 {6} 모두 lcm = 6).  → countable many
distinct kernels (one per natural number lcm).

### A.2 Function-space Lens via pointwise combine
For each f : Nat → Bool, define L_f : Lens (Nat → Bool) with
combine = pointwise xor (or ∧, ∨).

**문제**: pointwise xor 의 경우, kernel 이 (count_a mod 2,
count_b mod 2) 의 leaf parity Lens 로 collapse — f 와
무관.  Pointwise ∧/∨: Raw 가 {Raw.a, Raw.b, slash-stuff}
의 3 class 로 collapse, f 와 무관.

### A.3 f-dependent combine (if-then-else gate)
For each f, combine x y := if f n then x n ∧ y n else x n ∨ y n.

**관찰**: kernel 이 f 에 따라 약간 변함 (Raw.a, Raw.b
와 slash 의 view 가 const-true/const-false 으로 collapse
하면 서 f 가 그 안에 들어감).

**문제**: 대부분 의 distinct f 가 결국 같은 partition 을
유도.  Continuum 분리 부재.

## 결론 (잠정)

위 세 angle 다 fundamental obstruction:

- Slash-compatibility 가 kernel 의 self-similar structure 를
  강제 — 임의 f 의 정보 가 kernel 에 leak 되 는 channel 부재.
- Bool-valued fold-structured 함수 자체 가 countable
  (BoolSqClassification: 4 class × base values).
- Higher-codomain Lens 도 view function 이 fold-structured
  로 제약 받음 — 그 자체 가 countable many "shapes".

## Open status

- 정말 K 가 countable 일 수 있음 (slash-congruences on Raw
  가 fold-structured 라는 강제 가 partition 의 자유 도 제한).
- 또는 더 정교 한 construction (e.g., higher-order Lens
  tower 에서 의 distinct kernel) 이 continuum 줄 가능.

다음 시도 candidate:
- **Recursive Lens^n α tower** (LensOnLensImage 에서 collapse
  가 이미 관찰 됨 — 단순 한 case 는 안 됨).
- **Sum/Product 의 자유 결합**: Lens (α × β) 가 (Lens α) ×
  (Lens β) 보다 더 큰 space 인지.
- **Cantor diagonalization ON the kernel space directly**:
  슬슬 LEM-flavor 가 들어갈 수 있어 risky.

## ROI 평가

부분 결과 (countable lower bound 는 이미 PAPER1 §5.4 +
KernelCardinalityLB).  Uncountable lower bound 의 결정 적
증명 또 는 반증 은 더 큰 작업.

이 note 는 invest 한 시간 의 record + 다음 시도 의 starting
point.  당분간 status = open.
