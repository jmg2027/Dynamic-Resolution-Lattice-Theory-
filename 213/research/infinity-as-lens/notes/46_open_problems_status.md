# 46 — 열린 문제들의 최종 상태

이 arc 마지막 정리.  각 열린 문제에 대한 해결 / 미해결 상태.

## ✓ 해결 (Lean 검증)

### swap_slash (기술적)

- **`Firmware/Raw/SwapSlash.lean`**: `Raw.swap_slash` 완전 증명.
- canonical form 의 case analysis, Tree.swap + Tree.cmp 의
  4 × 3 combination.
- **귀결**: `Research/SwapLens.lean` 의 swapLens (Raw.swap 이
  view 인 Lens) 구성 가능.  Raw 의 유일한 nontrivial
  automorphism 이 Lens 수준에서 실현됨.

### Join = gcd (specific case)

- **`Research/ModJoinExample.lean`**: `mod_4_6_refines_parity`.
- L_4.refines N ∧ L_6.refines N → L_2.refines N.
- Bezout chain: +6 (L_6) → -4 (L_4) = +2 step, induction on
  다수.
- **귀결**: Join(L_4, L_6) = L_gcd(4,6) = L_2 완전 확정
  (bounds + least direction 양쪽).

## 부분 해결 / 프레임워크 있음

### Join = gcd (일반 m, k)

- Bezout chain 패턴은 확립 (mod 4/6 예시).
- **Euclidean step (`ModJoinEuclidean.euclidean_step`) 형식화
  완료** (note 49): m > k ≥ 2, m - k ≥ 2 → L_m + L_k → L_{m-k}.
- 일반 m, k 의 uniform induction (strong rec on m+k) 은
  iteration bookkeeping 필요 — 아직 미완.
- **상태**: 한 step 완결, 전체 iteration 미완.

## ✗ 미해결 (heavy 하거나 open conjecture)

### Q37.3 일반 Quotient Lens

- 임의 Lens L 에 대해 Raw / L.equiv 의 canonical Lens 구성.
- Constructive 가능 (Raw.toNat minimum representative, note 44).
- 구현 heavy — subtype 또는 Quot 기반 + well-definedness
  verification.
- **상태**: 이론적 접근 명확, 구현 여유 필요.

### Lens kernel 공간 Cardinality

- 상한: 𝔠 (Raw 가 countable 이므로 equivalence 공간 최대 2^ℵ₀).
- 하한: 최소 countable 무한 (mod m family).
- 실제 값 미답.  Slash-congruence 의 structural 제약이
  countable 로 제한하는가?
- **상태**: open conjecture.

### Meta-213 Hierarchy (Lens on Lens)

- Lens α 의 type 을 codomain 으로 하는 Lens 의 natural 구성
  부재.
- `Lens α ≃ α × α × (α → α → α)` 이지만 자연 combine 없음.
- idLens 가 최소 Meta form (note 36) 이나 더 깊은 계층 불분명.
- **상태**: 개념 vague, 자연 구성 없음.

### Physics Chapter 감사

- Framework 준비 완료: fold-structured iff, slash-congruence
  특성화, meta-vocabulary = fudge 신호 (note 44).
- 별도 디렉토리 격리 (CLAUDE.md 지시).
- **상태**: 작업 대기.  다음 세션 후보.

## 진행 평가

**해결된 모든 건**: 각각 Lean 으로 0 sorry, 0 axiom 확인.
**남은 것들**: 이론 자체가 open (cardinality, hierarchy) 이거나
기술적 중량 (general join, quotient Lens).

Arc 의 **구조적 중심** 은 완성:
- Lens 의 dual 특성화 (kernel = fold-structured = slash-congruence).
- Refines preorder (⊥, ⊤, meet, mod sublattice).
- 선택 / 메타의 해소 (213 의 self-containment).

남은 것들은 **구조 확장** 이지 **이론 핵심** 은 아님.

## 변경 이력

- 2026-04-24: 열린 문제 최종 상태.  해결 / 부분 해결 /
  미해결 분류.  arc 의 구조적 완성도 평가.
