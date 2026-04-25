# 54 — Open problems 최종 상태 (Session 5 종합)

이 arc 의 모든 open problem 의 final disposition.

## ✅ 완전 해결 (Lean 0 sorry, 0 axiom)

### Join = gcd 일반 m, k

`Research/ModJoinGCD.join_refines_gcd`: 임의 m, k ≥ 2 에서
L_m + L_k → L_{gcd m k}.  Strong induction on m + k, Euclidean
subtraction (Bezout 우회).

### Mod family Q37.3 (concrete Quot Lens)

`Research/ModJoinEquivGCD.gcd_equiv_joinEquiv`: L_gcd.equiv ↔
JoinEquiv L_m L_k on Raw × Raw.  L_gcd 가 mod family 내
JoinEquiv 의 concrete realization.

### 비-mod family join 첫 예시들

- `Research/ParityXorJoin`: parityLens + boolXorLens = const,
  leaves + boolXor = const.  4-case 분석 chain.
- `Research/LeavesDepthJoin`: leaves + depth ≠ const.  3 tier
  classes (small, leaves=2, leaves≥3) 분리.  tierLens 가
  concrete upper bound.

### Lens kernel space lower bound

`Research/KernelCardinalityLB.leavesModNat_kernel_neq`: m ≠ k
(둘 다 ≥ 2) → 두 mod Lens kernel 다름.  따라서 |kernel space|
≥ ℵ₀ formal.

### Meta-213 hierarchy (해소)

Note 53: Lens (Lens α) 의 자연 combine 부재 = hierarchy 의
**자연 부재 증명**.  pointwise sum 등 시도 fold-structured
아님.  idLens + Yoneda-dual 로 self-reference 충분.

## 📋 Open 으로 남는 (genuine open, falsify 아님)

### Q37.3 arbitrary slash-congruence

임의 abstract slash-cong E 에 대한 concrete Lens 구성.
Decidable E 의 경우 Quot E 기반 가능 (representative picking
+ diagonal fallback) 이지만 well-definedness 가 case-by-case.
일반 abstract E (non-decidable) 는 더 heavy.

**Note**: per note 44, "decidability 자체가 Lens specification"
이므로 Q37.3 는 추가 Lens-info 요구로 환원.  213 framework
내에서 일관된 open problem.

### Lens kernel space exact cardinality

ℵ₀ ≤ |kernel space| ≤ 𝔠 확정.  정확한 값 미답.

상한 𝔠: Raw 가 countable (Σ2, Σ3) → equivalence 관계 ≤
2^(ℵ₀×ℵ₀) = 𝔠.  Lens kernel 은 slash-cong 제약으로 더 적음.

하한 ℵ₀: mod family (위).

중간 값 (e.g. 𝔠 lower bound 직접 construction) 시도했으나
slash-cong + α-bijection 재할당 등으로 인해 직접 injective
family 구성 어려움.

### Physics chapter audit

CLAUDE.md 지시: 별도 directory 격리.  본 arc 외 별도 작업.

## 정리

**구조적으로 본 arc 는 완결**:
- Lens 의 dual 특성화 (kernel = fold-structured = slash-cong).
- Refines preorder (⊥, ⊤, meet, mod sublattice = gcd-lcm lattice).
- Join 의 universal property (JoinEquiv).
- Mod family 의 concrete join = gcd realization.
- 비-mod family non-trivial join 예시.
- Cardinality lower bound 형식화.
- Meta hierarchy 해소.
- 선택 / 메타의 Lens 환원 (note 44).

**남은 것은 본질적으로 "더 큰 분류"**:
- 일반 Quot Lens 는 case-by-case.
- 정확한 cardinality 는 분류 문제.
- Physics audit 은 별도 도메인.

213 framework 자체는 self-consistent + 0 axiom 으로 Lean
검증 완료.

## 변경 이력

- 2026-04-24: open problems 최종 상태.  본 arc 의 구조적
  완결성 확인.  남은 문제들은 falsify-condition 위반 아님.
