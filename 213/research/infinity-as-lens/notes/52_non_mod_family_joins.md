# 52 — 비-mod family join 첫 예시: parityLens ⊔ boolXorLens = const

## 결과

`Research/ParityXorJoin.lean` (0 sorry, 0 axiom):

1. **`joinEquiv_parityLens_boolXorLens_universal`**: JoinEquiv
   parityLens boolXorLens r r' 가 임의 r, r' 에 대해 성립.
2. **`joinEquiv_leavesLens_boolXorLens_universal`**: JoinEquiv
   Lens.leaves boolXorLens r r' 도 universal.
3. `refine_parity_boolXor_implies_const` + `refine_leaves_boolXor_implies_const`:
   respective constant 귀결.

즉 parityLens, leaves, boolXorLens 의 pair 는 mod family 외부
에서도 concrete join = constLens 확정.

## 증명 구조

모든 r 에 대해 JoinEquiv r Raw.a 를 show → trans + symm.

### parityLens ⊔ boolXorLens

(parityLens.view r, boolXorLens.view r) 4 케이스:
- (T, T): ofM via boolXorLens (same a-parity odd)
- (T, F): ofL via parityLens (same total parity odd)
- (F, T): ofM via boolXorLens (same a-parity odd)
- (F, F): chain ofM via Raw.b + ofL via leaves=1 parity

### leaves ⊔ boolXorLens

boolXorLens.view r 2 케이스:
- T (a odd): ofM direct to Raw.a
- F (a even): chain ofM to Raw.b + ofL via leaves=1

## 남은 것

**비-mod 이면서 non-constant join** 예시 필요.  현재 발견한
비-mod pair 는 모두 universal.  이는 parity-like 정보
("mod 2" 의 변주) 가 서로 "coprime" 이기 때문.

가능한 non-trivial case:
- abLens + 무엇?: abLens 가 refines preorder 에서 많은 것
  아래 있어 incomparable pair 찾기 어려움.
- Non-Bool-valued 정보와 Bool-valued 의 결합: leaves +
  parityLens = parityLens (leaves refines parity).
- 완전 다른 structure 의 Lens: depth-based? (depthLens 는
  아직 catalogue 미정리).

## 의의

- Mod family: L_gcd 로 concrete, gcd ≥ 2 이면 non-trivial.
- 비-mod family: 지금까지 본 모든 경우 universal.
- **Non-trivial non-mod join** 은 open.

## 변경 이력

- 2026-04-24: parityLens ⊔ boolXorLens, leaves ⊔ boolXorLens
  모두 universal 확정.  비-mod family 첫 concrete join 예시.
