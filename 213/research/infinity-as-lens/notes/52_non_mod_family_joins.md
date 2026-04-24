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

## 비-mod non-trivial join 발견 (2026-04-24)

**`Research/LeavesDepthJoin.lean`**:
- `leaves_depth_join_not_universal`: JoinEquiv Lens.leaves
  Lens.depth 는 Raw.a 와 Raw.slash Raw.a Raw.b 를 분리.
- 즉 **leaves ⊔ depth ≠ constLens** — 비-mod family 에도
  non-trivial (non-universal) join 존재.

핵심 invariant: `small r := leaves r = 1`.  small 은 JoinEquiv
하에 preserved (leaves-equiv, depth-equiv 모두 small/¬small
를 mix 하지 않음, slash_cong output 항상 ¬small).

Raw.a 는 small (leaves=1), Raw.slash Raw.a Raw.b 는 ¬small
(leaves=2).  따라서 JoinEquiv 분리.

## 일반 패턴

비-mod family 에서 join 이:
- Universal (constLens): parity + boolXor, leaves + boolXor.
  두 Lens 의 정보가 "coprime" 해서 chain 으로 모든 Raw 연결.
- Non-universal: leaves + depth.  두 Lens 둘 다 counts (leaves,
  depth 값 범위) 정보를 가져, "small" 같은 invariant 존재.
  따라서 classes 분리 유지.

## 의의

- Mod family: L_gcd 로 concrete, gcd ≥ 2 이면 non-trivial.
- 비-mod family: 지금까지 본 모든 경우 universal.
- **Non-trivial non-mod join** 은 open.

## 변경 이력

- 2026-04-24: parityLens ⊔ boolXorLens, leaves ⊔ boolXorLens
  모두 universal 확정.  비-mod family 첫 concrete join 예시.
