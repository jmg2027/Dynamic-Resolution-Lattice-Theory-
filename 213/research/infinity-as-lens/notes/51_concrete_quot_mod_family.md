# 51 — Concrete Quot Lens (mod family): L_gcd = JoinEquiv

## 결과 (Q37.3 의 mod family 한정 완전 해결)

`Research/ModJoinEquivGCD.lean`:

**`gcd_equiv_joinEquiv`** (0 sorry, 0 axiom):

```
theorem gcd_equiv_joinEquiv (m k : Nat) (hm : m ≥ 2) (hk : k ≥ 2)
    (r r' : Raw) :
    (leavesModNat (Nat.gcd m k)).equiv r r' ↔
      JoinEquiv (leavesModNat m) (leavesModNat k) r r'
```

즉 **L_gcd 는 JoinEquiv L_m L_k 의 concrete Lens realization**
(mod family 한정).

## 의의

Note 48 의 "concrete Quot Lens construction" open problem 의
**중대한 진전**:

- 일반 Lens L, M 에 대해서는 여전히 open (Raw.toNat 기반
  canonical rep 필요, decidability 문제).
- 하지만 **mod family 내부** 에서는 JoinEquiv 가 항상 concrete
  Lens (L_gcd) 로 realize 됨.
- 이는 Classical.choice 없이 순수 constructive 하게 달성.

## 구조

Chain 증명을 JoinEquiv level 로 복원:

1. `chain_step_sub_JE`: +(m-k) step 의 JE version.  Intermediate
   Raw w (leaves = leaves r + m) 를 via `leaves_surjective_pos`.
   `ofL (r ~_m w) + ofM (w ~_k r')` + trans.
2. `step_plus_nd_JE`: +n(m-k) chain iteration.
3. `euclidean_step_JE`: L_{m-k}.equiv r r' → JoinEquiv L_m L_k r r'.
4. `consecutive_refines_all_JE`: m = k+1 → any r, r' 가 JoinEquiv.
5. `lift_sub_JE`: JoinEquiv L_{m-k} L_k → JoinEquiv L_m L_k.
   JE inductive on constructors.
6. `swap_JE`: JoinEquiv 의 L, M 교환 symmetry.
7. `join_eq_gcd_JE_sorted`: strong induction on m + k, m ≥ k.
8. `gcd_subset_joinEquiv`: 외부 swap 처리.

## ⟺ 증명 두 방향

- **← (JoinEquiv → L_gcd.equiv)**: `joinEquiv_subset_gcd`
  (ModJoinGCD).  `JoinEquiv_is_least` + `gcd_upper_bound` 의
  직접 귀결.  L_gcd 가 L_m, L_k 의 refinement target 이고
  combine 대칭이므로, JoinEquiv 의 universal property 로 포함.
- **→ (L_gcd.equiv → JoinEquiv)**: `gcd_subset_joinEquiv`
  (이 파일의 메인 결과).  Chain 구조를 JoinEquiv level 에
  복원해 construct.  Heavy 하지만 직접적.

## 남은 open problem

- **일반 Lens L, M (mod family 밖)**: 예컨대 leaves Lens 와
  boolXorLens, parityLens 와 같은 다른 Lens 의 join.  각
  specific pair 마다 concrete Lens 찾기.  pattern 은 "양쪽을
  refine 하는 것들 중 least".  일부 pair 는 이미 known (e.g.
  leaves 와 parity 의 join 은 leaves, since leaves refines
  parity).
- **일반 Quot Lens 존재 (arbitrary slash-congruence)**:
  note 48 의 Raw.toNat 기반 canonical rep 접근.  Decidability
  가 bottleneck.

## Q37.3 현 상태

- ✓ Abstract JoinEquiv 존재 (inductive, universal property).
- ✓ Mod family 의 concrete realization (L_gcd).
- 부분 해결 → 중대한 진전.
- 일반 Lens 는 case-by-case 또는 Raw.toNat extension 필요.

## 변경 이력

- 2026-04-24: Mod family 에서 L_gcd = JoinEquiv 증명.  Q37.3
  partial resolution 의 quantitative 진전.
