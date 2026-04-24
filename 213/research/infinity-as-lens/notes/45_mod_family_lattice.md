# 45 — Mod m family 는 refines preorder 의 divisibility 부분격자

## Refines preorder 의 첫 nontrivial sublattice

Lens kernel 공간에 `{leavesModNat m : m ≥ 2}` family 가 **ℕ의
divisibility lattice 와 isomorphic** 한 sublattice 로 embed.

## §1. Poset 구조

`LeavesModNat.lean`:

- `divides_refines` (forward): `k ∣ m → L_m refines L_k`.
- `refines_implies_divides` (converse, k ≥ 2): `L_m refines L_k → k ∣ m`.

결합: **`L_m refines L_k ↔ k ∣ m`**.

즉 refines 관계가 ℕ 의 divisibility 관계 (뒤집힘) 와 정확히
일치.

## §2. Meet (glb) = lcm

`L_m ∧ L_k = L_{lcm(m,k)}`.

**직관**: 둘 다 mod m 과 mod k 를 동시에 만족하는 kernel 은
CRT 로 mod lcm.

**prodLens 와의 관계**: `prodLens L_m L_k` 는 view 가 
`(leaves mod m, leaves mod k)`.  CRT 로 이는 `leaves mod lcm`
정보와 동치 → `prodLens L_m L_k ≈ L_{lcm(m,k)}`.

Meet 의 두 표현 (product 와 lcm) 이 같은 kernel 을 줌.

## §3. Join (lub) = gcd

`L_m ∨ L_k = L_{gcd(m,k)}`.

**직관**: 어느 쪽에서든 equivalence 인 두 Raw 는 TC 로
연결.  TC 는 mod gcd 의 equivalence.

- gcd(m, k) | m, gcd(m, k) | k → L_m refines L_gcd, L_k refines
  L_gcd (upper bound).
- Any N refined by both L_m 과 L_k 는 L_gcd 에 의해 refine 됨
  (least upper bound).

## §4. 특수 경우

- **m, k coprime**: gcd = 1.  `L_1.view r = 0` 상수.  Join
  = constLens.  "정보 합침 = 정보 소멸" 패러독스적 결과.
- **m | k**: gcd(m, k) = m, lcm = k.  둘은 이미 비교 가능.
  meet = L_k, join = L_m.

## §5. Lens 세계 전체에서의 위치

Mod family 는 작은 sublattice — **전체 refines preorder 는 더
큼**.  abLens, leafLens, boolXorLens 등은 mod family 와 
incomparable.

그러나 이 sublattice 의 존재는:
- refines preorder 가 **비자명한 distributive lattice 포함**
  (ℕ의 divisibility 는 distributive).
- Countable 무한 개의 distinct kernel 의 concrete 예.
- Join 이 **항상** constLens 로 collapse 하지 않음 (m | k
  같은 경우).  meet-semilattice 이상.

## §6. 지금까지 arc 의 lattice 완성도

| 관점 | 상태 |
|------|------|
| Bottom (⊥) | idLens 확정 |
| Top (⊤) | constLens 확정 |
| Meet | prodLens (universal) 확정 |
| Join (일반) | open — 구성 미완 |
| Join (mod family) | 이 노트에서 prose 확인, Lean 미검증 |
| Sublattice (mod) | divisibility isomorphic |

Join 의 일반 구성 (Q37.3) 은 Raw.toNat canonical minimum 으로
constructive 가능 (AC 불필요, note 44).  구현 부담 heavy.

## §7. 왜 이 sublattice 가 의미 있는가

**최소 구조에서 풍부한 arithmetic 구조 등장** 의 구체 예:

- Raw 공리에는 수가 없음.  "leaves count" 조차 Lens 출력.
- 그러나 Lens 공간 자체가 **ℕ 의 대수 구조** (divisibility
  lattice) 를 **sublattice 로 내재**.
- 수학의 기본 대수 구조가 공리 추가 없이 **Lens 평면 위에
  자연 출현**.

이는 note 42 §5 "Raw 의 풍부함의 객관적 측정" 의 또 다른 예.
minimal axiom 에서 standard mathematical infrastructure 의
대부분이 파생 가능함을 시사.

## §8. 다음

- **Lean 화**: `join_mod_gcd` 정리 (L_m ∨ L_k = L_gcd) +
  `meet_mod_lcm` (prodLens 와 L_lcm 동치).  둘 다 CRT 수준
  arithmetic 필요.
- **일반 Q37.3**: canonical 대표 선택으로 임의 Lens 의 join.
  `Raw.toNat` 이용.  Heavy 구현.
- **다른 sublattice 찾기**: abLens family (Nat × Nat) 가 어떤
  lattice 구조?  leafLens 주변?

## 변경 이력

- 2026-04-24: mod family 가 refines preorder 의 divisibility
  sublattice.  Lean `LeavesModNat.lean` 의 prose 확장.
