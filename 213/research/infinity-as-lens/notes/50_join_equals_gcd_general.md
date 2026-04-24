# 50 — 일반 join = gcd (임의 m, k ≥ 2)

## 결과

`Research/ModJoinGCD.lean`:

**`join_refines_gcd`** (0 sorry, 0 axiom):

```
theorem join_refines_gcd {α : Type} (N : Lens α) (m k : Nat)
    (hm : m ≥ 2) (hk : k ≥ 2)
    (hLm : (leavesModNat m).refines N)
    (hLk : (leavesModNat k).refines N) :
    (leavesModNat (Nat.gcd m k)).refines N
```

임의 m, k ≥ 2 에서 `L_m + L_k → L_{gcd(m,k)}`.  Refines preorder
의 **least upper bound characterization** (gcd 이 universal
upper bound).  특수 경우 (4, 6), (2, 3), consecutive 와 일관.

## 구조

Strong induction on `s = m + k`, `m ≥ k` 정렬 auxiliary 로:

1. m = k: gcd = m, L_m.refines N 직접.
2. m > k, m - k = 1 (consecutive): N constant (consecutive_refines_const),
   gcd = 1, L_1.refines N = N const.
3. m > k, m - k ≥ 2: euclidean_step 으로 L_{m-k}.refines N.
   재귀. Sum 엄격 감소: (m-k) + k = m ≤ n (since k ≥ 2).
   m - k ≥ k 일 때 (m-k, k), 아닐 때 (k, m-k) 로 정렬 유지.

메인: 외부에서 Nat.gcd_comm 으로 swap 처리.

## Lean core 만으로 달성

- Nat.gcd_rec (core 에 존재)
- Nat.gcd_comm, Nat.gcd_self
- Nat.mod_one, Nat.add_mod_right
- strong induction via `succ n ih` pattern

## Bezout 없이

Note 주목: 전형적 join = gcd 증명은 Bezout identity
(`a m + b k = gcd m k` with integer coefficients) 을 사용.
하지만 Lean core 에는 Nat.xgcd 가 없고 Bezout 구현은 heavy.

대신 **Euclidean algorithm 의 subtraction form** 을 직접
iterate 해서 같은 결과 도달.  각 step 이 `L_m + L_k → L_{m-k}`
Lens refinement 수준에서 작동하면 충분.  Bezout coefficient
explicit 구성 불필요.

## Mod family 의 Lattice 구조 완성

`LeavesModNat.gcd_upper_bound` (L_m, L_k ⊏ L_gcd) +
`join_refines_gcd` (L_gcd 가 upper bound 중 least):

⟹ **gcd 이 L_m, L_k 의 join** (refines preorder 에서).

또한:
- `LeavesModNat.lcm_lower_bound` (L_lcm ⊏ L_m, L_k):
  lcm 이 lower bound.  Meet 으로도 least lower bound
  (prodLens universal property 로 확립됨).
- gcd 이 join, lcm 이 meet: **mod family 는 distributive
  lattice isomorphic to (Nat, ∣)-order** (divisibility).

## 남은 것

- **Concrete Lens quotient** (Q37.3): JoinEquiv 의 canonical
  Lens 구성은 여전히 open (note 48).  단 mod family 안 에서는
  모든 join 이 이미 L_gcd 로 specific Lens.
- **Non-mod family Lens 사이의 join**: 일반 Lens L, M 의 join
  은 JoinEquiv 수준 universal property 만 확립.  Concrete
  Lens instance 는 pair-by-pair.

## 변경 이력

- 2026-04-24: 일반 join = gcd 확정 (임의 m, k ≥ 2).
  Bezout 우회, Euclidean subtraction iterate.
