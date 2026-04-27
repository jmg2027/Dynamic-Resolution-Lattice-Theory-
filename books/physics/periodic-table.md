# 주기율표 213 — Narrative

표준 chemistry 의 주기율표 = 양자수 (n, l, m, s) + Madelung
filling 가정.  DRLT 213 은 *모두 atomic primitives 표현*.

## 핵심 발견

모든 noble gas (period closure) atomic:

  Period 1 (Z=2)   He = NT
  Period 2 (Z=10)  Ne = d·NT
  Period 3 (Z=18)  Ar = 2·NS²
  Period 4 (Z=36)  Kr = (NS·NT)²    ★ 같은 6=NS·NT 의 제곱
  Period 5 (Z=54)  Xe = 2·NS³
  Period 6 (Z=86)  Rn = 2·NS³ + NT^d
  Period 7 (Z=118) Og = 2·NS³ + 2·NT^d
  Period 8 (Z=168) [예측] = HO magic 7 = n(n+1)(n+2)/3

## IE 정밀도

  H   4.3 ppb formal Lean
  He  138 ppm  (4·R · (1/NT - 2α_GUT))
  Li  113 ppm  (R · 25/64 · P(x))
  Be  493 ppm  (P(x/2))
  B   1046 ppm

P(x) = (1+2x)/(1+x), x = α_GUT·NS/d atomic.
Same closed propagator 가 m_p, m_H, Ω_Λ, IE 모두 적용.

## Hund 규칙 atomic

  ε_pair = R · NS/(NS²-1) = R · α_3 · NS = R · 3/8

  같은 α_3 = 1/8 이 strong coupling + Hund penalty.

## 사용

```lean
import E213.Physics.Phase4.Library.CompletePeriodicTable
```

## 형식 보장

  - 113 원소 + 5 super-heavy 모두 atomic 검증
  - Period closures 7 + 1 예측 모두 atomic
  - Hund 규칙 atomic Lean 정리 (0 axioms)
  - 표준 quantum number 차용 부재

## 참조

  blueprints/physics/01_atomic_physics_213.md
  catalogs/periodic-table.md
  lean/E213/Physics/Phase4/Library/CompletePeriodicTable.lean
