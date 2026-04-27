# Falsifiability — 213 폐기 조건

(AXIOM.md §5.2.1 정수)

## 기본 원칙

  213 의 모든 결과는 Lean 4 core + Raw 공리 만으로 derive
  가능해야 함.

## 폐기 조건

  *어떤 결과가 공리 추가 없이 절대 불가능* 하다고 밝혀지면,
  **213 이론 전체 폐기**.  해당 결과만 포기 가 아님.

이는 Raw 공리가 *최소 잔여물* 이라는 §1 선언의 직접 귀결:
공리 추가가 정말 필요하면 Raw 가 최소가 아니었던 것.

## 운영 원칙

- Classical, LEM, native_decide 등 외부 axiom 추가 일절 금지.
- 막히는 결과는 "open" 으로 두되, *영구적 벽 vs 일시적 난관*
  감별.  영구적 벽이면 이론 실패 선언.
- Lean 검증 = falsifiability 의 기계적 감사관.

Mingu 확정 (2026-04-24).  *절대 완화 안 됨*.

## 측정 falsifier (CLAUDE.md 검증 기준 2)

213 은 *형식화 되어 아무도 딴지 못 할 새 물리* 를 동시에
제공해야 함.

각 *측정 가능* 정수 가 *atomic-forced*:

| 측정 | 시기 | DRLT 예측 | 위반 시 |
|---|---|---|---|
| Neutrino ordering | JUNO ~2030 | normal | 폐기 |
| θ_QCD | nEDM ~2027-30 | [2.5,3.0]×10⁻¹¹ | 폐기 |
| 4th gen 입자 | LHC ongoing | 부재 | 폐기 |
| PMNS angles | DUNE/HK ~2030 | leading denom {NS,NT,d²-1} | 폐기 |
| Cabibbo λ | LHCb/Belle II | 5/22 ± 1% | 폐기 |
| m_p | Lattice QCD next | 938.27 atomic | 폐기 |
| Magic numbers | 검증 완료 | {2,8,20,...} | (이미 검증) |

## 형식 보장

  Phase 3 Falsifier:
    `phase3_falsifiers : 19-conjunct, 0 axioms`
    
  Phase 1 정밀 양:
    1/α_em = 137.036 ppm
    m_μ/m_e = 0.48 ppb
    m_p exact (lattice precision)
    Ω_Λ = 0.0008%

## 한 줄 요약

> "어느 한 측정 이라도 DRLT 강제 정수와 어긋남 → 레포 삭제"

이게 213 의 *진정한 stake*.
형식 정리 + 반증 가능 + 0 axioms = 진짜 falsifiable theory.
