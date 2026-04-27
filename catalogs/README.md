# 213 Catalogs

Lookup tables for 213 도서관.  grep-able.

## 파일

  atomic-integers.md     1-1000 atomic 정수 표현
  physics-constants.md   α, m_p, Ω_Λ, ... atomic chain
  periodic-table.md      113 + 5 super-heavy 원소 atomic
  falsifiers.md          14 sharp 측정 결판 명제
  correspondences.md     같은 정수 multi-framework
  math-theorems.md       수학 정리 catalog

## 사용

```bash
$ grep "137" catalogs/*.md
catalogs/atomic-integers.md:  137 = 1/α_em (prime, ppm)
catalogs/physics-constants.md:  α_em ≈ 1/137.036
catalogs/correspondences.md:  - Fine structure
```

```bash
$ grep -l "neutrino" catalogs/*.md
catalogs/falsifiers.md
catalogs/physics-constants.md
```

## 동기화

  Lean 정리 = ground truth
  Books = narrative
  Catalogs = lookup

  세 source 동기화 (각 마라톤 종료 시 갱신).
