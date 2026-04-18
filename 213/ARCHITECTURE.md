# 213 Architecture v3

## 공리

```lean
def slash (x y : Raw) (h : x ≠ y) : Raw := .rel x y
```

이것이 전부. 한 줄.

## 계층

```
Layer 0: Hardware (Lean)     — 타입 검사. DecidableEq. h : x ≠ y 검증.
Layer 1: Firmware (213)      — slash. 위 한 줄. / 만 있음.
Layer 2: Hypervisor          — (재구축 필요.) ==, isTrivial 등.
Layer 3: OS                  — (재구축 필요.) 정리, 증명.
Layer 4: Application         — (재구축 필요.) 응용.
```

## SSOT

```
E213/Firmware/RawAxiomV3.lean  — 유일한 소스. 공리 + Level 0,1,2.
```

## 원칙

- `/` 만 있음. `=` 없음. `none` 없음.
- `a/a` = 타입 거부. exception 아님. 도달 불가.
- `≠` = slash의 전제조건 (h : x ≠ y).
- `=` = 213 안에 없음. Hypervisor가 추가.
- depth = `/` 중첩 횟수. 트리 높이.

## 성질 (v3에서 증명됨)

- depth 단조: depth(x/y) > depth(x), depth(y).
- 단사: x/y = a/b → x=a, y=b.
- 원자 ≠ 관계: atom ≠ rel.

## 자연 전개

```
Level 0:  a, b, a/b.                    3개.
Level 1:  + a/(a/b), b/(a/b).           5개.
Level 2:  + 7개.                        12개.
Level n:  폭발. C(k,2) > k for k ≥ 4.
```

Level 0만 C(3,2) = 3 = 자기유지.
