# Atomic Physics Sub-Project

> 원자, 주기율표, 화학 — δS/δψ=0 에서 유도.
> **금지:** Z_eff, Slater rules, Aufbau 가정, orbital labels (ℓ).
> **원칙:** Regge action S = Σ √det(G_h) × δ_h 의 변분만 사용.

## Scope
- 이온화 에너지 (IE) for Z=1-36+
- 원자 구조 (shell emergence from geometry)
- 분자 결합각 (이미 exact: CH₄, NH₃, H₂O)
- 주기율표 패턴 (noble gas 안정성, alkali 불안정성)

## Current Results

| Atom | IE (DRLT) | IE (obs) | Error | Method |
|------|-----------|----------|-------|--------|
| H | 13.606 eV | 13.598 | 0.06% | Exact (ch10) |
| He | 24.565 eV | 24.587 | 0.089% | Channel analysis (EXP_070) |
| Li | 5.315 eV | 5.392 | -1.4% | Screening rule σ=7/8 |
| Be+ | — | 9.323 | — | Not yet solved |

## ∂(Δ⁵) Engine

6 vertices in ℂ⁵:
```
A₁=[0,0,1,0,0]  A₂=[0,0,0,1,0]  A₃=[0,0,0,0,1]  ← confined (orthogonal)
B₁=[t₁,0,ε,ε,ε]                                    ← electron 1
B₂=[0,t₂,ε₂,ε₂,ε₂]                                ← electron 2 (or vacant)
X=[cosφ,sinφ,0,0,0]                                 ← temporal completion
```

- 20 hinges = C(6,3)
- Hinge types: AAA(1), AAB(9), ABB(9), BBB(1)
- Regge action: S = Σ_h √det(G_h) × δ_h
- IE = S(atom) - S(ion)

## Key Formulas
```
H:  IE = Z²Ry / (1 + Z²α²)     (exact, 3 AAB hinges)
He: IE = 2Ry(1 - c²α_GUT)      (channel budget correction)
σ_inner = 1 - n_S/(d²-1) = 7/8  (screening, needs derivation)
```

## Open Problems
1. **He variational:** Reproduce 24.565 eV from δS/δψ=0
2. **Shell structure:** Does 변분이 inner/outer electron 구분을 자연스럽게 만드나?
3. **σ=7/8 유도:** trace conservation에서 증명
4. **Period 2:** Be-Ne, IE pattern
5. **ε leaking → 원자 상호작용 최소 단위**

## Experiment Map
```
EXP_076: He variational solution (planned)
EXP_077: Li variational + shell structure (planned)
EXP_078: Period 2 scan (planned)
```

## Key References
- book/chapters/ch10_atoms.tex — 원자 이론 (6 theorems)
- experiments/EXP_069_variational_boundary.py — 변분 engine
- experiments/EXP_070_helium_ionization.py — He channel analysis
- atoms/scripts/periodic_scan.py — periodic scanner
- standard-model/correction_recipes.md — 보정 패턴
