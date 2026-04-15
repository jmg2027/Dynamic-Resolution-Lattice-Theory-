# Atoms Sub-Project — CLOSED

## Status: CLOSED ✓ (55 experiments, 10 theorems)

## Final Results
- **IE median: 2.9%** (118 elements, 0 free parameters)
- **<5%: 84/118** (71%), **<10%: 112/118** (95%)
- **Period 2: 0.5%** (self-consistent, adjoint corrected)
- **Bond angles: 0.00°** (CH₄, NH₃, H₂O exact)
- **H-H bond: +1.3%**, **F EA: +2%**

## Theory (atomic_formulary.md)
- 10 formalized theorems
- Self-consistent algebraic solver (coupled rational equations)
- Screening constants = leading order of SC equation
- All quantities rational with ζ₉

## Key Theorems
1. Atom = simplex geometry
2. N_S=3 unique for 2l+1 degeneracy → d=5
3. Aufbau from n+l (simplex energy)
4. Pauli from det(G) > 0
5. Hinge determinant: det = 1-ε_i²-ε_j²
6. Hydrogen degeneracy from hinge cancellation
7. IE = Z_eff² × Ry / n²
8. Born-Screening duality (d=5 uniqueness)
9. Adjoint resummation f = 24α/(24+α+α²)
10. Z_max = 168 (Hadamard bound)

## Residual ~3%
- Core screening: layered σ model은 leading order.
  s-block 알칼리 부호 반전, 상대론적 원소(Hg 등) 미해결.
- 측정 불확도: Period 7 초중량 원소 참조값 불확실.
- Self-consistent 반복이 leading order를 넘어서지만 (61/118 개선),
  σ 함수 자체의 구조가 한계. 더 정밀한 σ = 변분 직접 풀이 필요.
