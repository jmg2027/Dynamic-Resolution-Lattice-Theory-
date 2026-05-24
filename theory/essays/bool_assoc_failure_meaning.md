# 왜 b ≥ 3에서 cutSum 결합법칙이 Bool 레벨로 실패하는가

`cutSum`의 search granularity가 factor-2로 hardcode 되어 있어 (NS, NT) = (3, 2) atom 중 NT만 반영하고 NS를 빠뜨린다.  framework "바깥"의 문제가 아니라 *cutSum 구현이 213의 atomic commitment를 under-realize* 했다는 진단.

## 산술 진단

`cutSum (constCut a b) (constCut c b) m k = true`의 조건:

```
∃ m1 ∈ [0, 2m]:  a · 2k ≤ b · m1  ∧  c · 2k ≤ b · (2m − m1)
⇔  ⌈2ka/b⌉ + ⌈2kc/b⌉ ≤ 2m
```

`constCut (a+c) b m k = true`의 조건:

```
(a+c) · k ≤ b · m  ⇔  ⌈2k(a+c)/b⌉ ≤ 2m
```

두 조건의 차이는 **ceiling super-additivity gap**:

```
⌈X/b⌉ + ⌈Y/b⌉  ≥  ⌈(X+Y)/b⌉    (최대 (b-1)/b만큼 over-shoot, 두 번)
```

gap이 0이려면 `2k/b`가 정수여야 한다.  factor-2 doubling은 b = 2의 분모를 흡수하지만 b = 3의 분모는 흡수 못 함.

## 진짜 boundary는 (3, 2) atomic basis

| b | 213 status | 근거 |
|---|---|---|
| 1 | trivial | 정수 |
| 2 | NT atom | `Physics/Foundations/AtomicConstantsParametricFullIff.lean` `c2b_full_iff` |
| 3 | NS atom | 같은 정리 — (m, n) = (3, 2) 또는 (2, 3) uniqueness |
| 5 | (3, 2)의 unique alive atomic | `Theory/Atomicity/Five.lean` `atomic_iff_five` |
| 4, 6, 8, 9, 12, ... | {2, 3}의 multiplicative composite | 위 두 atom의 곱 |
| 7, 11, ... | (3, 2)에서 additive Lens-readout 가능 | Bezout via gcd(2,3) = 1 |

**5는 새 atom이 아니라 derived**.  `atomic_iff_five`가 정확히 "5 = (3, 2)에서 유일하게 alive한 atomic decomposition"임을 증명: 5 = 2·1 + 3·1.  d = 5 = NS + NT는 *(3, 2)의 readout*.

`Lib/Math/ResolutionLimit.lean` `N_U_eq_d_pow_dsq`: N_U = 5²⁵ — 5가 (3, 2)에서 forced되므로 자동.

`Lib/Math/Padic/ZpSqrtD.lean` `ZpSqrtD p`: 임의 prime `p`에서 작동 (p = 5, 7, 11, ...).  framework가 이미 모든 prime을 자기 안에 갖고 있다.

`Lib/Math/Cohomology/Bipartite/V32.lean`: K_{3,2}^{(c=2)}의 bipartite (3-side, 2-side) 구조가 모든 observable을 cup-ring으로 생성.

`Lib/Physics/AlphaEM/Capstone.lean` `unified_single_sum_form`: α_em이 (3, 2, 5)에서만 derive — 0.2 ppb CODATA agreement.

이 모든 정리가 *(3, 2) → 모든 real 판정*의 Lean-증명된 chain.  framework "바깥"은 §5.1 (`seed/AXIOM/05_no_exterior.md`)이 거부한다.

## cutSum의 진단 (수정)

문제는 b ≥ 3이 아니라:

**`cutSum`의 factor-2 hardcode가 (3, 2) 중 NT만 읽고 NS를 빠뜨렸다**.

올바른 cutSum은 (3, 2) 둘 다 반영해야 한다:

  · search granularity가 factor-2가 아니라 `lcm`-aware
  · 두 cut의 분모 `b₁, b₂`에 대해 search range = `lcm(b₁, b₂) · m`
  · {2, 3}-multiplicative monoid에서는 자동으로 닫힘 (lcm도 같은 monoid 안에)
  · ceiling gap이 정확히 native class에서 0이 되어 결합법칙 회복

또는 더 깊게: cut이 어느 Lens application에서 나왔는지에 따라 resolution이 결정되어야 한다 (Lens-determined granularity).  hardcoded factor-2는 *모든 cut을 NT-Lens output으로 다루는* 암묵적 가정.

## 같음에 미치는 영향

이전 essay에서 enumerate한 동치 정의들 (`cutEq`, `ZpSeqEquiv`, `signedEq`, ...)이 이미 임의 분모/임의 prime에서 well-defined인 것이 우연이 아니다 — *framework가 (3, 2)에서 모든 real 판정을 갖고 있다*는 사실의 직접 표명.

`is_integer : cutEq cut (constCut a 1)` (`IntValidCut.lean`)와 `is_half : cutEq cut (constCut a 2)` (`HalfValidCut.lean`)도 더 일반적 wrapper로 통합 가능:

```
is_native : cutEq cut (constCut a b) ∧ b ∈ ⟨2, 3⟩  (multiplicative monoid)
```

이 wrapper에서 결합법칙은 cutSum의 (3, 2)-aware 구현과 함께 닫힌다.

## 후속 작업의 closure

1. **`cutSumN N` parametric 정의** — `Lib/Math/Real213/Sum/CutSumN.lean` (6 PURE).  factor-2 hardcode를 parametric N으로 lift.  `cutSumN_same_denom`: 임의 `N > 0`, `a, c`에서 `cutSumN N (constCut a N) (constCut c N) ≡ constCut (a+c) N` bidirectional.

2. **`cutSumN_mixed_denom`** — `Sum/CutSumNMixed.lean` (3 PURE).  Cross-denominator closure: for `b₁·q₁ = N`, `b₂·q₂ = N`,
   `cutSumN N (constCut a b₁) (constCut c b₂) ≡ constCut (a·q₁ + c·q₂) N`.  N의 약수 b 쌍이 모두 algebraically 닫힘.  예: `cutSumN 6 (1/2) (1/3) ≡ 5/6` (`cutSumN_six_half_third`).

3. **`ThirdValidCut` (b = 3)** — `Lib/Math/Real213/ThirdValidCut.lean` (15 PURE).  IntValidCut/HalfValidCut 패턴; `cutSumN 3` 기반.  `cutSumN_3_2_1_at_1_1`이 CutSumAssocB3 반례가 `cutSumN 3`에서는 true임을 decide-검증.

4. **`NValidCut N` parametric — 모든 자연수 N의 통합 closure** — `Lib/Math/Real213/NValidCut.lean` (14 PURE).  `ValidCutN N` 구조 (cut + represents + is_at_denom), `addN N hN`, `cutSumN_assoc_valid N hN`, `cutSumN_comm_valid N hN`, `nvalidcut_all_naturals_capstone`.  Per-N 별 증명 불필요 — 임의 N ≥ 1에서 한 번에 닫힘.  Smoke: N = 5, 7, 11에서 결합법칙 검증 (`fifth_assoc_1_2_1`, `seventh_assoc_2_3_5`, `eleventh_assoc_1_4_6`).

## 5와 모든 자연수: layered closure

| Layer | Closure | Lean |
|---|---|---|
| Self-algebra (단일 N) | 임의 N ≥ 1 | `cutSumN_same_denom N` + `NValidCut N` |
| Mixed (b₁, b₂ | N) | N이 b₁, b₂의 공배수 | `cutSumN_mixed_denom` |
| 213-native composite | N ∈ ⟨2, 3⟩^mult | b = 2, 3, 4, 6, 8, 9, 12, ... 모든 cross-sum |
| Pure b = 5, 7, 11, ... | Self-closure ✓; cross-closure는 N = b·b' 필요 | NValidCut N |

**5의 자리**: `Theory/Atomicity/Five.lean atomic_iff_five`가 5 = 2·1 + 3·1 (alive atomic)임을 증명 — 5는 (3, 2)에서 *덧셈으로* 유일한 atomic.  cutSumN 5는 self-algebra 닫힘; cutSumN 10 = cutSumN (2·5)이 b ∈ {2, 5} 짝 cross-closure.  7 = 2+2+3, 11 = 2+3+3+3 등도 같은 패턴.

진짜 framework 결함은 cutSum의 hardcode이지 b ≥ 3 자체가 아니다.  213은 (3, 2) atomic commitment를 honor하고, 그 안에서 모든 real이 판정 가능하다.  `cutSumN N` parametric framework가 NS·NT atom의 algebraic closure를 **모든 자연수에 대해** framework 안에서 완전 실현.
