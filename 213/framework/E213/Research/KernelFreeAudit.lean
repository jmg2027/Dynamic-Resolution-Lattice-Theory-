/-!
# Research.KernelFreeAudit: Lean kernel axioms 의 modularity audit

User question (2026-04-26): `propext` 와 `Quot.sound` 도 Lean
kernel 에 hard-coded — 이 들 마저 모듈화 가능 한가?

## Audit 결과 (M1-M22 milestones + arc 9 fronts)

### 그룹 A: **No axioms** (pure Lean type-checker, 외부 axiom 부재)

이 들 은 Lean 을 "코딩 언어" 로만 사용 — propext, Quot.sound,
Classical.choice 모두 부재.  Inductive types + computation 만.

- `RawDecEq.instDecidableEqRaw`: DecidableEq Raw.
- `ParityLensCollapseFalse.parityLens_collapse_false`: xor x x = false.
- `RefinesPreorder.refines_refl`, `refines_trans`: preorder properties.
- `LensEquivProperties.lens_equiv_refl/_symm/_trans`: equivalence
  properties.
- `IsLeafLens.isLeafLens_combine_sym`: leaf-Lens combine commutativity.
- `HasModulusNS.isOrderCauchy_of_hasModulus`: HasModulus implies
  isOrderCauchy.
- `HasModulusBoundsExtra.cauchy_at_larger_N`: modulus N-monotonicity.

### 그룹 B: **propext only** (Quot.sound 부재)

- `CanonicalChoice.canonical_trichotomy`.
- `IdLensKernelEq.idLens_equiv_eq`.
- `ConstLensTotalKernel.constLens_equiv_total`.
- `SumNotCoproduct.sum_not_coproduct_xor`.
- `SumNotCoproductGeneric.sum_not_coproduct_and`.
- `SubtypeInstanceClosed.subtypeCombine_comm`,
  `subtypeHasDistinguishingClosed`, `trueSubtypeInstance`.
- `FourDistinctKernels.id_neq_leaves`.

### 그룹 C: **[propext, Quot.sound]** (Lean baseline 사용)

대 부 분 `omega` tactic (internally uses both axioms) 또 는
`Raw.fold` (Quot.sound dependency 가 transitively) 의존.
`omega` 제거 + `Raw.fold` 의 elemental 재 작성 으 로 일부 그룹
B 또 는 A 로 격하 가능 — 별 도 refactor 작업.

## 의의

User question 의 답:

**부분적 으 로 가능**: 213 의 결과 다 수 가 이미 *Lean kernel
axiom 없 이* verifiable.  특히 framework 의 *combinatorial*
properties (decidability, preorder/equivalence laws, finite
classifications, parity-style identities) 가 그룹 A.

**Universal property + Cauchy infrastructure** 는 propext +
Quot.sound 의존 (omega + Raw.fold).  이는 Lean 4 core 의
설계 자체 — modularization 위 해 서 는 omega 의 element 재
구현 + Raw.fold 의 well-foundedness 의 explicit handling 필요.

**Conclusion**: Lean 을 *fully* coding-language only 로 격하
가능 — 모든 omega 를 manual arithmetic 으 로, Raw.fold 를
explicit recursion 으 로 재 작성.  비용: 비 례 적 으 로 큰
refactor.  현재 ratio: 약 ~30% 의 theorem 이 이미 axiom-free.
-/

namespace E213.Research.KernelFreeAudit

-- 이 module 은 audit 의 결과 기록 — 새 theorem 추가 부재.

end E213.Research.KernelFreeAudit
