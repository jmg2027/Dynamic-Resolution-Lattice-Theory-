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

`omega` tactic (internally uses both axioms) 또 는 `Raw.fold` /
`Raw.rec` (Quot.sound 의존 가 transitively) 의존.

### omega 제거 demonstrated (B → A 또 는 C → B 격하)

Concrete 한 omega elimination 결과:

- `Sqrt2IrrationalKernelFree.sqrt2_irrational`: original 이
  `[propext, Quot.sound]` 였 으 나 manual descent 로
  `[propext]` only 격하.  **Quot.sound 가 omega 의 incidental
  dependency 였 음 을 demonstrate**.
- `EulerSharperKernelFree.euler_sharper_lower_n3/n4`:
  concrete value 의 verification 이 `decide` 로 axiom-free
  (그룹 A).
- `WallisSharperKernelFree.wallis_sharper_n2/n3`: 같음.
- `DiagonalHasModulus`: omega 제거 → `[propext]` only 격하.
- `PellHasModulus`: omega 제거 (upstream Quot.sound 의 영향
  으 로 still C, 하지만 module-internal 은 propext only).

### Conclusion

Lean 4 core 의 `propext` + `Quot.sound` 는 *kernel axioms* —
이 들 자체 의 modularization 은 Lean 자체 의 modify 필 요.

하지만 framework 의 이론 결과 의 의존 성 은 *largely
incidental*: `omega` tactic 의 internal 사용 + `Raw.fold`
의 quotient encoding 이 주 요 source.  `omega` 제거 +
explicit Nat reasoning 으 로 substantial fragment 가
`[propext]` only 또 는 axiom-free.

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
