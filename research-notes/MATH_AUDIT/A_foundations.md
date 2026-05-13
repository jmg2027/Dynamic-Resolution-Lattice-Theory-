# Chunk A — Foundations + Helpers audit

**Clusters**: NatHelpers (8), Modulus (4), ModArith (9), Choice (4),
AxiomSystems (4), Tactic (6), Logic (5), Search (2).
Total **42 files**.

**Audit date**: 2026-05-12.

## §0 Summary

| Cluster | Files | Lines | Spec status |
|---|---|---|---|
| NatHelpers/   | 8 | 1279 | 1 violation (IntHelpers → Int213) |
| Modulus/      | 4 |  246 | ✓ |
| ModArith/     | 9 | 1442 | ✓ |
| Choice/       | 4 |  514 | 2 violations (BootstrapWitness, Canonical → Theory.Raw) |
| AxiomSystems/ | 4 |  262 | 4 violations (all → Theory.Raw) |
| Tactic/       | 6 |  366 | ✓ |
| Logic/        | 5 |  337 | ✓ |
| Search/       | 2 |  116 | ✓ |

Chunk total = **7 violations** (1 Theory.Internal + 6 Theory.Raw).

## §1 Ring violations

### Theory.Internal.Int213 (1 file)

- **NatHelpers/IntHelpers.lean** (90) — basic Int self-multiplication
  facts.  Used by every `Domain` module (ZIDomain, ZSqrt2Domain, …).
  Reach-in pattern same as chunk C 의 Z-quad files.  처리 옵션:
  Theory.Internal.Int213 의 promotion (THEORY_AUDIT §4.2) 와 함께.

### Theory.Raw direct (6 files)

**AxiomSystems** (4): *주제 자체* 가 "classical axiom = Raw 위 lens
composition" — Raw 위 추론이 필수 콘텐츠.
- ClassicalAnalysisCompletenessAsLens, CrossTheoryCohabit,
  PeanoAsLensComposition, ZFCExtensionalityAsLens

**Choice** (2): canonical-form selection 의 Raw 직접 추론.
- BootstrapWitness — Nat-bootstrap circularity (Lens.leaves 의
  codomain 이 자기 자신 = Nat)
- Canonical — canonical-form selection 의 constructive nature

→ 이 6 파일의 의문: *Lib 거주* 가 맞는가? 주제 (axiom system /
choice 의 Lens 해석) 가 사실 **Lens 또는 Theory.Atomicity 의 cousin**.
거주 재검토 후보 (§5 mid).

## §2 Cluster docstring overview

### NatHelpers/ (8 files)

213-native ∅-axiom replacements for Lean-core `Nat.*` lemmas that
leak `propext` (gcd termination, div, max, add_mod, mul_assoc).
**다른 cluster (Lens, Theory) 의 reach-in source** — Lens/Leaves/
ModNat, Lens/Algebra/CardinalityLB 등 6 Lens 파일이 NatHelpers
import (LENS_AUDIT §1).

| File | Lines | Role |
|---|---|---|
| AddMod213 | 229 | `Nat.add_mod` 대체 |
| Gcd213 | 514 | gcd 정리 (가장 큰) |
| BinomSymm | 149 | C(n,k) = C(n,n-k) |
| PureNat | 134 | mul_assoc, add_mul 등 |
| IntHelpers | 90 | Int self-mul (Theory.Internal.Int213 reach-in) |
| Max213 | 62 | Nat.max 정리 |
| NatDiv213 | 61 | div/mod 정리 |
| EncodePair213 | 40 | (a,b) → a·n+b 인코딩 |

### Modulus/ (4 files)

Bishop-style Cauchy modulus typeclass infrastructure.
- HasModulus (49) — base typeclass
- HasModulusBoundsExtra (25) — derived
- PellHasModulus (111) — Pell sequence instance
- StrongModulus (61) — bounded view-variation

### ModArith/ (9 files)

Modular arithmetic — Join/CRT/gcd 패턴 (Notes 45 §3).
- LensCRT, JoinGCD, JoinEquivGCD (largest 279) — general join=gcd
- JoinBezout/Coprime/Euclidean/Example — sub-step constructions
- PureNatMod3/5 — explicit small cases

### Choice/ (4 files)

Choice as Lens specification (Note 44).
- BootstrapWitness (130), Canonical (44) — Theory.Raw reach-in
- CanonicalTruthChar (291) — canonical truth characterization
- Resolved (49) — "choice = Lens spec" 의 explicit version

### AxiomSystems/ (4 files)

Classical axiom systems as Lens compositions on Raw.
- ClassicalAnalysisCompleteness (74), CrossTheoryCohabit (53),
  PeanoAsLensComposition (67), ZFCExtensionalityAsLens (68)

### Tactic/ (6 files)

213-native tactic infrastructure.
- HurwitzRing (98) — CD polynomial identities
- Ring213 (142) — Mathlib-free `ring` 대체
- IntSquare (29) — Int self-mul macro
- QuadExtension (62) — ℤ[√-D] conjugation instance generator
- Test/IntSquareTest, Test/QuadExtensionTest — tests

다른 cluster 의 reach-in source: Theory/Raw/Mobius 가 Ring213
사용 (THEORY_AUDIT §2.1 의 violation 진원지), CayleyDickson 의
Heavy files 가 HurwitzRing 사용.

### Logic/ (5 files)

213-native predicate calculus + cut elimination.  ∅-axiom.
- Predicate, Proof, Intuitionistic, CutElimination, Capstone

### Search/ (2 files, tiny)

213-native search algorithm + instances.
- FindStructure (64) — universal search building block
- Instances (52) — specialization catalog

Fold candidate → PatternCatalog/ 또는 Meta/.

## §3 Naming + 조직 평가

### Folds + promotions

| 후보 | 액션 |
|---|---|
| Search/ (2 files) | → PatternCatalog/ 또는 Meta/Tactic/ |
| AxiomSystems/ (4 files) | **거주 재검토** — Lens 또는 Theory.Atomicity cousin |
| Choice/ (4 files) | **거주 재검토** — 일부 (BootstrapWitness, Canonical) 는 Theory/Lens 거주 후보 |
| NatHelpers/ (8 files) | **promotion 후보** — Lens/Theory/Lib 의 reach-in source, Meta/Tactic/ 또는 더 깊은 곳에 |
| Tactic/ (6 files) | 위치 OK 단 Ring213/HurwitzRing 의 의미 (Lib 전체 reach-in target) → Meta/Tactic 와 통합 후보 |

### Naming OK

- Modulus, ModArith, Logic — 명확
- Tactic, NatHelpers — 명확하지만 다른 ring 의 dep source

### INDEX.md 추가 권장

- Modulus/ (4 files, INDEX 없음)
- AxiomSystems/, Choice/, Search/ (작지만 INDEX 가 가독성 도움)

## §4 Axiom status

NatHelpers 의 모든 파일이 *명시적으로 ∅-axiom* — Lean-core 의
propext-bearing lemma 의 대체.  따라서 chunk A 의 PURE 비율 매우
높음 (~95%+).

- NatHelpers: ~100% PURE (제목 그대로 axiom-free).
- Modulus, ModArith: ~100% PURE.
- Choice: PURE 다수 (CanonicalTruthChar 가 일부 DIRTY 가능 —
  STRICT_ZERO_AXIOM 의 Cat 5 "Choice canonical" 표시 영역).
- AxiomSystems, Logic, Tactic, Search: ~100% PURE.

## §5 처리 priority

### Quick wins

1. **Search/ fold** → PatternCatalog/ 또는 Meta/Tactic/ — 2 files
2. **Modulus/, AxiomSystems/, Choice/, Search/ INDEX.md 추가**
3. **NatHelpers/IntHelpers** 의 Theory.Internal.Int213 reach-in —
   chunk C 의 Z-quad family 와 함께 (Int213 promotion 시 일괄 처리)

### Mid-term

4. **AxiomSystems/ + Choice/ 거주 재검토** — 주제가 Raw 위 lens 라
   Lens layer 또는 Theory 거주가 자연.  Lib 잔류 / 이동 결정.
5. **NatHelpers/ 위치 재검토** — Lens/Theory/Lib 의 reach-in source.
   Meta/Tactic/ 와 통합 (Mod213, Nat213 이 거기 있음) 가능?  단
   AddMod213, Gcd213 같이 큰 파일 (229, 514) 은 Math 잔류가 자연.
6. **Tactic/ + Meta/Tactic/ 의 경계** — 명확화.  Ring213, HurwitzRing
   은 Math.Tactic, Nat213/Mod213 은 Meta.Tactic.  둘 다 ring-
   independent 같은데 위치 다른 이유?

### Long-term

7. **ModArith Join family 의 universal lens algebra reference** —
   Note 45 §3 "Join = gcd" 가 Lens layer 의 lattice 와 깊이 연결.
   Lens.Lattice/ 와 cross-ref 강화.

## §6 결정 보류

§3 fold/promotion 후보, §5 작업 priority 모두 **기록만**.
Mingu Jeong 결정 대기.

특이사항:
- **AxiomSystems + Choice** 의 6 Theory.Raw reach-in 은 주제 자체가
  "Raw 위 lens 적용" 이라 spec 위반이 *명확* 하지만 *해결* 은 거주
  재검토 (이동) 또는 ARCHITECTURE.md 의 예외 처리 가 필요.
- **NatHelpers** 가 Math 전체에서 가장 자주 reach-in 되는 source —
  promotion 결정이 cascade 영향.  Meta/Tactic 으로 옮기면 ring-
  independence + 다른 ring 모두 사용 가능.
