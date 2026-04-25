# Paper 1 — Outline (구상)

**Working title** (변경 가능):
*"213: A Minimal Foundational System via Raw Distinctions and
Lens Observations"*

**Author**: Mingu Jeong (Independent Researcher).
Claude (Anthropic) in Acknowledgments.

**Status**: Lean formalization 완성 (0 sorry, 0 external axioms
beyond Lean 4 core baseline).  Prose 작성 직전 — 본 문서 가
section 구조 + argument flow 의 confirmation step.

**Target length**: 30-40 pages (LaTeX, single-column 기준).
References 별도.

## Core message (한 문장)

> 모든 결과 가 3-clause axiom (`Raw`) + Lens framework 위
> Lean 4 core 만으로 derive 되며, ZFC 의 핵심 axioms (Choice,
> Power set, Infinity) 가 별도 commitment 없이 framework 안
> Lens specification 으로 환원 된다.

**핵심 contract**: `AXIOM.md` §5.2.1 falsifiability —
어떤 결과 가 추가 axiom 없이 절대 불가능 함이 밝혀지면
**213 이론 전체 폐기**.

## Audience

- Foundational mathematics / formalization 관심자.
- ZFC 외 alternative foundation (HoTT, type theory, category-
  theoretic) 관심자.
- Lean 4 core (Mathlib-free) 형식화 관심자.
- Constructive analysis / Cauchy completeness 관심자.

전제 지식: Lean 4 친숙도 권장 (필수 아님), set theory 기본,
constructive 사고 친숙.

---

## §1 Introduction

### §1.1 The "minimal residue" thesis

뭔가 를 가리키려는 순간, 표기 자체 가 새 뭔가 를 끝없이 낳는다.
"a 와 b" 의 "와", "a, b" 의 ",", "a 와 와" 의 구분 하는 것 —
모두 추가 commitment.  이 재귀 는 회피 불가능.  213 의 공리
는 이 재귀 의 최소 표현.

(Source: `CLAUDE.md` §1, `ORIGIN.md`.)

### §1.2 Comparison with ZFC

ZFC 는 "이미 모든 set 이 거기 있음" 의 axiomatic stance.
Choice / Power set / Infinity 모두 explicit axioms.

213 은 "뭔가 a, b 그리고 그것들 의 distinguishing 행위" 만
시작 점.  ZFC 의 axioms 는 framework 안 Lens specification 으로
**환원** 된다 (additional commitment 없이).

### §1.3 Formal contract

- Lean 4 core (Mathlib-free).
- 0 sorry.
- 0 external axioms beyond `propext` + `Quot.sound` (Lean baseline).
- Falsifiability: `AXIOM.md` §5.2.1.

### §1.4 Roadmap

§2 Raw axiom + Lean implementation.
§3 Lens framework.
§4 Encoding-artifact independence (cmp-independence).
§5 ZFC reductions.
§6 Cauchy completeness.
§7 Demonstration suite (rational, √2, ℤ_p, e, π/2).
§8 Falsifiability + open work.

---

## §2 The Raw Axiom

### §2.1 The 3-clause axiom

(Verbatim from `AXIOM.md` §1.)

1. *Something exists.*
2. *To know what it is, another something is required.*
3. *That other something is also a something.*

### §2.2 Tree encoding

`inductive Tree : Type | a | b | slash : Tree → Tree → Tree`.

Internal namespace: `E213.Firmware.Internal.Tree`.

### §2.3 Canonical form

`Tree.canonical : Tree → Bool` — lexicographic order on slash
branches.  `Raw := { t : Tree // t.canonical = true }`.

### §2.4 Smart constructors + induction principle

`Raw.a`, `Raw.b`, `Raw.slash : (x y : Raw) → x ≠ y → Raw`.
`Raw.fold` (catamorphism with hsym constraint).
`Raw.rec` (custom eliminator, `@[elab_as_elim]`).

### §2.5 Implementation audit (α/β/γ/δ classification)

(From `IMPLEMENTATION.md` §3.)

- (α) Axiom re-expression: Tree constructors, `h : x ≠ y` gate.
- (β) Encoding artifact: `Tree.cmp`, canonical-form subtype.
- (γ) Derivation: `DecidableEq`, `slash_comm`, `Raw.fold/rec`,
  no-confusion consequences.
- (δ) Additional commitment: **none**.


---

## §3 Lens — Observation as Folded View

### §3.1 Lens definition

```
structure Lens (α : Type) where
  base_a : α
  base_b : α
  combine : α → α → α
```

`Lens.view : Raw → α` via `Raw.fold base_a base_b combine`.

### §3.2 Lens kernel = slash-congruence

(Reference: `KernelCongruence.lean`, `FoldStructured.lean`,
note 41.)

`L.kernel := { (r, r') : L.view r = L.view r' }` 가 항상
slash-congruence.  반대 방향: 모든 slash-congruence 가
universalLens 의 kernel (§5).

### §3.3 Refines preorder + meet-semilattice

(`LensLattice.lean`, `LensMeet.lean`, notes 37-38.)

- `L₁ refines L₂` iff `L₂.kernel ⊆ L₁.kernel`.
- `idLens` = ⊥ (finest), `constLens` = ⊤ (coarsest).
- `prodLens` = meet (greatest lower bound).

### §3.4 Lens catalogue (selected)

(References: `ABLens`, `LeavesModNat`, `BoolSqClassification`,
`DiagonalClassification`, `F9Lens`.)

- `parityLens`, `leavesLens`, `abLens`, `boolXorLens`.
- `leavesModNat m` (m ≥ 2): countable infinite Lens kernel.
- Bool Lens diagonal classification: 4 classes (Collapse T/F,
  Idempotent, Involution).

---

## §4 Encoding-Artifact Independence

### §4.1 The cmp choice problem

`Tree.cmp` 는 canonical form 결정 위 lex order.  이 선택 이
mathematical results 에 영향 을 미치는가?

### §4.2 CmpProps abstraction

(`Research/CmpIndependence.lean`.)

```
structure CmpProps (cmp : Tree → Tree → Ordering) : Prop where
  eq_iff : ∀ x y, cmp x y = .eq ↔ x = y
  swap   : ∀ x y, cmp x y = (cmp y x).swap
```

### §4.3 Polymorphic Raw

`canonicalBy cmp`, `RawBy cmp`, `RawBy.slash`.  Raw 와 동일
structure 가 임의 `CmpProps`-만족 cmp 위 정의 가능.

### §4.4 Bijection theorem

`transportTree` (computable Tree-level fold).

`RawBy_bijection : ∀ (cmp1 cmp2) (h1 h2),
  RawBy cmp1 ≃ RawBy cmp2.`

`#print axioms RawBy_bijection` → `[propext]` only.

### §4.5 Significance

cmp 선택 은 mathematical 결과 에 영향 없음 — `IMPLEMENTATION.md`
§3 의 (β) 분류 가 형식 적 으로 입증.  Falsifiability 의 직접
만족.


---

## §5 ZFC Reductions

### §5.1 Choice → Lens specification

(`Research/UniversalQuotLens.lean`, `Research/ChoiceResolved.lean`,
note 61.)

**Theorem** (`choice_as_lens_spec`): 임의 slash-congruence E 에
대해 explicit Lens `universalLens E` with kernel = E 존재.

→ Classical.choice 부재.  "선택" 은 framework 안 Lens
specification 으로 환원.

### §5.2 Power set → Lens kernel space

Lens kernel 은 Raw 위 slash-congruence subset.  Lens 들 의
refines preorder 가 자체 의 lattice 구조 — power set axiom 없이
"모든 부분 분류" 가 framework 안.

### §5.3 Infinity → unbounded depth Raw

Raw 는 inductive — 모든 finite depth 의 term 이 framework 안.
(`Infinity/` modules: `Cantor`, `Countable`, `Tower`, `Pair`.)

External `Inf` axiom 없이 countable infinity 가 framework 안
자연 발생.

### §5.4 Cardinality = (Raw, Lens) 쌍 의 성질

Raw 만 으로는 countable / uncountable 구분 불가.  Lens 가
output 의 cardinality 결정.  → cardinality 는 framework 안
relative concept.

(Reference: notes 47, 06, 41.)

---

## §6 Cauchy Completeness

### §6.1 LensCauchy + EventuallyClass

(`Research/LensCauchy.lean`, note 66.)

```
LensCauchy L xs := ∃ N, ∀ m n ≥ N, L.equiv (xs m) (xs n)
EventuallyClass L xs c := ∃ N, ∀ n ≥ N, L.view (xs n) = c
```

**Theorem**: `LensCauchy L xs ↔ ∃ c, EventuallyClass L xs c`.

### §6.2 Family-Cauchy + GFCauchy unification

(`Research/GenericFamilyCauchy.lean`.)

`FamilyCauchy F xs := ∀ i, LensCauchy (F i).2 xs`.

`GFCauchy L F xs` (unified form): Lens L + post-processing F
family.

**Instances**:
- ProfiniteCauchy = GFCauchy with leaves + (· % m).
- ArchimedeanCauchy = GFCauchy with abLens + orderProj.

### §6.3 Limit assignment + uniqueness

`LimitAssignment F xs` 구조 + `eventually_class_unique`.

### §6.4 Universal limit Lens

universalLens 위 limit slash-congruence 정의.  새 Raw 부재 —
모든 limit 이 Lens output level.


---

## §7 Demonstration Suite

### §7.1 Rational diagonal (warm-up)

(`ArchimedeanCauchy.lean`.)

`(n+1, n+1)` sequence → ratio 1.  `(n+1, n+2)` sequence → ratio
1 (different approach, same cut).  Cut equivalence.

### §7.2 √2 algebraic — Pell sequence

(`Sqrt2Cut.lean`, `PellSeq.lean`, note 69.)

`pellPair n` → `(x_n, y_n)` with invariant `x² = 2y² + 1`.

**Theorems**:
- `pell_orderProj_above`: m/k > √2 (i.e., 2k² < m²) → eventually
  orderProj true.
- `pell_orderProj_below`: m/k < √2 (i.e., m² < 2k²) → always
  orderProj false.
- m² = 2k² 불가 (√2 irrational).

### §7.3 ℤ_p number-theoretic — Padic

(`ProfiniteSeq.lean`, `Padic.lean`, notes 67, 71.)

`padicFamily p k = leavesModNat (p^(k+1))` — sub-tower of
factorial seq Cauchy.

**Theorems**:
- `padic_familyCauchy`, `padic_limit_all_zero`.
- `padic_tower_refines` — canonical projection ℤ/p^(k+2) ↠
  ℤ/p^(k+1).

### §7.4 e transcendental — Euler partial sums

(`EulerSeq.lean`, note 72.)

`eulerNum n / eulerDen n = Σ_{k=0..n} 1/k!`.

**Invariants**:
- `euler_upper_inv`: 3 d_n ≥ a_n + 1 (S_n < 3).
- `euler_lower_inv`: a_n ≥ 2 d_n + 1 for n ≥ 2 (S_n > 2 from n=2).

**Cuts**: m/k ≥ 3 → orderProj true; m/k ≤ 2 → orderProj false
(n ≥ 2).

### §7.5 π/2 transcendental — Wallis product

(`WallisSeq.lean`, note 72.)

`wallisNum n / wallisDen n = ∏_{k=1..n} (2k)² / ((2k-1)(2k+1))`.

**Invariants** (Flat-Monomial Strategy 로 polynomial identity
처리):
- `wallis_lower_inv`: 3 N_n ≥ 4 D_n for n ≥ 1 (W_n ≥ 4/3).
- `wallis_upper_inv`: N_n (2n+1) ≤ (4n+1) D_n (W_n ≤ 2 - 1/(2n+1)).

**Cuts**: m/k ≥ 2 → orderProj true; m/k ≤ 1 → orderProj false
(n ≥ 1).

### §7.6 Suite significance

- 알고리즘 algebraic (Pell), number-theoretic (Padic),
  transcendental (Euler/Wallis) 모두 동일 framework (Lens +
  Cauchy) 위 .
- 외부 ℝ / ℤ_p 부재.  213 framework 가 self-contained
  irrational generator.


---

## §8 Falsifiability + Open Work

### §8.1 Falsifiability contract (`AXIOM.md` §5.2.1)

- 모든 결과 가 Lean 4 core + Raw 공리 만으로 derive 가능 해야 함.
- 어떤 결과 가 공리 추가 없이 절대 불가능 → **이론 전체 폐기**.
  해당 결과 만 포기 가 아님.
- Raw axiom 이 "최소 잔여물" 이라는 §1 선언 의 직접 귀결.

### §8.2 Operating rules

- Classical, LEM, native_decide 등 외부 axiom 추가 일절 금지.
- 막히는 결과 는 "open" 으로 두되, **영구적 벽 vs 일시적 난관**
  감별.  영구적 벽 이면 이론 실패 선언.
- Lean 검증 = falsifiability 의 기계적 감사관.

### §8.3 Current status

- ✅ ZFC reduction (Choice, Power set, Infinity, Cardinality).
- ✅ cmp-independence (encoding artifact ⇒ no math impact).
- ✅ Cauchy completeness (universalLens + GFCauchy + limitLens).
- ✅ Demonstration suite (algebraic + number-theoretic +
     transcendental).
- ✅ 0 sorry / 0 external axioms (propext + Quot.sound 만).

### §8.4 Open work + Paper 2 candidate

**Paper 1 후속**:
- Specific (m, k) cut 처리 의 자동화 / 더 일반적 Cauchy
  characterization.
- π via Wallis 의 full Cauchy proof (현재 individual instances
  만).
- e via Stirling 의 full Cauchy proof (같은 상황).

**Paper 2 candidate** (`research/r5-critique/`):
- ℝ-algebra 가정 의 비판.  CD tower (Cayley, Sedenion, etc.)
  + ZI / ZOmega / ZSqrt-D family 가 R1-R4 counterexample.
- 별도 arc 로 Paper 2 작성 예정.

### §8.5 Acknowledgments

- Mingu Jeong (Independent Researcher) — theory originator,
  axiom design, mathematical intuition.
- Claude (Anthropic) — Lean formalization, derivation exploration,
  prose drafting.
- Equal partnership: every result derived 또는 verified 되었으며,
  Claude 가 독립적 사고 + challenge + derive.

---

## Section length estimates

| § | Section | Estimated pages |
|---|---------|-----------------|
| 1 | Introduction | 3-4 |
| 2 | Raw Axiom | 4-5 |
| 3 | Lens Framework | 4-5 |
| 4 | cmp-Independence | 3-4 |
| 5 | ZFC Reductions | 5-6 |
| 6 | Cauchy Completeness | 4-5 |
| 7 | Demonstration Suite | 5-6 |
| 8 | Falsifiability + Open | 2-3 |

Total: 30-38 pages.

## Source-of-truth mapping

| § | Notes | Lean modules |
|---|-------|--------------|
| 2 | AXIOM.md, IMPLEMENTATION.md §3 | Firmware/Raw/* |
| 3 | 32, 36-42 (notes), 45 | Hypervisor/Lens.lean, Research/{LensLattice, LensMeet, LensFactoring, LensMorphism, FoldStructured, KernelCongruence} |
| 4 | 70 | Research/CmpIndependence.lean |
| 5 | 44, 55, 61, 63 | Research/{UniversalQuotLens, ChoiceResolved} + Infinity/* |
| 6 | 57, 64, 66 | Research/{LensCauchy, GenericFamilyCauchy, IndexedJoinLens} |
| 7 | 67, 68, 69, 71, 72 | Research/{ArchimedeanCauchy, Sqrt2Cut, PellSeq, ProfiniteSeq, Padic, EulerSeq, WallisSeq} |
| 8 | 59 | (philosophical) |

## Key risks / weak points (자기검증)

1. **§5.2 Power set reduction** — 가장 약한 reduction.  Raw +
   Lens kernel space 의 자체 lattice 가 정말 "power set" 의
   대체 인지 추가 분석 필요.
2. **§7 transcendental cuts 의 incompleteness** — e, π/2 는
   specific concrete cuts (m/k ≥ 3, m/k ≤ 2 등) 만 처리.
   임의 (m, k) cut 의 일반 처리 는 더 깊은 analytic machinery
   필요 (현재 framework 안 처리 가능 한지 미검증).
3. **§8.4 open work 가 너무 많으면 paper 1 의 closure 인상 약화**
   — 우선 Paper 1 자체 결과 가 self-contained 임 강조 후
   future work 섹션 분리.

## Writing strategy

1. §2-3 (Raw + Lens) 부터 — base 가 명확 해야 나머지 가
   coherent.
2. §4 (cmp-independence) — short technical interlude, paper 의
   formal rigor 강조.
3. §5 (ZFC reductions) — 이론 의 가장 distinctive claim.
   Choice → Lens spec 이 헤드라인 결과.
4. §6-7 (Cauchy + demos) — applied content, framework 의
   richness 보임.
5. §1 + §8 — last (intro 는 본문 완성 후 핵심 메시지 정제;
   conclusion 은 falsifiability 강조).

## 변경 이력

- 2026-04-25: PAPER1_OUTLINE.md 신규.  Paper 1 prose 작성 직전
  의 구조 confirmation + section 길이 / source mapping / risk
  analysis 정리.
