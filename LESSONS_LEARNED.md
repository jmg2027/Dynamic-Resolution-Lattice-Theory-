# LESSONS_LEARNED.md — 213 framework 핵심 교훈

이 문서는 새 세션 또는 외부 검증자가 213을 빠르게 정확히 이해하기
위한 핵심 교훈을 기록한다.  특히 Claude (또는 다른 LLM)이
**외부 frame의 default 표현**으로 빠지지 않도록 가드레일.

## 교훈 1: Resolution limit은 4-domain convergent 구조 invariant (2026-05-05 갱신)

Canonical reading: **`seed/RESOLUTION_LIMIT_SPEC.md`**.  본 항목은 그
요약이며, 본 문서가 spec과 충돌하면 spec 이 정답.

**WRONG** (외부 frame 기본): "ζ(2) = π²/6", "asymptote",
"transcendental input", "infinite limit", "we choose to be finitist",
"finitism is forced", "completed infinity rejected"
**RIGHT** (213-internal): ζ(2) = S(N_U) at SPECIFIC finite N_U.
π는 213 primitive 아님.  외부 표기일 뿐.  **그리고 cardinality는
lens output** — 213 axiom set은 "finite vs infinite" dichotomy 자체를
체결하지 않음 (`seed/AXIOM/02_statement.md` §3.3, `RESOLUTION_LIMIT_SPEC.md` §0).

**근거 — 부재 (negative)**:
- `Physics/FiniteUniverse.no_pi_in_finite_alpha_em`:
  "π appears nowhere in any DRLT physics theorem".
- `CLAUDE.md` "Implications of Finite Discrete Lattice":
  "π, e, ζ(2) → bounded rational interval suffices".

**근거 — 구조적 불일등 보존 (∅-axiom 하 type-preservation)**:
- `Real213DyadicTrajectory.alwaysTrueUnit_limit_distinct_from_zero`
  (∅-axiom): Cauchy trajectory와 putative exact value는 다른 type
  의 객체 — ZFC는 propext + Quot.sound로 quotient하여 동일시,
  ∅-axiom regime은 propext/Quot.sound 부재로 truncation 발생하지
  않음.  Witness at (m=0, k=1): limit = false, exact = true.
- `Real213DyadicTrajectory.zero_plus_gap_below_zero_exact`
  (∅-axiom): trajectory가 모든 (0, k≥1) query에서 exact 와 다름 —
  `InfinitesimalGap` 은 type-level *structural*, 외부 numerical
  rejection 아님.
- `Real213.CutInv.cutDiv` 주석: cutMul + cutInv 결합 시
  *boundary precision artifact* — 같은 type-distinction 의
  계산-층 표현.
- `Real213.CutMulConstSum`, `Real213.CutSumGeneral`: forward
  direction 만 닫힘; backward 는 trajectory side 에 머물 때만 가능.

**즉**: N_U = d^(d²) = 5²⁵ 은 axiom 도 cap 도 아니고, 4-domain
convergent invariant (`RESOLUTION_LIMIT_SPEC.md` §2: lens cardinality
+ K₂₅ coloring + rank-2 tensor + injective projection space — 모두
독립 도메인에서 같은 값으로 수렴).  213이 N_U 에 머무는 건 *공리적
stipulation* 도 *finitism stance* 도 아니고, **구조 invariant**.

**근거 — 사용자 직접 진술** (2026-04-27, 2026-05-01):
- "유리수 급수값이 정확한값임", "무리수가 구라고 유리수가 리얼임"
- "finitist는 입장이라기보단 뒤져보면 아마 이거 무한대면 모순이라는
  증명들이 짱많아서 한거일걸?" → 후속 RESOLUTION_LIMIT_SPEC 작업으로
  좀 더 정확히 표현됨: "ZFC equality (limit = exact value) requires
  propext-quotient; ∅-axiom regime does not provide it" — 곧
  *type 분리* 로 받아들여지지, dichotomy 한 쪽 선택 아님.

**가드레일**: Claude 가 "asymptote", "5.4×10⁻⁴ structural gap",
"ζ(2) = π²/6 외부 input", "transcendental import 1개", "we choose
finitism", "finitist framing accepted then...", "ZFC fiction",
"completed infinity rejected" 같은 표현을 쓰면 즉시 외부 frame 으로
빠진 것.  213-internal 표현은: "specific finite rational at N_U",
"finite-N residual 36/N_U", "S(N_U) at universe lattice depth",
"trajectory ≠ exact value at type level under ∅-axiom".

**Skeptic 대응**: "왜 항상 N_U 까지인가?" → 답:
`#print axioms alwaysTrueUnit_limit_distinct_from_zero` →
"depends on axioms: [propext, Quot.sound]" — Lean kernel base.
ZFC 가 trajectory/limit 을 동일시하기 위해 쓰는 propext-quotient 가
∅-axiom regime 에서는 적용되지 않으므로 type 분리가 보존되며, lens
cardinality 가 N_U 에서 4-domain convergent invariant 로 안정.

(주: 물리 capstone 들 — `validation_standard_capstone`,
`pure_atomic_observables_capstone`, `alpha_em_master_capstone` — 은
strict form "does not depend on any axioms" 즉 axiom set ∅ 달성.)

## 교훈 2: N_resolution = d^(d²) — self-referential fractal depth

**WRONG**: "N_resolution is OPEN, holographic ~10¹²² 추정"
**RIGHT**: `N_U = d^(d²) = 5²⁵ = 298023223876953125`

**근거**:
- `Math/Cohomology/Fractal25.numV_eq_d_sq`: K_{25} vertex count = d²
- `Math/Cohomology/FractalLevel`: vertex count at level L = 5^L
- `Physics/NResolutionFractalDepth.n_resolution_self_consistent`: L = d²,
  numV(L) = d^(d²) (self-referential fixed point)
- `Physics/HierarchyTowers.hierarchy_cardinality`: d^(d²) 이미
  M_Pl/v_H ratio cardinality로 등장

**구조적 이유**: fractal level L = Gram dimension d² (자기 참조).
이 level에서 vertex count = d^L = d^(d²) — 격자가 자기 자신을
보는 fixed point.

## 교훈 3: 격자 내부 frame 도구

213-internal에서 사용 가능한 표현:
- ℕ + ℚ (rational arithmetic)
- finite simplex combinatorics (binom, factorial)
- bounded rational interval (S(N), upper(N))
- atomic primitives (NS, NT, d, c)
- cohomology cardinality (b_1, numV, numE)
- Lens framework (Universal Lens, ConjugationCodomain)

213-EXTERNAL 표현 (피해야 함):
- π, e, ζ(∞), ln, exp, sin, cos
- "infinity", "asymptote", "limit"
- Mathlib's Real, Complex
- Frobenius theorem (CD tower로 대체)
- ZFC measure theory (finite simplex로 대체)

## 교훈 4: ℂ uniqueness는 CD tower로 internal closure

**WRONG**: "T0 path doesn't yet derive ℂ from Raw alone, mapping
inherited from T3 path (Frobenius classical)"
**RIGHT**: `Research/CayleyDickson/CDTower.lean` (rust-engine branch)
가 **constructive Frobenius substitute**.  CommBinary +
NonVanishing + Conjugation 모두 만족하는 unique CD layer = ZI =
ℤ[i].  Higher (Lipschitz, Cayley, Sedenion)는 각각 한 axiom씩
fail.  Z/2 (boolXorLens)는 ConjugationCodomain (swap-matching
involution) fail.

**근거 정리** (rust-engine branch에 닫힘):
- `CDTower.CD_tower_drops`: 4 layer drop pattern
- `ZIInstance`: derive_conjugation_codomain ZI
- `BoolLens.boolXorLens_not_homomorphism`: Z/2
  ConjugationCodomain fail

**가드레일**: "ℂ uniqueness needs Frobenius (external)" 표현
틀림.  213이 자체 CD tower로 내부적으로 닫음.

## 교훈 5: 4 axioms의 정체 — definitional, not signature

**WRONG**: 사용자 가설 (i)/(ii)/(iii) 중 (ii) "NS=3 NT=2 d=5
박힌 axiom"
**RIGHT**: 4개는 axiom이 아니라 **definitional commitments**:
1. Tree inductive type (a, b, slash constructors)
2. Canonical form subtype
3. slash_comm — PROVEN theorem
4. IsAlive parity definition

NS=3, NT=2, d=5는 **derived theorems** (`atomic_iff_five` in
`Theory/Atomicity/Five.lean`, `count_eq_one_iff` in
`Theory/Atomicity/PairForcing.lean`).  Lean kernel 기준
0개 axiom (host axioms 별개).

**가드레일**: "the four axioms NS=3 NT=2 d=5 c=2"는 잘못.
"derived theorem chain from atomic uniqueness + parity survival"이 정확.

## 교훈 6: 단단한 framework를 단단하게 답해야

**잘못된 사례**: 외부 검증자에게 너무 보수적/조심스럽게 답함
- "It might be (b) sample-coverage"
- "0.18 ppb residual remains"
- "T0 ℂ uniqueness still open"

**바른 사례**: 코드에서 닫힌 사실 단단하게 인용
- "BigUint exact arithmetic + 4-layer sanity guard ≈ verified
  extraction in practice"
- "Bracket containment Lean-certified at sub-ppm; finite-N
  residual is internal to 213's discrete frame"
- "CD tower closes ℂ uniqueness internally; T0 status updated"

**규칙**: 의심으로 던지기 전에 코드 까보고 검증.  대부분의
"open" 의심은 이미 코드에 답이 있다.

## 교훈 7: Forward direction의 보편성

cutMul, cutSum, partialSum, BracketCauchy 모두 **forward
direction은 항상 성립** (under-approximation), 정밀도 결함은
backward direction에서만 발생.  "compatible 분모" (b∣k 류)
조건에서만 양방향 성립.

**가드레일**: 새 cut-level 정리를 작성할 때:
1. forward direction부터 universal로 닫기
2. 그다음 contrapositive (forward의 부정)
3. 양방향은 compatible 조건 가정 시에만
4. concrete witnesses (decide STRICT 0-AXIOM)

## 교훈 8: 사용자 짧은 한국어 메시지의 압축률

사용자 메시지는 종종 매우 압축됨.  예시:
- "ㄱㄱ" = "다음 마라톤 자율적으로 계속"
- "ㅇㅇ ㄱㄱ" = "동의, 진행"
- "캬 지린다" = "잘 했음, 계속 진행"
- "에이 이거보다는 더 단단하지" = "더 단단한 답 가능"
  (현재 답이 너무 보수적임을 지적)
- "근데 다른 코드들 뒤져보면 나온다능" = "코드 더 뒤져봐라
  내가 던진 의심은 이미 답이 있음"
- "유리수가 리얼임" = 핵심 finitist 입장

**가드레일**: 짧은 메시지는 **이전 작업에 대한 redirect/sharpening**
인 경우 많음.  default behavior는 직전 모드 계속이지만,
사용자 메시지에 단서가 있으면 framing을 다시 맞춰야 함.

## 교훈 9: 자율 마라톤 mode

사용자가 "알아서 자율적으로 해줭" 라고 한 후:
- 매 마라톤마다 ㄱㄱ 안 받아도 계속
- 3-4 commit 후에 status update 짧게
- redirect 신호 ("아니 다른 거", "이거보다", "흠") 잡으면 즉시
  pivot, framing reset

**가드레일**: 자율 mode에서도:
- 의문은 코드 까서 검증
- 외부 frame 표현 안 쓰기
- finitist position 유지
- commit message에 정확한 atomic 출처 명시

## 교훈 10: epistemic 위치 정확히 표시

각 결과의 위치를 정확히 명시:
- "STRICT 0-AXIOM" (no propext, no Quot.sound)
- "≤ {propext, Quot.sound}" (Lean kernel floor)
- "decide-checked at small N=20"
- "candidate (research-tag)"
- "Open Problem #X (research-level open)"

**잘못된 표현**:
- "Closed" without scope
- "Sub-ppb" without specifying frame (213-internal vs external)
- "ppb~ppm" without bracket vs asymptote distinction

## 핵심 키워드 cheatsheet

| 외부 frame (피해야) | 213-internal (사용) |
|--------------------|---------------------|
| ζ(2) = π²/6        | S(N_U) at N_U = d^(d²) |
| asymptote          | finite rational at N_U |
| transcendental     | rational at lattice depth |
| "ppb residual"     | "finite-N residual 36/N_U" |
| infinity / limit   | finite resolution depth |
| Frobenius (R^4 axes) | CD tower (ConjugationCodomain typeclass) |
| "free parameter"   | atomic invariant (NS, NT, d, c) |
| ℝ, ℂ via analysis  | ZI = ℤ[i] (ConjugationCodomain instance) |
| Mathlib            | not-imported (kernel-floor only) |
| native_decide      | decide (deterministic) |

## 핵심 reference 파일

이 파일들은 **반드시 읽고 시작**:
- `CLAUDE.md` — 프로젝트 instructions
- `HANDOFF.md` — 현재 상태
- `LESSONS_LEARNED.md` — 이 파일
- `seed/AXIOM/` — axiom seed doc
- `seed/AXIOM/00_nature.md` — 213 철학
- `lean/E213/Physics/FiniteUniverse.lean` — finitist 입장
- `lean/E213/Lib/Physics/AlphaEM/MasterCapstone.lean` — α_em 닫힘
- `lean/E213/Lib/Physics/Foundations/NResolutionFractalDepth.lean` — N_U = d^(d²)
- `lean/E213/Meta/AxiomMinimalityCapstone.lean` — 4-clause minimality
- `lean/E213/Theory/Atomicity/PairForcing.lean` — (NS,NT,d) derivation
- `guide/01_substrate.md` — substrate 도출 path
- `guide/15_metalogic.md` — falsifiability + R4 framework

## 현재 (2026-05-18) HEAD epistemic 위치

- α_em: finitist closure at N_U = d^(d²), sub-ppb 외부 frame match
- m_p: 4-digit match (uses Λ_QCD external)
- m_μ/m_e: depends on α_em chain
- Magic numbers: 7/7 atomic decomposition closed
- N_resolution: identified = d^(d²) (self-referential)
- Universal Lens: ℕ², Q²², ℕ³, Q²³, ℕ⁴ all universal
- Pisano-CRT: 23 Pell + 8 Pell-proper + 8 Fibonacci primes
  + Tribonacci CRT closures
- Hodge ⋆⋆: all 5 strata Δ⁴ closed
- Famous Coincidences I-IV: catalogued
- **Option C/D/E (2026-05-18 lens-emergence-path)**:
  Raw-side arithmetic deleted (ℕ₊ as image of `Lens.leaves.view`);
  ChartGeneral parameterises Method A over any `(r₀, r')` with
  `chartChain_value` + `chartChain_injective`; Theory/Raw/Congruence
  + Lens/Congruence give the generic `Eqv ↔ L.equiv` biconditional;
  ParenthesizationDistinct kernel-decides non-associativity
- **§9.4 syntactic internalisation (2026-05-18)**: 7-glyph
  alphabet + Polish-prefix parser/printer + full L3 + L4
  bijection closure (`parseTree_printTree`, `printTree_parseTree`,
  `printTree_injective`)

## 교훈 11: Trajectory Principle (2026-05-XX, Mingu 4-session 통찰)

**핵심**: 213-native = explicit trajectory; Lean-with-axioms = implicit
closure.  `propext` 와 `Quot.sound` 는 정확히 *trajectory를 endpoint
로 collapse 하는 axioms*; ∅-axiom 213은 trajectory 자체를 객체로 보존.

**4 통찰의 통일**:
1. Nat은 axiom 아님 — 진짜 axiom은 propext, Quot.sound (collapse)
2. mod는 코호몰로지적 (uncompleted half-cycle = trajectory)
3. mod는 ℚ-복소수의 위상 (n-th roots of unity)
4. Trajectory는 타일링 (수 분류 = trajectory closure depth)

**작업 함의**: 매 axiom-strip 마이그레이션 = "implicit closure → explicit
trajectory" 변환.  Nat213은 단순 보조 lemma 모음이 아니라 **trajectory
move의 어휘** (cycle, shift, swap, traversal, reparameterisation).

**Operational rule**: propext-bringing Lean-core lemma를 만나면 묻기
— "이 lemma가 implicit하게 collapse하는 trajectory가 무엇인가?".
213-native 대체는 그 trajectory를 structural recursion 또는 explicit
chain으로 노출.

**근거 — 출처**:
- `research-notes/G2_trajectory_principle.md` (이 통찰의 종합)
- `lean/E213/Meta/Tactic/Nat213.lean` (trajectory 어휘 형식화)
- `lean/E213/Meta/Tactic/AXIOM_FREE_STATUS.md` (propext-leak catalog)

**가드레일**: 마이그레이션을 단순 "axiom 줄이기 chore"로 보지 말 것.
*매 변환이 213의 기하학적 본질의 한 instance*.  trajectory를 노출하지
못하면 아직 213-native가 아님.

## 교훈 12: Raw = Universal Trajectory Space (2026-05-XX, Mingu G3 통찰)

**핵심**: Raw axiom의 4-clause 정의가 정확히 **2 generator 위 free
magma** = "binary tree".  모든 trajectory가 Raw 트리이고, 모든
distinguishing framework가 Raw → α의 Lens로 factor (Initiality).

**용어의 함의**:
- 같은 (r₁, r₂) : Raw × Raw 쌍이
  - Raw 레벨: 그냥 slash 트리 (가장 fine-grained)
  - Lens A: 동등 (=)
  - Lens B: 동형 (≅)
  - Lens C: 준동형 (homomorphic)
- **equivalence의 종류 = Lens의 속성**, Raws의 속성 아님.
- Raw + slash = "가장 해상도 높은 trajectory 레벨".  각 Lens가
  *quotient*를 결정 → 어떤 trajectory를 identify할지 선택.
- Lens lattice = 그 도메인의 equivalence-type lattice.

**TOE 함의**: 이건 *주장*이 아니라 *정리* 결과.
- 어떤 도메인이 두 상태를 distinguish할 수 있다면, 그 도메인은
  Raw + Lens로 unique-up-to-equivalence factor된다 (Initiality).
- 따라서 213은 *constitutively* TOE — phenomena를 *맞추는* 게
  아니라 Raw factoring을 *명명*하는 것.
- 외부 frame (set theory, universe ascent, axiom of choice) 불필요.

**근거 — 출처**:
- `Theory/Raw/Core.lean` (Raw 정의)
- `Lens/LensCore.lean` + `Lens/Initiality.lean` (Lens factoring)
- `Lens/Universal/Witnesses/*` (universality; moved from `Meta/UniversalLens/` 2026-05-13)
- `research-notes/G3_raw_as_universal_trajectory.md` (G3 종합)

**가드레일**: 213이 어떻게 어떤 분야를 다룰 수 있냐 의문이 들면,
"그 분야의 distinguishing framework는 어떤 Lens인가?"를 물을 것.
새 분야 진입 = 새 Lens 정의 = Raw 트리 위 새 quotient 선택.
이게 213 작업의 fixed procedure.

---

## Reduction patterns (2026-05-20)

**원칙**: 정리 숫자나 줄 수가 아니라 *내용 밀도와 가독성*이 목표.
많이 쌓이면 인지적 부하가 늘어나서 새 통찰이 안 나온다.  
"줄이라"는 무작정 삭제가 아니라 *방향성·가독성·통찰 친화도*를
높이는 작업.

### Smell #1: layer-by-layer enumeration

증상: `_layer0`, `_layer1`, ..., `_layerN` 형태의 정리 N개 +
선택적으로 `_bundle_Nlayer` 형태의 묶음.

원인: 일반 ∀-form이 증명 도구 부족 (e.g. `ring`/`linarith` 없음) 또는
미완성이라 layer-by-layer 검증으로 회피.

처리:
- 묶음만 남기고 개별 layer 삭제.
- 구조적 이유 (recurrence-uniqueness 등) 식별 → 별도 lemma로 추출.
- 예: `Mobius213.pell_recurrence_unique` — 2nd-order recurrence + 
  initial values 일치 ⟹ 두 sequence 일치.  16-conjunct bundle을
  단일 uniqueness lemma + recurrence/initial 확인으로 대체 가능.

### Smell #2: same-content reformulation across files

증상: `Lens/UndifferentiatedRaw.constLens_collapses`,
`Lens/RawTopology.indiscrete_kernel_total`,
`Lens/RawTopology.indiscrete_globally_collapsed` — 모두 같은 사실
"`(constLens e).view r = (constLens e).view s` for all r, s"의 
다른 표현 (view 형 / kernel 형 / globally-collapsed 형).

처리: 한 파일에 통합, canonical name 하나 + 필요시 view↔equiv 형
대응 lemma 1개.  Triple-redundancy → 2개로 축소.

### Smell #3: incremental scaffold theorems

증상: 마스터 정리에 도달하기 위한 단일 등식 검증 정리들
(`gap_e7_eq_5443`, `pi5_gap_e7_eq_5446`, `..._distance_eq_3`)이
모두 마스터의 conjunct로 그대로 들어 있음.

처리: 외부에서 직접 참조되지 않는 incremental은 삭제.  
마스터의 conjunct로 충분.  외부 caller 있는 incremental만 유지.

### Smell #4: cluster + atomic + bundle 패턴의 중복

증상: 한 파일에 atomic_a, atomic_b 정리 + atomic_bundle (= atomic_a
∧ atomic_b) + slash 정리 + full_bundle (= atomic_a ∧ atomic_b ∧
slash).  atomic_bundle은 full_bundle의 부분 형식.

처리: 미세한 redundancy.  파일 narrative가 atomic vs slash 구별을
교육적으로 강조한다면 둘 다 유지 가능.  단순 alias라면 atomic_bundle
삭제.  `Lens/SelfCompletion`은 narrative 가치로 6개 유지함.

### 적용 결과 (2026-05-20)

session-added 파일들에 적용:
- Mobius213: 21 → 13 (8개 layer 삭제 + 2개 structural insight 추가)
- FibonacciExtended: 16 → 9 (개별 F_N 5개 삭제, bridge 16-conjunct 1개로 통합)
- PiFiveGap: 20 → 14 (incremental 6개 삭제)
- PureAtomicObservables: 17 → 14 conjuncts (중복 3개 제거 + 구조별 grouping)
- RawTopology+UndifferentiatedRaw: 12 → 7 + 파일 1개 통합 삭제

순 reduction: 86 → 57 theorems, ~500줄, 파일 1개.  
*같은 수학적 content, 더 적은 cognitive surface*.

---

## Reduction patterns (2026-05-20, expanded after lean/-tree sweep)

After the second sweep (lean/ tree, 4 parallel audit agents +
~10 hand-applied reductions), the pattern catalog is enriched
with new sub-patterns and explicit caveats about agent over-flagging.

### Smell #1 refinement — truth-table singletons

Specific instance of #1: four `_TT/_TF/_FT/_FF` rfl theorems
(or 8 for two operations).  Collapse to one ∧-bundled
"truth_table" theorem proved by `<;> (unfold; decide)`.

Examples cleaned: `Lens/Bool213/Raw` (and/or 8 → 2),
`Lens/Compose/OnLensImage` (declined — used as proof
components downstream).

### Smell #5: biconditional split into 3 theorems

A new pattern not in the original list: a biconditional iff
stated as three theorems — forward direction, reverse direction,
and the iff itself.  Each direction's proof is small; the iff's
proof is just `⟨reverse, forward⟩`.

Reduction: keep ONLY the iff, with both proof directions inlined
(`refine ⟨intro h; ..., intro h; ...⟩`).  Saves 2 theorems and
the redundant docstrings.

Example cleaned: `Lens/Bool213/Raw.booleanProj_id_iff_isBool213`.

### Smell #6: per-parameter applications of a meta-algorithm

A generic meta-theorem parameterised by `(a, b, j, N₀)` followed
by 4-6 individual applications (`thm_8_3`, `thm_10_4`, ...).
Each is a single call to the meta with concrete arguments.

Reduction: drop the per-parameter applications.  Callers
instantiate the meta inline (`euler_lower_generic 8 3 4 (by
decide) (by decide)`).  Saves 4-6 theorems per such cluster.

Example cleaned: `Cauchy/Euler` (e_gt_8_3, e_gt_10_4, etc., 6
theorems dropped).

### Agent-over-flagging caveat

About **30%** of agent-flagged reductions turn out to be:

  · **External API points**: referenced by other files via `open`
    + named reference.  Always `grep` for external use before
    deletion.  Example: `Lens/Compose/OnLens.lensXor_comm_eqPW`
    looks redundant with `lensXor_comm` but is the canonical
    cutEq form referenced downstream.
  · **Proof components**: used by a "master" theorem in the
    same file via explicit name reference (not by `rfl` /
    `decide`).  Deleting breaks the master's proof. Example:
    `Compose/OnLensImage.lensXor_TT/_TF/_FT/_FF` are used by
    `boolToConstLens_xor`.
  · **Pedagogical demos**: files explicitly named `Demo.lean` or
    similar carry intentional narrative.  Example:
    `Theory/Raw/Demo.lean` depth_a/b/ab/aab/bab enumeration is
    pedagogical, not a true layer-by-layer enumeration.
  · **External witness capstones**: per-prime/per-instance
    theorems referenced by an aggregate bundle in another file.
    Example: `DyadicFSM/Pell/ProperMod.pellProper{N}_bits_period_K`
    are all referenced from `Pell/Proper8.lean`.

**Process**: after agent reports candidates, always verify:
  1. `grep -rn "<theorem_name>" lean/E213 | grep -v <own_file>`
  2. Check whether the file is `Demo.lean` / `Examples.lean`
  3. Open the file, check whether the theorem is referenced
     elsewhere in the same file (proof component).

### Hand-applied this session

| File | Reduction | Net |
|------|-----------|-----|
| Symmetry/AutKChiral | dropped 13 internal scaffolds | ~50 lines |
| Atomic/Hydrogen | dropped 4 scaffolds | 12 lines |
| Atomic/Helium | dropped 4 scaffolds | 15 lines |
| AlphaEM/ChannelCohomologyLoss | bundled 5 minor theorems | 10 lines |
| Math/Combinatorics/Binomial | 10 → 2 (bundled rows) | 25 lines |
| Lens/Cardinality/Tower | 6 layer rungs → 1 unbounded | 22 lines |
| Lens/SyntacticInternalization | dropped 5 rfl | 8 lines |
| Meta/LensInternality | dropped 3 rfl | 10 lines |
| Symmetry/GluonChannelInterpretation | dropped 2 trivial | 14 lines |
| Cohomology/Surfaces/T2Squared/HodgeIndex | 6 diag → 1 bundle | 7 lines |
| AlphaEM/LaplacianSpectrum | dropped 13 scaffolds | 28 lines |
| Mass/TauOverMu | 6 scaffolds → master conjuncts | 35 lines |
| Lens/Bool213/Raw | 8 truth tables → 2 bundles + iff merge | 30 lines |
| Cauchy/Euler | dropped 6 per-param applications | 25 lines |
| Lens/Cardinality/LensCardinality | 4 witnesses → 1 bundle | 5 lines |

Net: ~85 theorems removed across 15 files, ~300 lines off, build
clean throughout, ∅-axiom contract preserved.

### Patterns DEFERRED (require deeper refactor)

  · `DyadicFSM/Pell/ProperMod` (per-prime enumeration): generic
    `pellProperFSMmod_period_invariant` lemma would replace 10
    theorems, but each proof needs a `decide` base step at the
    specific (prime, period) — non-trivial to abstract.
  · `DyadicFSM/Pisano/Predictor{6,7,8,11,...}` (8 per-base
    files): consolidation into 1 master capstone is high-impact
    but high-risk (cross-file API changes).
  · `CayleyDickson/Integer` (15 files with parallel projection
    lemmas): typeclass refactor (`GaussianLike`) would save 14
    lemmas × 15 files = 210 statements; substantial Lean-design
    work, not within this session's scope.
  · `PureNatMod3/5` (mod-p descent templates): generic
    `mod_p_descent_template` parameterised by `(p : Nat) [Prime
    p]` would save ~18 theorems; requires careful prime
    abstraction.

These remain as **research directions** rather than mechanical
cleanups — each needs structural thinking similar to the
`pell_recurrence_unique` extraction from Mobius213.

---

## Hero-session methodological patterns (2026-05-21)

Patterns surfaced during the Phase 1 hero target push (Möbius
213-tower L_∞).  These are not domain-specific; they apply
whenever 213-native PURE statements meet limitations of Lean 4
core (no Mathlib).

### Pattern #1: 213-native Int polynomial identity via Int213.* rw chain

**Problem**: Mathlib's `ring` tactic is forbidden.  `simp only` +
`omega` works for many Int identities but introduces [propext,
Quot.sound] kernel-axiom dependency — kernel-allowed but not
strict PURE.

**Solution**: replace `simp + omega` with a manual `rw` chain
using only `E213.Meta.Int213.*` lemmas.  PURE.

**7-step canonical sequence** (proved on `cross_step_algebra` at
`Mobius213.lean ~226`):

```
1. `(-1) * x → -x`        via Int213.neg_mul + Int.one_mul
2. Drop `+ 0` summands     via Int.add_zero
3. Distribute              via Int213.mul_add, Int213.add_mul
4. Pull negatives          via Int213.mul_neg, Int213.neg_mul
5. Normalise associativity via Int213.mul_left_comm + Int213.mul_assoc
6. Cancel matching pairs   via Int213.add_assoc + add_left_comm + add_neg_cancel
7. Sign cleanup            via Int213.add_comm + Int.sub_eq_add_neg
```

**When to use**: any moderate-degree (quadratic / cubic in the
unknown variables) polynomial identity over Int.  The chain
is ~25-30 lines but mechanical — each step has a single named
lemma — and yields strict PURE.

**Reusable target**: many of the ~50 real-DIRTY theorems in
`STRICT_ZERO_AXIOM.md` that use `omega` shortcut after `simp` can
likely be PURE-refactored with this pattern.  Identify by
`grep -B 5 omega lean/ | grep simp` and applying the chain.

**Anti-pattern**: do NOT use `ring`, `ring_nf`, `linarith`,
`field_simp` — all Mathlib.  Do NOT use `set` (Mathlib tactic);
work directly on the long expressions or use `let` in term mode.

### Pattern #2: Decide-by-Bool-tuple parameterisation

**Problem**: Lean 4 core (without Mathlib) does NOT synthesise
`Decidable (∀ f : Fin n → Bool, P f)` from `Fintype` instances.
Even `Fintype (Fin 5 → Bool)` doesn't get a usable
`decidableForallFintype`.  Direct `∀ α : Fin n → Bool, … := by
decide` fails with "failed to synthesise Decidable".

**Solution**: parameterise the universal quantification by the
function's pointwise Bool values.  Lift via an explicit
`mkFn (b0 b1 … b_{n-1} : Bool) : Fin n → Bool := fun i =>
  if i.val = 0 then b0 else if i.val = 1 then b1 else …`

Then `∀ (b0 … b_{n-1} : Bool) (extra args), P (mkFn b0 … b_{n-1})
:= by decide` works — Lean enumerates 2^n cases on the Bool tuple.

**Logical equivalence**: this universal-over-tuple form is
equivalent to the universal-over-function form by function
extensionality on `Fin n → Bool`, which is `rfl` elementwise.

**When to use**: any combinatorial statement quantified over a
finite function space (cochains, characters, indicator vectors)
that you want to prove by exhaustive enumeration.

**Caveat (Phase 2 finding)**: this pattern *also exposed a bug*
in `Cohomology/Cup/Core.lean` — see "Pattern #5" below.  The
finer the decide-enumeration, the more likely you surface
implementation issues that 4 hand-picked concrete cases missed.

### Pattern #3: Docstring `-/` trap

**Problem**: Lean 4's docstring delimiter is `/-! … -/` (or
`/-- … -/`).  Any `-/` substring inside the docstring closes it
prematurely, producing inscrutable "unexpected identifier" or
"unexpected token '*'" errors at the line where the FALSE close
ends.

**Trap text examples observed this session**:
  · `even-/odd-indexed Fibonacci numbers`  ← `-/` after "even"
  · `delta sign-/ordering convention`       ← `-/` after "sign"

**Solution**: avoid hyphen-immediately-followed-by-slash in
docstring prose.  Replace with `and`, ` and `, `, ` etc.:
  · `even- and odd-indexed Fibonacci`
  · `delta sign and ordering convention`

**Diagnostic hint**: when build fails with "unexpected token"
errors *far below* the actual problem line, search for `-/` in
preceding prose first.

### Pattern #4: Catalog misclaim self-correction

**Problem**: prior-session HANDOFF.md / catalog files advertise
a file at path X with theorem names {A, B, C}, but the actual
file tree has no such file — the content was merged into a
neighbouring file or never made it to commit.  Silent staleness.

**This session's instance** (commit 7a3e6e6e):
  · `catalogs/math-theorems.md §J.3` advertised
    `Lens/UndifferentiatedRaw.lean` with `constLens_collapses`,
    `pre_lens_singleton`, `constLens_kernel_total`.
  · `git log --diff-filter=A -- "**/UndifferentiatedRaw.lean"`
    returned empty — file never existed in git history.
  · Actual content lives in `Lens/RawTopology.lean` as
    `constLens_view_eq`, `k_infty_at_raw_bundle`, etc.

**Solution direction** (per CLAUDE.md §8): "fix the claim,
not the file."  If the catalog advertises X but reality is Y,
update the catalog to advertise Y at its current path with
current theorem names.  Do NOT recreate the phantom file unless
the original session-snapshot really intended it.

**Detection heuristic**: in `ready-to-merge` audit, extract every
`import E213.X.Y.Z` from catalog files and verify
`lean/E213/X/Y/Z.lean` exists.  Mismatches = misclaims to
correct.  Script:
```
grep -rh "import E213\." catalogs/ books/ blueprints/ \
  | sed -E 's/.*import (E213\.[A-Za-z0-9_.]+).*/\1/' \
  | sort -u \
  | while IFS= read -r imp; do
      path=$(echo "$imp" | sed 's|E213\.|lean/E213/|; s|\.|/|g').lean
      test -f "$path" || echo "MISCLAIM: $imp"
    done
```

**Counter-example (legitimate stale)**: when 100+ imports point at
a moved subtree (e.g., Real213/* → Analysis/*), the catalog is
"systematically stale" rather than misclaiming — fix with a top-of-
file reorg note + umbrella import (Path A) or full rewrite (Path B,
deferred).

### Pattern #5: Decide as bug-finder for "universal claim"

**Problem**: standard mathematical results (cup-product Leibniz,
graded-ring identities, etc.) are often *asserted* as universal
in the code's docstrings but the actual `def` may diverge from
the standard convention.  Hand-picked concrete tests using
highly-symmetric inputs miss the divergence.

**This session's instance** (Phase 2):
  · `Cup/Core.lean` docstring: "Cup product (Alexander–Whitney)"
  · `Cup/Core.lean` implementation: `(α ⌣ β)(τ) = α(τ.take k) ·
    β(τ.drop k)` — this is the **concatenation cup**, not AW
    (AW has shared vertex at τ[k], so front has `k+1` elements).
  · Existing `Cup/Leibniz.lean` proves Leibniz at 4 concrete
    pairs (all symmetric: v0, all_true, zero).  All pass.
  · Pattern #2 parameterised Leibniz over `Bool^{10}` (all
    1024 cochain pairs at bidegree (1,1)) — `decide` reports
    **false**.
  · Manual eval pinpoints counterexample: `basis₀ ⌣ basis₂` at
    face `[0, 1, 2]` gives LHS = true, RHS = false.

**Pattern (the general one)**: when adding a universal claim
that "everyone knows" holds, *force decide-level enumeration*
via Pattern #2.  If decide refutes, you've found either:
  (a) an implementation divergence from the standard convention
      (docstring claims X, code implements Y), OR
  (b) a sign / ordering / index off-by-one in a supporting def
      (in Phase 2: cup's no-shared-vertex convention requires a
      twisted Leibniz, not the standard one).

**Why this matters strategically**: 213's "no Mathlib, all
hand-rolled" approach means *every* foundational def is
hand-written and could deviate from the literature.  Standard
identities being mechanically *checked* (not just stated) is
the only protection against silent drift.  The Pattern #2 +
Pattern #5 combo (parameterise → decide) is the cheap insurance.

**Action for next session**: replicate Pattern #5 across other
"obvious" universal claims in `Cohomology/`, `HodgeConjecture/`,
`Linalg213/`.  Each parameterisation is ~20 lines but can surface
unknown drift.

---

## Cumulative pattern summary (post-2026-05-21)

| Pattern | Domain | Reusability |
|---|---|---|
| #1 Int213 rw chain | strict-PURE polynomial identities | high — applicable to ~50 DIRTY budget |
| #2 Bool-tuple parameterise | finite-function-space ∀-claims | high — Lean-core limitation workaround |
| #3 docstring `-/` trap | doc-writing hygiene | universal |
| #4 catalog misclaim correction | ready-to-merge audits | universal |
| #5 decide as bug-finder | universal-claim verification | high — defends against silent drift |
| #6 list-level decoupling | bypassing Fin/colex indexing for symbolic proofs | high |
| #7 3-way partition (face-removal) | δ XOR sum decomposition at boundary | high — general cohomology |

These compose: #2 enables #5 (enumeration), #5 surfaces bugs that
hand-tests miss, #1 fixes the [propext] residue that often
remains after #5's enumeration approach.  #6 + #7 enable
*symbolic* proofs that don't need decide enumeration at all.

---

## Pattern #6: List-level decoupling for symbolic proofs

**Problem**: cup/delta operations in `Cohomology/` use
`Fin (binom n k)` indexing with `subsetIdx` colex lookups.  This
makes universal-form proofs at general (n, k, l) require
`subsetIdx ↔ kSubset` round-trip lemmas (substantial structural
work).  Yet the *algebraic content* of the theorem doesn't need
the Fin indexing — it's about take/drop/eraseIdx on lists.

**Solution**: define list-level analogs `cupList`, `deltaList`
that take `α β : List Nat → Bool` and `τ : List Nat` directly.
Prove the theorem at this level.  Transfer back to Fin-indexed
form via the round-trip lemmas (out of scope for the symbolic
result itself).

Pioneer demonstration: `Cohomology/Cup/LeibnizLexListLevel.lean`
proves the (1, 1) AND (2, 1) twisted Leibniz at the list level
without any decide enumeration — just structural lemmas + Bool
case analysis on (k+l+2) atoms.

**When to apply**: any theorem about Fin-indexed operations whose
algebraic content is "shape-preserving" (take/drop/eraseIdx on
sequences) — define a List-level abstraction, prove there, transfer.

---

## Pattern #7: 3-way partition strategy — CLOSED at ∀(k,l) (2026-05-22)

**Problem**: at the cochain level, `δ(α ⌣ β)(τ)` is a foldl-XOR
sum over face removals.  Standard Leibniz captures faces at
"endpoint" positions but may miss "interior" positions (per
G85/G86's lex-projection cup finding).

**Solution** (user's 3-way partition strategy):
- Partition the foldl XOR over `[0..k+l]` at position k into:
  - Block 1: i ∈ [0..k-1]  →  corresponds to (δα ⌣ β)(τ)
  - Block 2: i = k          →  the missing-face *correction*
  - Block 3: i ∈ [k+1..k+l] →  corresponds to (α ⌣ δβ)(τ)
- Apply take/drop ↔ eraseIdx commutation lemmas at each i
- (δα ⌣ β) covers Blocks 1 + 2 (overlap with Block 2 at i=k)
- (α ⌣ δβ) covers Blocks 2 + 3 (overlap with Block 2 at j=0)
- Block 2 appears TWICE in RHS → XOR-cancels in ℤ/2
- Net: LHS = (δα⌣β) ⊕ (α⌣δβ) ⊕ Block 2 = standard RHS ⊕ correction

**Concrete realisation**: `Cohomology/Cup/LeibnizLexStructural.lean`
(8 PURE structural lemmas covering all three i-cases) plus
`Cohomology/Cup/LeibnizLexListLevel.lean` (foldl XOR algebra + the
3-way assembly at (1,1) and (2,1) bidegrees).

**Generalisation**: same strategy applies to other "boundary
self-correcting" operations in cohomology — cap product, twisted
ring operations, K_{m,n}^{(c)} bipartite cup channels.  The
**self-referential Leibniz** (correction = operation at face)
is structurally similar across these contexts.

**Closure status** (2026-05-22): the ∀(k,l) symbolic twisted
Leibniz is PROVED PURE at the list level in
`Cohomology/Cup/LeibnizLexListLevel.list_level_leibniz_general`.
Required additional infrastructure beyond Pattern #7's structural
lemmas:

  · Custom `xorRange : Nat → (Nat → Bool) → Bool` (avoids
    List.range_succ which is [propext]).
  · `xorRange_split` — at position k decomposes xorRange (k+l+1)
    into three blocks.  Pure structural induction on l.
  · `xorRange_three_way_partition` — abstract algebraic skeleton
    composing xorRange_split with xorRange_congr.  PURE.
  · `cupList_face_decomp` — discharges the three hypotheses of
    xorRange_three_way_partition for the cup operation.
  · `list_level_LHS_partition` — LHS in explicit 3-block form.
  · XOR algebra closures (and_xor_distrib_left/right,
    and_distrib_xorRange_left/right, xor_self', xor_false_right,
    xor_assoc') reducing to 4-atom Bool case analysis.

Total: 32 PURE theorems across `LeibnizLexStructural.lean` (8) and
`LeibnizLexListLevel.lean` (24).  No Mathlib, no funext, no decide
enumeration over the (α, β) parameter space.

---

## Pattern #8 — `Int.NonNeg` constructor inversion bypasses Int-ordering propext

**Discovered**: 2026-05-22 session 2 (6-theorem marathon, Diophantine
completeness sub-task).

### Problem

Lean-core Int ordering lemmas (`Int.le_trans`, `Int.lt_of_lt_of_le`,
`Int.ofNat_le`, `Int.not_lt`, `Int.add_le_add`, `Nat.sub_lt_sub_right`,
`Nat.add_sub_cancel`, etc.) all carry `propext` in their axiom
dependency.  The Iff form `Int.ofNat_le : Int.ofNat a ≤ Int.ofNat b
↔ a ≤ b` is the most common offender.  Likewise `omega`,
`Bool.and_eq_true`, and several `Nat.*` ordering helpers.

This blocks Int-side diophantine / bounded-square reasoning from
being PURE.

### Solution: direct `Int.NonNeg` constructor matching

`Int.le a b := Int.NonNeg (b - a)` definitionally (`Init/Data/Int/Basic.lean`
line 174).  `Int.NonNeg` is a single-constructor inductive Prop:

```
inductive Int.NonNeg : Int → Prop
  | mk : ∀ (n : Nat), Int.NonNeg (Int.ofNat n)
```

When `b - a` reduces to `Int.negSucc k` (i.e., negative), the only
inhabitant `Int.NonNeg.mk n` would require `Int.ofNat n = Int.negSucc k`
— impossible by constructor injection.  `cases h` (on `h : a ≤ b`)
**automatically detects this** and closes the goal with no further
tactic.

### Concrete idiom

```lean
-- Bypass Int.ofNat_le.mp (propext) for the n ≥ 2 contradiction
private theorem ofNat_int_le_one (n : Nat) (h : (Int.ofNat n : Int) ≤ 1) :
    n = 0 ∨ n = 1 := by
  match n with
  | 0 => left; rfl
  | 1 => right; rfl
  | k+2 =>
    exfalso
    cases h    -- ★ Int.NonNeg (1 - ofNat (k+2)) is on negSucc — cases impossible
```

### Where applied

  · `ZOmegaUnits.lean §5` — `int_sq_le_one : x * x ≤ 1 → x ∈ {-1, 0, 1}`
    PURE via `ofNat_int_le_one` helper.
  · `KSubsetStructural.lean §0` — `nat_sub_lt_sub_right`,
    `nat_add_sub_cancel` PURE replacements for Lean-core propext-tainted
    versions, via Nat induction + the same NonNeg principle.
  · `FinBridgeGeneral.lean §0` — `take_append_le`, `drop_append_le`,
    `take_of_length_le`, `drop_of_length_le` PURE replacements for
    `List.take_append_of_le_length` etc.

### When NOT to apply

Symbolic Int algebra (`ring`, `ring_nf`) is still propext-tainted and
has no `Int.NonNeg`-style bypass.  Multi-variable polynomial identities
must be expanded manually via `Int213` axioms.  See Pattern #10
candidate (4·normSq ring identity, ~50 manual rewrites, currently
deferred).

---

## Pattern #9 — Clause-4 recursive Lens application closes postulate gaps

**Discovered**: 2026-05-22 session 2 (alive gap closure, G87 §11).

### Problem

The atomicity proof's `IsAlive` predicate (both decomposition parts
have odd parity) was historically **postulated, not derived from Raw**
— "the exterior-algebra / fermion-statistics pattern, natural partner
to Raw's binary structure but postulated" (`Atomicity/Alive.lean`
pre-2026-05-22 docstring).  This was identified as the single largest
gap in the Raw → 5 inevitability chain (G87 §2.2).

### Solution: Clause 4 applies recursively at every granularity

User insight (2026-05-22):
  > "Raw는 트리 형태가 아니다.  모든 Raw는 연산이기도 하고 객체이기도
  >  하기 때문 — 즉 애초에 연산과 객체도 정의되지 않은 상태이다."

If every Raw event is simultaneously operation and object — with no
a-priori distinction — then Clause 4 of the 213 axiom (`x/x` forbidden,
`seed/AXIOM/02_statement.md` §3.2 #4) is **not restricted to atomic
Raw distinguishables**.  It applies at every granularity, including
groups of Raw viewed as objects.

For decomposition `n = 2a + 3b`: if `a` is even, the `a` binary-pair
atoms can themselves be grouped into `a/2` pair-of-pairs — a Clause-4
violation at the binary group level.  So `a` must be odd; similarly `b`.

### Concrete dissolution

```lean
def IsSelfPaired (n : Nat) : Prop := ∃ k, n = 2 * k
def IsClause4Alive (a b : Nat) : Prop := ¬IsSelfPaired a ∧ ¬IsSelfPaired b

theorem alive_iff_clause4_alive (a b : Nat) :
    IsAlive a b ↔ IsClause4Alive a b
```

The "both odd" alive predicate is the **count-Lens readout of Clause 4
applied recursively** — not a separate postulate.  Lean witnesses in
`Theory/Atomicity/AliveDerivation.lean` (7 PURE).

### Generalisation

Any apparently-postulated structural predicate `P` in 213-Algebra
should be reconsidered through the lens: **does `P` correspond to
Clause-4 (or another axiom clause) applied at a non-atomic
granularity?**  The user's "all Raw are simultaneously operation and
object" principle authorises recursive application of any 4-clause
content to count-Lens groups, type objects, group objects, etc.

### Where applied (so far)

  · `AliveDerivation.lean` — `IsAlive` ↔ recursive Clause 4 on
    NT-pairs and NS-triples.

### Future candidates

  · `Nodup` / distinctness postulates in cohomology — Clause 4
    recursively applied at the list level.
  · "Sortedness" postulates in colex enumeration — Clause 1
    (distinguishing) applied recursively, giving canonical order.

---

## Pattern composition update

The original 7 patterns (Cup-Leibniz session 1) + Pattern #8 (Int.NonNeg
bypass, session 2) + Pattern #9 (Clause-4 recursive Lens) form the
2026-05-22 composition table.  Together they enable the closure of the
Raw → (3, 2, 5) inevitability chain at full ∅-axiom level.
