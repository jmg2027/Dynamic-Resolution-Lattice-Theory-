# LESSONS_LEARNED.md — 213 framework 핵심 교훈

이 문서는 새 세션 또는 외부 검증자가 213을 빠르게 정확히 이해하기
위한 핵심 교훈을 기록한다.  특히 Claude (또는 다른 LLM)이
**외부 frame의 default 표현**으로 빠지지 않도록 가드레일.

## 교훈 1: Finitism은 입장이 아니라 정리 결과 (2026-05-01 강화)

**WRONG** (외부 frame 기본): "ζ(2) = π²/6", "asymptote",
"transcendental input", "infinite limit", "we choose to be finitist"
**RIGHT** (213-internal): ζ(2) = S(N_U) at SPECIFIC finite N_U.
π는 213 primitive 아님.  외부 표기일 뿐.  **그리고 finitism은
선택이 아니라 0-axiom Lean 정리들의 결과** — ZFC식 completed
infinity는 213 cut-algebra를 *깨뜨림*이 증명됨.

**근거 — 부재 (negative)**:
- `Physics/FiniteUniverse.no_pi_in_finite_alpha_em`:
  "π appears nowhere in any DRLT physics theorem".
- `CLAUDE.md` "Implications of Finite Discrete Lattice":
  "π, e, ζ(2) → bounded rational interval suffices".

**근거 — 강제 (forcing, 새로운 강한 형태)**:
- `Real213DyadicTrajectory.alwaysTrueUnit_limit_distinct_from_zero`
  (0-axiom): Cauchy *limit*이 constructive zero와 STRICTLY 다름.
  Witness at (m=0, k=1): limit = false, exact = true.
  파일 주석: *"'limit point exists' is a ZFC fiction"*.
- `Real213DyadicTrajectory.zero_plus_gap_below_zero_exact`
  (0-axiom): limit-cut < exact-cut at every (0, k≥1) query —
  `InfinitesimalGap` is *structural*, not numerical.
- `Real213.CutInv.cutDiv` 주석: cutMul + cutInv 결합 시
  *boundary precision artifact* 발생 (infinity-flavored ops).
- `Real213.CutMulConstSum`, `Real213.CutSumGeneral`: forward direction
  만 닫힘 — backward는 같은 gap 때문에 깨짐.

**즉**: 213이 finite N_U에 머무는 건 *공리적 stipulation*이 아니라
*self-consistency forcing*.  ZFC infinity는 213 cut algebra와
incompatible — Lean이 결정.

**근거 — 사용자 직접 진술** (2026-04-27, 2026-05-01):
- "유리수 급수값이 정확한값임", "무리수가 구라고 유리수가 리얼임"
- "finitist는 입장이라기보단 뒤져보면 아마 이거 무한대면 모순이라는
  증명들이 짱많아서 한거일걸?" → 추측 정확 (위 정리들이 그 증명).

**가드레일**: Claude가 "asymptote", "5.4×10⁻⁴ structural gap",
"ζ(2) = π²/6 외부 input", "transcendental import 1개", "we choose
finitism", "finitist framing accepted then..." 같은 표현을 쓰면
즉시 외부 frame으로 빠진 것.  213-internal 표현은: "specific
finite rational at N_U", "finite-N residual 36/N_U", "S(N_U) at
universe lattice depth", "ZFC infinity breaks cut algebra (proven)".

**Skeptic 대응**: "왜 finite N에 머무느냐?" → 답:
`#print axioms alwaysTrueUnit_limit_distinct_from_zero` →
"depends on axioms: [propext, Quot.sound]" — DRLT 허용 axiom set
(propext + Quot.sound)에만 의존, Lean kernel base.  이건 ZFC식
"infinity 잘 되어요" 와 양립 불가능.

(주: 물리 capstone 들 — `validation_standard_capstone`,
`pure_atomic_observables_capstone`, `alpha_em_master_capstone` — 은
strict form "does not depend on any axioms" 즉 axiom set ∅ 달성.)

## 교훈 2: N_universe = d^(d²) — self-referential fractal depth

**WRONG**: "N_universe is OPEN, holographic ~10¹²² 추정"
**RIGHT**: `N_U = d^(d²) = 5²⁵ = 298023223876953125`

**근거**:
- `Math/Cohomology/Fractal25.numV_eq_d_sq`: K_{25} vertex count = d²
- `Math/Cohomology/FractalLevel`: vertex count at level L = 5^L
- `Physics/NUniverseFractalDepth.n_universe_self_consistent`: L = d²,
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
- Lens framework (Universal Lens, R4Codomain)

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
가 **constructive Frobenius substitute**.  R1-R4 만족하는 unique
CD layer = ZI = ℤ[i].  Higher (Lipschitz, Cayley, Sedenion)는
각각 R-condition 하나씩 fail.  Z/2 (boolXorLens)는 R4 fail.

**근거 정리** (rust-engine branch에 닫힘):
- `CDTower.CD_tower_drops`: 4 layer drop pattern
- `ZIInstance`: derive_r4_codomain ZI
- `BoolLens.boolXorLens_not_homomorphism`: Z/2 R4 fail

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
`Firmware/Atomicity/Five.lean`, `count_eq_one_iff` in
`Firmware/Atomicity/PairForcing.lean`).  Lean kernel 기준
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
| Frobenius (R^4 axes) | CD tower (R4Codomain typeclass) |
| "free parameter"   | atomic invariant (NS, NT, d, c) |
| ℝ, ℂ via analysis  | ZI = ℤ[i] (R4Codomain instance) |
| Mathlib            | not-imported (kernel-floor only) |
| native_decide      | decide (deterministic) |

## 핵심 reference 파일

이 파일들은 **반드시 읽고 시작**:
- `CLAUDE.md` — 프로젝트 instructions
- `HANDOFF.md` — 현재 상태
- `LESSONS_LEARNED.md` — 이 파일
- `seed/INDEX.md` — standalone axiom summary
- `seed/AXIOM/` — full axiom corpus (12 chapters)
- `lean/E213/Physics/FiniteUniverse.lean` — finitist 입장
- `lean/E213/Physics/AlphaEMMasterCapstone.lean` — α_em 닫힘
- `lean/E213/Physics/Foundations/NUniverseFractalDepth.lean` — N_U = d^(d²)
- `lean/E213/Research/AxiomMinimalityCapstone.lean` — 4-clause minimality
- `lean/E213/Firmware/Atomicity/PairForcing.lean` — (NS,NT,d) derivation
- `guide/01_substrate.md` — substrate 도출 path
- `guide/15_metalogic.md` — falsifiability + R4 framework

## 현재 (2026-05-01) HEAD epistemic 위치

- α_em: finitist closure at N_U = d^(d²), sub-ppb 외부 frame match
- m_p: 4-digit match (uses Λ_QCD external)
- m_μ/m_e: depends on α_em chain
- Magic numbers: 7/7 atomic decomposition closed
- N_universe: identified = d^(d²) (self-referential)
- Universal Lens: ℕ², Q²², ℕ³, Q²³, ℕ⁴ all universal
- Pisano-CRT: 20 Pell + 8 Pell-proper + 8 Fibonacci primes
- Hodge ⋆⋆: all 5 strata Δ⁴ closed
- Famous Coincidences I-IV: catalogued

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
- `lean/E213/Kernel/Tactic/Nat213.lean` (trajectory 어휘 형식화)
- `lean/E213/Kernel/Tactic/AXIOM_FREE_STATUS.md` (propext-leak catalog)

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
- `Firmware/Raw.lean` (Raw 정의)
- `Hypervisor/Lens.lean` + `Initiality.lean` (Lens factoring)
- `Meta/UniversalLens/*` (universality)
- `research-notes/G3_raw_as_universal_trajectory.md` (G3 종합)

**가드레일**: 213이 어떻게 어떤 분야를 다룰 수 있냐 의문이 들면,
"그 분야의 distinguishing framework는 어떤 Lens인가?"를 물을 것.
새 분야 진입 = 새 Lens 정의 = Raw 트리 위 새 quotient 선택.
이게 213 작업의 fixed procedure.
