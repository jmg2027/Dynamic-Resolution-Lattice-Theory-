# Session Handoff — DRLT 213 (2026-05-11)

## Branch
`claude/raw-data-demo-W8aVV` — pushed, up to date with origin.
Latest: `b5d698be CLOSED_FORM_SPEC: marathon section 갱신`.

## What Was Done This Session

### 1. ★ Theory/Closed/* — closed-form pattern unification (4-domain catalog)

Vertical-internal projection 메타 패턴 4개 도메인 위 작동:

| domain | object | projection | Lean module |
|---|---|---|---|
| Nat213 | Raw | leavesCountRaw | Theory/Closed/Nat213Bridge |
| Bool213 | Raw | booleanProj | Theory/Closed/Bool213 |
| RawCut | Raw²→Raw | cutBooleanProj | Theory/Closed/RawCut |
| CauchyCutSeq | structure | cauchyProj | Lib/Math/Analysis/CauchyProj |

각 도메인 위 4 정리: closure + idempotence + boundary commutativity +
fixed-point ↔ image.  CauchyProj 의 정리들은 모두 `rfl`.

### 2. ★ ChainToCut bridge — Closed Nat213 → Real213 cut 우주

`lean/E213/Lib/Math/Real213/ChainToCut.lean` (13 PURE):

| Real213 cut 연산 | Bridge 정리 |
|---|---|
| `cutSum` (add) | `cutSum_chainToCut` |
| `cutMul` (mul) | `cutMul_chainToCut` |
| `cutLe` (≤) | `cutLe_chainToCut_iff` |
| `cutMax` (LUB) | `cutLe_cutMax_chainToCut_iff` |
| `cutMin` (GLB) | `cutLe_cutMin_chainToCut_iff` |

closed-Raw 의 add/mul/order/lattice 모두 Real213 cut 우주로 lift.
Theory/Closed/* 가 압축 도구임 입증.

### 3. Bridge composition (ChainCauchy)

`Lib/Math/Analysis/ChainCauchy.lean` (3 PURE, all rfl):
`chainCauchyCutSeq r := constCauchyCutSeq (chainToCut r)`.
ChainToCut + CauchyProj 자연스럽게 결합, 추가 axiom 0.

### 4. Tier 5 spec 문서 (`seed/CLOSED_FORM_SPEC.md`)

정식 spec 문서:
  - 4-domain meta-pattern catalog
  - ChainToCut bridge table
  - Bridge composition
  - **8-pattern propext-avoidance trick set** (재사용)
  - Marathon 사례 + 한계 catalog
  - Future work

`seed/INDEX.md` directory layout 에 추가.

### 5. Marathon: 14 real DIRTY → PURE in single sprint

| Module | # | Tricks |
|---|---|---|
| EulerSharperPure.e_partial_neq_third_a | 1 | 3+4+6 |
| CutLatticeEq.{cutMax,cutMin}_cutLe_* | 6 | 5 (Bool helpers) |
| CutMulConstConst.cutMul_const_const_* | 2 | 2+8 |
| ValidCutOps.{cutMax,cutMin,cutSum}_valid | 4 | 5+2+8 |
| CutMidMono.cutLe_cutMid_b_at | 1 | 2+6+8 |

**~120 → ~106 real DIRTY** (이번 sprint -14).

### 6. Propext-avoidance trick set (8 patterns, future Claude anchor)

  1. `rw [Iff_lemma]` → `Iff.trans (lemma) ?_`
  2. `rw [Iff_lemma] at hyp` → `(Iff_lemma _ _).mp hyp` 직접
  3. `rw [Eq_lemma] at hyp` → `Eq_lemma ▸ hyp` (term-mode)
  4. `▸` motive 모호 → `calc` 으로 명시 step
  5. `Bool.{and,or}_eq_true` Iff → 직접 Bool match helpers
  6. Nat-core leak → `E213.Tactic.Nat213.*` helpers
  7. `decide_eq_true_iff` → 직접 `Iff.intro` 양방향
  8. `by_cases` / `omega` / `simp` / `congr 1` → cases / match / manual

## Cumulative State

- **2519 PURE / ~106 real DIRTY / 0 sealed** (estimate after marathon)
- 4-domain vertical-internal projection meta-pattern fully cataloged
- ChainToCut bridge: closed-Raw 산술이 Real213 cut 우주에서 그대로 작동
- 정식 Tier 5 spec (`seed/CLOSED_FORM_SPEC.md`) anchor 확립

## Open Problems (Priority Order)

### 1. Marathon: deeper propext leaks (~106 잔존)
한계 사례 — surface trick set 으로 부분만 해결.  필요 deeper investigation:
  - `Real213.CutSumGeneral` (4) — Quot.sound 제거됐지만 propext 잔존
  - `Real213.CutMidMono.cutLe_a_cutMid_at` — Nat.lt_of_not_le 의심
  - `Cauchy.GenericFamily.*` — funext-by-design (eqPW refactor)
  - `Cauchy.WallisSharper.wallis_sharper_lower` — omega + by_cases chain
  - `Theory.Internal.Raw.CmpIndependence` (9) — Raw transport
  - 다양한 deeper sources

다음 step: bisection 으로 정확한 propext source identify, 9번째 trick
추가 또는 G83 eqPW strategic refactor.

### 2. DRLT Validation Standard closure
"precision theorem AND falsifier 같은 observable 위" — 명시 closure
미달.  하나의 observable 에 둘 다 닫힌 사례 필요.

### 3. ChainToCut 확장 (G84 Tier 4 후속)
- Cauchy seq 위 cutSum/cutMul (sequence-level bridge).
- DyadicTrajectory ↔ ChainToCut 연결.

### 4. Lens 5번째 도메인 (eqPW 일반화)
funext-by-design 자리들 (~18 modules) 의 eqPW refactor.

## Unresolved from This Session

- WallisSharper omega + by_cases chain → propext 잔존, 부분 fix 후 revert.
- CutMidMono.cutLe_a_cutMid_at → Quot.sound 제거됐지만 propext 잔존.
- BracketCauchyModulus → 부분 fix 후 revert (deeper dependency leak).
- GenericFamily.projectionLens_view → funext required, refactor scope 큼.

## Next Experiment

Marathon 계속.  Concrete next:
  - propext bisection on CutMidMono.cutLe_a_cutMid_at
  - 또는 단순 한 propext 만 있는 다른 module batch

## File Map

새 파일 / 확장:
```
Theory/Closed/Nat213Bridge.lean      ← extended (leavesCountRaw fixed-point)
Theory/Closed/Bool213.lean           ← extended (booleanProj + boolValue + ↔)
Theory/Closed/Nat213.lean            ← extended (value_numeral)
Theory/Closed/RawCut.lean            ← extended (cutBooleanProj + cutBoolValue)
Lib/Math/Real213/ChainToCut.lean     ← NEW (chain → cut bridge, 13 PURE)
Lib/Math/Analysis/CauchyProj.lean    ← NEW (4th domain, 7 PURE all rfl)
Lib/Math/Analysis/ChainCauchy.lean   ← NEW (composition, 3 PURE all rfl)
seed/CLOSED_FORM_SPEC.md             ← NEW (Tier 5 spec)
seed/INDEX.md                        ← updated
research-notes/G84_*.md              ← extended
```

Marathon (DIRTY → PURE):
```
Cauchy/EulerSharperPure.lean         ← 1 theorem PURE
Real213/CutLatticeEq.lean            ← 6 PURE (Bool helpers)
Real213/CutMulConstConst.lean        ← 2 PURE
Real213/ValidCutOps.lean             ← 4 PURE
Real213/CutMidMono.lean              ← 1 of 2 PURE
```

## Key Anchor Documents

- `seed/CLOSED_FORM_SPEC.md` — Tier 5 정식 spec (이 세션 생성)
- `research-notes/G84_closed_form_pattern_unification.md` — 탐색 노트
- `STRICT_ZERO_AXIOM.md` — 전체 PURE/DIRTY catalog (오래됨, 갱신 필요)
- `CLAUDE.md` boot sequence + ∅-axiom standard

다음 세션: boot sequence 후 `seed/CLOSED_FORM_SPEC.md` 확인 → propext
leak 만나면 8 trick 적용 → marathon 계속.
