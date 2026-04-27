# 213 Forbidden Patterns — Hook 강제 금지 코드 카탈로그

훅이 자동으로 차단하는 코드 패턴 목록.
CLAUDE.md "DRLT 검증 기준" 의 형식적 가드.

## 강제 메커니즘

  PreToolUse  Write|Edit  → chunk-guard.sh    (80줄 제한)
  PreToolUse  Write|Edit  → purity-guard.sh   (Tier1 + Tier2)
  PreToolUse  Bash         → no-amend.sh       (amend / force-push)
  PostToolUse Write|Edit  → kernel-axiom-check.sh  (axiom 회귀)

설정: `.claude/settings.json`
스크립트: `.claude/hooks/*.sh`

## Tier 1 — 모든 lean/E213/*.lean

| 패턴 | 차단 사유 |
|---|---|
| `^[[:space:]]*sorry\b`, `:= sorry`, `by sorry` | DRLT 폐기 trigger |
| `^[[:space:]]*axiom[[:space:]]` | 외부 axiom = 이론 폐기 |
| `import Mathlib` | 213-native 강제 |
| `open Classical` | constructive 증명만 |
| `native_decide` | binary trust = 형식 증명 아님 |

위반 시: hook 이 `block` 반환 → 편집 거부.

## Tier 2 — lean/E213/Kernel/**/*.lean (Kernel-strict)

비전 강제: kernel 은 *literally 0 axiom* — propext, Quot.sound 도
load-bearing 불가.

| 패턴 | 차단 사유 |
|---|---|
| `by decide` | Decidable typeclass → propext |
| `by simp`, `simp only` | propext 단골 |
| `rw [...]` | Prop rewrite = propext |

우회 방법:
  - `rfl` (definitional reduction)
  - `Nat.beq` / `Nat.ble` (Bool 등호/비교)
  - `Eq.subst` 명시 motive
  - 구조귀납 (private helpers)
  - `Bool.cond` (if-then-else)

예: `Nat.beq_refl` 대신 `private theorem beq_refl' : ∀ n, Nat.beq n n
= true | 0 => rfl | n+1 => beq_refl' n` (구조귀납).

## Bash hook — git 안전

| 패턴 | 차단 |
|---|---|
| `git commit --amend` | "절대 amend 안 함" |
| `git push --force` / `-f` | 강제 푸시 차단 |

## Kernel axiom regression (PostToolUse)

Kernel 파일 변경 후 자동 실행:
  1. `tools/kernel_regress.sh` 호출
  2. `lake build --rehash` → `#print axioms` 출력
  3. 어떤 Kernel 정리가 axiom 의존하면 block

성공 시 silent.  실패 시 위반 정리 + axiom 목록.

## 수동 검증

  ./tools/kernel_regress.sh        # 즉시 검증
  python3 tools/audit_axioms.py    # 상세 분류
  python3 tools/port_candidates.py # 미포팅 후보

## 한 줄

> "물리·수학을 모르는 검증자가 봐도, 정의 + Lean kernel reduction
>  만으로 닫히는 정리만 허용한다."
