# DRLT 원론 (Elements) — 상세 구현 스펙

## 개요

단일 공리 `Entity.point`에서 출발하여:
1. 명제 논리를 유도 (Phase 1-2)
2. 자연수를 유도 (Phase 1-3)
3. 산술을 유도 (Phase 1-4)
4. 순서를 유도 (Phase 1-5)
5. Bridge에서 Lean Init과 동치 증명 (Phase 2)
6. 기존 770정리를 Bridge 위에 재배치 (Phase 3)

모든 Phase 1 파일은 `prelude` (Init 미사용, 택틱 없음).

## 커널이 제공하는 것 (prelude 상태)

| 사용 가능 | 사용 불가 |
|-----------|-----------|
| `Sort u`, `Prop`, `Type` | `Eq`, `True`, `False` |
| `→`, `∀` (Pi 타입) | `And`, `Or`, `Not` |
| `inductive` + recursor | `simp`, `omega` |
| `Nat` (zero, succ, rec) | `Nat.add`, `+`, `*` |
| `def`, `theorem` | `@[implemented_by]` |

핵심: `Nat`은 커널 빌트인. `Eq`는 아님.

---

## Phase 1-1: Entity.lean (THE AXIOM)

**목적:** 유일한 공리 선언 + 동치 관계 정의

```lean
prelude

-- ═══ THE SOLE AXIOM ═══
-- "존재하는 것들은 쌍 관계를 가진다"
inductive Entity : Type where
  | point : Entity               -- 존재
  | pair  : Entity → Entity → Entity  -- 쌍 관계

-- ═══ 동치 (Eq) ═══
-- Lean 커널이 제공하지 않으므로 직접 정의
inductive Eq {α : Sort u} : α → α → Prop where
  | refl : ∀ (a : α), Eq a a

-- Eq의 기본 성질 (커널 recursor로 증명)
theorem Eq.symm {α} {a b : α} : Eq a b → Eq b a
  | .refl _ => .refl _

theorem Eq.trans {α} {a b c : α} : Eq a b → Eq b c → Eq a c
  | .refl _, h => h

theorem Eq.subst {α} {a b : α} {p : α → Prop}
    : Eq a b → p a → p b
  | .refl _, h => h

-- congr: f a = f b from a = b
theorem Eq.congr {α β} {a b : α} (f : α → β)
    : Eq a b → Eq (f a) (f b)
  | .refl _ => .refl _
```

**줄 수:** ~35줄
**택틱:** 없음 (순수 패턴 매칭)
**의존성:** 없음 (최하위 파일)

---

## Phase 1-2: Logic.lean (명제 논리)

**목적:** True, False, And, Or, Not, Iff, Exists를 Entity 위에 정의

```lean
prelude
import DRLT.Entity

-- ═══ 명제 상수 ═══
inductive True : Prop where | intro
inductive False : Prop  -- 생성자 없음 = 증명 불가

-- ex falso quodlibet
theorem False.elim {α : Sort u} : False → α
  | h => nomatch h  -- 또는 False.rec로

-- ═══ 논리 연결사 ═══
inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

def Not (a : Prop) : Prop := a → False

structure Iff (a b : Prop) : Prop where
  intro :: (mp : a → b) (mpr : b → a)

-- ═══ 존재 양화사 ═══
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p

-- ═══ 결정가능성 (Phase 1-5에서 필요) ═══
inductive Decidable (p : Prop) : Type where
  | isFalse : Not p → Decidable p
  | isTrue  : p → Decidable p
```

**줄 수:** ~40줄
**택틱:** 없음
**의존성:** Entity.lean

---

## Phase 1-3: Nat.lean (자연수 유도)

**목적:** Entity에서 자연수 인코딩 + 커널 Nat과 동형 증명

```lean
prelude
import DRLT.Logic

-- ═══ Entity → Nat 인코딩 ═══
-- 정규형: point = 0, pair point x = succ(x)
-- 비정규형 (pair a b where a ≠ point) → 0으로 사상

def Entity.encode : Nat → Entity
  | .zero   => .point
  | .succ n => .pair .point (Entity.encode n)

def Entity.decode : Entity → Nat
  | .point          => .zero
  | .pair .point n  => .succ (Entity.decode n)
  | .pair _ _       => .zero

-- ═══ 왕복 증명 (iso) ═══
-- decode ∘ encode = id  (term-mode, Nat.rec 사용)

theorem decode_encode : ∀ n : Nat,
    Eq (Entity.decode (Entity.encode n)) n :=
  fun n => Nat.rec
    (Eq.refl Nat.zero)  -- base: decode(point) = 0
    (fun n ih =>         -- step: decode(pair point (encode n))
      -- = succ(decode(encode n)) = succ n
      -- ih : Eq (decode (encode n)) n
      -- 필요: Eq (succ (decode (encode n))) (succ n)
      Eq.congr Nat.succ ih)
    n

-- encode ∘ decode ∘ encode = encode  (약한 방향)
theorem encode_decode_encode : ∀ n : Nat,
    Eq (Entity.encode (Entity.decode (Entity.encode n)))
       (Entity.encode n) :=
  fun n => Eq.congr Entity.encode (decode_encode n)
```

**줄 수:** ~40줄
**택틱:** 없음 (Nat.rec + Eq.congr)
**의존성:** Logic.lean
**핵심:** decode_encode가 iso의 한 방향. 반대는 정규형에서만 성립.

---

## Phase 1-4: Arithmetic.lean (덧셈, 곱셈)

**목적:** Entity 레벨에서 산술 정의 + 기본 성질 증명

```lean
prelude
import DRLT.Nat

-- ═══ 덧셈 (Entity 레벨) ═══
def Entity.add : Entity → Entity → Entity
  | .point, b          => b                          -- 0 + b = b
  | .pair .point a, b  => .pair .point (Entity.add a b)  -- (1+a)+b = 1+(a+b)
  | a, _               => a                          -- 비정규: 항등

-- ═══ 곱셈 (Entity 레벨) ═══
def Entity.mul : Entity → Entity → Entity
  | .point, _          => .point                     -- 0 × b = 0
  | .pair .point a, b  => Entity.add b (Entity.mul a b)  -- (1+a)×b = b + a×b
  | a, _               => a

-- ═══ Nat 레벨 산술 (커널 Nat 직접 사용) ═══
def DRLT.add : Nat → Nat → Nat
  | .zero, b   => b
  | .succ a, b => .succ (DRLT.add a b)

def DRLT.mul : Nat → Nat → Nat
  | .zero, _   => .zero
  | .succ a, b => DRLT.add b (DRLT.mul a b)

-- ═══ 기본 성질 (term-mode, Nat.rec) ═══

-- add 우항등원: a + 0 = a
theorem add_zero : ∀ a : Nat, Eq (DRLT.add a .zero) a :=
  fun a => Nat.rec
    (Eq.refl .zero)
    (fun n ih => Eq.congr .succ ih)
    a

-- add 결합법칙: (a + b) + c = a + (b + c)
-- 증명 전략: a에 대한 귀납법
-- base: (0+b)+c = b+c = 0+(b+c) ✓
-- step: succ(a+b)+c = succ((a+b)+c) =ih= succ(a+(b+c)) = succ(a)+(b+c) ✓
-- ~15줄 term-mode 증명

-- add 교환법칙: a + b = b + a
-- 보조정리 필요: succ a + b = a + succ b
-- ~25줄 term-mode 증명

-- mul 분배법칙, 결합법칙, 교환법칙
-- 각각 ~20줄 term-mode 증명
```

**줄 수:** ~120줄 (정의 40 + 증명 80)
**택틱:** 없음
**의존성:** Nat.lean
**난이도:** ★★★ (교환법칙 증명이 가장 길다)

---

## Phase 1-5: Order.lean (순서, 결정가능성)

**목적:** ≤, < 정의 + Decidable 인스턴스 + 기본 보조정리

```lean
prelude
import DRLT.Arithmetic

-- ═══ 순서 ═══
def DRLT.le (a b : Nat) : Prop :=
  Exists (fun k => Eq (DRLT.add a k) b)

def DRLT.lt (a b : Nat) : Prop :=
  DRLT.le (.succ a) b

-- ═══ 결정 가능성 ═══
-- le에 대한 Decidable 인스턴스
-- 핵심: (a, b) 쌍에 대한 구조적 재귀
def DRLT.decLe : ∀ (a b : Nat), Decidable (DRLT.le a b) :=
  -- zero ≤ b: 항상 True (k = b)
  -- succ a ≤ zero: 항상 False
  -- succ a ≤ succ b: a ≤ b로 귀결
  ...  -- ~20줄 패턴매칭

-- ═══ 기본 성질 ═══
-- le_refl: a ≤ a
-- le_trans: a ≤ b → b ≤ c → a ≤ c
-- le_antisymm: a ≤ b → b ≤ a → a = b
-- le_total: a ≤ b ∨ b ≤ a
```

**줄 수:** ~80줄
**택틱:** 없음
**의존성:** Arithmetic.lean
**Phase 1 합계:** ~315줄 (5파일)

---

## Phase 2-1: Bridge.lean (Init 연결)

**목적:** DRLT 정의와 Lean Init을 연결. 이 시점부터 택틱 사용 가능.

```lean
-- ★ prelude가 아님! Init을 import!
import Init
import DRLT.Order

-- ═══ 동치 증명: DRLT.Eq ↔ Lean.Eq ═══
theorem drlt_eq_iff_lean_eq {α : Sort u} (a b : α) :
    DRLT.Entity.Eq a b ↔ @Eq α a b := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst h; exact DRLT.Entity.Eq.refl _

-- ═══ 동치 증명: DRLT.add ↔ Nat.add ═══
theorem drlt_add_eq_nat_add : ∀ a b : Nat,
    DRLT.add a b = Nat.add a b := by
  intro a b
  induction a with
  | zero => rfl
  | succ a ih => simp [DRLT.add, Nat.add, ih]

-- ═══ 동치 증명: DRLT.mul ↔ Nat.mul ═══
theorem drlt_mul_eq_nat_mul : ∀ a b : Nat,
    DRLT.mul a b = Nat.mul a b := by
  intro a b
  induction a with
  | zero => rfl
  | succ a ih =>
    simp [DRLT.mul, Nat.mul, drlt_add_eq_nat_add, ih]

-- ═══ 성능 매핑 ═══
@[implemented_by Nat.add]
def DRLT.add_fast (a b : Nat) : Nat := DRLT.add a b

@[implemented_by Nat.mul]
def DRLT.mul_fast (a b : Nat) : Nat := DRLT.mul a b

-- ═══ 이 시점부터 omega, native_decide 사용 가능 ═══
-- Bridge가 제공하는 것:
-- 1. DRLT 산술 = Lean 산술 (증명됨)
-- 2. 네이티브 속도 (implemented_by)
-- 3. 택틱 (simp, omega, native_decide)
```

**줄 수:** ~60줄
**택틱:** simp, induction (Phase 2부터 허용)
**의존성:** Init + DRLT.Order
**핵심:** 이 파일이 Phase 1과 Phase 3을 연결하는 교량

---

## Phase 2-2: Compat.lean (기존 코드 호환)

**목적:** 기존 PmfRh 코드가 사용하는 정의를 Bridge 위에서 재수출

```lean
import DRLT.Bridge

-- 기존 Core.lean의 정의를 DRLT 체인 위에서 재정의
-- isAdditiveAtom, NDA, σ_stat_nat 등을
-- DRLT.add, DRLT.mul로 표현

-- 핵심: 기존 코드는 이 파일만 import하면
-- 동일한 API로 동작하되, 체인이 Entity까지 연결됨
```

**줄 수:** ~100줄 (기존 정의 래핑)
**의존성:** Bridge.lean

---

## Phase 3: 기존 770정리 재배치

**작업:** critical-line/lean/PmfRh/*.lean 65파일의 import를 변경

**변경 범위:**
- Core.lean: `import DRLT.Compat` 추가
- 나머지 64파일: 변경 없음 (Core를 통해 전이적으로 DRLT 의존)

**검증:** `lake build` 통과 확인

---

## 전체 의존성 체인

```
Entity.point  (단일 공리)
    │
    ▼
Entity.lean   ← prelude, 택틱 없음
    │ Eq, symm, trans, subst, congr
    ▼
Logic.lean    ← prelude, 택틱 없음
    │ True, False, And, Or, Not, Exists, Decidable
    ▼
Nat.lean      ← prelude, 택틱 없음
    │ encode/decode, iso 증명
    ▼
Arithmetic.lean ← prelude, 택틱 없음
    │ add, mul, comm, assoc, distrib
    ▼
Order.lean    ← prelude, 택틱 없음
    │ le, lt, decidability
    ▼
═══ Bridge.lean ═══  ← import Init (택틱 해금)
    │ DRLT.add = Nat.add, @[implemented_by]
    ▼
Compat.lean
    │ 기존 API 래핑
    ▼
Core.lean (기존)
    │
    ▼
나머지 64파일 + 770정리 전부
```

**모든 정리가 Entity.point까지 추적 가능.**

---

## 규모 요약

| Phase | 파일 수 | 줄 수 | 택틱 | 난이도 |
|-------|---------|-------|------|--------|
| 1-1 Entity | 1 | ~35 | 없음 | ★ |
| 1-2 Logic | 1 | ~40 | 없음 | ★ |
| 1-3 Nat | 1 | ~40 | 없음 | ★★ |
| 1-4 Arithmetic | 1 | ~120 | 없음 | ★★★ |
| 1-5 Order | 1 | ~80 | 없음 | ★★ |
| **Phase 1 합계** | **5** | **~315** | **없음** | |
| 2-1 Bridge | 1 | ~60 | simp | ★★ |
| 2-2 Compat | 1 | ~100 | 자유 | ★ |
| **Phase 2 합계** | **2** | **~160** | | |
| 3 재배치 | 65 | ~수정만 | 자유 | ★ |
| **총합** | **72** | **~475 신규** | | |

---

## 리스크와 대응

| 리스크 | 확률 | 대응 |
|--------|------|------|
| prelude에서 Eq.congr 타입 에러 | 중 | universe 매개변수 명시 |
| add 교환법칙 term 증명 너무 길어짐 | 중 | 보조 정리 분리 (4-5개) |
| Bridge에서 implemented_by 거부 | 낮 | opaque def로 대체 |
| 기존 코드 import 변경 시 이름 충돌 | 중 | namespace 분리 |
| Nat.rec 직접 사용 시 termination 에러 | 낮 | structural recursion 사용 |

---

## 작업 순서 (추천)

1. lakefile.toml 작성 (5분)
2. Entity.lean 작성 + lake build (30분)
3. Logic.lean 작성 + lake build (30분)
4. Nat.lean 작성 + lake build (1시간)
5. Arithmetic.lean 작성 + lake build (2시간, 핵심)
6. Order.lean 작성 + lake build (1시간)
7. Bridge.lean 작성 + lake build (30분)
8. Compat.lean + Core.lean 연결 (1시간)
9. 전체 lake build 검증 (30분)

**총 예상:** ~7시간 (1 세션 + α)
