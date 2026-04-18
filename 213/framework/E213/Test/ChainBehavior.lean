import E213.Firmware.Axiom
import E213.Translation.Translate

/-
  Firmware 테스트 3: 다양한 rel에서 chain 행동.
  +, ×, mod, min, max, xor 등으로 chain 실행.
  chain_add (ℕ 구조) 검증.
-/

-- ═══ T1: 덧셈 chain ═══
def tN : Triple Nat := ⟨1, 2, 3⟩

#eval (chain (· + ·) tN 0).x  -- 1
#eval (chain (· + ·) tN 1).x  -- 3 (1+2)
#eval (chain (· + ·) tN 2).x  -- 7 (3+4)
#eval (chain (· + ·) tN 3).x  -- 11

-- 값이 성장: 덧셈은 chain을 키움.

-- ═══ T2: 곱셈 chain ═══
#eval (chain (· * ·) tN 0).x  -- 1
#eval (chain (· * ·) tN 1).x  -- 2 (1×2)
#eval (chain (· * ·) tN 2).x  -- 12 (2×6)

-- 더 빠르게 성장: 곱셈 체인은 지수적.

-- ═══ T3: mod chain (유한 공간) ═══
def addM (m : Nat) (a b : Nat) : Nat := (a + b) % m

#eval (chain (addM 3) ⟨0, 1, 2⟩ 0).x  -- 0
#eval (chain (addM 3) ⟨0, 1, 2⟩ 1).x  -- 1
#eval (chain (addM 3) ⟨0, 1, 2⟩ 2).x  -- 0  주기 2!

#eval (chain (addM 5) ⟨0, 1, 2⟩ 0).x  -- 0
#eval (chain (addM 5) ⟨0, 1, 2⟩ 4).x  -- 0  주기 4!

-- ═══ T4: min chain ═══
#eval (chain Nat.min tN 0).x  -- 1
#eval (chain Nat.min tN 1).x  -- 1
#eval (chain Nat.min tN 2).x  -- 1  붕괴! 전부 1.

-- min은 chain을 붕괴시킴 (최솟값으로 수렴).

-- ═══ T5: max chain ═══
#eval (chain Nat.max tN 0).x  -- 1
#eval (chain Nat.max tN 1).x  -- 2
#eval (chain Nat.max tN 2).x  -- 3  고정!

-- max는 chain을 안정시킴 (최댓값에 고정).

-- ═══ T6: XOR chain ═══
#eval (chain Nat.xor ⟨5, 3, 7⟩ 0).x  -- 5
#eval (chain Nat.xor ⟨5, 3, 7⟩ 1).x  -- 6 (5⊕3)
#eval (chain Nat.xor ⟨5, 3, 7⟩ 2).x  -- 1

-- ═══ T7: chain_add (ℕ 구조) ═══

-- chain(chain(t,m), n) = chain(t, m+n).
-- 이것이 ℕ 덧셈의 근거.
theorem t7_add (m n : Nat) :
    chain (· + ·) (chain (· + ·) tN m) n =
    chain (· + ·) tN (m + n) :=
  chain_add (· + ·) tN m n

-- 구체적 확인:
theorem t7_2_3 :
    chain (· + ·) (chain (· + ·) tN 2) 3 =
    chain (· + ·) tN 5 :=
  chain_add (· + ·) tN 2 3

-- ═══ 요약 ═══
-- +: 성장. ×: 지수 성장. mod: 주기. min: 붕괴. max: 고정. xor: 비규칙.
-- chain_add: 모든 rel에서 성립. ℕ 구조 = firmware 불변량.
