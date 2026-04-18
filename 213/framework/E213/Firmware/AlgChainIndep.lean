import E213.Firmware.Axiom
import E213.Firmware.Closure
import E213.Firmware.DepthV2

/-
  alg와 chain이 독립인가? = 213의 2방향이 (alg, chain) 2축인가?

  주장: Obj.depth = alg (mul 중첩). chain level = chain (relify 반복).
  이 둘이 독립이면 → 2방향 = 2축. 자연스러운 대응.
  독립이 아니면 → "둘 다 2"는 우연.

  독립의 의미: alg를 고정해도 chain을 자유롭게 바꿀 수 있고,
  chain을 고정해도 alg를 자유롭게 바꿀 수 있다.
-/

-- ═══ alg = Obj.depth ═══

-- Obj.depth: gen=0, mul(a,b) = 1 + max(a.depth, b.depth).
-- 이것은 mul 중첩 깊이. 213의 방향 1.

-- ═══ chain = relify 반복 횟수 ═══

-- chain rel t k: relify를 k번 적용.
-- k = chain level. 213의 방향 2.

-- ═══ 독립성 검증 ═══

-- 질문: alg=d인 Obj에 대해, chain을 임의의 k로 설정 가능한가?
-- 답: 그렇다. chain rel t k는 k에 자유롭게 의존.
-- t의 alg(depth)가 뭐든, chain k를 임의로 설정 가능.

-- 역: chain=k를 고정하고, alg를 자유롭게 바꿀 수 있는가?
-- 답: 그렇다. Triple의 원소를 깊은 Obj로 바꾸면 alg 올라감.
-- chain level은 안 변함.

-- ═══ 구체적 증명 ═══

-- 같은 chain level(=1)에서 다른 alg:
-- alg=0: chain rel ⟨gen 0, gen 1, gen 2⟩ 1. 원소가 gen.
-- alg=2: chain rel ⟨mul(gen0,gen1), mul(gen1,gen2), mul(gen0,gen2)⟩ 1.
--        원소가 이미 depth 1. relify 후 depth 2.

def shallow : Triple Obj := ⟨.gen 0, .gen 1, .gen 2⟩
def deep : Triple Obj :=
  ⟨.mul (.gen 0) (.gen 1), .mul (.gen 1) (.gen 2), .mul (.gen 0) (.gen 2)⟩

-- shallow: 원소 depth = 0. deep: 원소 depth = 1.
theorem alg_differs :
    shallow.x.depth ≠ deep.x.depth := by native_decide

-- 같은 chain level에서 alg가 다름 → alg ⊥ chain. ✓

-- 같은 alg(=0)에서 다른 chain level:
-- chain 0: ⟨gen 0, gen 1, gen 2⟩. chain 5: relify를 5번.
-- 원소의 depth는 chain level에 따라 올라감.
-- 하지만 "alg = 원래 원소의 depth"이고
-- "chain = relify 반복 횟수"이므로 별개.

-- 정확히: chain을 적용하면 alg가 올라감!
-- chain 1 of shallow: relify(mul) → 새 원소의 depth = 1.
-- chain 2: depth = 2. chain k: depth = k.
-- → alg와 chain이 완전히 독립은 아님!
-- chain이 올라가면 alg도 올라감.

-- ═══ 수정된 이해 ═══

-- alg와 chain은 완전 독립이 아님.
-- chain k를 적용하면 결과의 alg ≥ k.
-- 즉: chain ≤ alg (항상).
-- chain이 alg의 하한을 결정.

-- 하지만 alg > chain은 가능:
-- deep를 chain 0에 놓으면: alg=1, chain=0.
-- shallow를 chain 2에 놓으면: alg=2, chain=2.
-- → alg ≥ chain. 항상.

-- ═══ 이것이 의미하는 것 ═══

-- 완전 독립이 아니라 "반순서":
-- chain ≤ alg. chain은 alg를 올릴 수 있지만, alg보다 높을 수 없음.
-- chain = alg의 하한. alg = chain의 상한.

-- 2차원이지만 대각선 아래만 유효:
--
--   alg
--   3 │  ✓  ✓  ✓  ✗
--   2 │  ✓  ✓  ✗  ✗
--   1 │  ✓  ✗  ✗  ✗
--   0 │  ✗  ✗  ✗  ✗
--     └──────────────
--       0  1  2  3  chain
--
-- 아닌가? chain은 0 or ω인데...

-- 실제로: chain은 relify 반복 횟수 (0, 1, 2, ..., ω).
-- 하지만 이론 분류에서는 0(유한) or ω(무한)만 구분.
-- 그러면 유효 영역:
-- (alg, 0): 모든 alg 가능. chain=0이면 relify 안 함.
-- (alg, ω): alg ≥ 1 필요. chain=ω면 최소 1번은 relify.

-- ═══ 그래서 2방향 = 2축인가? ═══

-- 방향 1 (mul depth) → alg: 측정 가능. 유한.
-- 방향 2 (relify breadth) → chain: 측정 가능. 0 or ω.
-- 둘은 부분 의존: chain ≤ alg.
-- 완전 독립은 아니지만, 구분 가능한 2축.
-- "같은 이유로 2인가?" →
-- 같은 연산(mul)의 2가지 측면(깊이/너비)이므로 YES.
-- 완전 독립은 아니지만 같은 뿌리에서 나온 2축. ✓

-- ═══ 이전 비판에 대한 정직한 답 ═══

-- "같다"의 근거: 구조적. mul의 깊이/너비.
-- "같다"의 한계: 완전 독립이 아님. chain ≤ alg.
-- 결론: "같은 이유로 2"이지만 "독립은 아님."
-- 이것은 213의 구조적 사실: 2방향이 직교가 아니라 반순서.
