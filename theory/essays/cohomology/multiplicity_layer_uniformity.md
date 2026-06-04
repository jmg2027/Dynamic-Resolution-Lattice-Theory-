# 모든 multiplicity layer에서 같은 ψ-kill이 작동하는 이유: `9·m` cancellation의 구조적 의미

K_{3,3}^{(c)} 의 enriched 2-complex 에서 bottom layer 에서 성립하는
`ψ_0 (cupOpp_param (starS i ⟨0,hc⟩) β) = false` (그리고 T 쪽 dual) 가
임의의 layer `m : Fin c` 에서도 *동일한 증명 템플릿*으로 닫힌다.
유일하게 추가로 필요한 step 은 `Nat` 위에서의 left-cancellation
`(9·m + a == 9·m + b) = (a == b)` 한 줄.  이 cancellation 이 곧
edge-disjoint direct-sum decomposition (`disjoint_layers_as_direct_sum.md`)
의 *증명-레벨 그림자* 다.

## 213-native answer

Enriched complex 의 layer-m sector 는 layer-0 sector 의 **translate**
이다 — edge index 가 `9·m` 만큼 평행이동했을 뿐, 내부 결합 구조 (어떤
edge 가 어떤 face 에 4번 들어가는가, 어떤 edge 가 어떤 starS / incidT
generator 의 support 인가)는 layer 마다 동일.  Lean 증명에서 이
translate 는 *오직* `Nat.beq` 비교에서 `9·m.val` offset 으로만 나타나며,
layer 내부 계산 (Bool XOR pattern, Fin 3 case-bash, edge-in-face
count) 에는 전혀 들어가지 않는다.

따라서 cancellation `(9·m + a == 9·m + b) = (a == b)` 가 closed 되는
순간, layer-m 의 kill 증명은 layer-0 의 kill 증명과 *syntactically*
같다.  새로운 정리도 새로운 case-bash 도 필요 없다 — *같은 정리를
다시 평가하는 것* 이다.

## 도출

Bottom-layer kill 의 핵심 reduction:

```
unfold psi_layer cupOpp_param diag_pair_param starS pair_lo pair_hi
cases β (edge_idx c ⟨1, _⟩ ⟨0, _⟩ ⟨0, hc⟩) <;> … <;> rfl
```

는 m = 0 에서 `9·0 = 0` 이 정의적으로 `rfl` 환원되므로 `Nat.beq`
비교가 모두 ground Nat 계산으로 해소된다.  예: `(0 + 3·0 + 0 == 0 + 3·0)`
는 `(0 == 0) = true`, `(0 + 3·0 + 0 == 0 + 3·0 + 1)` 는
`(0 == 1) = false`.

임의 `m` 에서는 `9·m.val + 3·0 + 0 == 9·m.val + 3·0` 의 형태 — 두
edge index 모두 같은 `9·m.val` 접두사를 가진다.  이 접두사를 떼기만
하면 m=0 case 와 정확히 같은 ground Nat 비교가 남는다:

```
nat_decide_add_left_assoc1 (9 · m.val) (3 · i'.val) j'.val (3 · i.val)
  : (9·m.val + 3·i'.val + j'.val == 9·m.val + 3·i.val)
    = (3·i'.val + j'.val == 3·i.val)
```

(`Meta/Nat/Beq213.lean`, PURE.)  이 lemma 의 증명은
`Nat.add_assoc` 으로 reassoc 한 후 `nat_beq_add_left` 의 `Nat` 위
structural recursion 을 호출.  `_assoc2` 는 양쪽에 `+ k` 가 붙은
변형, `_assoc1` 은 한쪽만.  두 lemma 가 `starS` (3-disjunct)
와 `incidT` (3-disjunct) 의 9 가지 `Nat.beq` 패턴을 모두 cover.

`starS_at_edge_idx_same_m` 과 `incidT_at_edge_idx_same_m`
(`V33EnrichedParametric.lean` §20) 가 이 cancellation 을
`starS c i m (edge_idx c i' j' m)` 형태에 한 번 적용해서 layer-free
형태로 환원한다:

```
starS c i m (edge_idx c i' j' m)
= (3·i' + j' == 3·i) || (3·i' + j' == 3·i + 1) || (3·i' + j' == 3·i + 2)
```

`m` 은 RHS 에 *나타나지 않는다*.  이후 6-edge β case-bash (S-star
case) / 9-edge α case-bash (T-incid case) 는 bottom layer 와 동일한
tactic 으로 닫힘.  총 6 개 PURE 정리 (S₀, S₁, S₂ 좌측 + T₀, T₁, T₂
우측) + `parametric_arbitrary_m_full_kill_capstone`.

## Dual function

이 essay 는 *cancellation 이 일종의 trick* 이 아니라
*layer-translation invariance 의 evidence* 라는 주장.

Edge index `9·m + 3·i + j` 에서 `9·m` 은 layer m 의 **starting
address**, `3·i + j` 는 그 layer 안에서의 *intra-layer position*.
Layer 내부 계산 (어떤 (i, j) pair 가 어떤 face 에 들어가는가) 은
오직 후자에만 의존.  Layer 들 사이의 차이는 오직 starting address 의
이동.  `Nat.beq` cancellation 은 *두 edge 가 같은 layer 에 있을 때*
이 starting address 를 양쪽에서 동시에 빼주는 연산 — 결과는 intra-layer
position 만 남는다.

이것이 `disjoint_layers_as_direct_sum.md` 의 직접합 분해를 *증명*
레벨에서 본 모습이다.  직접합은 "layer m sector 가 layer 0 sector
의 자기복사 (a self-copy)" 라는 categorical 진술; cancellation 은
그 자기복사를 *Lean 의 `decide` reduction* 으로 만든 진술.

(`disjoint_layers_as_direct_sum.md` 가 "왜 codim 이 c 와 함께
선형으로 자라는가" 의 *categorical* 답이라면, 이 essay 는 "왜
하나의 kill 증명이 모든 layer 에 적용되는가" 의 *operational* 답.
같은 사실의 두 frame.)

## Cross-frame connections

같은 "layer 마다 같음" 사실의 세 가지 layered 표현:

  - **Indexing rule** (`disjoint_layers_as_direct_sum.md`):
    `c·k + m` 분해 가 layer-m edge subset 을 layer-0 edge subset
    의 isomorphic copy 로 만든다.  *Chain level*.
  - **ψ-discriminator orthogonality** (`parametric_c_independent_h2_classes`):
    `ψ_m (e_face_layer m')` 가 Kronecker δ 로 평가됨 — layer 들이
    cohomologically separated.  *Functional level*.
  - **`9·m` cancellation** (이 essay, §20 kill capstone):
    `starS / incidT` 의 same-layer evaluation 이 layer 와 무관한
    ground Bool 식으로 환원.  *Proof level*.

세 frame 이 같은 사실의 다른 형식화: layer-m 과 layer-0 은
*같은 internal structure 의 다른 instance*.

`Mobius213K33StateClass.state_class_NSscaled_pell_capstone` 의
"NS-scaled depth-1" 도 같은 패턴 — Pseq seedZero 의 depth-k
iterate 는 seedZero 자체의 *internal pattern 을 k번 복제* 한다.
P-orbit 의 "Stack k independent copies" 와 enriched complex 의
"Stack c independent layers" 는 cardinal 만 다를 뿐 *같은 구조의
재현*.

## ∅-axiom 의 가치

Cancellation 을 통상 cite 하는 `Nat.add_left_cancel` 은 core Lean
에서 `propext` 에 의존한다 (`#print axioms Nat.add_left_cancel`).
DRLT 213 의 strict ∅-axiom 표준은 `propext` 를 금지하므로
(`STRICT_ZERO_AXIOM.md`), 자체 PURE 버전 `nat_add_left_cancel_pure`
를 만들었다:

```
nat_add_left_cancel_pure : ∀ {a b c : Nat}, a + b = a + c → b = c
  | 0, b, c, h => by rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | a+1, b, c, h => by
    rw [nat_succ_add a b, nat_succ_add a c] at h
    exact nat_add_left_cancel_pure (Nat.succ.inj h)
```

`a` 에 대한 structural recursion 만 사용; `Nat.zero_add`,
`Nat.succ.inj` 모두 core 에서 PURE.  이 한 정리가 axiomatic
overhead 없이 *모든* layer-uniformity 결과를 받쳐준다.

부차적 surface-form 주의: `e.val == k` 가 `Nat` 에서는
`decide (e.val = k)` 로 desugar (generic `[DecidableEq α] ⇒ BEq α`
instance), `Nat.beq e.val k` 가 아님.  같은 cancellation 의 두
표면 형태 (`nat_beq_add_left_*` 와 `nat_decide_add_left_*`) 가
모두 `Beq213.lean` 에 존재.  `starS` / `incidT` 가
`e.val == k` 를 emit 하므로 §20 의 bridge lemma 는 decide-form
변형을 사용.

## Open frontier

  · **K_{NS, NT}^{(c)} 일반화**: 현재 layer translation invariance
    는 `NS = NT = 3` 에서 증명됨.  Edge index `c·(NT·i + j) + m`
    이 (NS, NT) 일반에서도 동일한 layer-translation 구조를 갖지만,
    starS / incidT 의 일반화 (general S-star = `Fin NT`-disjunct,
    general T-incid = `Fin NS`-disjunct) 에서 같은 cancellation
    template 이 유지되는지 확인이 필요.  Layer-uniformity 자체는
    (3, 3) 에 의존하지 않으므로 전이 가능할 것으로 예상.
  · **Cohomology-level isomorphism statement**: 현재의 결과는
    "각 layer 의 cup-kill 이 같은 형태로 닫힌다" 이다.  여기서
    `enriched_complex_iso_direct_sum : C¹_enr ≅ ⊕_m C¹_simple_m`
    type-isomorphism 을 PURE Lean 으로 진술하면 cancellation =
    direct-sum component evaluation 임이 *type level* 에서 명시됨.
    `disjoint_layers_as_direct_sum.md` 의 open frontier 와 동일.
  · **`9·m` 의 일반화 `period·m`**: edge_idx 의 9 는 `NS · NT = 9`.
    일반 (NS, NT) 에서는 `NS · NT · m` 이 offset.  Cancellation
    lemma 자체는 generic `a` 에 대해 성립하므로 (`nat_decide_add_left`),
    layer count `c` 와 period `NS · NT` 가 매개변수가 되는
    `nat_decide_period_cancel (period m a b : Nat) :
    (period · m + a == period · m + b) = (a == b)` 형태로 lift
    가능.  K_{NS, NT}^{(c)} 일반화의 부속 헬퍼.

가리킬 수 있는 정리:
`parametric_arbitrary_m_full_kill_capstone` —
한 PURE 정리가 "모든 c, 모든 m : Fin c, 모든 i, j ∈ Fin 3" 에서
bilateral cup-image kill 을 진술.  6 개 base kill (각 1개씩) 과
한 개 bridge lemma 가 6,400,000 ~ 12,800,000 maxHeartbeats 안에
case-bash 로 닫힘.  Cancellation 이 *layer 들을 한 곳으로 모아주는*
operational 메커니즘.

## Cross-references

  · `theory/math/cohomology/k_nm_c_classification.md`
    §"Arbitrary-m bilateral kill" — Lean 정리 카탈로그 + Lean
    source 위치
  · `theory/essays/cohomology/disjoint_layers_as_direct_sum.md` —
    categorical / chain-level 자기복사 진술 (이 essay 의 dual)
  · `theory/essays/cohomology/c_counter_as_layer_count.md` — c 를 depth 가
    아닌 layer count 로 읽는 reframing (이 essay 의 전제)
  · `theory/essays/methodology/pure_funext_avoidance.md` —
    `propext` 의존 없이 PURE 정리를 닫는 일반 입장.  `nat_add_left_cancel_pure`
    가 같은 *strict purity* discipline 의 사례
  · `lean/E213/Meta/Nat/Beq213.lean`
    — cancellation 헬퍼 (Nat.beq form + decide form)
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33EnrichedParametric.lean`
    §20 — bridge lemma + 6 kill + capstone
