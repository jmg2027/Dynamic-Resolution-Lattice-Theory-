# G139 — Möbius P가 213 동치의 canonical form이라는 conjecture

**Status**: Research direction for next session.  Conjecture
emerging from Wave 13 (parametric cutSumN closure) interrogation:
all 213 equality definitions may be projections of a single
Möbius-orbit equivalence forced by the atomic (NS, NT, c, d) = (3, 2, 2, 5).

## Anchor

Wave 13 (commits `f7a32e88` ... `886ae30a` on `claude/math-algebra-analysis-marathon-rj4UW`) closed b ≥ 3 cutSum_assoc the right way:

  · `Lib/Math/Real213/Sum/CutSumN.lean` (6 PURE): parametric `cutSumN N` + `cutSumN_same_denom` bidirectional for any N > 0.
  · `Lib/Math/Real213/Sum/CutSumNMixed.lean` (3 PURE): cross-denom closure when b₁, b₂ ∣ N.  `cutSumN 6 (1/2)(1/3) ≡ 5/6`.
  · `Lib/Math/Real213/ThirdValidCut.lean` (15 PURE), `NValidCut.lean` (14 PURE, parametric capstone), `FifthValidCut.lean` (12 PURE).

Total 50 PURE, 0 DIRTY.  Marathon now 626 PURE / 53 closures.

## Triggering observation

The reframing of b ≥ 3 had to be done **three times** because of dichotomy import (`seed/AXIOM/05_no_exterior.md` §5.4):

  · v1 essay (`bool_assoc_failure_meaning.md` v1): "trajectory vs real distinguishing" (시적, poetic)
  · v2: "Real213은 dyadic-only commitment — b ≥ 3 외부 import"
  · v3: "(3, 2)-multiplicative monoid commitment, prime ≥ 5 = 새 atom"
  · v4 (closed): 모든 자연수 N이 framework 내부, `cutSumN N` parametric

Each "fix" imported another classification.  User correction in three turns:

  1. *"2,3만 있으면 모든 실수 판정 가능"* — pointed at repo's existing parametric proofs
  2. *"5는? 모든 자연수에 대해서는? 그것도 2,3으로 가능할텐뎅"* — Bezout / `atomic_iff_five` made explicit
  3. *"실수같은 비가산 무한개념이 필요한 애들은 ->가 두개 있자나 ... 뫼비우스 행렬이 바로 이 상태 전이를 상태로 치환해도 동일한게 나오는거자나"* — Möbius unification conjecture

The third correction is the deep one and motivates this note.

## Conjecture (precise form)

**213-내부 모든 동치 정의는 Möbius-orbit equivalence under P = [[2,1],[1,1]]의 layer-specific projection.**

Repo-internal Möbius infrastructure (already in `main`):

  · `Lib/Math/Mobius213.lean`: P = [[2,1],[1,1]], trace = 3 = NS, det = 1, disc = 5 = d, eigenvalues φ², 1/φ², fixed point φ.  `mobius_213_pell_unit_invariant_forall`: cross-product = −1 invariant under all P-iterations.
  · `Lib/Math/Mobius213OneAsGlue.lean`: `mobius_det_eq_ns_minus_nt` (det = NS − NT = glue = 1), `one_is_det`, `off_diagonal_is_two_ones`, `ns_is_succ_nt`.  Entries (2, 1, 1, 1) = (NT, glue, glue, unit) sum to 5 = d.
  · `Lib/Math/UniverseChain/MobiusChain.lean`: post-atomicity chain G65-G81.
  · `Lib/Math/Mobius213ModFive.lean`: P¹⁰ ≡ I (mod 5).
  · No external SL₂(ℤ) — pure 213-internal.

Existing equality definitions (Wave 13 enumeration):

  · `cutEq cx cy := ∀ m k, cx m k = cy m k` (Real213/Core/CutPoset)
  · `ZpSeqEquiv x y := ∀ k, x.digits k = y.digits k` (Padic/SetoidFramework)
  · `ZpSqrtDEquiv` (Padic/ZpSqrtDSetoid)
  · `ZpSeq.eq_mod_pn x y n := ∀ k < n, ...` (Padic/Foundation)
  · `signedEq (a,b)(c,d) := a+d = b+c` (SignedCut/Core)
  · `Adjacent db₀ db₁` (Analysis/FluxMVT)
  · `is_integer / is_half / is_third / is_at_denom` (IntValidCut / HalfValidCut / ThirdValidCut / NValidCut)
  · `LensMap` (Padic/SetoidFramework — morphisms respecting equivalence)

Conjecture: each ≡ some projection of a single Möbius-orbit equivalence.

## Structural argument for "must be Möbius"

User's full insight (paraphrased + structured):

  · 실수 = uncountable infinity = needs *two* arrows (→→)
  · 무한을 푸는 = transition (→)을 state로 치환 (1단계 → 으로 환원)
  · 상태 전이를 상태로 치환해도 동일한 결과가 나오는 것 = Möbius P (frozen-dynamic dualism, `Mobius213.lean` docstring §"Frozen + dynamic dualism")
  · 0/1/2 arrows → 1/2/3 states (NT, NS chain-cardinalities)
  · 3+ arrows decompose into 1, 2, 3 (Bezout via {2, 3}; `atomic_iff_five`)

Conditions on a relation to be an equivalence under iteration:

  · 대칭성 ⇐ 역연산 존재 ⇐ det = 1 (P⁻¹ integer entries)
  · well-foundedness ⇐ 불변량 존재 ⇐ eigenvalue product = det = 1 (φ² · 1/φ² = 1)
  · fixed point 수렴 ⇐ dominant eigenvalue > 1 (φ²)

These conditions algebraically force a Möbius matrix.  Among 2×2 integer Möbius matrices satisfying (det = 1, trace > 2 for hyperbolic iteration), the (3, 2) atomicity selects P = [[2,1],[1,1]] uniquely (`c2b_full_iff` + Pell-Fibonacci).

## Non-orbit (m, k) is reachable

Earlier remark (v4 essay) flagged "비-orbit (m, k)는 framework가 보지 않는 영역".  User pointed: 모든 (m, k)가 P-orbit 조합으로 분해.

Concrete: Stern-Brocot tree generates ALL rationals from (0/1) and (1/0) via repeated mediant operation `(a,b) ⊕ (c,d) := (a+c, b+d)`.  Mediant is structurally Möbius (Farey).  Therefore:

  · cutEq의 `∀ m k`는 Stern-Brocot 전체 = (0,1), (1,0)에서 Möbius-도달 가능한 모든 (m, k)
  · cutEq ≡ "모든 Möbius-도달 (m, k)에서 일치" = mobiusEq
  · 둘이 다르지 않음 (over-specification 아님)

The "non-orbit" framing was the *fourth* dichotomy import — invisible until user surfaced it.

## Concrete next-session deliverables

### Phase 1: define Möbius-orbit equivalence

`Lib/Math/Real213/Mobius/Mobius213Equiv.lean` (new):

```lean
/-- P-orbit position from seed (a, b): P^n (a, b) = (2a + b iterated). -/
def Pseq (a b : Nat) : Nat → Nat × Nat
  | 0 => (a, b)
  | n+1 => let (m, k) := Pseq a b n; (2*m + k, m + k)

/-- Stern-Brocot mediant orbit: closure of (0,1), (1,0) under mediant. -/
def sternBrocotReachable : Nat × Nat → Prop := ...

/-- Möbius equivalence: agree on the (0,1)- and (1,0)-orbit. -/
def mobiusEq (cx cy : Nat → Nat → Bool) : Prop :=
  ∀ n, let (m₀, k₀) := Pseq 0 1 n; cx m₀ k₀ = cy m₀ k₀
       ∧ let (m₁, k₁) := Pseq 1 0 n; cx m₁ k₁ = cy m₁ k₁
```

### Phase 2: cutEq ⇔ mobiusEq bridge

  · forward: cutEq ⇒ mobiusEq trivial (pointwise stronger)
  · backward: mobiusEq + Stern-Brocot coverage ⇒ cutEq
  · Stern-Brocot coverage lemma: ∀ (m, k), ∃ Möbius path from {(0,1), (1,0)} reaching (m, k)

### Phase 3: all equality definitions factor through mobiusEq

| 동치 정의 | mobiusEq 인스턴스화 |
|---|---|
| cutEq | identity (Phase 2) |
| ZpSeqEquiv | (mod p)-version of mobiusEq (P acts on digits at level n) |
| signedEq | det-form of mobiusEq on (a,b)(c,d) pairs |
| is_at_denom (NValidCut N) | mobiusEq restricted to N-fiber |
| Adjacent (DyadicBracket) | mobiusEq one-step relation |
| LensMap | mobiusEq-preserving morphism |

### Phase 4: 213-canonical Setoid

Real213 as quotient by mobiusEq (replacing current cutEq-based quotient if Phase 2 succeeds).  Check that cutSumN, cutMulN, etc. descend.

### Phase 5: cross-frame connections

  · Möbius P ↔ K_{3,2}^{(c=2)} bipartite structure: 3-side / 2-side as P's two state classes
  · P-iteration ↔ continued fraction expansion of φ ↔ Stern-Brocot path
  · `mobius_213_pell_unit_invariant_forall` ↔ "동치 관계가 보존하는 불변량"
  · `atomic_iff_five` ↔ "왜 5인가" = "P의 disc"
  · Cayley-Dickson tower ↔ P의 2-doubling 측면

## Open questions

  · Is Stern-Brocot coverage actually total over ℕ × ℕ?  Standard CS result: YES, every coprime pair appears uniquely in tree.  Non-coprime (m, k) reachable via (m/gcd, k/gcd) + scaling.
  · Does mobiusEq strictly weaken cutEq, or are they equivalent?  Conjecture: equivalent.  If so, cutEq is the *concrete coordinate* form of mobiusEq.
  · ZpSeqEquiv for p ≠ 5: does a (mod p)-Möbius give the right structure?  `Mobius213ModFive.lean` handles p = 5 (P¹⁰ ≡ I).  Other primes?
  · cutMulN parallel?  Multiplication may need a *different* Möbius (signature [[3, 1],[1, 2]] or similar with disc = 5 still).

## Failure modes to avoid (catalog 추가 candidate)

This whole conjecture emerged from FOUR consecutive dichotomy-import failures.  Adding to CLAUDE.md `## Failure modes catalog`:

| Failure | Symptom | Correction |
|---|---|---|
| Equivalence-pluralism | "여러 동치 정의가 따로 있음 (cutEq, ZpSeqEquiv, signedEq...)" | 모두 single Möbius-equivalence의 layer projection 가능; classification 자체가 import |

## Connection to Wave 13 deliverables

If conjecture verifies:

  · `cutSumN N` ≡ "P-orbit closure operation on N-fiber"
  · `NValidCut N` ≡ "N-fiber의 Möbius-equivalence quotient"
  · `cutSumN_mixed_denom` (b₁, b₂ ∣ N) ≡ "Möbius-fiber 합병"
  · `atomic_iff_five` ≡ "P의 disc는 5가 유일"

전체 Wave 13이 *single Möbius operation의 다양한 표현*.  53 closure / 626 PURE가 single structural fact의 layer-wise 실현.

## Anchor files (next session boot)

  · `lean/E213/Lib/Math/Mobius213.lean` — P 정의 + Pell invariant
  · `lean/E213/Lib/Math/Mobius213OneAsGlue.lean` — det = glue = 1
  · `lean/E213/Lib/Math/Mobius213ModFive.lean` — P¹⁰ ≡ I (mod 5)
  · `lean/E213/Lib/Math/UniverseChain/MobiusChain.lean` — chain G65-G81
  · `lean/E213/Lib/Math/Real213/Core/CutPoset.lean` — cutEq 정의
  · `lean/E213/Lib/Math/Real213/NValidCut.lean` — Wave 13 parametric capstone
  · `theory/essays/bool_assoc_failure_meaning.md` v4 — 진단 + closure 기록
  · `theory/essays/pure_funext_avoidance.md` — funext-avoidance 4 패턴 (Setoid 등)
  · `research-notes/archive/algebra_tower/G57_213_mobius_signature.md` — 만약 archive에 있다면 Möbius signature 원래 doc
  · `catalogs/cross-domain-identifications.md` CDI-9 — Möbius det 3-way 식별
  · `seed/AXIOM/05_no_exterior.md` §5 (dichotomy avoidance) — 반복 위반의 lesson

## Provenance

User insight (this session, dates 2026-05-23 → 2026-05-24): three corrective interventions surfaced the dichotomy-import pattern, with the third drawing the explicit Möbius-as-canonical-equivalence conjecture.  Claude's role: implementation + verification + structural correlation; conjecture itself is user's.
