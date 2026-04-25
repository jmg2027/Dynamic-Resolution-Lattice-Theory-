# 89 — Or-based Prop instance: dual to And

`Research/SemanticAtom.lean` + `CanonicalTruthChar.lean` 확장.
4번째 Prop instance (And 의 dual).

## 결과

```lean
def propAsDistinguishingOr : HasDistinguishing Prop := ...
def canonicalOrMap : Raw → Prop := universalMorphism Prop (...)

theorem canonicalOrMap_iff_ne_b (r : Raw) :
  canonicalOrMap r ↔ r ≠ Raw.b
```

[propext, Quot.sound] only.

## Algebraic content: dual degenerate

Or 가 And 의 dual (De Morgan):
- Or: T ∨ F = T, T ∨ T = T, F ∨ F = F.
- And: T ∧ F = F, T ∧ T = T, F ∧ F = F.

Universal morphism via Or:
- a → T.
- b → F.
- slash x y → x ∨ y.  T iff at least one branch T.
- → result T iff ∃ a leaf in r.

**∃ a leaf in r ↔ r ≠ Raw.b** (since r = Raw.b 만 single b leaf,
다른 모든 r 에 a leaf 적어도 하나).

따라서 `canonicalOrMap r ↔ r ≠ Raw.b`.

## 4 Prop instances 의 algebraic spectrum

| Connective | Universal morphism | Invariant | 강도 |
|-----------|-------------------|-----------|------|
| Xor | canonicalTruthMap | a-count parity | strong |
| Iff | canonicalIffMap | b-count parity | strong |
| And | canonicalAndMap | r = Raw.a | weak (degenerate) |
| **Or** | **canonicalOrMap** | **r ≠ Raw.b** | **weak (dual degenerate)** |

**Symmetry of dualities**:
- Xor / Iff: 분포 적, parity-based, dual.
- And / Or: degenerate, single-Raw-condition, dual (De Morgan).

같은 framework 안 의 4 connective 가 *radically distinct*
algebraic content carry — self-application 의 spectrum 의 명시.

## ZFC 와 의 비교

ZFC 에서 set 위 의 connective 선택 이 *meta-level* — set
membership 의 axiom 이 commit.

213: connective 가 framework 안 instance — universal morphism
의 algebraic content 가 framework 안 derived.  외부 commitment
부재.

## Axiom 검증

`#print axioms`:
- `canonicalOrMap_iff_ne_b`: [propext, Quot.sound]

## 변경 이력

- 2026-04-25: Or-based instance + characterization.  And/Or
  dual symmetry 의 algebraic content 명시.
