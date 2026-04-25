# 64 — Indexed Join Lens (임의 family 의 join)

## 결과

`Research/IndexedJoinLens.lean`:

**임의 indexed family `{L_i}_{i ∈ I}` 의 concrete join** —
`iJoinLens F : Lens (Raw → Prop)`.

- `IJoinEquiv F`: 모든 L_i.equiv 를 포함하는 smallest slash-cong.
- `iJoinLens F := universalLens (IJoinEquiv F)`.

## 정리

- `iJoinLens_kernel`: kernel = IJoinEquiv F.
- `each_refines_iJoinLens`: 모든 L_i refines iJoinLens (upper
  bound 성).
- `iJoinLens_is_least`: least upper bound (universal property).

## 의의

이전 까지 binary join (`joinLens L M`) 만 explicit.  이제 **임의
indexed family** 까지 확장.  Mod m family (countable infinite)
같은 case 에서:

- `F : ℕ≥2 → Σ α, Lens α`, F m := ⟨Nat, leavesModNat m⟩.
- iJoinLens F = mod family 전체 의 common upper bound.
- Universal property 로 leaves Lens 가 이 join 과 같음 (since
  leaves refines all leavesModNat m, and is least such).

## 213 framework 의 표현력

지금 까지 형식 화 된 lattice operations:
- **Bottom** (⊥): `idLens` (most discriminating).
- **Top** (⊤): `constLens` (least discriminating).
- **Binary meet**: `prodLens`.
- **Binary join**: `joinLens`.
- **Indexed join**: `iJoinLens` (NEW).

각 operation 의 universal property 가 explicit Lean theorem.
External axiom 0.

## 변경 이력

- 2026-04-25: indexed join Lens.  임의 family 의 universal
  property 까지 확장.
