import E213.Lens.Number.Int213.Raw

/-! Spec-as-code entry point for `E213.Lens.Number.Int213`.

  Int213 — Raw 의 `⟨1, -1, +⟩` lens 시점에서 본 ℤ.

  **The point**: Nat213.Raw 가 Raw 의 `Lens.leaves = ⟨1, 1, +⟩` 시점이라면,
  Int213.Raw 는 같은 Raw 의 `signedLens = ⟨1, -1, +⟩` 시점.  같은 Raw,
  다른 lens — 새 type 도입 안 함.

  ## Sub-modules

    * `Raw` — signedLens `⟨1, -1, +⟩ : Lens Int` 정의 + view (`value`),
              negation (`Raw.swap`, `value_neg`), lens-induced equivalence
              (`equiv`).  Canonical minimal-leaves representatives:
              `zero = slash a b`, `one = Raw.a`, `negOne = Raw.b`.

  ## ℤ 가 lens-emergent 한 정확한 이유

  Raw 의 두 atom (a, b) 에 부호를 ±1 로 부여 + slash 가 덧셈으로 작용
  + Raw.swap 이 자동으로 (-1)-multiplier (이미 `Raw.fold_signed_swap`
  로 증명).  추가 quotient 도, 추가 sum-type 도, 추가 axiom 도 필요
  없음 — Lens framework 이 quotient 의미를 자동 처리.

  ## Multiple Raws → same ℤ (lens 다대일)

  `value r = 0` 인 Raw 무수히 많음 (slash a b, slash a (slash b (slash a
  b)), ...).  이게 문제 아니라 *lens 의 본질* — Nat213.Raw 도 같은 leaves
  count 의 Raw 가 여럿이지만 `Lens.equiv` (Lens-induced equality) 으로
  처리됨.  ℤ 의 quotient 도 똑같이 `signedLens.equiv` 으로 처리.

  ## Parallel ℤ-constructions (이 codebase)

    * `Lens.Number.Nat213.Tower.NatPairToInt` — ℕ × ℕ diagonal
      quotient (G62 framing).  Pair-and-quotient 구성.
    * `Lens.Number.Int213.Raw` (이 파일) — Raw 의 직접 lens-view.
      Atom-level sign 부여로 ℤ 가 자연 emergent.

  All theorems ∅-axiom.
-/
