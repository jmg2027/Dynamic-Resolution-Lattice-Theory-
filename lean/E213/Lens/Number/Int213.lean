import E213.Lens.Number.Int213.Raw

/-! Spec-as-code entry point for `E213.Lens.Number.Int213`.

  Int213 — Raw-derived inductive ℤ (sign-extension of Nat213.Raw).

  ## Sub-modules

    * `Raw` — 3-갈래 sum-type 인덕티브 ℤ.  Carriers 가 `E213.Theory.Raw`
              (Method A chain 권장).  부호·0 확장으로 additive inverse
              (`add_neg_self`) 와 closed subtraction (`sub`) 가 비로소
              가능 — Nat213 에선 없던 성질.  같은 부호 add/mul 은
              `Nat213.Raw.add`/`mul` 로 위임, mixed-sign 은 `cancel`
              (Lean Nat boundary 의 value 비교).

  ## Parallel constructions (different framings of the same ℤ)

    * `Lens.Number.Nat213.Tower.NatPairToInt` — ℕ × ℕ diagonal
      quotient (G62 framing).  Lean Nat carriers, Lean Int output.
    * `Lens.Number.Int213.Raw` (이 파일) — Raw inductive sum-type.
      213-native carriers, 자체 Int213 type.

  All theorems ∅-axiom.
-/
