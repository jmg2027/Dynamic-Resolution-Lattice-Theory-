import E213.Theory.Closed.Nat213
import E213.Theory.Nat213.Core

/-!
# Theory.Closed.Nat213Bridge — Layer 1 ↔ Layer 2 동형성

두 종류 Nat213 표현:
  - Layer 1 (closed Raw):  `Theory.Closed.Nat213` — Method A Raw chain.
                            `one := Raw.a`, `succ n := slashOrSelf n Raw.b`
  - Layer 2 (inductive):   `Theory.Nat213.Nat213` — `inductive | one | succ`

이 모듈은 둘 사이 bridge.  결론: 두 표현이 산술 (succ/add/mul) 위에서
**isomorphic** — 산술 연산들이 bridge 를 따라 commute.

이게 framework 의 정합성: closed-Raw 가 inductive Nat213 의 진짜 모델.
-/

namespace E213.Theory.Closed.Nat213Bridge

open E213.Theory

/-! ### Layer 2 → Layer 1: inductive Nat213 → Method A Raw chain -/

/-- `toRaw n` — inductive `Nat213` 의 element 를 Method A Raw chain 으로. -/
def toRaw : Theory.Nat213.Nat213 → Raw
  | .one    => Theory.Closed.Nat213.one
  | .succ k => Theory.Closed.Nat213.succ (toRaw k)

/-- 기본 케이스. -/
theorem toRaw_one :
    toRaw Theory.Nat213.Nat213.one = Theory.Closed.Nat213.one := rfl

/-- succ commute. -/
theorem toRaw_succ (k : Theory.Nat213.Nat213) :
    toRaw (Theory.Nat213.Nat213.succ k)
      = Theory.Closed.Nat213.succ (toRaw k) := rfl

end E213.Theory.Closed.Nat213Bridge

namespace E213.Theory.Closed.Nat213Bridge

open E213.Theory

/-! ### Layer 1 chain 은 항상 Raw.b ≠ — bridge homomorphism 의 보조 lemma -/

/-- toRaw 의 image 는 항상 Raw.b 와 다름.  Method A chain 의 invariant. -/
theorem toRaw_ne_b (k : Theory.Nat213.Nat213) : toRaw k ≠ Raw.b := by
  induction k with
  | one =>
      -- toRaw .one = Closed.Nat213.one = Raw.a ≠ Raw.b
      intro h
      have hval : Raw.a.val = Raw.b.val := congrArg Subtype.val h
      exact Theory.Internal.Tree.noConfusion hval
  | succ k ih =>
      -- toRaw (.succ k) = succ (toRaw k) = slashOrSelf (toRaw k) Raw.b
      -- (toRaw k ≠ Raw.b) → slashOrSelf reduces to Raw.slash → .slash form ≠ Raw.b
      show Theory.Closed.Nat213.succ (toRaw k) ≠ Raw.b
      unfold Theory.Closed.Nat213.succ Theory.Closed.slashOrSelf
      rw [dif_neg ih]
      intro h
      have hval : (Raw.slash (toRaw k) Raw.b ih).val = Raw.b.val := congrArg Subtype.val h
      unfold Raw.slash at hval
      split at hval
      · exact Theory.Internal.Tree.noConfusion hval
      · exact Theory.Internal.Tree.noConfusion hval
      · rename_i hcmp
        exact ih (Subtype.ext (Theory.Internal.Tree.cmp_eq_to_eq _ _ hcmp))

/-! ### + family homomorphism: toRaw 가 add 를 보존 -/

/-- **`toRaw (add m n) = add (toRaw m) (toRaw n)`** — Layer 2 의 덧셈이
    Layer 1 의 덧셈과 정확히 일치 (bridge 를 따라).

    이게 두 표현이 산술적으로 동형임의 증거. -/
theorem toRaw_add (m n : Theory.Nat213.Nat213) :
    toRaw (Theory.Nat213.Nat213.add m n)
      = Theory.Closed.Nat213.add (toRaw m) (toRaw n) := by
  induction m with
  | one =>
      -- Layer 2: add one n = succ n.  Layer 1: add one (toRaw n) = succ (toRaw n).
      show toRaw (Theory.Nat213.Nat213.succ n)
         = Theory.Closed.Nat213.add Theory.Closed.Nat213.one (toRaw n)
      rw [Theory.Closed.Nat213.one_add]
      rfl
  | succ k ih =>
      -- Layer 2: add (succ k) n = succ (add k n).
      -- Layer 1: add (succ (toRaw k)) (toRaw n) = succ (add (toRaw k) (toRaw n))
      --                                   (by add_succ_left, since toRaw k ≠ Raw.b)
      show toRaw (Theory.Nat213.Nat213.succ (Theory.Nat213.Nat213.add k n))
         = Theory.Closed.Nat213.add
              (Theory.Closed.Nat213.succ (toRaw k)) (toRaw n)
      rw [toRaw_succ, Theory.Closed.Nat213.add_succ_left _ _ (toRaw_ne_b k), ih]

end E213.Theory.Closed.Nat213Bridge

namespace E213.Theory.Closed.Nat213Bridge

open E213.Theory

/-! ### × family homomorphism: toRaw 가 mul 도 보존 -/

/-- **`toRaw (mul m n) = mul (toRaw m) (toRaw n)`** — 곱셈도 bridge 를
    따라 일치.  + family 모든 연산이 bridge 를 따라 commute. -/
theorem toRaw_mul (m n : Theory.Nat213.Nat213) :
    toRaw (Theory.Nat213.Nat213.mul m n)
      = Theory.Closed.Nat213.mul (toRaw m) (toRaw n) := by
  induction m with
  | one =>
      -- Layer 2: mul one n = n.  Layer 1: mul one (toRaw n) = toRaw n.
      show toRaw n = Theory.Closed.Nat213.mul Theory.Closed.Nat213.one (toRaw n)
      rw [Theory.Closed.Nat213.one_mul]
  | succ k ih =>
      -- Layer 2: mul (succ k) n = add n (mul k n).
      -- Layer 1: mul (succ (toRaw k)) (toRaw n)
      --       = add (toRaw n) (mul (toRaw k) (toRaw n))   (mul_succ_left)
      show toRaw (Theory.Nat213.Nat213.add n (Theory.Nat213.Nat213.mul k n))
         = Theory.Closed.Nat213.mul
              (Theory.Closed.Nat213.succ (toRaw k)) (toRaw n)
      rw [Theory.Closed.Nat213.mul_succ_left _ _ (toRaw_ne_b k)]
      rw [toRaw_add, ih]

end E213.Theory.Closed.Nat213Bridge
