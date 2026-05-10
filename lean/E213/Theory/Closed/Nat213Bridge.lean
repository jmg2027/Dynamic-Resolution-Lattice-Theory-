import E213.Theory.Closed.Nat213
import E213.Theory.Nat213.Core
import E213.Lib.Math.NatHelpers.PureNat

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

namespace E213.Theory.Closed.Nat213Bridge

open E213.Theory

/-! ### + family laws lifted via bridge

Layer 2 의 정리들 (add_comm, add_one_right, add_succ_right) 을
toRaw bridge 통해 Layer 1 (closed Raw chain) 으로 lift.

이게 G84 Tier 2 작업 — Layer 2 에서 이미 증명된 정리를 Layer 1 에서
재증명 하지 않고 동형성으로 이전. -/

/-- `add_comm` (Layer 1, Method A chain 위): `add m n = add n m` for chains
    coming from Layer 2.  toRaw bridge 통해 Layer 2 add_comm 활용. -/
theorem add_comm (m n : Theory.Nat213.Nat213) :
    Theory.Closed.Nat213.add (toRaw m) (toRaw n)
      = Theory.Closed.Nat213.add (toRaw n) (toRaw m) := by
  rw [← toRaw_add, ← toRaw_add, Theory.Nat213.Nat213.add_comm]

/-- `add_one_right`: `add m one = succ m` for chains from Layer 2.
    Layer 2 의 `add_one_right` 직접 활용. -/
theorem add_one_right (m : Theory.Nat213.Nat213) :
    Theory.Closed.Nat213.add (toRaw m) Theory.Closed.Nat213.one
      = Theory.Closed.Nat213.succ (toRaw m) := by
  rw [← toRaw_one, ← toRaw_add, Theory.Nat213.Nat213.add_one_right, toRaw_succ]

/-- `add_succ_right`: `add m (succ n) = succ (add m n)` (chains).  Layer 2
    의 `add_succ_right` 활용. -/
theorem add_succ_right (m n : Theory.Nat213.Nat213) :
    Theory.Closed.Nat213.add (toRaw m)
        (Theory.Closed.Nat213.succ (toRaw n))
      = Theory.Closed.Nat213.succ
          (Theory.Closed.Nat213.add (toRaw m) (toRaw n)) := by
  rw [← toRaw_succ, ← toRaw_add, Theory.Nat213.Nat213.add_succ_right,
      toRaw_succ, toRaw_add]

end E213.Theory.Closed.Nat213Bridge

namespace E213.Theory.Closed.Nat213Bridge

open E213.Theory

/-! ### value 동형성 — Layer 1 → Lean Nat

추가 bridge: closed Raw chain 의 leaves count (`value`) 가 Lean Nat 의
산술과 호환.  inductive Nat213 의 `toNat` 과 일치.

이게 두 번째 종류의 bridge:
  - 첫 번째 (toRaw): Layer 2 → Layer 1 (inductive → closed Raw)
  - 두 번째 (value): Layer 1 → Lean Nat (closed Raw → 외부 Nat) -/

/-- Layer 2 toNat 와 Layer 1 value 가 toRaw 따라 일치. -/
theorem value_toRaw (m : Theory.Nat213.Nat213) :
    Theory.Closed.Nat213.value (toRaw m) = m.toNat := by
  induction m with
  | one => rfl
  | succ k ih =>
      -- value (succ (toRaw k)) = (toRaw k) + 1 since toRaw k ≠ Raw.b
      -- toNat (succ k) = k.toNat + 1
      show Theory.Closed.Nat213.value
              (Theory.Closed.Nat213.succ (toRaw k))
         = k.toNat + 1
      rw [Theory.Closed.Nat213.value_succ_of_ne _ (toRaw_ne_b k), ih]

/-! ### Layer 2 toNat additive homomorphism (보조 lemma) -/

/-- Layer 2 의 toNat 가 add 를 보존: `(add m n).toNat = m.toNat + n.toNat`.
    이게 Layer 1 value_add 의 enabler. -/
private theorem toNat_add (m n : Theory.Nat213.Nat213) :
    (Theory.Nat213.Nat213.add m n).toNat = m.toNat + n.toNat := by
  induction m with
  | one =>
      -- Layer 2: add one n = succ n.  toNat: 1 + n.toNat.
      show (Theory.Nat213.Nat213.succ n).toNat = 1 + n.toNat
      show n.toNat + 1 = 1 + n.toNat
      exact Nat.add_comm _ _
  | succ k ih =>
      -- Layer 2: add (succ k) n = succ (add k n).  toNat: (add k n).toNat + 1
      --                                                = (k.toNat + n.toNat) + 1
      -- RHS: (succ k).toNat + n.toNat = (k.toNat + 1) + n.toNat
      show (Theory.Nat213.Nat213.add k n).toNat + 1
         = (k.toNat + 1) + n.toNat
      rw [ih]
      -- Goal: k.toNat + n.toNat + 1 = k.toNat + 1 + n.toNat
      exact (Nat.add_right_comm _ _ _).symm

/-! ### value_add (★ 핵심): closed-Raw add 가 Lean Nat add 와 호환 -/

/-- **`value (add m n) = value m + value n`** — Layer 1 (closed Raw)
    덧셈이 Lean Nat 덧셈과 정확히 일치 (Layer 2 chain 위).

    이게 closed-form ↔ external Nat 의 정확한 동형성 표현. -/
theorem value_add (m n : Theory.Nat213.Nat213) :
    Theory.Closed.Nat213.value
        (Theory.Closed.Nat213.add (toRaw m) (toRaw n))
      = Theory.Closed.Nat213.value (toRaw m)
      + Theory.Closed.Nat213.value (toRaw n) := by
  rw [← toRaw_add, value_toRaw, value_toRaw, value_toRaw, toNat_add]

end E213.Theory.Closed.Nat213Bridge

namespace E213.Theory.Closed.Nat213Bridge

open E213.Theory

/-! ### Layer 2 toNat multiplicative homomorphism + value_mul -/

/-- Layer 2 toNat 가 mul 도 보존. -/
private theorem toNat_mul (m n : Theory.Nat213.Nat213) :
    (Theory.Nat213.Nat213.mul m n).toNat = m.toNat * n.toNat := by
  induction m with
  | one =>
      -- Layer 2: mul one n = n.  toNat: 1 * n.toNat.
      show n.toNat = 1 * n.toNat
      rw [Nat.one_mul]
  | succ k ih =>
      -- Layer 2: mul (succ k) n = add n (mul k n).
      show (Theory.Nat213.Nat213.add n
              (Theory.Nat213.Nat213.mul k n)).toNat
         = (k.toNat + 1) * n.toNat
      rw [toNat_add, ih]
      -- Goal: n.toNat + k.toNat * n.toNat = (k.toNat + 1) * n.toNat
      rw [E213.Lib.Math.NatHelpers.PureNat.add_mul, Nat.one_mul, Nat.add_comm]

/-- **`value (mul m n) = value m * value n`** — Layer 1 곱셈이
    Lean Nat 곱셈과 일치. -/
theorem value_mul (m n : Theory.Nat213.Nat213) :
    Theory.Closed.Nat213.value
        (Theory.Closed.Nat213.mul (toRaw m) (toRaw n))
      = Theory.Closed.Nat213.value (toRaw m)
      * Theory.Closed.Nat213.value (toRaw n) := by
  rw [← toRaw_mul, value_toRaw, value_toRaw, value_toRaw, toNat_mul]

end E213.Theory.Closed.Nat213Bridge
