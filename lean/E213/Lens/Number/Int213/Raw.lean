import E213.Theory.Raw.API
import E213.Lens.LensCore
import E213.Meta.Int213.Core
import E213.Lens.Number.Nat213.Tower.NatPairToInt

/-!
# Lens.Number.Int213.Raw — Raw 를 signed lens 로 본 ℤ

**The point**: Nat213.Raw 는 Raw 의 `⟨1, 1, +⟩` 시점이고, Int213.Raw 는
Raw 의 `⟨1, -1, +⟩` 시점.  같은 Raw, 다른 lens.

  - `Lens.leaves = ⟨1, 1, +⟩ : Lens Nat` — atom a, b 둘 다 +1, combine 은
    덧셈.  view = leaves count.  Lens.equiv = "같은 leaves count".
    Nat213.Raw 의 의미.
  - `signedLens = ⟨1, -1, +⟩ : Lens Int` — atom a 는 +1, atom b 는 -1,
    combine 은 덧셈.  view = signed leaves net.  Lens.equiv = "같은
    signedNet".  **이 파일의 Int213**.

**새 type 도입 안 함**.  Carrier 는 그냥 Raw.  "ℤ" 는 codomain (Lean
Int) 에 emergent, Raw 쪽에는 quotient 으로 implicit — `Lens.equiv`
로 처리.  Parallel: Nat213.Raw 도 leaves-quotient 이 다대일 (e.g.
slash a b 와 slash b a 는 cmp 로 canonical 화 후 같음; slash a (slash a b)
와 slash b (slash a (slash a b)) 등은 leaves 다름이지만 같은 ℕ₊
quotient 에서 normalized).

**0 의 출처**: 213 axiom 에 nullary atom 없음, 그러나 ⟨1, -1, +⟩
codomain 이 ℤ 라 0 이 codomain 의 algebraic 결과 (1 + -1 = 0).  Raw
쪽 대응: `value r = 0` 인 Raw 무수히 많음 — minimal leaves canonical 은
`slash a b`.  parallel: Nat213 의 numeral n 이 leaves count n+1 의
canonical representative 인 것과 동형.

**Negation lens**: Raw.swap.  `Raw.fold_signed_swap` (Theory/Raw/
Signed.lean) 이 `value (swap r) = - value r` 을 이미 증명.

∅-axiom; Mathlib/Classical 사용 0.
-/

namespace E213.Lens.Number.Int213.Raw

open E213.Theory
open E213.Lens

/-! ## Signed lens — Raw 의 ℤ 시점 -/

/-- ℤ-valued signed lens — atom a = +1, atom b = -1, combine = (·+·). -/
def signedLens : Lens Int := ⟨1, -1, (· + ·)⟩

/-- Raw 의 signed integer view (signedLens.view). -/
def value (r : Raw) : Int := signedLens.view r

theorem value_a : value Raw.a = 1 := rfl
theorem value_b : value Raw.b = -1 := rfl

/-- `slash` 의 signed-add 호환: combine 가 Int 의 + 이고 add_comm 이
    symmetric 이라 `Raw.fold_slash` 가 직접 적용. -/
theorem value_slash (x y : Raw) (h : x ≠ y) :
    value (Raw.slash x y h) = value x + value y :=
  Raw.fold_slash (1 : Int) (-1) (· + ·)
    (fun u v => E213.Meta.Int213.add_comm u v) x y h

/-! ## Negation via Raw.swap

Tree-level `Tree.fold_signed_swap` 와 Raw-level `Raw.fold_signed_swap`
이 이미 증명: signedLens 의 codomain 에서 swap 이 `-·` 로 작용. -/

/-- 부호 반전 — Raw.swap.  (lens 시점에서) `value (neg r) = -value r`. -/
def neg : Raw → Raw := Raw.swap

theorem value_neg (r : Raw) : value (neg r) = -value r :=
  Raw.fold_signed_swap r

theorem neg_neg (r : Raw) : neg (neg r) = r := Raw.swap_swap r

theorem neg_a : neg Raw.a = Raw.b := Raw.swap_a
theorem neg_b : neg Raw.b = Raw.a := Raw.swap_b

/-! ## Lens-induced equality (the ℤ-equivalence on Raw)

두 Raw 가 "같은 정수" iff `signedLens.view` 가 같음.  `Lens.equiv`
(LensCore) 의 instance. -/

/-- Int213-equality on Raw: signedLens.view 가 일치. -/
def equiv (x y : Raw) : Prop := signedLens.equiv x y

theorem equiv_iff (x y : Raw) : equiv x y ↔ value x = value y := Iff.rfl

theorem equiv_refl (r : Raw) : equiv r r := signedLens.equiv_refl r
theorem equiv_symm {x y : Raw} : equiv x y → equiv y x := signedLens.equiv_symm
theorem equiv_trans {x y z : Raw} : equiv x y → equiv y z → equiv x z :=
  signedLens.equiv_trans

/-- `neg` 는 lens-equivalence 보존 — neg 이 단사 (Raw.swap_swap 으로). -/
theorem equiv_neg {x y : Raw} (h : equiv x y) : equiv (neg x) (neg y) := by
  have h' : value x = value y := h
  show value (neg x) = value (neg y)
  rw [value_neg, value_neg, h']

/-! ## Canonical Raw representatives — Method A for ℤ

Nat213.Raw 의 `one = Raw.a`, `numeral n = succ chain` 과 평행.
여기선 minimal-leaves canonical 만 노출 (chain extension 은 추가
가능). -/

/-- `Raw.a ≠ Raw.b` — decidable. -/
private theorem a_ne_b : Raw.a ≠ Raw.b := by decide

/-- ℤ 의 0 — canonical Raw 대표 `slash a b`.  signedLens.view = 0. -/
def zero : Raw := Raw.slash Raw.a Raw.b a_ne_b

theorem value_zero : value zero = 0 := rfl

/-- ℤ 의 +1 — canonical Raw 대표 `Raw.a`. -/
def one : Raw := Raw.a

theorem value_one : value one = 1 := rfl

/-- ℤ 의 -1 — canonical Raw 대표 `Raw.b`. -/
def negOne : Raw := Raw.b

theorem value_negOne : value negOne = -1 := rfl

theorem neg_one : neg one = negOne := Raw.swap_a
theorem neg_negOne : neg negOne = one := Raw.swap_b

/-- `zero` 는 `neg` 의 fixed point — 0 = -0. -/
theorem neg_zero : equiv (neg zero) zero := by
  show value (neg zero) = value zero
  rw [value_neg, value_zero]
  rfl

/-! ## Pair lens — signedLens 의 orthogonal-axis 분해

`signedLens = ⟨1, -1, +⟩ : Lens Int` 의 codomain `Int` 을 두 ℕ-axis 로
분해: a-count 와 b-count 를 따로 누적하면 `Lens (ℕ × ℕ)`.  이 pair
lens 의 view 를 `Tower.NatPairToInt.npairToInt` 로 project 하면
signedLens 와 일치 — **`signedLens = npairToInt ∘ pairLens`**. -/

/-- 컴포넌트-wise pair add. -/
private def pairCombine (p q : Nat × Nat) : Nat × Nat := (p.1 + q.1, p.2 + q.2)

/-- pairLens — Raw 의 atom 분해.  atom a = (1, 0), atom b = (0, 1),
    combine = component-wise +.  view = (a-count, b-count). -/
def pairLens : Lens (Nat × Nat) := ⟨(1, 0), (0, 1), pairCombine⟩

/-- Raw 의 atom-decomposition pair (pairLens.view). -/
def pairCount (r : Raw) : Nat × Nat := pairLens.view r

theorem pairCount_a : pairCount Raw.a = (1, 0) := rfl
theorem pairCount_b : pairCount Raw.b = (0, 1) := rfl

/-- pairCombine 은 가환 — component-wise Nat.add_comm. -/
private theorem pairCombine_comm (p q : Nat × Nat) :
    pairCombine p q = pairCombine q p := by
  show (p.1 + q.1, p.2 + q.2) = (q.1 + p.1, q.2 + p.2)
  rw [Nat.add_comm p.1 q.1, Nat.add_comm p.2 q.2]

/-- pairLens 의 slash 호환: view (slash x y) = combine (view x) (view y). -/
theorem pairCount_slash (x y : Raw) (h : x ≠ y) :
    pairCount (Raw.slash x y h) = pairCombine (pairCount x) (pairCount y) :=
  Raw.fold_slash (1, 0) (0, 1) pairCombine pairCombine_comm x y h

/-! ### Factoring: signedLens = npairToInt ∘ pairLens

Keystone `Meta.Int213.subNatNat_add_subNatNat` 가 이미 ∅-axiom 으로
`subNatNat a b + subNatNat c d = subNatNat (a+c) (b+d)` 를 증명;
Tree induction 한 줄로 factoring 닫힘. -/

open E213.Term.Internal (Tree)

/-- Tree-level factoring (private; Raw-level lift 는 아래). -/
private theorem tree_signedLens_factor (t : Tree) :
    Tree.fold (1 : Int) (-1) (· + ·) t
      = Int.subNatNat
          (Tree.fold (1, 0) (0, 1) pairCombine t).1
          (Tree.fold (1, 0) (0, 1) pairCombine t).2 := by
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      show Tree.fold (1 : Int) (-1) (· + ·) x
           + Tree.fold (1 : Int) (-1) (· + ·) y
         = Int.subNatNat
             ((Tree.fold (1, 0) (0, 1) pairCombine x).1
              + (Tree.fold (1, 0) (0, 1) pairCombine y).1)
             ((Tree.fold (1, 0) (0, 1) pairCombine x).2
              + (Tree.fold (1, 0) (0, 1) pairCombine y).2)
      rw [ihx, ihy]
      exact E213.Meta.Int213.subNatNat_add_subNatNat _ _ _ _

/-- ★ Factoring: signedLens.view 가 pairLens.view 를 `npairToInt`
    (Tower 의 morphism) 으로 project 한 것과 일치.  즉 Raw → ℤ 가
    Raw → ℕ × ℕ → ℤ 로 commute. -/
theorem signedLens_factors_through_pairLens (r : Raw) :
    value r = E213.Lens.Number.Nat213.Tower.NatPairToInt.npairToInt (pairCount r) :=
  tree_signedLens_factor r.val

/-- pairLens 가 signedLens 를 refine — 같은 pairCount 면 같은 signed
    value.  Factoring 의 직접 따름결. -/
theorem pairLens_refines_signedLens : pairLens.refines signedLens := by
  intro x y h
  show value x = value y
  rw [signedLens_factors_through_pairLens x,
      signedLens_factors_through_pairLens y]
  exact congrArg _ h

end E213.Lens.Number.Int213.Raw
