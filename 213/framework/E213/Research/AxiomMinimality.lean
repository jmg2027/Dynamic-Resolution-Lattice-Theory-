/-!
# Research.AxiomMinimality: Raw axiom 의 minimum 성

Raw axiom 의 3 clauses (Raw.a, Raw.b, slash with x ≠ y) 가 진짜
minimum 임을 형식적 demonstration.

## 결과

Raw.b 제거 한 가상 axiom 은 generation 붕괴.  Single base + slash
with distinctness 만으로는 single element 만 생성.

따라서 (Raw.a, Raw.b) 두 base 가 essential.

## 접근

- TreeA: Raw.b 없는 inductive type.  diagonal slash 도 일단 허용.
- RawA: TreeA 의 subtype (no diagonal slashes).
- 정리: ∀ r : RawA, r.val = TreeA.a.
-/

namespace E213.Research.AxiomMinimality

/-- Raw.b 없는 가상 tree.  diagonal slash 는 syntactically 허용
    되지만 RawA subtype 으로 제외. -/
inductive TreeA : Type where
  | a
  | slash : TreeA → TreeA → TreeA
deriving DecidableEq

/-- TreeA 안 어딘가에 diagonal slash (x = y) 가 있는지. -/
def TreeA.hasDiag : TreeA → Bool
  | .a => false
  | .slash x y => decide (x = y) || hasDiag x || hasDiag y

/-- RawA: diagonal slash 없는 TreeA. -/
abbrev RawA : Type := { t : TreeA // t.hasDiag = false }

/-- RawA.a — 유일하게 자명한 element. -/
def RawA.a : RawA := ⟨.a, rfl⟩

/-- TreeA without diag and without Raw.b → only TreeA.a.
    Strong induction on TreeA. -/
theorem treeA_no_diag_only_a : ∀ t : TreeA, t.hasDiag = false → t = TreeA.a := by
  intro t
  induction t with
  | a => intro _; rfl
  | slash x y ihx ihy =>
      intro hnd
      have hexpand : TreeA.hasDiag (TreeA.slash x y)
                       = (decide (x = y) || x.hasDiag || y.hasDiag) := rfl
      rw [hexpand] at hnd
      have h1 := Bool.or_eq_false_iff.mp hnd
      have h2 := Bool.or_eq_false_iff.mp h1.1
      have hxy : ¬ (x = y) := decide_eq_false_iff_not.mp h2.1
      have hx_a : x = TreeA.a := ihx h2.2
      have hy_a : y = TreeA.a := ihy h1.2
      rw [hx_a, hy_a] at hxy
      exact absurd rfl hxy

/-- **AxiomMinimality 정리**: Raw.b 제거 한 axiom 은 single
    element (RawA.a) 만 생성.  Generation 붕괴 demonstration. -/
theorem rawA_trivial : ∀ r : RawA, r = RawA.a := by
  intro ⟨t, h⟩
  have : t = TreeA.a := treeA_no_diag_only_a t h
  subst this
  rfl

end E213.Research.AxiomMinimality
