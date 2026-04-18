import E213.OS.Provability

/-
  OS Layer: Naive Set Theory 를 / 위에.

  렌즈: Lens.atomSet (α = List (Fin 3), 원자 사용 집합).
  Set encoding:
    ∅       → atom 0
    {x} ∪ S → rel x S.toRaw  (cons-like)

  같은 set = 렌즈 kernel 에서 같음 = 같은 원자를 사용.
  Extensionality: 렌즈 수준에서 자동.

  Peano/Logic 과 평행:
    Peano : depth 렌즈, atom 0=zero, rel=succ.
    Logic : truthValue 렌즈, atom 0=⊤, rel=imp.
    Set   : atomSet 렌즈, atom 0=∅,  rel=cons.
-/

-- ═══ Membership ═══

-- x 가 set s 에 있는가.
def Raw.memSet (x : Raw) : Raw → Bool
  | .atom _  => false               -- atom 은 ∅ 또는 urelement
  | .rel a s => x == a || s.memSet x

-- ═══ Set 렌즈 ═══

-- 사용된 atom 인덱스의 (중복 없는) 집합.
def Lens.atomSet : Lens (List (Fin 3)) :=
  ⟨fun i => [i], fun a b => (a ++ b).dedup⟩

-- ═══ 구체 집합들 ═══

-- ∅
def emptySet : Raw := a₀

-- {atom 1}  (rel atom 1 ∅, atom 1 ≠ ∅ 필요)
def singleB : Raw := .rel b₀ emptySet

-- {atom 1, atom 2}  (rel atom 2 (rel atom 1 ∅))
def pairBC : Raw := .rel (.atom 2) singleB

-- ═══ Membership 테스트 ═══

example : ¬ (emptySet.memSet b₀ = true) := by decide
example : singleB.memSet b₀ = true := by decide
example : ¬ (singleB.memSet (.atom 2) = true) := by decide
example : pairBC.memSet b₀ = true := by decide
example : pairBC.memSet (.atom 2) = true := by decide

-- ═══ 렌즈 kernel: "같은 set" ═══

-- {atom 1} 과 다시 {atom 1} (같은 구성)
example : Lens.atomSet.view singleB = [1] := by decide

-- {atom 1, atom 2} 의 atomSet
example : Lens.atomSet.view pairBC = [2, 1] := by decide

-- 순서 바뀐 구성: rel atom 1 (rel atom 2 ∅)
def pairBC' : Raw := .rel b₀ (.rel (.atom 2) emptySet)
example : Lens.atomSet.view pairBC' = [1, 2] := by decide

-- 순서는 다르지만 원소 집합은 같음 (둘 다 {1, 2}).
-- 하지만 렌즈가 List 를 결과로 주므로 list equality 는 다름.
-- → List.Perm 기반 kernel 사용.

-- ═══ Set Equality: 렌즈 view 의 Perm ═══

def Raw.setEq (s t : Raw) : Prop :=
  List.Perm (Lens.atomSet.view s) (Lens.atomSet.view t)

notation:50 s " ≡s " t => Raw.setEq s t

instance (s t : Raw) : Decidable (s ≡s t) :=
  List.decidablePerm _ _

-- 동치관계 (List.Perm 의 일반 성질).
theorem setEq_refl (s : Raw) : s ≡s s := List.Perm.refl _
theorem setEq_symm {s t : Raw} : s ≡s t → t ≡s s := List.Perm.symm
theorem setEq_trans {s t u : Raw} :
    s ≡s t → t ≡s u → s ≡s u := List.Perm.trans

-- ═══ Extensionality: 순서 무관, 원소만 같으면 ≡s ═══

example : pairBC ≡s pairBC' := by decide
example : pairBC ≡s pairBC := by decide

-- ═══ Subset ═══

def Raw.subsetOfSet (s t : Raw) : Prop :=
  ∀ i ∈ Lens.atomSet.view s, i ∈ Lens.atomSet.view t

instance (s t : Raw) : Decidable (s.subsetOfSet t) :=
  List.decidableBAll _ _

example : emptySet.subsetOfSet singleB := by decide
example : singleB.subsetOfSet pairBC := by decide
example : ¬ pairBC.subsetOfSet singleB := by decide

-- ═══ Provability Classifier 적용 ═══

-- 명제: "이 Raw 는 atom 2 를 포함한다."
def containsAtom2 : Raw → Prop :=
  fun x => (2 : Fin 3) ∈ Lens.atomSet.view x

instance : DecidablePred containsAtom2 := fun x =>
  inferInstanceAs (Decidable (_ ∈ _))

-- atomSet 렌즈는 이 명제를 자동 respects.
theorem containsAtom2_respects :
    RespectsLens Lens.atomSet containsAtom2 := by
  intro x y h
  unfold containsAtom2 Lens.equiv at *
  rw [h]

-- 하지만 depth 렌즈에선 Independent!
-- pairBC =[depth] (다른 어떤 Raw), 하지만 containsAtom2 다를 수 있음.

-- 구체 독립성 증명.
-- depth 1 이고 atom 2 없음: ab₀ = rel a₀ b₀.
-- depth 1 이고 atom 2 있음: relC_a = rel (atom 2) a₀.
def relC_a : Raw := .rel (.atom 2) a₀

example : IndependentIn Lens.depth containsAtom2 := by
  refine ⟨relC_a, ab₀, ?_, ?_, ?_, ?_, ?_⟩
  · exact .step (.atom 2) (.atom 0) (by decide)   -- Reachable relC_a
  · exact .step (.atom 0) (.atom 1) (by decide)   -- Reachable ab₀
  · decide   -- relC_a.depth = ab₀.depth (둘 다 1)
  · decide   -- containsAtom2 relC_a (true)
  · decide   -- ¬ containsAtom2 ab₀ (false)

-- 결과: depth 렌즈는 "atom 2 가 있는지" 를 결정 못 함.
-- 두 Raw 가 같은 depth 이지만 atom 2 포함 여부가 다름.
-- → atomSet 렌즈 필요 (더 세밀한 kernel).
