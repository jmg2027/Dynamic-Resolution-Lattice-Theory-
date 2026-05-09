import E213.Lib.Math.CayleyDickson.ZSqrtMinus2L6Witnesses

/-!
# Meta search algorithm: Rust-discovered → Lean-proven pipeline

`findZD` is a pure recursive search; `findZD_sound` is its soundness
lemma.  Plug any candidate list and `decide` the find result; the
existence theorem then follows mechanically.

Pattern (general):
  algorithm : Cands → Option Witness
  soundness : algorithm cs = some w → P w  (induction)
  application: ∃ w, P w  (decide find = some w; apply soundness)
-/

namespace E213.Lib.Math.CayleyDickson.ZSqrtMinus2

def findOneZD (a : L6T) : List L6T → Option L6T
  | [] => none
  | b :: bs =>
    if a ≠ L6z ∧ b ≠ L6z ∧ a * b = L6z then some b
    else findOneZD a bs

def findZD : List L6T → List L6T → Option (L6T × L6T)
  | [], _ => none
  | a :: as, bs =>
    match findOneZD a bs with
    | some b => some (a, b)
    | none => findZD as bs

theorem findOneZD_sound (a : L6T) :
    ∀ (bs : List L6T) b, findOneZD a bs = some b →
      a ≠ L6z ∧ b ≠ L6z ∧ a * b = L6z := by
  intro bs
  induction bs with
  | nil => intro b h; cases h
  | cons head tail ih =>
    intro b h
    simp only [findOneZD] at h
    by_cases hp : a ≠ L6z ∧ head ≠ L6z ∧ a * head = L6z
    · rw [if_pos hp] at h; cases h; exact hp
    · rw [if_neg hp] at h; exact ih b h

theorem findZD_sound :
    ∀ (xs ys : List L6T) p, findZD xs ys = some p →
      p.1 ≠ L6z ∧ p.2 ≠ L6z ∧ p.1 * p.2 = L6z := by
  intro xs
  induction xs with
  | nil => intros ys p h; cases h
  | cons a as ih =>
    intro ys p h
    simp only [findZD] at h
    cases hone : findOneZD a ys with
    | none => rw [hone] at h; exact ih ys p h
    | some b =>
      rw [hone] at h; cases h
      exact findOneZD_sound a ys b hone

def candidates : List L6T := [zd_a, zd_b, e1, e4, e10, e15]

theorem findZD_finds_witness :
    findZD candidates candidates = some (zd_a, zd_b) := by decide

/-- ★ ∅-axiom existence via meta search pipeline. -/
theorem L6_has_zero_divisor :
    ∃ a b : L6T, a ≠ L6z ∧ b ≠ L6z ∧ a * b = L6z := by
  obtain ⟨h1, h2, h3⟩ :=
    findZD_sound candidates candidates _ findZD_finds_witness
  exact ⟨zd_a, zd_b, h1, h2, h3⟩

end E213.Lib.Math.CayleyDickson.ZSqrtMinus2
