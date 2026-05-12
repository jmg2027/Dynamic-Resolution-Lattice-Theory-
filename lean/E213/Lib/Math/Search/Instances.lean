import E213.Lib.Math.Search.FindStructure

/-!
# Instances of `findStructure`

Each algorithm = one specialization of `findStructure` with specific
`(D, pred, cands)`.  Soundness is automatic via `findStructure_sound`.

Instances:
  * `findCounterexample` — find (a, b) ∈ xs×ys with `prop a b = true`
  * `findIdempotent`     — find `a*a = a`, `a ∉ {0, 1}` in xs

All ∅-axiom by construction.
-/

namespace E213.Lib.Math.Search

/-- ∅-axiom Bool destructor (inlined to avoid cross-tier import). -/
private theorem and_eq_true_pair : ∀ {a b : Bool},
    (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | false, _, h => by cases h
  | true, false, h => by cases h

/-- Find first `(a, b) ∈ xs × ys` with `prop a b = true`. -/
def findCounterexample {α β : Type}
    (prop : α → β → Bool) (xs : List α) (ys : List β) : Option (α × β) :=
  findStructure (fun (p : α × β) (_ : Unit) => prop p.1 p.2)
    (xs.flatMap (fun a => ys.map (Prod.mk a))) ()

theorem findCounterexample_sound {α β : Type}
    (prop : α → β → Bool) (xs : List α) (ys : List β) (p : α × β) :
    findCounterexample prop xs ys = some p → prop p.1 p.2 = true :=
  fun h => findStructure_sound _ _ _ p h

/-- Find first `a ∈ xs` with `a*a = a`, `a ≠ zero`, `a ≠ one`. -/
def findIdempotent {α : Type} [DecidableEq α]
    (mul : α → α → α) (zero one : α) (xs : List α) : Option α :=
  findStructure (fun (a : α) (_ : Unit) =>
    decide (mul a a = a) && decide (a ≠ zero) && decide (a ≠ one)) xs ()

theorem findIdempotent_sound {α : Type} [DecidableEq α]
    (mul : α → α → α) (zero one : α) (xs : List α) (a : α) :
    findIdempotent mul zero one xs = some a →
    mul a a = a ∧ a ≠ zero ∧ a ≠ one := by
  intro h
  have hp := findStructure_sound _ _ _ a h
  have ⟨h12, h3⟩ := and_eq_true_pair hp
  have ⟨h1, h2⟩ := and_eq_true_pair h12
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3⟩

end E213.Lib.Math.Search
