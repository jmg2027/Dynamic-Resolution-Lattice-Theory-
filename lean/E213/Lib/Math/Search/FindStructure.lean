/-!
# `findStructure` — universal 213-native search building block

Generic search algorithm with ∅-axiom soundness lemma.  All concrete
searchers (`findZD`, `findIsomorphism`, `findIdempotent`, ...) are
instances obtained by specializing `(D, pred, cands)`.

213-native: candidate sets are drawn from internal corpus, never
external classifications.

Implementation note: `List.find?` from Lean core uses `match`-style
reduction that pulls `propext` via `simp only`. We define a
hand-rolled `findIf` with explicit `if` so unfolding stays ∅-axiom.
-/

namespace E213.Lib.Math.Search

/-- Hand-rolled find — keeps unfolding ∅-axiom-clean (no `match`/`bif`). -/
def findIf {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | a :: l => if p a then some a else findIf p l

/-- Generic search: find first `d` in `cands` with `pred d data = true`. -/
def findStructure {D X : Type}
    (pred : D → X → Bool) (cands : List D) (data : X) : Option D :=
  findIf (fun d => pred d data) cands

theorem findIf_sound {α : Type} (p : α → Bool) :
    ∀ (l : List α) a, findIf p l = some a → p a = true := by
  intro l
  induction l with
  | nil => intro a h; cases h
  | cons head tail ih =>
    intro a h
    simp only [findIf] at h
    by_cases hp : p head = true
    · rw [if_pos hp] at h; cases h; exact hp
    · rw [if_neg hp] at h; exact ih a h

theorem findIf_mem {α : Type} (p : α → Bool) :
    ∀ (l : List α) a, findIf p l = some a → a ∈ l := by
  intro l
  induction l with
  | nil => intro a h; cases h
  | cons head tail ih =>
    intro a h
    simp only [findIf] at h
    by_cases hp : p head = true
    · rw [if_pos hp] at h; cases h; exact List.Mem.head _
    · rw [if_neg hp] at h; exact List.Mem.tail _ (ih a h)

/-- ∅-axiom soundness for the generic searcher. -/
theorem findStructure_sound {D X : Type}
    (pred : D → X → Bool) (cands : List D) (data : X) (d : D) :
    findStructure pred cands data = some d → pred d data = true :=
  findIf_sound (fun d' => pred d' data) cands d

/-- Membership corollary. -/
theorem findStructure_mem {D X : Type}
    (pred : D → X → Bool) (cands : List D) (data : X) (d : D) :
    findStructure pred cands data = some d → d ∈ cands :=
  findIf_mem (fun d' => pred d' data) cands d

end E213.Lib.Math.Search
