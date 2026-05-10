import E213.Theory.Atomicity.Five
import E213.Theory.Atomicity.PairForcing

/-!
# 4-simplex structure: 5 vertices, (3,2) partition, Aut-invariant weights

From `Atomic 5` (Atomicity) + `canonical_partition` (a=b=1, i.e.
one 3-atom + one 2-atom), the vertex set is `Fin 5` with the canonical
partition `V_A = {0, 1, 2}, V_B = {3, 4}`.

We formalize the partition, block-pair classification, and the
statement that an `Aut_atom = S_3 × S_2`-invariant weight function on
`Fin 5 × Fin 5` is exactly one that factors through the block-pair
classifier. Full bidirectional equivalence requires a generating
transposition argument; we provide the setup + the easy direction
here.
-/

namespace E213.App.Simplex

/-- The (3, 2) partition: V_A = {0, 1, 2}, V_B = {3, 4}. -/
def isA (i : Fin 5) : Bool := i.val < 3

/-- Fine block-pair classifier (6 equivalence classes under S_3 × S_2
    diagonal action). Counts: 3 + 6 + 6 + 6 + 2 + 2 = 25 = d². -/
inductive BlockPair
  | AAdiag | AAoff | AB | BA | BBdiag | BBoff
  deriving DecidableEq, Repr

/-- Classify a pair (i, j) ∈ Fin 5² into its block-pair class. -/
def classify (i j : Fin 5) : BlockPair :=
  match isA i, isA j with
  | true,  true  => if i = j then .AAdiag else .AAoff
  | true,  false => .AB
  | false, true  => .BA
  | false, false => if i = j then .BBdiag else .BBoff

/-- A permutation of `Fin 5` preserves the (3, 2) partition. -/
def PreservesPartition (σ : Fin 5 → Fin 5) : Prop :=
  ∀ i : Fin 5, isA (σ i) = isA i

/-- W is invariant under diagonally-applied partition-preserving
    permutations. (This encodes `S_3 × S_2` action; bijectivity is
    automatic for `Fin 5` injections preserving cardinalities, left
    implicit here.) -/
def AutInvariant {α : Type} (W : Fin 5 → Fin 5 → α) : Prop :=
  ∀ σ : Fin 5 → Fin 5, PreservesPartition σ →
    (∀ x y, σ x = σ y → x = y) →
    ∀ i j, W (σ i) (σ j) = W i j

/-- W is block-constant: determined by the `BlockPair` class. -/
def BlockConstant {α : Type} (W : Fin 5 → Fin 5 → α) : Prop :=
  ∃ f : BlockPair → α, ∀ i j, W i j = f (classify i j)

/-- classify is invariant under partition-preserving injections:
    classify (σ i) (σ j) = classify i j.  Proved by case analysis on
    the four (isA i, isA j) cases and decidable Fin equality, avoiding
    the propext leak of `simp [Iff_hyp]`. -/
private theorem classify_aut_inv (σ : Fin 5 → Fin 5)
    (hσ : PreservesPartition σ) (hinj : ∀ x y, σ x = σ y → x = y)
    (i j : Fin 5) : classify (σ i) (σ j) = classify i j := by
  unfold classify
  rw [hσ i, hσ j]
  cases isA i <;> cases isA j <;> simp only []
  all_goals {
    match h : decide (i = j) with
    | true =>
        have heq : i = j := of_decide_eq_true h
        have hσeq : σ i = σ j := by rw [heq]
        rw [if_pos hσeq, if_pos heq]
    | false =>
        have hne : i ≠ j := of_decide_eq_false h
        have hσne : σ i ≠ σ j := fun he => hne (hinj _ _ he)
        rw [if_neg hσne, if_neg hne]
  }

/-- **Easy direction:** block-constant ⟹ Aut-invariant.
    Any partition-preserving injection sends a block-pair class to
    itself, so a function factoring through `classify` is invariant. -/
theorem block_constant_implies_aut_invariant {α : Type}
    (W : Fin 5 → Fin 5 → α) (h : BlockConstant W) : AutInvariant W := by
  obtain ⟨f, hf⟩ := h
  intro σ hσ hinj i j
  rw [hf (σ i) (σ j), hf i j, classify_aut_inv σ hσ hinj i j]

end E213.App.Simplex
