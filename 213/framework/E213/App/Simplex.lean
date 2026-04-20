import E213.OS.Atomicity

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

/-- **Easy direction:** block-constant ⟹ Aut-invariant.
    Any partition-preserving injection sends a block-pair class to
    itself, so a function factoring through `classify` is invariant. -/
theorem block_constant_implies_aut_invariant {α : Type}
    (W : Fin 5 → Fin 5 → α) (h : BlockConstant W) : AutInvariant W := by
  obtain ⟨f, hf⟩ := h
  intro σ hσ hinj i j
  rw [hf (σ i) (σ j), hf i j]
  -- classify (σ i) (σ j) = classify i j : partition is preserved and
  -- i = j ↔ σ i = σ j (by injectivity).
  have hi : isA (σ i) = isA i := hσ i
  have hj : isA (σ j) = isA j := hσ j
  have heq : (σ i = σ j) ↔ (i = j) :=
    ⟨fun h => hinj i j h, fun h => h ▸ rfl⟩
  simp [classify, hi, hj, heq]

end E213.App.Simplex
