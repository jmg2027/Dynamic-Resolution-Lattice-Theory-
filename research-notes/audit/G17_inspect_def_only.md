# Cluster def_only — 1369 decls (sample 50)

## \`isA\` (E213/App/Simplex.lean)

```lean
def isA (i : Fin 5) : Bool := i.val < 3

/-- Fine block-pair classifier (6 equivalence classes under S_3 × S_2
    diagonal action). Counts: 3 + 6 + 6 + 6 + 2 + 2 = 25 = d². -/
inductive BlockPair
  | AAdiag | AAoff | AB | BA | BBdiag | BBoff
  deriving DecidableEq, Repr

/-- Classify a pair (i, j) ∈ Fin 5² into its block-pair class. -/
```

## \`classify\` (E213/App/Simplex.lean)

```lean
def classify (i j : Fin 5) : BlockPair :=
  match isA i, isA j with
  | true,  true  => if i = j then .AAdiag else .AAoff
  | true,  false => .AB
  | false, true  => .BA
  | false, false => if i = j then .BBdiag else .BBoff

/-- A permutation of `Fin 5` preserves the (3, 2) partition. -/
```

## \`PreservesPartition\` (E213/App/Simplex.lean)

```lean
def PreservesPartition (σ : Fin 5 → Fin 5) : Prop :=
  ∀ i : Fin 5, isA (σ i) = isA i

/-- W is invariant under diagonally-applied partition-preserving
    permutations. (This encodes `S_3 × S_2` action; bijectivity is
    automatic for `Fin 5` injections preserving cardinalities, left
    implicit here.) -/
```

## \`AutInvariant\` (E213/App/Simplex.lean)

```lean
def AutInvariant {α : Type} (W : Fin 5 → Fin 5 → α) : Prop :=
  ∀ σ : Fin 5 → Fin 5, PreservesPartition σ →
    (∀ x y, σ x = σ y → x = y) →
    ∀ i j, W (σ i) (σ j) = W i j

/-- W is block-constant: determined by the `BlockPair` class. -/
```

## \`residue\` (E213/Firmware/Atomicity/Alive.lean)

```lean
def residue (a : Nat) : Nat := a % 2

/-- A multiplicity *survives* iff its residue is 1 (odd). -/
```

## \`Survives\` (E213/Firmware/Atomicity/Alive.lean)

```lean
def Survives (a : Nat) : Prop := residue a = 1
```

## \`BothSurvive\` (E213/Firmware/Atomicity/Alive.lean)

```lean
def BothSurvive (a b : Nat) : Prop := Survives a ∧ Survives b
```

## \`isBase\` (E213/Firmware/Atomicity/ArityForcingGeneral.lean)

```lean
def isBase {N k : Nat} : RawNk N k → Bool
  | .object _ => true
  | .rel _    => false

/-- Constructive index extraction.  `Classical.choice`-free analogue
    of `Exists.choose`: given `h : isBase x = true`, returns the
    `Fin N` witness by structural pattern match. -/
```

## \`getBase\` (E213/Firmware/Atomicity/ArityForcingGeneral.lean)

```lean
def getBase {N k : Nat} : (x : RawNk N k) → isBase x = true → Fin N
  | .object i, _ => i
  | .rel _,    h => by cases h

/-- The witness recovered by `getBase` indeed makes `x = .object _`. -/
```

## \`Decomp\` (E213/Firmware/Atomicity/Five.lean)

```lean
def Decomp (n a b : Nat) : Prop := n = 2 * a + 3 * b

/-- Alive: both parts odd (survive swap annihilation).
    213-native via cohomological parity (Nat213.parity) — direct
    step-2 recursion, ∅-axiom, vs. Lean's well-founded `% 2`
    which brings propext through `Nat.add_mod_right` etc. -/
```

## \`IsAlive\` (E213/Firmware/Atomicity/Five.lean)

```lean
def IsAlive (a b : Nat) : Prop := parity a = true ∧ parity b = true

/-- n is atomic: has a unique decomposition, and it is alive. -/
```

## \`Atomic\` (E213/Firmware/Atomicity/Five.lean)

```lean
def Atomic (n : Nat) : Prop :=
  ∃ a b, Decomp n a b ∧ IsAlive a b ∧
         ∀ a' b', Decomp n a' b' → a' = a ∧ b' = b

/-- 213-native: `2 * a = 5 → False` via case analysis on `a`. -/
private theorem two_mul_ne_five (a : Nat) (h : 2 * a = 5) : False :=
  match Nat.lt_or_ge a 3 with
  | Or.inl hlt =>
    match cases_lt_three hlt with
    | Or.inl h0 => absurd (h0 ▸ h) (by decide)
    | Or.inr (Or.inl h1) => absurd (h1 ▸ h) (by decide)
    | Or.inr (Or.inr h2) => absurd (h2 ▸ h) (by decide)
  | Or.inr hge =>
    have : 6 ≤ 2 * a := Nat.mul_le_mul_left 2 hge
    absurd (h ▸ this) (by decide)

/
... [truncated]
```

## \`Decomposable\` (E213/Firmware/Atomicity/NonDecomposable.lean)

```lean
def Decomposable (n : Nat) : Prop :=
  ∃ a b : Nat, a ≥ 2 ∧ b ≥ 2 ∧ a + b = n

/-- Non-decomposable and `≥ 2` (the "atoms"). -/
```

## \`NonDecomposable\` (E213/Firmware/Atomicity/NonDecomposable.lean)

```lean
def NonDecomposable (n : Nat) : Prop :=
  n ≥ 2 ∧ ¬ Decomposable n

private theorem two_or_three_of_lt_four {n : Nat}
    (h2 : 2 ≤ n) (h4 : n < 4) : n = 2 ∨ n = 3 :=
  match Nat.lt_or_ge n 3 with
  | Or.inl hlt3 =>
    Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ hlt3) h2)
  | Or.inr hge3 =>
    Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ h4) hge3)

private theorem n_sub_two_ge_two_of_ge_four {n : Nat} (h : 4 ≤ n) : 2 ≤ n - 2 :=
  le_sub_of_add_le h

private theorem two_plus_n_sub_two_eq {n : Nat} (h : 2 ≤ n) : 2 + (n - 2) = n :=
  add_sub_of_le h

private theorem add_ge_four_of_each_ge_two {a b
... [truncated]
```

## \`Decomp\` (E213/Firmware/Atomicity/PairForcing.lean)

```lean
def Decomp (p q n a b : Nat) : Prop := n = p * a + q * b

/-- Alive: both parts odd (positive).  213-native via cohomological
    parity (Mod213.parity) — matches Five.IsAlive. -/
```

## \`IsAlive\` (E213/Firmware/Atomicity/PairForcing.lean)

```lean
def IsAlive (a b : Nat) : Prop :=
  E213.Tactic.Mod213.parity a = true ∧ E213.Tactic.Mod213.parity b = true

/-- n is atomic under atom pair (p, q): unique decomp AND alive. -/
```

## \`Atomic\` (E213/Firmware/Atomicity/PairForcing.lean)

```lean
def Atomic (p q n : Nat) : Prop :=
  ∃ a b, Decomp p q n a b ∧ IsAlive a b ∧
         ∀ a' b', Decomp p q n a' b' → a' = a ∧ b' = b

/-- Count of atomic candidate pairs (a, b):
    a odd positive, a < q; b odd positive, b < p.
    Equals ⌊p/2⌋ · ⌊q/2⌋. -/
```

## \`count\` (E213/Firmware/Atomicity/PairForcing.lean)

```lean
def count (p q : Nat) : Nat := (p / 2) * (q / 2)

-- Sanity checks.
example : count 2 3 = 1 := rfl
example : count 3 5 = 2 := rfl
example : count 4 5 = 4 := rfl
example : count 5 7 = 6 := rfl
```

## \`pairSize\` (E213/Firmware/Atomicity/PrimitiveSizes.lean)

```lean
def pairSize : Nat := 2

/-- The first closure: the pair plus their relation. Named by the axiom. -/
```

## \`closureSize\` (E213/Firmware/Atomicity/PrimitiveSizes.lean)

```lean
def closureSize : Nat := 3

/-- The input pair size is non-decomposable. -/
```

## \`cmpRev\` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
def cmpRev (cmp : Tree → Tree → Ordering) (x y : Tree) : Ordering :=
  (cmp x y).swap
```

## \`canonicalBy\` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
def canonicalBy (cmp : Tree → Tree → Ordering) : Tree → Bool
  | .a => true
  | .b => true
  | .slash x y =>
      canonicalBy cmp x && canonicalBy cmp y &&
      (match cmp x y with | .lt => true | _ => false)

/-- **RawBy cmp**: subtype of cmp-canonical Trees. -/
```

## \`RawBy\` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
def RawBy (cmp : Tree → Tree → Ordering) : Type :=
  { t : Tree // canonicalBy cmp t = true }

/-- When using the original Tree.cmp, canonicalBy = Tree.canonical. -/
```

## \`slashTree\` (E213/Firmware/Raw/CmpIndependence.lean)

```lean
def slashTree (cmp : Tree → Tree → Ordering) (x y : Tree) : Tree :=
  match cmp x y with
  | .lt => .slash x y
  | .gt => .slash y x
  | .eq => .slash x y

/-- slashTree is commutative (using only CmpProps). -/
```

## \`constSeq\` (E213/Firmware/Raw/ComplexityClass.lean)

```lean
def constSeq (r : Raw) : Nat → Raw := fun _ => r

/-- Constant sequence is a 1-state FSM. -/
```

## \`altState\` (E213/Firmware/Raw/ComplexityClass.lean)

```lean
def altState : Nat → Bool
  | 0 => true
  | n + 1 => !altState n

/-- Alternating Raw sequence: a, b, a, b, .... -/
```

## \`altSeq\` (E213/Firmware/Raw/ComplexityClass.lean)

```lean
def altSeq (n : Nat) : Raw := if altState n then Raw.a else Raw.b

/-- Bool → Fin 2 (pattern match for definitional unfolding). -/
```

## \`boolToFin2\` (E213/Firmware/Raw/ComplexityClass.lean)

```lean
def boolToFin2 : Bool → Fin 2
  | true => ⟨0, Nat.zero_lt_succ _⟩
  | false => ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩

/-- Fin 2 → Bool (pattern match). -/
```

## \`Tree\` (E213/Firmware/Raw/Core.lean)

```lean
def Tree.cmp : Tree → Tree → Ordering
  | .a,         .a         => .eq
  | .a,         .b         => .lt
  | .a,         .slash _ _ => .lt
  | .b,         .a         => .gt
  | .b,         .b         => .eq
  | .b,         .slash _ _ => .lt
  | .slash _ _, .a         => .gt
  | .slash _ _, .b         => .gt
  | .slash x₁ y₁, .slash x₂ y₂ =>
      match Tree.cmp x₁ x₂ with
      | .eq => Tree.cmp y₁ y₂
      | .lt => .lt
      | .gt => .gt
```

## \`Raw\` (E213/Firmware/Raw/Core.lean)

```lean
def Raw : Type := { t : Tree // t.canonical = true }
```

## \`Tree\` (E213/Firmware/Raw/Fold.lean)

```lean
def Tree.fold {α : Type}
    (fa fb : α) (fc : α → α → α) : Tree → α
  | .a         => fa
  | .b         => fb
  | .slash x y => fc (Tree.fold fa fb fc x) (Tree.fold fa fb fc y)
```

## \`Raw\` (E213/Firmware/Raw/Fold.lean)

```lean
def Raw.fold {α : Type}
    (base_a : α) (base_b : α) (combine : α → α → α)
    (r : Raw) : α :=
  Tree.fold base_a base_b combine r.val

example : Raw.fold (0 : Nat) 1 (· + ·) Raw.a = 0 := rfl
example : Raw.fold (0 : Nat) 1 (· + ·) Raw.b = 1 := rfl
```

## \`Tree\` (E213/Firmware/Raw/Levels.lean)

```lean
theorem Tree.swap_depth :
    ∀ t : Tree, t.canonical = true → (Tree.swap t).depth = t.depth := by
  intro t h
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      have hc := h
      simp only [Tree.canonical, Bool.and_eq_true] at hc
      obtain ⟨⟨hx, hy⟩, _⟩ := hc
      have hlt := Tree.canonical_slash_lt h
      have ihx' := ihx hx
      have ihy' := ihy hy
      simp only [Tree.swap]
      split <;> rename_i hcmp
      · simp only [Tree.depth, ihx', ihy']
      · simp only [Tree.depth, ihx', ihy', Nat.max_comm]
      · exact (Tree.swap_eq_unreach hx hy hlt hcmp).elim
```

## \`Raw\` (E213/Firmware/Raw/Levels.lean)

```lean
theorem Raw.swap_depth (r : Raw) : (Raw.swap r).depth = r.depth :=
  Tree.swap_depth r.val r.property
```

## \`Raw\` (E213/Firmware/Raw/Rec.lean)

```lean
noncomputable def Raw.recAux {motive : Raw → Sort u}
    (a : motive Raw.a)
    (b : motive Raw.b)
    (slash : ∀ (x y : Raw) (h : x ≠ y),
                  motive x → motive y →
                  motive (Raw.slash x y h)) :
    ∀ (t : Tree) (hcanon : t.canonical = true), motive ⟨t, hcanon⟩ := by
  intro t
  induction t with
  | a => intro _; exact a
  | b => intro _; exact b
  | slash x y ihx ihy =>
      intro hcanon
      have hc := hcanon
      unfold Tree.canonical at hc
      obtain ⟨hxy, _⟩ := Bool.and_eq_true_to_pair hc
      obtain ⟨hx, hy⟩ := Bool.and_eq_true_to_pair hxy
      have h
... [truncated]
```

## \`Raw\` (E213/Firmware/Raw/Slash.lean)

```lean
def Raw.slash (x y : Raw) (h : x ≠ y) : Raw :=
  match hc : Tree.cmp x.val y.val with
  | .lt => ⟨.slash x.val y.val, by
            unfold Tree.canonical
            rw [x.property, y.property, hc]; rfl⟩
  | .gt => ⟨.slash y.val x.val, by
            have hlt : Tree.cmp y.val x.val = .lt :=
              Tree.cmp_gt_to_lt_swap x.val y.val hc
            unfold Tree.canonical
            rw [y.property, x.property, hlt]; rfl⟩
  | .eq => absurd (Tree.cmp_eq_to_eq _ _ hc)
            (fun e => h (Subtype.ext e))
```

## \`Tree\` (E213/Firmware/Raw/Slash.lean)

```lean
def Tree.depth : Tree → Nat
  | .a         => 0
  | .b         => 0
  | .slash x y => 1 + max x.depth y.depth
```

## \`Tree\` (E213/Firmware/Raw/Swap.lean)

```lean
def Tree.swap : Tree → Tree
  | .a         => .b
  | .b         => .a
  | .slash x y =>
      let x' := Tree.swap x
      let y' := Tree.swap y
      match Tree.cmp x' y' with
      | .lt => .slash x' y'
      | .gt => .slash y' x'
      | .eq => x'
```

## \`Raw\` (E213/Firmware/Raw/Swap.lean)

```lean
def Raw.swap (r : Raw) : Raw :=
  ⟨Tree.swap r.val, Tree.swap_canonical r.val r.property⟩
```

## \`Raw\` (E213/Firmware/RawLevels.lean)

```lean
def Raw.level1_set : List Raw :=
  [Raw.a, Raw.b, Raw.slash Raw.a Raw.b (by decide)]

/-- Level-2 additions: the Raw terms `a/(a/b)`, `b/(a/b)`. -/
```

## \`pointwiseEq\` (E213/Hypervisor/Lens/AxiomLenses/Core/Funext.lean)

```lean
def pointwiseEq {α β : Type} (f g : α → β) : Prop :=
  ∀ x, f x = g x
```

## \`iffEquiv\` (E213/Hypervisor/Lens/AxiomLenses/Core/Propext.lean)

```lean
def iffEquiv (P Q : Prop) : Prop := P ↔ Q
```

## \`view\` (E213/Hypervisor/Lens/AxiomLenses/Core/Propext.lean)

```lean
def view (P : Prop) : Prop := P

/-- The lens kernel = iffEquiv. -/
```

## \`quotient\` (E213/Hypervisor/Lens/AxiomLenses/Core/QuotSound.lean)

```lean
def quotient {α : Type} (s : SetoidLens α) : Type := Quot s.rel

/-- The "view" projecting α onto its equivalence class. -/
```

## \`project\` (E213/Hypervisor/Lens/AxiomLenses/Core/QuotSound.lean)

```lean
def project {α : Type} (s : SetoidLens α) (a : α) : quotient s :=
  Quot.mk s.rel a
```

## \`signedLens\` (E213/Hypervisor/Lens/Characterisation/Catalog.lean)

```lean
def signedLens : Hypervisor.Lens Int where
  base_a  := 1
  base_b  := -1
  combine := (· + ·)

/-- Swap acts as negation on the image of the signed Lens. -/
```

## \`NonVanishing\` (E213/Hypervisor/Lens/Characterisation/Catalog.lean)

```lean
def NonVanishing {α : Type} [Zero α] (L : Hypervisor.Lens α) : Prop :=
  ∀ u v : α, u ≠ 0 → v ≠ 0 → L.combine u v ≠ 0

/-- **R4 — Swap matches exactly one nontrivial involution.**  On
    the codomain `α` there is a function `conj : α → α` such that
    `conj` is an involution, `conj ≠ id`, and `view (swap r) = conj (view r)`
    for every `r`. Uniqueness (at most one such `conj`) is a
    separate condition on injective Lenses. -/
```

## \`SwapMatching\` (E213/Hypervisor/Lens/Characterisation/Catalog.lean)

```lean
def SwapMatching {α : Type} (L : Hypervisor.Lens α) (conj : α → α) : Prop :=
  (∀ u, conj (conj u) = u) ∧
  conj ≠ id ∧
  (∀ r : Raw, L.view (Raw.swap r) = conj (L.view r))

/-- **R5 — Distinguishing.**  Different Raw terms have different
    images; equivalently, `L.view` is injective.  The continuity /
    minimality clause of R5 (the image is the smallest connected
    ℝ-algebra on which this is possible) is not expressible in
    Lean 4 core; we record the injectivity half and treat the
    minimality identification (→ ℝ) at the prose level. -/
```

## \`Distinguishing\` (E213/Hypervisor/Lens/Characterisation/Catalog.lean)

```lean
def Distinguishing {α : Type} (L : Hypervisor.Lens α) : Prop :=
  Function.Injective L.view
```

## \`IsLensMorphism\` (E213/Hypervisor/Lens/Compose/Morphism.lean)

```lean
def IsLensMorphism {α β : Type} (h : α → β) (L : Lens α) (M : Lens β) :
    Prop :=
  h L.base_a = M.base_a ∧
  h L.base_b = M.base_b ∧
  ∀ u v : α, h (L.combine u v) = M.combine (h u) (h v)

/-- **Factoring through morphism**: if h is a Lens morphism then
    `M.view r = h (L.view r)` for all r. -/
```
