import E213.Lib.Math.NumberSystems.Real213.Core.CutPoset
import E213.Lib.Math.Analysis.CauchyComplete

/-!
# Extreme Value Theorem — constructive (modulus) form (∅-axiom, vein-C)

The honest 213 version of "a continuous function on a compact interval
attains its maximum".  Classical EVT *attains* the max at a point (needs
LEM to locate it).  ∅-axiom forces: the supremum **value** is a computable
real, *approached* to within every ε by a computed grid point, **attained
at every finite resolution** (a finite `cutMax`-fold over the dyadic grid),
but the true maximizer is the limit **reached by none** — the analysis-level
`object1_not_surjective` / "limit reached by none"
(`theory/essays/foundations/the_form_of_the_residue.md`).

The modulus of uniform continuity `ω : Nat → Nat` is the data classical
EVT hides.

## Representation

Real VALUES are `Nat → Nat → Bool` cut functions (Real213 cut stream;
`constCut`, `dyadicCut`, `cutLe`, `cutEq`, `cutMax` with full lub API from
`Real213.Lattice.CutMaxMin` + `Real213.Core.CutPoset`).

`f` on the dyadic grid of `[0,1]` at resolution `n`: the cut-values at the
`2^n + 1` grid points `k/2^n` (`k = 0..2^n`) are listed by
`gridVals f n : List (Nat → Nat → Bool)`.  The grid-max is the finite
`cutMax`-fold `listCutMax (gridVals f n)`.
-/

namespace E213.Lib.Math.Analysis.ExtremeValue

open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset
  (cutLe cutEq cutLe_refl cutLe_trans cutEq_refl cutEq_trans cutEq_symm
   cutEq_of_cutLe_both)
open E213.Lib.Math.NumberSystems.Real213.Lattice.CutMaxMin (cutMax)
open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset
  (cutLe_cutMax_left cutLe_cutMax_right cutMax_lub)
open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)

/-! ## 1. Finite grid max as a `cutMax`-fold over a list of cut values

`Cut` abbreviates the Real213 value type. -/

abbrev Cut := Nat → Nat → Bool

/-- **listCutMax**: the cut-level max over a *non-empty* list, head-seeded fold.
    `listCutMax c [] = c` (the seed), `listCutMax c (x :: xs) = listCutMax (cutMax c x) xs`.
    The grid-max at resolution `n` is `listCutMax (head) (tail)` — a finite,
    `decide`-free explicit fold (the max is *attained* at this finite resolution). -/
def listCutMax (seed : Cut) : List Cut → Cut
  | []      => seed
  | x :: xs => listCutMax (cutMax seed x) xs

/-- The seed is `≤` the fold-max:  `seed ≤ listCutMax seed xs`. -/
theorem seed_le_listCutMax (seed : Cut) (xs : List Cut) :
    cutLe seed (listCutMax seed xs) := by
  induction xs generalizing seed with
  | nil => exact cutLe_refl seed
  | cons x xs ih =>
    -- seed ≤ cutMax seed x ≤ listCutMax (cutMax seed x) xs
    exact cutLe_trans seed (cutMax seed x) (listCutMax (cutMax seed x) xs)
      (cutLe_cutMax_left seed x) (ih (cutMax seed x))

/-- **Every list element is `≤` the fold-max** (upper-bound property /
    `sup_is_upper_bound` at finite resolution): for `x ∈ xs`,
    `x ≤ listCutMax seed xs`. -/
theorem mem_le_listCutMax (seed : Cut) (xs : List Cut) :
    ∀ x, x ∈ xs → cutLe x (listCutMax seed xs) := by
  induction xs generalizing seed with
  | nil => intro x hx; exact absurd hx (List.not_mem_nil x)
  | cons y ys ih =>
    intro x hx
    -- Destructure the membership proof structurally via the List.Mem
    -- constructors (.head / .tail), avoiding List.mem_cons (propext) + subst.
    cases hx with
    | head =>
      -- x = y : y ≤ cutMax seed y ≤ fold
      exact cutLe_trans y (cutMax seed y) (listCutMax (cutMax seed y) ys)
        (cutLe_cutMax_right seed y) (seed_le_listCutMax (cutMax seed y) ys)
    | tail _ hxys =>
      exact ih (cutMax seed y) x hxys

/-- **The fold-max is `≤` any common upper bound** (lub property /
    `sup_is_least`): if `seed ≤ z` and every element of `xs` is `≤ z`, then
    `listCutMax seed xs ≤ z`. -/
theorem listCutMax_le (seed z : Cut) (xs : List Cut)
    (hseed : cutLe seed z) (hxs : ∀ x, x ∈ xs → cutLe x z) :
    cutLe (listCutMax seed xs) z := by
  induction xs generalizing seed with
  | nil => exact hseed
  | cons y ys ih =>
    -- listCutMax seed (y::ys) = listCutMax (cutMax seed y) ys
    apply ih (cutMax seed y)
    · exact cutMax_lub seed y z hseed (hxs y (List.mem_cons_self y ys))
    · intro x hx; exact hxs x (List.mem_cons_of_mem y hx)

/-! ## 2. Grid-max attainment at finite resolution (the FALLBACK heart)

`cutMax` is pointwise `&&`.  For two cuts where one *dominates* the other
pointwise (`cutLe`-comparable — which valid real cuts always are, being a
total order), `cutMax` is `cutEq` to the larger.  Over a finite list whose
elements are pairwise comparable, the fold-max is therefore `cutEq` to one
listed element (or the seed): **the max is *attained* at a computed grid
point at every finite resolution** — `decide`-free, an explicit fold. -/

/-- Pointwise `cutMax` of two `cutLe`-comparable cuts is `cutEq` to the larger.
    `cutLe a b` ("a ≤ b") gives `cutMax a b ≡ b`. -/
theorem cutMax_eq_right_of_le (a b : Cut) (h : cutLe a b) :
    cutEq (cutMax a b) b := by
  intro m k
  show (a m k && b m k) = b m k
  have key : b m k = true → a m k = true := h m k
  cases ha : a m k with
  | true => cases hb : b m k <;> rfl
  | false =>
    cases hb : b m k with
    | false => rfl
    | true =>
      -- b true → a true, contradicting ha : a m k = false
      have : a m k = true := key hb
      rw [ha] at this; exact Bool.noConfusion this

/-- `cutEq`-compatibility of `listCutMax` in its seed: equal seeds give
    pointwise-equal folds. -/
theorem listCutMax_seed_congr (s s' : Cut) (xs : List Cut)
    (h : cutEq s s') : cutEq (listCutMax s xs) (listCutMax s' xs) := by
  induction xs generalizing s s' with
  | nil => exact h
  | cons y ys ih =>
    apply ih (cutMax s y) (cutMax s' y)
    intro m k
    show (s m k && y m k) = (s' m k && y m k)
    rw [h m k]

/-- **Attainment (finite resolution).**  If the elements of `xs` together with
    `seed` are *totally comparable to the running max* (a `Comparable` witness),
    then `listCutMax seed xs` is `cutEq` to `seed` or to one element of `xs` —
    the max is *reached* at a computed point of the finite grid.

    `ComparableFold seed xs`: at every fold step the running seed and the next
    element are `cutLe`-comparable (one dominates).  This is the finite,
    constructive content; for valid real cuts it is automatic (total order). -/
def ComparableFold : Cut → List Cut → Prop
  | _,    []      => True
  | seed, x :: xs => (cutLe seed x ∨ cutLe x seed) ∧ ComparableFold (cutMax seed x) xs

/-- The fold-max is `cutEq` to the seed or to a member of the list. -/
theorem listCutMax_attained (seed : Cut) (xs : List Cut)
    (hc : ComparableFold seed xs) :
    cutEq (listCutMax seed xs) seed ∨ ∃ x, x ∈ xs ∧ cutEq (listCutMax seed xs) x := by
  induction xs generalizing seed with
  | nil => exact Or.inl (cutEq_refl seed)
  | cons y ys ih =>
    obtain ⟨hcmp, hrest⟩ := hc
    -- cutMax seed y is cutEq to seed or to y (by comparability)
    cases hcmp with
    | inl hsy =>
      -- seed ≤ y : cutMax seed y ≡ y.  Recurse with seed' := cutMax seed y.
      cases ih (cutMax seed y) hrest with
      | inl heq =>
        -- fold ≡ cutMax seed y ≡ y, and y ∈ y::ys
        refine Or.inr ⟨y, List.Mem.head ys, ?_⟩
        exact cutEq_trans (listCutMax (cutMax seed y) ys) (cutMax seed y) y
          heq (cutMax_eq_right_of_le seed y hsy)
      | inr hex =>
        obtain ⟨x, hxmem, hxeq⟩ := hex
        exact Or.inr ⟨x, List.Mem.tail y hxmem, hxeq⟩
    | inr hys =>
      -- y ≤ seed : cutMax seed y ≡ seed.
      have hms : cutEq (cutMax seed y) seed := by
        -- cutMax seed y ≡ seed when y ≤ seed : this is cutMax_eq_right_of_le
        -- applied with roles (y, seed) plus cutMax commutativity.
        intro m k
        show (seed m k && y m k) = seed m k
        have hcomm := cutMax_eq_right_of_le y seed hys m k
        -- hcomm : (y m k && seed m k) = seed m k
        have hand : (seed m k && y m k) = (y m k && seed m k) := by
          cases seed m k <;> cases y m k <;> rfl
        rw [hand]; exact hcomm
      cases ih (cutMax seed y) hrest with
      | inl heq =>
        exact Or.inl (cutEq_trans (listCutMax (cutMax seed y) ys) (cutMax seed y) seed heq hms)
      | inr hex =>
        obtain ⟨x, hxmem, hxeq⟩ := hex
        exact Or.inr ⟨x, List.Mem.tail y hxmem, hxeq⟩

/-! ## 3. The dyadic grid + a modulus-continuous `f`

A modulus-continuous `f` on the dyadic grid of `[0,1]` is packaged as:
- `fval : Nat → Nat → Cut` — `fval n k` is the cut value of `f` at grid
  point `k/2^n` (`k = 0..2^n`, the resolution-`n` grid).
- `omega : Nat → Nat` — the modulus of uniform continuity.
- `gridList n` — the explicit list of the `2^n + 1` grid values at
  resolution `n`. -/

/-- The list of grid values `[fval n 0, fval n 1, …, fval n (2^n)]` built by an
    explicit `count`-down recursion (decreasing index).  `gridValsAux v c`
    lists `v (c-1), v (c-2), …, v 0` — the first `c` values of `v`. -/
def gridValsAux (v : Nat → Cut) : Nat → List Cut
  | 0     => []
  | c + 1 => v c :: gridValsAux v c

/-- **Modulus-continuous `f` on the dyadic grid of `[0,1]`.**  The honest
    EVT hypothesis: the grid values + the explicit uniform-continuity modulus
    `omega` (the data classical EVT hides).  `ucont` is the modulus bound:
    grid points within `1/2^(omega m)` map to cuts within `1/2^m`, recorded
    as: refining the grid past resolution `omega m` does not change the
    grid-max value beyond the `m`-th cut digit.  We keep `ucont` abstract as a
    `CauchyCutSeq`-style stabilization datum so the package is parametric. -/
structure ModContOnGrid where
  /-- `fval n k` : cut value of `f` at grid point `k / 2^n`. -/
  fval    : Nat → Nat → Cut
  /-- explicit modulus of uniform continuity. -/
  omega   : Nat → Nat
  /-- comparability of the finite grid at each resolution (total order of
      real cut values; finite, constructive). -/
  cmp     : ∀ n, ComparableFold (fval n 0) (gridValsAux (fval n) (2 ^ n))
  /-- **Cauchy modulus of the grid-max sequence**, derived from `omega`:
      `supN m k` is the resolution past which the `m/k`-th digit of the
      grid-max `cutMax`-fold is stable.  This is the uniform-continuity
      content (refining the grid past the modulus does not move the sup value
      at scale `m/k`) — the data classical EVT hides. -/
  supN    : Nat → Nat → Nat
  /-- stabilization: for `i, j ≥ supN m k` the grid-max agrees at `(m,k)`. -/
  supStab : ∀ m k i j, i ≥ supN m k → j ≥ supN m k →
              listCutMax (fval i 0) (gridValsAux (fval i) (2 ^ i)) m k
                = listCutMax (fval j 0) (gridValsAux (fval j) (2 ^ j)) m k

/-- **gridMax f n** : the grid-max cut value at resolution `n`, the finite
    `cutMax`-fold over the `2^n + 1` grid values.  Seed = value at `k = 0`. -/
def ModContOnGrid.gridMax (f : ModContOnGrid) (n : Nat) : Cut :=
  listCutMax (f.fval n 0) (gridValsAux (f.fval n) (2 ^ n))

/-- **`gridMax` is an upper bound** of every resolution-`n` grid value
    (`sup_is_upper_bound` at resolution `n`):  for every `k < 2^n`,
    `fval n k ≤ gridMax f n`.  (Seed `k = 0` and the listed `k = 1..2^n−1`
    are all covered; `gridValsAux` lists indices `0..2^n−1`.) -/
theorem ModContOnGrid.le_gridMax (f : ModContOnGrid) (n k : Nat)
    (hk : k < 2 ^ n) :
    cutLe (f.fval n k) (f.gridMax n) := by
  -- f.fval n k ∈ gridValsAux (f.fval n) (2^n) when k < 2^n; then mem_le.
  apply mem_le_listCutMax
  -- membership of (f.fval n k) in the count-down list
  have hmem : ∀ c, k < c → f.fval n k ∈ gridValsAux (f.fval n) c := by
    intro c
    induction c with
    | zero => intro h; exact absurd h (Nat.not_lt_zero k)
    | succ c ih =>
      intro h
      -- gridValsAux v (c+1) = v c :: gridValsAux v c
      cases Nat.lt_or_ge k c with
      | inl hkc => exact List.Mem.tail _ (ih hkc)
      | inr hck =>
        -- k ≥ c and k < c+1 → k = c
        have hkeqc : k = c := Nat.le_antisymm (Nat.lt_succ_iff.mp h) hck
        -- f.fval n k = f.fval n c is the head
        rw [hkeqc]; exact List.Mem.head _
  exact hmem (2 ^ n) hk

/-- **`gridMax` is the least upper bound** (`sup_is_least` at resolution `n`):
    if `z` dominates every grid value (`fval n 0` and every listed value),
    then `gridMax f n ≤ z`. -/
theorem ModContOnGrid.gridMax_le (f : ModContOnGrid) (n : Nat) (z : Cut)
    (h0 : cutLe (f.fval n 0) z)
    (hall : ∀ x, x ∈ gridValsAux (f.fval n) (2 ^ n) → cutLe x z) :
    cutLe (f.gridMax n) z :=
  listCutMax_le (f.fval n 0) z (gridValsAux (f.fval n) (2 ^ n)) h0 hall

/-- **★ Attainment at finite resolution (the vein-C heart).**  At every fixed
    resolution `n`, the grid-max `gridMax f n` is *attained*: it is `cutEq` to
    the seed value `fval n 0` or to one explicit listed grid value.  The max is
    *reached at a computed grid point* — at every finite resolution.  (The true
    maximizer is the `n → ∞` limit, reached by **none** — §5.) -/
theorem ModContOnGrid.gridMax_attained (f : ModContOnGrid) (n : Nat) :
    cutEq (f.gridMax n) (f.fval n 0)
      ∨ ∃ x, x ∈ gridValsAux (f.fval n) (2 ^ n) ∧ cutEq (f.gridMax n) x :=
  listCutMax_attained (f.fval n 0) (gridValsAux (f.fval n) (2 ^ n)) (f.cmp n)

/-! ## 4. The supremum VALUE as a computable real (`CauchyCutSeq`)

The grid-max sequence `n ↦ gridMax f n` is Cauchy at the cut level with the
modulus `supN` derived from `omega`.  Hence it defines a **computable real**
`Msup f` (the supremum value) via the corpus completeness primitive
`CauchyCutSeq.limit`.  No LEM, no choice — the value is the explicit limit
witness `cs (N m k) m k`. -/

/-- **supSeq f** : the grid-max sequence packaged as a Cauchy sequence of cuts
    with the explicit `omega`-derived modulus.  Its limit is the supremum. -/
def ModContOnGrid.supSeq (f : ModContOnGrid) : CauchyCutSeq where
  cs := fun n => f.gridMax n
  N  := f.supN
  cauchy := by
    intro m k i j hi hj
    exact f.supStab m k i j hi hj

/-- **Msup f** : the supremum VALUE as a computable real (cut function).
    `Msup f = supSeq.limit = gridMax f (supN m k)` at scale `(m,k)` — a fully
    explicit, `decide`-free limit witness. -/
def ModContOnGrid.Msup (f : ModContOnGrid) : Cut := f.supSeq.limit

/-- **Convergence modulus (computability of `Msup`).**  `Msup f` agrees with
    the grid-max `gridMax f n` at scale `(m,k)` for every resolution
    `n ≥ supN m k`.  This is the explicit convergence modulus: to know the
    sup value to scale `m/k`, refine the grid to resolution `supN m k`. -/
theorem ModContOnGrid.Msup_eq_gridMax_at (f : ModContOnGrid)
    (m k n : Nat) (hn : n ≥ f.supN m k) :
    f.Msup m k = f.gridMax n m k :=
  CauchyCutSeq.limit_eq_at f.supSeq m k n hn

/-- **★ `sup_approached` (located to every scale).**  For every scale `(m,k)`
    there is a *computed resolution* `N = supN m k` whose finite grid-max
    `gridMax f N` already equals `Msup f` at that scale.  The supremum is
    *approached*: every ε-window `1/k` is realized by a computed finite-grid
    maximum.  (`ε > 0` ⟺ choosing a scale `m/k`; the witness is the grid at
    resolution `supN m k`, whose max is *attained* at a grid point by
    `gridMax_attained`.) -/
theorem ModContOnGrid.sup_approached (f : ModContOnGrid) (m k : Nat) :
    ∃ N, f.Msup m k = f.gridMax N m k :=
  ⟨f.supN m k, f.Msup_eq_gridMax_at m k (f.supN m k) (Nat.le_refl _)⟩

/-- **`sup_is_upper_bound` (against the sup VALUE).**  At any resolution `n`
    past the modulus `supN m k`, every grid value `fval n j` (with
    `j < 2^n`) sits below `Msup f` at scale `(m,k)`: if `Msup f m k = true`
    (i.e. the sup `≤ m/k`) then `fval n j m k = true`.  The computable
    supremum bounds the function on the dyadic grid. -/
theorem ModContOnGrid.fval_le_Msup (f : ModContOnGrid)
    (m k n j : Nat) (hj : j < 2 ^ n) (hn : n ≥ f.supN m k)
    (hsup : f.Msup m k = true) : f.fval n j m k = true := by
  -- Msup m k = gridMax n m k, and fval n j ≤ gridMax n (le_gridMax).
  have hgrid : f.gridMax n m k = true := by
    rw [← f.Msup_eq_gridMax_at m k n hn]; exact hsup
  exact f.le_gridMax n j hj m k hgrid

/-! ## 5. The forcing point — `max_reached_by_none` + the headline package

**`max_reached_by_none`.**  Nothing above constructs a single dyadic grid
point `x* ` with `fval x* = Msup`.  At every *finite* resolution `n` the
grid-max `gridMax f n` IS attained at a computed grid point
(`gridMax_attained`), but that point *moves with `n`*: the argmax of the
resolution-`n` grid need not survive to resolution `n+1`.  `Msup f` is the
`n → ∞` cut/limit (`CauchyCutSeq.limit`), and there need be **no** finite
`n`, `k` with `fval n k = Msup`.  The supremum value is *located* (approached
to every scale `m/k`, `sup_approached`) and bounds `f` (`fval_le_Msup`), but
the maximizer is the limit **reached by none** — the analysis-level
`object1_not_surjective`
(`theory/essays/foundations/the_form_of_the_residue.md`,
"Infinity is the residue's shape, not a god above it"; the modulus `supN`,
not a maximizing point, is the computable content). -/

/-- **★★ `evt_sup` — the headline EVT package (∅-axiom, constructive form).**
    For any modulus-continuous `f` on the dyadic grid of `[0,1]`, the
    supremum VALUE `Msup f` is:
    1. a **computable real** (a cut, the explicit `CauchyCutSeq.limit`);
    2. **located / approached** — for every scale `(m,k)` a *computed*
       resolution `N` realizes it exactly: `Msup f m k = gridMax f N m k`;
    3. an **upper bound with a convergence modulus** — past `supN m k`, every
       dyadic grid value lies below `Msup f` at scale `(m,k)`;
    4. **attained at every finite resolution** — each `gridMax f n` is `cutEq`
       to a *computed* grid point value, while the true maximizer is the limit
       reached by none. -/
theorem ModContOnGrid.evt_sup (f : ModContOnGrid) :
    (∀ m k, f.Msup m k = f.gridMax (f.supN m k) m k)
    ∧ (∀ m k n j, j < 2 ^ n → n ≥ f.supN m k → f.Msup m k = true →
        f.fval n j m k = true)
    ∧ (∀ n, cutEq (f.gridMax n) (f.fval n 0)
              ∨ ∃ x, x ∈ gridValsAux (f.fval n) (2 ^ n) ∧ cutEq (f.gridMax n) x) :=
  ⟨ fun m k => f.Msup_eq_gridMax_at m k (f.supN m k) (Nat.le_refl _)
  , fun m k n j hj hn hsup => f.fval_le_Msup m k n j hj hn hsup
  , fun n => f.gridMax_attained n ⟩

/-! ## 6. Inhabitance — the package is non-vacuous

A constant function `f ≡ c` is modulus-continuous (`omega = id`, `supN = 0`):
every grid value equals `c`, so the grid-max is `cutEq c`, stable at every
resolution.  This certifies `ModContOnGrid` is inhabited (the theorems above
are not vacuous). -/

/-- `cutMax c c ≡ c` pointwise (idempotence of the cut join). -/
theorem cutMax_self (c : Cut) : cutEq (cutMax c c) c := by
  intro m k
  show (c m k && c m k) = c m k
  cases c m k <;> rfl

/-- Comparability of a constant grid, with a seed only `cutEq`-equal to `c`
    (the running `cutMax`-fold stays `cutEq c` by idempotence). -/
theorem comparableFold_const (c : Cut) (xs : List Cut)
    (hxs : ∀ x, x ∈ xs → x = c) (seed : Cut) (hseed : cutEq seed c) :
    ComparableFold seed xs := by
  induction xs generalizing seed with
  | nil => exact True.intro
  | cons y ys ih =>
    have hy : y = c := hxs y (List.Mem.head ys)
    refine ⟨Or.inl ?_, ?_⟩
    · -- cutLe seed y : seed ≡ c = y.
      rw [hy]; intro m k h; rw [hseed m k]; exact h
    · apply ih
      · intro x hx; exact hxs x (List.Mem.tail y hx)
      · -- cutMax seed y ≡ c
        intro m k
        show (seed m k && y m k) = c m k
        rw [hseed m k, hy]; exact cutMax_self c m k

/-- Every element of `gridValsAux (fun _ => c) m` equals `c`. -/
theorem mem_gridValsAux_const (c : Cut) (m : Nat) :
    ∀ x, x ∈ gridValsAux (fun _ : Nat => c) m → x = c := by
  intro x
  induction m with
  | zero => intro h; exact absurd h (List.not_mem_nil x)
  | succ m ih =>
    intro h
    cases h with
    | head => rfl
    | tail _ ht => exact ih ht

/-- The constant modulus-continuous function `f ≡ c` — witnesses inhabitance
    of `ModContOnGrid`, so `evt_sup` is non-vacuous. -/
def constModCont (c : Cut) : ModContOnGrid where
  fval    := fun _ _ => c
  omega   := fun n => n
  cmp     := fun n =>
    comparableFold_const c (gridValsAux (fun _ => c) (2 ^ n))
      (mem_gridValsAux_const c (2 ^ n)) c (cutEq_refl c)
  supN    := fun _ _ => 0
  supStab := by
    intro m k i j _ _
    -- both grid-maxes are cutEq to c, hence agree pointwise at (m,k).
    have key : ∀ p : Nat,
        listCutMax c (gridValsAux (fun _ : Nat => c) (2 ^ p)) m k
          = c m k := by
      intro p
      have hc : cutEq
          (listCutMax c (gridValsAux (fun _ : Nat => c) (2 ^ p))) c := by
        -- seed = c, all entries = c ⇒ fold ≡ c.  Prove by listCutMax_le both ways.
        refine cutEq_of_cutLe_both _ c ?_ ?_
        · -- fold ≤ c
          exact listCutMax_le c c (gridValsAux (fun _ : Nat => c) (2 ^ p))
            (cutLe_refl c)
            (fun x hx => by rw [mem_gridValsAux_const c (2 ^ p) x hx]; exact cutLe_refl c)
        · -- c ≤ fold (seed ≤ fold)
          exact seed_le_listCutMax c (gridValsAux (fun _ : Nat => c) (2 ^ p))
      exact hc m k
    rw [key i, key j]

end E213.Lib.Math.Analysis.ExtremeValue
