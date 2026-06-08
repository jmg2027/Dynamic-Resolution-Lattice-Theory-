import E213.Lib.Math.Algebra.Linalg213.Permutation
import E213.Meta.Tactic.List213

/-!
# Linalg213 — the symmetric-group operation on permutation value-lists

A permutation is carried as its value list `σ = [σ 0, σ 1, …]` (the `perms n` enumeration).  This
file gives that model its **group operation**: `composeList σ τ` realizes `(σ ∘ τ) i = σ (τ i)` by
`σ.getD (τ i) 0`.  The monoid laws — `iota n` is a two-sided identity (`composeList_iota_left/right`)
and composition is associative (`composeList_assoc`) — are proved by `getD`-extensionality
(`Meta.Tactic.List213.list_ext_getD`), with bound hypotheses (entries `< length`) in place of
`perms`-membership to keep the file independent of the enumeration's closure theory.

This is the substrate for the permutation **sign theory** (`psign(σ∘τ) = psign σ · psign τ`) toward
the transpose determinant `det Mᵀ = det M`.  All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.PermGroup

open E213.Lib.Math.Algebra.Linalg213.Permutation (iota)
open E213.Tactic.List213 (length_map getD_ge getD_map_ib list_ext_getD)

/-! ## §1 — `iota` indexing and length -/

/-- `map` over an append splits (clean, ∅-axiom). -/
theorem map_append' {α β : Type _} (f : α → β) : ∀ (L M : List α),
    (L ++ M).map f = L.map f ++ M.map f
  | [],     _ => rfl
  | a :: l, M => by show f a :: (l ++ M).map f = f a :: (l.map f ++ M.map f); rw [map_append' f l M]

/-- `iota (n+1) = 0 :: (iota n).map (·+1)` — peel from the front. -/
theorem iota_cons : ∀ (n : Nat), iota (n + 1) = 0 :: (iota n).map Nat.succ
  | 0     => rfl
  | n + 1 => by
    show iota (n + 1) ++ [n + 1] = 0 :: ((iota n ++ [n]).map Nat.succ)
    rw [iota_cons n, map_append' Nat.succ (iota n) [n]]
    rfl

/-- `|iota n| = n`. -/
theorem length_iota : ∀ n, (iota n).length = n
  | 0     => rfl
  | n + 1 => by
    rw [iota_cons n]
    show ((iota n).map Nat.succ).length + 1 = n + 1
    rw [length_map (iota n) Nat.succ, length_iota n]

/-- `(iota n).getD k 0 = k` for `k < n` — the identity permutation reads off its index. -/
theorem getD_iota : ∀ (n k : Nat), k < n → (iota n).getD k 0 = k
  | n + 1, 0,     _ => by rw [iota_cons n]; rfl
  | n + 1, k + 1, h => by
    rw [iota_cons n]
    show ((iota n).map Nat.succ).getD k 0 = k + 1
    rw [getD_map_ib Nat.succ 0 0 (iota n) k (by rw [length_iota]; exact Nat.lt_of_succ_lt_succ h),
        getD_iota n k (Nat.lt_of_succ_lt_succ h)]

/-! ## §2 — the composition operation and its `getD` law -/

/-- Composition of permutation value-lists: `(σ ∘ τ) i = σ (τ i)`, i.e. `σ.getD (τ i) 0`. -/
def composeList (σ τ : List Nat) : List Nat := τ.map (fun t => σ.getD t 0)

/-- `|σ ∘ τ| = |τ|`. -/
theorem composeList_length (σ τ : List Nat) : (composeList σ τ).length = τ.length :=
  length_map τ _

/-- The defining `getD` law: `(σ ∘ τ) i = σ (τ i)` in range. -/
theorem composeList_getD (σ τ : List Nat) (i : Nat) (hi : i < τ.length) :
    (composeList σ τ).getD i 0 = σ.getD (τ.getD i 0) 0 :=
  getD_map_ib (fun t => σ.getD t 0) 0 0 τ i hi

/-! ## §3 — the monoid laws (`iota n` identity, associativity) -/

/-- ★ **Left identity**: `iota n ∘ τ = τ` when every entry of `τ` is `< n`. -/
theorem composeList_iota_left (n : Nat) (τ : List Nat)
    (hτ : ∀ i, i < τ.length → τ.getD i 0 < n) : composeList (iota n) τ = τ := by
  refine list_ext_getD 0 (composeList_length (iota n) τ) (fun i => ?_)
  by_cases hi : i < τ.length
  · rw [composeList_getD (iota n) τ i hi, getD_iota n (τ.getD i 0) (hτ i hi)]
  · rw [getD_ge 0 (l := composeList (iota n) τ) (composeList_length (iota n) τ ▸ Nat.not_lt.mp hi),
        getD_ge 0 (Nat.not_lt.mp hi)]

/-- ★ **Right identity**: `σ ∘ iota n = σ` when `|σ| = n`. -/
theorem composeList_iota_right (n : Nat) (σ : List Nat) (hσ : σ.length = n) :
    composeList σ (iota n) = σ := by
  refine list_ext_getD 0 ((composeList_length σ (iota n)).trans (length_iota n |>.trans hσ.symm))
    (fun i => ?_)
  by_cases hi : i < n
  · rw [composeList_getD σ (iota n) i (by rw [length_iota]; exact hi), getD_iota n i hi]
  · rw [getD_ge 0 (l := composeList σ (iota n))
          (by rw [composeList_length, length_iota]; exact Nat.not_lt.mp hi),
        getD_ge 0 (hσ ▸ Nat.not_lt.mp hi)]

/-- ★ **Associativity**: `(σ ∘ τ) ∘ ρ = σ ∘ (τ ∘ ρ)` when every entry of `ρ` is `< |τ|`. -/
theorem composeList_assoc (σ τ ρ : List Nat) (hρ : ∀ i, i < ρ.length → ρ.getD i 0 < τ.length) :
    composeList (composeList σ τ) ρ = composeList σ (composeList τ ρ) := by
  refine list_ext_getD 0 ((composeList_length (composeList σ τ) ρ).trans
    (composeList_length σ (composeList τ ρ) |>.trans (composeList_length τ ρ)).symm) (fun i => ?_)
  by_cases hi : i < ρ.length
  · rw [composeList_getD (composeList σ τ) ρ i hi,
        composeList_getD σ τ (ρ.getD i 0) (hρ i hi),
        composeList_getD σ (composeList τ ρ) i (by rw [composeList_length]; exact hi),
        composeList_getD τ ρ i hi]
  · rw [getD_ge 0 (l := composeList (composeList σ τ) ρ)
          (by rw [composeList_length]; exact Nat.not_lt.mp hi),
        getD_ge 0 (l := composeList σ (composeList τ ρ))
          (by rw [composeList_length, composeList_length]; exact Nat.not_lt.mp hi)]

/-! ## §4 — the inverse permutation (`invPerm`) and the right-inverse law -/

/-- First position of `v` in a list (`|l|` if absent — never hit on a permutation). -/
def idxOf (v : Nat) : List Nat → Nat
  | []     => 0
  | a :: l => if a = v then 0 else idxOf v l + 1

/-- `getD` at the found position recovers the value (for `v ∈ σ`). -/
theorem idxOf_getD (v : Nat) : ∀ (σ : List Nat), v ∈ σ → σ.getD (idxOf v σ) 0 = v
  | a :: l, h => by
    by_cases hav : a = v
    · show (a :: l).getD (if a = v then 0 else idxOf v l + 1) 0 = v
      rw [if_pos hav]; exact hav
    · have hvl : v ∈ l := by
        cases h with
        | head => exact absurd rfl hav
        | tail _ h' => exact h'
      show (a :: l).getD (if a = v then 0 else idxOf v l + 1) 0 = v
      rw [if_neg hav]; exact idxOf_getD v l hvl

/-- The inverse permutation value-list: `(σ⁻¹) j = idxOf j σ`. -/
def invPerm (σ : List Nat) : List Nat := (iota σ.length).map (fun j => idxOf j σ)

/-- `|σ⁻¹| = |σ|`. -/
theorem invPerm_length (σ : List Nat) : (invPerm σ).length = σ.length := by
  show ((iota σ.length).map (fun j => idxOf j σ)).length = σ.length
  rw [length_map, length_iota]

/-- `(σ⁻¹) i = idxOf i σ` in range. -/
theorem invPerm_getD (σ : List Nat) (i : Nat) (hi : i < σ.length) :
    (invPerm σ).getD i 0 = idxOf i σ := by
  show ((iota σ.length).map (fun j => idxOf j σ)).getD i 0 = idxOf i σ
  rw [getD_map_ib (fun j => idxOf j σ) 0 0 (iota σ.length) i (by rw [length_iota]; exact hi),
      getD_iota σ.length i hi]

/-- ★★ **Right inverse**: `σ ∘ σ⁻¹ = iota n` (`n = |σ|`), when `σ` contains every value `< n`
    (true of any permutation of `iota n`).  Realizes the **group inverse** on the value-list model:
    every permutation has a two-sided inverse. -/
theorem composeList_invPerm_right (σ : List Nat) (hσ : ∀ j, j < σ.length → j ∈ σ) :
    composeList σ (invPerm σ) = iota σ.length := by
  refine list_ext_getD 0 ((composeList_length σ (invPerm σ)).trans
    ((invPerm_length σ).trans (length_iota σ.length).symm)) (fun i => ?_)
  by_cases hi : i < σ.length
  · rw [composeList_getD σ (invPerm σ) i (by rw [invPerm_length]; exact hi),
        invPerm_getD σ i hi, idxOf_getD i σ (hσ i hi), getD_iota σ.length i hi]
  · rw [getD_ge 0 (l := composeList σ (invPerm σ))
          (by rw [composeList_length, invPerm_length]; exact Nat.not_lt.mp hi),
        getD_ge 0 (l := iota σ.length) (by rw [length_iota]; exact Nat.not_lt.mp hi)]

/-- `getD` in range is a member. -/
theorem getD_mem : ∀ (σ : List Nat) (i : Nat), i < σ.length → σ.getD i 0 ∈ σ
  | a :: l, 0,     _ => List.Mem.head _
  | a :: l, k + 1, h => List.Mem.tail _ (getD_mem l k (Nat.lt_of_succ_lt_succ h))

/-- `idxOf v σ < |σ|` when `v ∈ σ`. -/
theorem idxOf_lt (v : Nat) : ∀ (σ : List Nat), v ∈ σ → idxOf v σ < σ.length
  | a :: l, h => by
    by_cases hav : a = v
    · show (if a = v then 0 else idxOf v l + 1) < (a :: l).length
      rw [if_pos hav]; exact Nat.succ_pos _
    · have hvl : v ∈ l := by
        cases h with
        | head => exact absurd rfl hav
        | tail _ h' => exact h'
      show (if a = v then 0 else idxOf v l + 1) < (a :: l).length
      rw [if_neg hav]; exact Nat.succ_lt_succ (idxOf_lt v l hvl)

/-- For a position-injective list (nodup), the first position of `σ i` is `i`. -/
theorem idxOf_getD_self (σ : List Nat)
    (hinj : ∀ i j, i < σ.length → j < σ.length → σ.getD i 0 = σ.getD j 0 → i = j)
    (i : Nat) (hi : i < σ.length) : idxOf (σ.getD i 0) σ = i := by
  have hmem : σ.getD i 0 ∈ σ := getD_mem σ i hi
  exact hinj _ i (idxOf_lt _ σ hmem) hi (idxOf_getD (σ.getD i 0) σ hmem)

/-- ★★ **Left inverse**: `σ⁻¹ ∘ σ = iota n`, for a position-injective `σ` (nodup) whose entries are
    `< |σ|`.  With `composeList_invPerm_right`, `invPerm σ` is a **two-sided inverse** — the
    value-list model of `iota n`-permutations is a group. -/
theorem composeList_invPerm_left (σ : List Nat)
    (hrange : ∀ i, i < σ.length → σ.getD i 0 < σ.length)
    (hinj : ∀ i j, i < σ.length → j < σ.length → σ.getD i 0 = σ.getD j 0 → i = j) :
    composeList (invPerm σ) σ = iota σ.length := by
  refine list_ext_getD 0 ((composeList_length (invPerm σ) σ).trans (length_iota σ.length).symm)
    (fun i => ?_)
  by_cases hi : i < σ.length
  · rw [composeList_getD (invPerm σ) σ i hi, invPerm_getD σ (σ.getD i 0) (hrange i hi),
        idxOf_getD_self σ hinj i hi, getD_iota σ.length i hi]
  · rw [getD_ge 0 (l := composeList (invPerm σ) σ)
          (by rw [composeList_length]; exact Nat.not_lt.mp hi),
        getD_ge 0 (l := iota σ.length) (by rw [length_iota]; exact Nat.not_lt.mp hi)]

end E213.Lib.Math.Algebra.Linalg213.PermGroup
