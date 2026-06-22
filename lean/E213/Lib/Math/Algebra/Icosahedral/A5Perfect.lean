import E213.Lib.Math.Algebra.Linalg213.DerivedSeries
import E213.Lib.Math.Algebra.Linalg213.DetTranspose
import E213.Lib.Math.Algebra.Linalg213.DetMul

/-!
# Icosahedral.A5Perfect — `A₅` is perfect: `[A₅,A₅] = A₅` (the `q=−1` quintic escape)

The **other pole** of `galois_correspondence.md`'s solvability tower.  `DerivedSeries` builds the
`q=+1` *converging* tower (`solvable_S3`: `S₃ ⊵ A₃ ⊵ {e}` terminates in two steps).  This file
builds the `q=−1` *escape*: **`A₅` is perfect** — its commutator subgroup is all of `A₅`, so the
derived series `A₅ ⊇ [A₅,A₅] ⊇ ⋯` is **constant at `A₅`** and never reaches `{e}`.  That
non-termination is the algebraic heart of the **insolvability of the quintic** (`A₅` is the Galois
group of the generic quintic; a solvable-by-radicals extension needs a terminating derived series).

`A₅` is the `perms 5` value-list group's even subgroup (`psign = 1`, 60 elements — the
`a5_order = 60` of `A5Bridge`).  The commutator `gcommP g h = g⁻¹h⁻¹gh` (`DerivedSeries`) and the
one-derived-step commutator list `commList` are reused verbatim.

## The two bounds (`[A₅,A₅] = A₅`)

* **Upper — `commutators_subset_A5` (structural).**  A commutator of two *even* permutations is
  even: `psign (g⁻¹h⁻¹gh) = psign(g)⁻¹·psign(h)⁻¹·psign(g)·psign(h) = 1` (sign is the homomorphism
  to `{±1}`, `psign_mul`/`psign_inv`).  So `[A₅,A₅] ⊆ A₅`.  No enumeration — holds for any `n`
  (`gcommP_even`).
* **Lower — `A5_subset_commutators` (`decide`).**  *Every* element of `A₅` actually **is** a
  commutator (`A₅ ⊆ commList A₅`) — the perfectness content.  Verified over the 60 elements by
  `decide` (∅-axiom; `#print axioms` clean).  3-cycles are commutators and generate `A₅`
  (`three_cycle_commutator_S5`, `DerivedSeries`); here the full lower bound is closed directly.

Together: **`[A₅,A₅] = A₅`** (`a5_perfect`), hence **`a5_not_solvable`** — the derived series is
constant at `A₅`.  Contrast `DerivedSeries.solvable_S3` (the `q=+1` terminating pole).

All ∅-axiom (`decide` on the finite enumeration for the lower bound; `psign` homomorphism algebra
for the upper bound).
-/

namespace E213.Lib.Math.Algebra.Icosahedral.A5Perfect

open E213.Lib.Math.Algebra.Linalg213.Permutation (perms psign)
open E213.Lib.Math.Algebra.Linalg213.PermGroup (composeList invPerm)
open E213.Lib.Math.Algebra.Linalg213.DerivedSeries (gcommP)
open E213.Lib.Math.Algebra.Linalg213.PermSign (psign_mul)
open E213.Lib.Math.Algebra.Linalg213.DetTranspose (psign_inv invPerm_mem_perms)
open E213.Lib.Math.Algebra.Linalg213.DetMul (composeList_mem_perms)
open E213.Tactic.List213 (mem_filter mem_filter_of mem_flatMap_intro mem_flatMap_elim
  mem_map_of_mem exists_of_mem_map)

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-! ## §1 — `A₅` as the even subgroup of `S₅`, and the commutator list -/

/-- `A₅` = the **even** permutations of `iota 5` (`psign = 1`): the alternating group, 60 elements
    (the `|A₅| = 60` of `A5Bridge.a5_order`). -/
def A5 : List (List Nat) := (perms 5).filter (fun p => decide (psign p = 1))

/-- One derived-series step as the **commutator list** (no dedup): all `gcommP g h`, `g,h ∈ G`.
    For perfectness only its *support as a set* matters, so the cheap un-deduplicated list is used
    (`DerivedSeries.commSet` adds an `eraseDups` not needed here). -/
def commList (G : List (List Nat)) : List (List Nat) :=
  G.flatMap (fun g => G.map (fun h => gcommP g h))

/-- ★★ `|A₅| = 60` on the value-list model (`= a5_order`, `A5Bridge`). -/
theorem A5_card : A5.length = 60 := by decide

/-! ## §2 — the upper bound (structural): a commutator of even permutations is even

`[A₅,A₅] ⊆ A₅`.  No enumeration: the sign of a commutator is `1` because `psign` is the
homomorphism `Sₙ → {±1}` (`psign_mul`) and inverse-invariant (`psign_inv`). -/

/-- ★★ **A commutator of even permutations is even** — `psign (gcommP g h) = 1` whenever
    `psign g = psign h = 1` (`g,h ∈ perms n`).  The sign homomorphism collapses the commutator:
    `psign (g⁻¹h⁻¹gh) = psign(g⁻¹)·psign(h⁻¹)·psign(g)·psign(h) = 1·1·1·1`.  Holds for **any** `n`
    (no enumeration) — the structural reason `[Aₙ,Aₙ] ⊆ Aₙ`. -/
theorem gcommP_even (n : Nat) (g h : List Nat) (hg : g ∈ perms n) (hh : h ∈ perms n)
    (hge : psign g = 1) (hhe : psign h = 1) : psign (gcommP g h) = 1 := by
  have hig : invPerm g ∈ perms n := invPerm_mem_perms n g hg
  have hih : invPerm h ∈ perms n := invPerm_mem_perms n h hh
  have h1 : composeList (invPerm g) (invPerm h) ∈ perms n := composeList_mem_perms n _ _ hig hih
  have h2 : composeList (composeList (invPerm g) (invPerm h)) g ∈ perms n :=
    composeList_mem_perms n _ _ h1 hg
  -- `gcommP g h` unfolds to the `composeList` chain `((g⁻¹ ∘ h⁻¹) ∘ g) ∘ h`
  show psign (composeList (composeList (composeList (invPerm g) (invPerm h)) g) h) = 1
  rw [psign_mul n _ h h2 hh, psign_mul n _ g h1 hg, psign_mul n _ (invPerm h) hig hih,
      psign_inv n g hg, psign_inv n h hh, hge, hhe]
  rfl

/-- A member of `A₅` is an even permutation of `iota 5`. -/
theorem mem_A5_iff {x : List Nat} : x ∈ A5 ↔ x ∈ perms 5 ∧ psign x = 1 := by
  constructor
  · intro h
    have := mem_filter h
    exact ⟨this.1, of_decide_eq_true this.2⟩
  · intro ⟨hp, hs⟩
    exact mem_filter_of hp (decide_eq_true hs)

/-- ★★★ **Upper bound `[A₅,A₅] ⊆ A₅`** — every commutator of `A₅` elements is again in `A₅`.
    The commutator set lands inside the alternating group (the structural `gcommP_even`). -/
theorem commutators_subset_A5 : ∀ x ∈ commList A5, x ∈ A5 := by
  intro x hx
  rcases mem_flatMap_elim hx with ⟨g, hg, hxm⟩
  rcases exists_of_mem_map hxm with ⟨h, hh, hxe⟩
  have hg' := (mem_A5_iff).mp hg
  have hh' := (mem_A5_iff).mp hh
  subst hxe
  refine (mem_A5_iff).mpr ⟨?_, gcommP_even 5 g h hg'.1 hh'.1 hg'.2 hh'.2⟩
  -- gcommP g h ∈ perms 5 (closure of perms under composeList/invPerm)
  have hig : invPerm g ∈ perms 5 := invPerm_mem_perms 5 g hg'.1
  have hih : invPerm h ∈ perms 5 := invPerm_mem_perms 5 h hh'.1
  have h1 : composeList (invPerm g) (invPerm h) ∈ perms 5 := composeList_mem_perms 5 _ _ hig hih
  have h2 : composeList (composeList (invPerm g) (invPerm h)) g ∈ perms 5 :=
    composeList_mem_perms 5 _ _ h1 hg'.1
  show composeList (composeList (composeList (invPerm g) (invPerm h)) g) h ∈ perms 5
  exact composeList_mem_perms 5 _ _ h2 hh'.1

/-! ## §3 — the lower bound (`decide`): every `A₅` element is a commutator

`[A₅,A₅] ⊇ A₅` — the perfectness content.  All 60 even permutations appear among the commutators
`gcommP g h`.  Verified directly over the enumeration. -/

/-- ★★★ **Lower bound `A₅ ⊆ [A₅,A₅]`** — *every* element of `A₅` is a commutator of two `A₅`
    elements: each of the 60 even permutations occurs in `commList A₅`.  This is the perfectness
    content (`[A₅,A₅] = A₅` modulo the trivial upper bound) — the `q=−1` commutator-escape that
    never descends.  `decide` over the 60-element group (∅-axiom). -/
theorem A5_subset_commutators : A5.all (fun a => (commList A5).contains a) = true := by decide

/-! ## §4 — `A₅` is perfect, hence not solvable (the `q=−1` pole) -/

/-- ★★★★ **`A₅` is perfect: `[A₅,A₅] = A₅`.**  The commutator list and `A₅` are the same set:
    every commutator is in `A₅` (`commutators_subset_A5`, structural) and every `A₅` element is a
    commutator (`A5_subset_commutators`, `decide`).  So one derived-series step returns `A₅`
    unchanged — the derived series is **constant at `A₅`**.

    This is the algebraic heart of the **insolvable quintic**: the `q=−1` *escape* pole, dual to
    `DerivedSeries.solvable_S3`'s `q=+1` *terminating* tower (`S₃ ⊵ A₃ ⊵ {e}`).  A solvable group
    has a derived series reaching `{e}`; `A₅`'s never does. -/
theorem a5_perfect :
    (∀ x ∈ commList A5, x ∈ A5) ∧ A5.all (fun a => (commList A5).contains a) = true :=
  ⟨commutators_subset_A5, A5_subset_commutators⟩

/-- ★★★★★ **`A₅` is not solvable.**  The derived series never terminates: one commutator step
    sends `A₅` back to (a list whose set is) `A₅` — every generator is recovered as a commutator
    (`A5_subset_commutators`) while no commutator escapes `A₅` (`commutators_subset_A5`).  Hence
    `A₅ ⊇ [A₅,A₅] ⊇ [[A₅,A₅],…] ⊇ ⋯` is constant at `A₅ ≠ {e}` — the `q=−1` non-terminating
    pole.  (`|A₅| = 60 ≠ 1`, `A5_card`, so the constant value is not the trivial group.)

    The quintic's insolvability-by-radicals reads off this: its Galois group `A₅` has no
    terminating derived series, so no radical tower resolves it — unlike `S₃` (`solvable_S3`). -/
theorem a5_not_solvable :
    -- the derived step returns A₅ (perfect): both containments
    (∀ x ∈ commList A5, x ∈ A5)
    ∧ A5.all (fun a => (commList A5).contains a) = true
    -- and A₅ is non-trivial: the constant value is not {e}
    ∧ A5.length = 60 :=
  ⟨commutators_subset_A5, A5_subset_commutators, A5_card⟩

end E213.Lib.Math.Algebra.Icosahedral.A5Perfect
