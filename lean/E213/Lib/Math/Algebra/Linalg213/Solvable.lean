import E213.Lib.Math.Algebra.Linalg213.DerivedSeries
import E213.Lib.Math.Algebra.Icosahedral.A5Perfect
import E213.Lib.Math.Foundations.ResidueTag

/-!
# Linalg213 — the general `isSolvable` / `isPerfect` predicate (the two solvability poles unified)

`DerivedSeries.solvable_S3` (the `q=+1` *terminating* tower `S₃ ⊵ A₃ ⊵ {e}`) and
`A5Perfect.a5_not_solvable` (the `q=−1` *non-terminating* perfect group `[A₅,A₅]=A₅`) are the two
poles of `galois_correspondence.md`'s located solvability break.  Before this file each pole was a
**bespoke fact**; the named residual (`FRONTIER_AUDIT.md`, line 77) was a **reusable
`isSolvable` predicate** with the derived series written as an *iterated operator*.

This file closes that residual ∅-axiom.

## The iterated operator

`derivedSeries step G 0 = G`, `derivedSeries step G (k+1) = step (derivedSeries step G k)` — the
derived series as the literal iterate of **one** single-derived-step `step`.  The canonical step is
`DerivedSeries.commSet` (the deduplicated commutator set `[G,G]`); both poles use it.

* **`isSolvable step G`** `:= ∃ k, SameSet (derivedSeries step G k) (One)` — the series reaches the
  trivial group `{e}` at some depth.  `One = [iota]` (here `[0,1,2]` / `[0,1,2,3,4]`).
* **`isPerfect step G`** `:= SameSet (step G) G` — one step returns `G` (as a set); the derived
  series is **constant at `G`**.

`SameSet` (mutual `contains`-membership, decidable, ∅-axiom) is the right relation: a derived step
permutes / deduplicates the element list, so list-equality is too strict — the *set* is the
subgroup.  For `S₃` the step lands on `One` up to ordering; for `A₅` the step lands back on `A₅`.

## The general principle (the `q=−1` escape, no enumeration)

`perfect_nontrivial_not_solvable : isPerfect step G → ¬ SameSet G One → ¬ isSolvable step G`.

Pure induction: `isPerfect` makes `derivedSeries step G k` `SameSet`-constant at `G`; if `G` is not
`SameSet`-trivial it can never reach `One`.  **No `decide`, no enumeration** — holds for any finite
group presentation, any step.  The `A₅` instance `a5_not_solvable'` feeds it `A5Perfect.a5_perfect`.

The two poles are now the two **values** of one predicate, exactly the `ResidueTag` dichotomy:
solvable = `converge` (`q=+1`), perfect-nontrivial = `escape` (`q=−1`).

## Honest scope (the remaining residual)

The single-derived-step `commSet` **is** the commutator subgroup only because for `S₃`/`A₃`/`A₅`
the commutator *set* is already closed under product and inverse (`DerivedSeries.A3_product_closed`
/ `A3_inverse_closed`; `A5Perfect.commutators_subset_A5`).  A **general** `commClosure` — the
subgroup *generated* by commutators, with a proven generation/closure step for groups whose
commutator set is not already closed — is **not** built here (it needs a real generation fixpoint,
heavy ∅-axiom).  `derivedSeries` is therefore stated parametrically in `step`, and the closed-case
instances supply `step = commSet`.  This is the precise residual: **the general
commutator-subgroup generation step** (`commClosure`), stated, not faked.

All ∅-axiom (`commSet`/`SameSet` are `decide`/`rfl`-computable; the general principle is induction;
the `A₅` set-fixedness is `decide` over the 60-element group).
-/

namespace E213.Lib.Math.Algebra.Linalg213.Solvable

open E213.Lib.Math.Algebra.Linalg213.DerivedSeries (commSet S3 A3 One gcommP solvable_S3
  derived_S3_step1 derived_A3_step2)
open E213.Lib.Math.Algebra.Icosahedral.A5Perfect (A5 commList commutators_subset_A5
  A5_subset_commutators A5_card)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## §1 — `SameSet`: two element-lists denote the same subgroup

`SameSet` is defined directly in **membership form** (`∀ a ∈ G, a ∈ H` both ways) so that
reflexivity / symmetry / transitivity are pure (no `propext`-leaking `List.all_eq_true`).  The
`decide`-backed facts (a step landing on a given set) come in via the **pure Bool→membership
bridges** `mem_of_all` / `mem_of_memB` (structural recursion over a `DecidableEq`-based `memB`, NOT
`List.contains` — whose `LawfulBEq (List Nat)` instance carries `propext` on application). -/

/-- **Pure** `l.all p = true → ∀ a ∈ l, p a = true` (structural recursion; no `List.all_eq_true`,
    which leaks `propext`).  `(x::xs).all p` is defeq `p x && xs.all p`. -/
theorem mem_of_all {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.all p = true → ∀ a ∈ l, p a = true
  | [], _, a, ha => nomatch ha
  | x :: xs, h, a, ha => by
      have hx : p x = true := by
        cases hpx : p x with
        | true => rfl
        | false =>
          exact absurd (hpx ▸ h : (false && xs.all p) = true)
            (by intro hc; exact Bool.noConfusion hc)
      have hxs : xs.all p = true := by
        cases hpx : p x with
        | true => exact (hpx ▸ h : (true && xs.all p) = true)
        | false =>
          exact absurd (hpx ▸ h : (false && xs.all p) = true)
            (by intro hc; exact Bool.noConfusion hc)
      cases ha with
      | head => exact hx
      | tail _ h2 => exact mem_of_all hxs a h2

/-- **Pure** `(∀ a ∈ l, p a = true) → l.all p = true` (structural recursion). -/
theorem all_of_mem {α : Type} {p : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = true) → l.all p = true
  | [], _ => rfl
  | x :: xs, h => by
      show (p x && xs.all p) = true
      rw [h x (List.Mem.head _), all_of_mem (fun a ha => h a (List.Mem.tail _ ha))]; rfl

/-- **Pure Bool membership** via `DecidableEq` (NOT `List.contains`, whose `BEq`/`LawfulBEq`
    instance for `List Nat` carries `propext` on application).  `memB l a = true ⟺ a ∈ l`, proved
    by structural recursion with `decide`-equality (pure on `List Nat`). -/
def memB (l : List (List Nat)) (a : List Nat) : Bool :=
  l.any (fun x => decide (a = x))

/-- **Pure** `memB l a = true → a ∈ l` (structural recursion; `of_decide_eq_true` on
    `DecidableEq`, no `LawfulBEq`). -/
theorem mem_of_memB {a : List Nat} :
    ∀ {l : List (List Nat)}, memB l a = true → a ∈ l
  | [], h => absurd h (by intro hc; exact Bool.noConfusion hc)
  | x :: xs, h => by
      have h' : (decide (a = x) || memB xs a) = true := h
      cases hb : (decide (a = x)) with
      | true => exact (of_decide_eq_true hb) ▸ List.Mem.head _
      | false =>
        have hxs : memB xs a = true := by rw [hb] at h'; exact h'
        exact List.Mem.tail _ (mem_of_memB hxs)

/-- **Pure** `a ∈ l → memB l a = true` (structural recursion). -/
theorem memB_of_mem {a : List Nat} :
    ∀ {l : List (List Nat)}, a ∈ l → memB l a = true
  | [], h => nomatch h
  | x :: xs, h => by
      cases h with
      | head =>
        show (decide (a = a) || memB xs a) = true
        rw [decide_eq_true (rfl : a = a)]; rfl
      | tail _ h2 =>
        show (decide (a = x) || memB xs a) = true
        rw [memB_of_mem h2]; exact Bool.or_true _

/-- **`SameSet G H`** — `G` and `H` have the same elements.  Membership form (pure refl/symm/trans);
    the right relation between two derived-series stages, since a derived step reorders / dedups the
    element list — the *set* (the subgroup), not the list, is the invariant content. -/
def SameSet (G H : List (List Nat)) : Prop :=
  (∀ a ∈ G, a ∈ H) ∧ (∀ a ∈ H, a ∈ G)

/-- `SameSet` membership form (definitional; kept for readability of the instance proofs). -/
theorem sameSet_iff {G H : List (List Nat)} :
    SameSet G H ↔ (∀ a ∈ G, a ∈ H) ∧ (∀ a ∈ H, a ∈ G) := Iff.rfl

/-- `SameSet` is reflexive. -/
theorem SameSet.refl (G : List (List Nat)) : SameSet G G := ⟨fun _ h => h, fun _ h => h⟩

/-- `SameSet` is symmetric. -/
theorem SameSet.symm {G H : List (List Nat)} (h : SameSet G H) : SameSet H G := ⟨h.2, h.1⟩

/-- List-equality is `SameSet`. -/
theorem SameSet.of_eq {G H : List (List Nat)} (h : G = H) : SameSet G H := h ▸ SameSet.refl G

/-! ## §2 — the derived series as an iterated operator -/

/-- ★★ **The derived series as the iterate of one single-derived-step `step`.**
    `derivedSeries step G 0 = G`, `derivedSeries step G (k+1) = step (derivedSeries step G k)`.
    The canonical `step` is `DerivedSeries.commSet` (the commutator set `[G,G]`, deduplicated);
    both poles instantiate it.  Parametric in `step` because the *general* commutator-subgroup
    generation (`commClosure`) is the named residual — for the closed-commutator groups
    `S₃`/`A₃`/`A₅` the set `commSet` already **is** the subgroup. -/
def derivedSeries (step : List (List Nat) → List (List Nat)) :
    List (List Nat) → Nat → List (List Nat)
  | G, 0     => G
  | G, k + 1 => step (derivedSeries step G k)

@[simp] theorem derivedSeries_zero (step : List (List Nat) → List (List Nat))
    (G : List (List Nat)) : derivedSeries step G 0 = G := rfl

@[simp] theorem derivedSeries_succ (step : List (List Nat) → List (List Nat))
    (G : List (List Nat)) (k : Nat) :
    derivedSeries step G (k + 1) = step (derivedSeries step G k) := rfl

/-! ## §3 — the two predicates: `isSolvable` and `isPerfect`

The trivial group `{e}` of a value-list group of width `n` is `trivialGroup n = [iota n]` (the
single identity permutation).  `isSolvable` is relative to it — `S₃`'s is `[[0,1,2]] = One`,
`A₅`'s is `[[0,1,2,3,4]]`. -/

/-- The trivial group `{e}` for width-`n` value-lists: the singleton identity `[iota n]`.
    (`trivialGroup 3 = One = [[0,1,2]]`; `trivialGroup 5 = [[0,1,2,3,4]]`.) -/
def trivialGroup (n : Nat) : List (List Nat) :=
  [E213.Lib.Math.Algebra.Linalg213.Permutation.iota n]

/-- ★★★ **`isSolvable step triv G`** — the derived series reaches the trivial group `triv = {e}`
    at some depth `k` (up to `SameSet`).  The `q=+1` *converge* pole: the commutator tower folds
    to `1`.  `S₃` satisfies it at `k = 2` with `triv = trivialGroup 3` (`solvable_S3'`). -/
def isSolvable (step : List (List Nat) → List (List Nat)) (triv G : List (List Nat)) : Prop :=
  ∃ k, SameSet (derivedSeries step G k) triv

/-- ★★★ **`isPerfect step G`** — one derived step returns `G` (as a set): `[G,G] = G`.  The
    `q=−1` *escape* pole: the derived series is **constant at `G`**, never descending.  `A₅`
    satisfies it (`a5_isPerfect`). -/
def isPerfect (step : List (List Nat) → List (List Nat)) (G : List (List Nat)) : Prop :=
  SameSet (step G) G

/-! ## §4 — the general principle: a perfect non-trivial group is not solvable (`q=−1`)

No enumeration: `isPerfect` makes the whole derived series `SameSet`-constant at `G` (induction),
so a `SameSet`-non-trivial `G` can never reach `One`.

The one honest hypothesis the abstract statement needs is that `step` **respects `SameSet`**
(`SameSet X Y → SameSet (step X) (step Y)`): a single derived step of two element-lists denoting
the same subgroup denotes the same subgroup.  This is a *property of the step*, not of `G`, and the
canonical `commSet` step satisfies it (the commutator set depends only on the underlying set).  We
take it as a hypothesis so the principle stays `step`-parametric; the `A₅` instance discharges it
with `commList_sameSet_cong` (the commutator list depends only on the underlying set). -/

/-- `SameSet` is transitive (needed to chain the constant series with the perfect step). -/
theorem SameSet.trans {G H K : List (List Nat)} (h1 : SameSet G H) (h2 : SameSet H K) :
    SameSet G K :=
  ⟨fun a ha => h2.1 a (h1.1 a ha), fun a ha => h1.2 a (h2.2 a ha)⟩

/-- A perfect group's derived series is `SameSet`-constant at `G` (every stage equals `G` as a
    set), given that `step` respects `SameSet`.  Pure induction on depth `k` — the structural
    reason the series never descends.  No `decide`, no enumeration; any `step`, any `G`. -/
theorem derivedSeries_perfect_const {step : List (List Nat) → List (List Nat)}
    (hcong : ∀ X Y, SameSet X Y → SameSet (step X) (step Y))
    {G : List (List Nat)} (hp : isPerfect step G) :
    ∀ k, SameSet (derivedSeries step G k) G := by
  intro k
  induction k with
  | zero => exact SameSet.refl G
  | succ n ih =>
    -- derivedSeries step G (n+1) = step (derivedSeries step G n) ~ step G ~ G
    show SameSet (step (derivedSeries step G n)) G
    exact SameSet.trans (hcong _ G ih) hp

/-- ★★★★ **The general principle: a perfect non-trivial group is not solvable.**
    If `step G` is `G` (as a set) — `isPerfect` — and `G` is not `SameSet`-trivial, then the
    derived series is `SameSet`-constant at `G` (`derivedSeries_perfect_const`) and so reaches
    `One` at no depth: `¬ isSolvable step G`.  This is the `q=−1` *escape* pole made general — the
    structural obstruction to solvability, **no enumeration**, holds for any finite group
    presentation and any `SameSet`-respecting derived step.  Dual to the `q=+1` `solvable_S3'`. -/
theorem perfect_nontrivial_not_solvable {step : List (List Nat) → List (List Nat)}
    (hcong : ∀ X Y, SameSet X Y → SameSet (step X) (step Y))
    {triv G : List (List Nat)} (hp : isPerfect step G) (hnt : ¬ SameSet G triv) :
    ¬ isSolvable step triv G := by
  rintro ⟨k, hk⟩
  -- derivedSeries step G k ~ G  and  derivedSeries step G k ~ triv  ⟹  G ~ triv, contradiction
  exact hnt (SameSet.trans (derivedSeries_perfect_const hcong hp k).symm hk)

/-! ## §5 — the `q=+1` instance: `S₃` is solvable

`S₃` reaches the trivial group in **two** `commSet` steps (`DerivedSeries.solvable_S3`:
`commSet (commSet S3) = One` as a *list*).  Hence `isSolvable commSet S3` at `k = 2`. -/

/-- ★★★ **`S₃` is solvable** (re-expressed via the general predicate): the derived series
    `derivedSeries commSet S3` reaches `One` at depth `k = 2`.  The `q=+1` converging pole, now an
    instance of `isSolvable`, not a bespoke fact.  Delegates to `DerivedSeries.solvable_S3`. -/
theorem solvable_S3' : isSolvable commSet (trivialGroup 3) S3 :=
  ⟨2, SameSet.of_eq (by
    show commSet (commSet S3) = trivialGroup 3
    rw [solvable_S3]; decide)⟩

/-- The derived series of `S₃` at each depth, explicit: `0 ↦ S₃`, `1 ↦ A₃`, `2 ↦ {e}`. -/
theorem derivedSeries_S3_explicit :
    derivedSeries commSet S3 1 = A3 ∧ derivedSeries commSet S3 2 = One :=
  ⟨derived_S3_step1, solvable_S3⟩

/-! ## §6 — the `q=−1` instance: `A₅` is perfect, hence not solvable

`A₅`'s single derived step is the (un-deduplicated) commutator list `commList`
(`A5Perfect.commList`).  `A5Perfect.a5_perfect` proves `commList A5` and `A5` are the **same set**
(both containments), i.e. `isPerfect commList A5`.  `commList` respects `SameSet`
(`commList_sameSet_cong`, from `flatMap`/`map` membership — no `eraseDups`), so the general
principle applies. -/

/-- Membership in `commList G`: `a ∈ commList G ↔ ∃ g ∈ G, ∃ h ∈ G, gcommP g h = a`.  (`commList`
    is `G.flatMap (fun g => G.map (gcommP g ·))`; pure `flatMap`/`map` membership.) -/
theorem mem_commList {G : List (List Nat)} {a : List Nat} :
    a ∈ commList G ↔ ∃ g, g ∈ G ∧ ∃ h, h ∈ G ∧ gcommP g h = a := by
  constructor
  · intro h
    rcases E213.Tactic.List213.mem_flatMap_elim h with ⟨g, hg, hgm⟩
    rcases E213.Tactic.List213.exists_of_mem_map hgm with ⟨h', hh', he⟩
    exact ⟨g, hg, h', hh', he⟩
  · rintro ⟨g, hg, h', hh', he⟩
    exact E213.Tactic.List213.mem_flatMap_intro hg
      (he ▸ E213.Tactic.List213.mem_map_of_mem (fun h => gcommP g h) hh')

/-- ★★ **`commList` respects `SameSet`.**  If `G` and `G'` denote the same set, so do their
    commutator lists: a commutator `gcommP g h` of `G`-elements is a commutator of `G'`-elements
    (each generator transported across the `SameSet`), and vice versa.  Discharges the `hcong`
    hypothesis of `perfect_nontrivial_not_solvable` for the `commList` step — `flatMap`/`map`
    membership only, **no `eraseDups`**. -/
theorem commList_sameSet_cong (G G' : List (List Nat)) (h : SameSet G G') :
    SameSet (commList G) (commList G') := by
  have mem_iff : ∀ {X Y : List (List Nat)}, SameSet X Y →
      ∀ a, a ∈ commList X → a ∈ commList Y := by
    intro X Y hXY a ha
    rcases mem_commList.mp ha with ⟨g, hg, h2, hh2, he⟩
    have hXY' := hXY.1
    exact mem_commList.mpr ⟨g, hXY' g hg, h2, hXY' h2 hh2, he⟩
  exact ⟨fun a ha => mem_iff h a ha, fun a ha => mem_iff h.symm a ha⟩

/-- `A₅ ⊆ commList A₅` in **pure** `memB` Bool form (`decide`; no `List.contains`/`LawfulBEq`).
    Restates `A5Perfect.A5_subset_commutators` against the propext-free `memB`. -/
theorem A5_subset_commutators_B : A5.all (fun a => memB (commList A5) a) = true := by decide

/-- ★★★ **`A₅` is perfect** (via the general predicate): `commList A5` and `A5` are the same set
    (`A5Perfect.commutators_subset_A5` ⊆, `A5_subset_commutators_B` ⊇).  `isPerfect commList A5`. -/
theorem a5_isPerfect : isPerfect commList A5 := by
  refine ⟨commutators_subset_A5, ?_⟩
  -- A5 ⊆ commList A5: from the pure Bool `A5_subset_commutators_B` via the pure bridges
  intro a ha
  exact mem_of_memB (mem_of_all A5_subset_commutators_B a ha)

/-- `A₅` is not `SameSet`-trivial: `|A₅| = 60 ≠ 1`, and `One = [iota 5]` has one element, so they
    cannot have the same elements (`A₅` contains a non-identity element). -/
theorem a5_not_sameSet_trivial : ¬ SameSet A5 (trivialGroup 5) := by
  intro h
  -- the 3-cycle (0 1 2) = [2,0,1,3,4] is in A5 but not in the trivial group {iota 5}.
  -- membership proved via the PURE `memB` Bool bridge (∈-via-`decide` leaks propext).
  have hmem : ([2, 0, 1, 3, 4] : List Nat) ∈ A5 :=
    mem_of_memB (by decide : memB A5 ([2, 0, 1, 3, 4] : List Nat) = true)
  have hin : ([2, 0, 1, 3, 4] : List Nat) ∈ trivialGroup 5 := h.1 _ hmem
  -- but `memB (trivialGroup 5) [2,0,1,3,4] = false`, so by `memB_of_mem` contradiction
  have : memB (trivialGroup 5) ([2, 0, 1, 3, 4] : List Nat) = true := memB_of_mem hin
  rw [show memB (trivialGroup 5) ([2, 0, 1, 3, 4] : List Nat) = false from by decide] at this
  exact Bool.noConfusion this

/-- ★★★★★ **`A₅` is not solvable** (via the general principle).  `A₅` is perfect
    (`a5_isPerfect`), `commList` respects `SameSet` (`commList_sameSet_cong`), and `A₅` is
    non-trivial (`a5_not_sameSet_trivial`) — so `perfect_nontrivial_not_solvable` gives
    `¬ isSolvable commList A5`.  The `q=−1` escape pole, now an **instance of the general
    principle**, not a bespoke `a5_perfect` repackaging.  Dual to `solvable_S3'`. -/
theorem a5_not_solvable' : ¬ isSolvable commList (trivialGroup 5) A5 :=
  perfect_nontrivial_not_solvable commList_sameSet_cong a5_isPerfect a5_not_sameSet_trivial

/-! ## §7 — the two poles as the two `ResidueTag` values

The solvability dichotomy **is** the `q=±1` `ResidueTag` of `Foundations.ResidueTag`: a solvable
group is the `converge` pole (`q=+1`, the commutator tower has a fixed point `{e}`, reached at a
finite depth), a perfect non-trivial group is the `escape` pole (`q=−1`, the derived step is
fixed-point-free *as a descent* — it returns `G`, never `{e}`).  We tag each pole and read off the
Cassini multiplier. -/

open E213.Lib.Math.Foundations.ResidueTag (ResidueTag multiplier)

/-- The residue tag from a solvability verdict: `converge` (`q=+1`) when solvable, `escape`
    (`q=−1`) when not.  Tagged from the witness (a `PSum`, not a decision of the predicate). -/
def tagOfVerdict {step : List (List Nat) → List (List Nat)} {triv G : List (List Nat)}
    (w : isSolvable step triv G ⊕' ¬ isSolvable step triv G) : ResidueTag :=
  match w with
  | .inr _ => .escape    -- q = −1 (perfect-nontrivial escape)
  | .inl _ => .converge  -- q = +1 (solvable, terminating tower)

/-- `S₃` (solvable) carries the `q=+1` `converge` tag, multiplier `+1`. -/
theorem tagOfVerdict_S3 :
    tagOfVerdict (.inl solvable_S3') = ResidueTag.converge ∧ multiplier .converge = 1 :=
  ⟨rfl, rfl⟩

/-- `A₅` (perfect, non-trivial) carries the `q=−1` `escape` tag, multiplier `−1`. -/
theorem tagOfVerdict_A5 :
    tagOfVerdict (.inr a5_not_solvable') = ResidueTag.escape ∧ multiplier .escape = -1 :=
  ⟨rfl, rfl⟩

/-- ★★★★ **The solvability dichotomy is the `q=±1` residue tag.**  One construct (the derived
    series as an iterated operator + `isSolvable`/`isPerfect`) under which both `galois_correspondence.md`
    poles are the two **values** of the `ResidueTag`:

    * **`S₃` — `converge` (`q=+1`, multiplier `+1`)**: `isSolvable commSet S3`, the derived series
      `S₃ ⊵ A₃ ⊵ {e}` reaches the trivial group at depth 2 (`solvable_S3'`);
    * **`A₅` — `escape` (`q=−1`, multiplier `−1`)**: `¬ isSolvable commList A5`, perfect and
      non-trivial, the derived series constant at `A₅` (`a5_not_solvable'`, via the **general**
      `perfect_nontrivial_not_solvable`).

    The two bespoke facts (`DerivedSeries.solvable_S3`, `A5Perfect.a5_not_solvable`) are now the two
    instances of one reusable predicate, tagged by one `±1` bit. -/
theorem solvability_two_poles :
    (isSolvable commSet (trivialGroup 3) S3
      ∧ tagOfVerdict (.inl solvable_S3') = ResidueTag.converge ∧ multiplier .converge = 1)
    ∧ (¬ isSolvable commList (trivialGroup 5) A5
      ∧ tagOfVerdict (.inr a5_not_solvable') = ResidueTag.escape ∧ multiplier .escape = -1) :=
  ⟨⟨solvable_S3', rfl, rfl⟩, ⟨a5_not_solvable', rfl, rfl⟩⟩

end E213.Lib.Math.Algebra.Linalg213.Solvable
