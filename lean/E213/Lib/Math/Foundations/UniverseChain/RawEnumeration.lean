import E213.Lib.Math.Foundations.UniverseChain.RawRecurrence
import E213.Meta.Tactic.List213

/-!
# Raw enumeration: general theorem |S_n| = rawCount n (∅-axiom)

General recurrence proof: actual canonical-Tree enumeration length
matches `rawCount n` for ALL n.

Avoids Lean-core `List.length_append` and `List.length_map` (which
leak `propext`); uses the shared `E213.Tactic.List213` replacements
`length_append_rev` and `length_map`.
-/

namespace E213.Lib.Math.Foundations.UniverseChain.RawEnumeration

open E213.Term.Internal (Tree)
open E213.Lib.Math.Foundations.UniverseChain.RawRecurrence (choose2)
open E213.Tactic.List213 (length_append_rev length_map)

/-- Local alias for the reversed-order length-of-append from
    `E213.Tactic.List213`.  Retained for readability of downstream
    proofs that already cite `myLengthAppend`. -/
theorem myLengthAppend (L1 L2 : List α) :
    (L1 ++ L2).length = L2.length + L1.length :=
  length_append_rev L1 L2

/-- Local alias for `length_map`. -/
theorem myLengthMap (L : List α) (f : α → β) :
    (L.map f).length = L.length :=
  length_map L f

/-- `choose2 (n+1) = n + choose2 n` (bridge for clean recurrence). -/
theorem choose2_succ (n : Nat) : choose2 (n + 1) = n + choose2 n := by
  match n with
  | 0 => rfl
  | k + 1 =>
    show choose2 (k + 1) + (k + 1) = (k + 1) + choose2 (k + 1)
    exact Nat.add_comm _ _

/-- For each (x, y) pair where x is earlier than y, generate
    `Tree.slash x y`. -/
def newSlashes : List Tree → List Tree
  | [] => []
  | x :: rest => rest.map (Tree.slash x) ++ newSlashes rest

/-- ★ `newSlashes` length = `choose2` of input length. -/
theorem newSlashes_length : ∀ L : List Tree,
    (newSlashes L).length = choose2 L.length
  | [] => rfl
  | x :: rest => by
    show (rest.map (Tree.slash x) ++ newSlashes rest).length
       = choose2 (rest.length + 1)
    rw [myLengthAppend, myLengthMap, newSlashes_length, choose2_succ]
    exact Nat.add_comm _ _

/-- Recursive enumeration of canonical Trees at depth ≤ n. -/
def enumTreeDepth : Nat → List Tree
  | 0 => [Tree.a, Tree.b]
  | n + 1 => [Tree.a, Tree.b] ++ newSlashes (enumTreeDepth n)

/-- ★★★ **Enumeration capstone** — general recurrence + low-n checks.

    Bundles:
      · ∀ n, (enumTreeDepth n).length = rawCount n  (general)
      · concrete witnesses at n = 0..3  (depth-0..3 counts 2, 3, 5, 12). -/
theorem enumeration_capstone :
    (∀ n, (enumTreeDepth n).length
        = E213.Lib.Math.Foundations.UniverseChain.RawRecurrence.rawCount n)
    ∧ (enumTreeDepth 0).length = 2
    ∧ (enumTreeDepth 1).length = 3
    ∧ (enumTreeDepth 2).length = 5
    ∧ (enumTreeDepth 3).length = 12 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      show ([Tree.a, Tree.b] ++ newSlashes (enumTreeDepth k)).length
         = 2 + choose2 (E213.Lib.Math.Foundations.UniverseChain.RawRecurrence.rawCount k)
      rw [myLengthAppend, newSlashes_length, ih]
      exact Nat.add_comm _ _
  all_goals decide

-- ═══ The honest count: members canonical + Nodup + complete ═══
--
-- `enumeration_capstone` matches lengths; the theorems below close
-- the semantic half: `enumTreeDepth n` lists *exactly* the
-- canonical Trees of depth ≤ n, without repetition.  Hence
-- `rawCount n` genuinely counts canonical Raws of depth ≤ n.
--
-- Engine: the strict-pairwise invariant `Pairwise (cmp · · = .lt)`.
-- No `cmp` transitivity is needed — only the lex head structure
-- (`cmp_slash_same`, `cmp_slash_lt_head`), `cmp_self_eq`, and the
-- swap conversions.

open E213.Term.Internal

/-- The strict enumeration order. -/
def cmpLt (x y : Tree) : Prop := Tree.cmp x y = .lt

private theorem cmp_slash_same (z u v : Tree) :
    Tree.cmp (.slash z u) (.slash z v) = Tree.cmp u v := by
  show (match Tree.cmp z z with
        | .eq => Tree.cmp u v | .lt => .lt | .gt => .gt) = Tree.cmp u v
  rw [Tree.cmp_self_eq]

private theorem cmp_slash_lt_head {z x' : Tree}
    (h : Tree.cmp z x' = .lt) (u y' : Tree) :
    Tree.cmp (.slash z u) (.slash x' y') = .lt := by
  show (match Tree.cmp z x' with
        | .eq => Tree.cmp u y' | .lt => .lt | .gt => .gt) = .lt
  rw [h]

private theorem map_mem_elim {f : Tree → Tree} :
    ∀ {l : List Tree} {t}, t ∈ l.map f → ∃ y, y ∈ l ∧ t = f y
  | _ :: _, _, .head _ => ⟨_, .head _, rfl⟩
  | _ :: _, _, .tail _ h' =>
    have ⟨w, hw, he⟩ := map_mem_elim h'
    ⟨w, .tail _ hw, he⟩

private theorem pairwise_append {S : Tree → Tree → Prop} :
    ∀ {l1 l2 : List Tree}, List.Pairwise S l1 → List.Pairwise S l2 →
      (∀ u, u ∈ l1 → ∀ v, v ∈ l2 → S u v) →
      List.Pairwise S (l1 ++ l2) := by
  intro l1
  induction l1 with
  | nil => intro l2 _ h2 _; exact h2
  | cons x l1 ih =>
    intro l2 h1 h2 hx
    cases h1 with
    | cons hxl h1' =>
      refine .cons ?_ (ih h1' h2 (fun u hu v hv => hx u (.tail _ hu) v hv))
      intro w hw
      cases E213.Tactic.List213.mem_append_iff hw with
      | inl h => exact hxl w h
      | inr h => exact hx x (.head _) w h

private theorem pairwise_map {S S' : Tree → Tree → Prop} {f : Tree → Tree}
    (hf : ∀ u v, S' u v → S (f u) (f v)) :
    ∀ {l : List Tree}, List.Pairwise S' l → List.Pairwise S (l.map f) := by
  intro l
  induction l with
  | nil => intro _; exact .nil
  | cons x l ih =>
    intro hp
    cases hp with
    | cons hx hl =>
      refine .cons ?_ (ih hl)
      intro w hw
      have ⟨y, hy, he⟩ := map_mem_elim hw
      rw [he]
      exact hf x y (hx y hy)

private theorem pairwise_imp {S S' : Tree → Tree → Prop}
    (h : ∀ u v, S u v → S' u v) :
    ∀ {l : List Tree}, List.Pairwise S l → List.Pairwise S' l := by
  intro l
  induction l with
  | nil => intro _; exact .nil
  | cons x l ih =>
    intro hp
    cases hp with
    | cons hx hl => exact .cons (fun w hw => h x w (hx w hw)) (ih hl)

/-- Member characterization of `newSlashes` over a strictly-ordered
    list: every member is a slash of two list members in `cmp`-order. -/
theorem newSlashes_mem_char :
    ∀ {L : List Tree}, List.Pairwise cmpLt L →
      ∀ {t}, t ∈ newSlashes L →
      ∃ x y, t = Tree.slash x y ∧ x ∈ L ∧ y ∈ L
        ∧ Tree.cmp x y = .lt := by
  intro L
  induction L with
  | nil => intro _ t ht; exact absurd ht (fun h => nomatch h)
  | cons z rest ih =>
    intro hp t ht
    cases hp with
    | cons hz hrest =>
      cases E213.Tactic.List213.mem_append_iff ht with
      | inl hl =>
        have ⟨y, hy, he⟩ := map_mem_elim hl
        exact ⟨z, y, he, .head _, .tail _ hy, hz y hy⟩
      | inr hr =>
        have ⟨x, y, he, hx, hy, hcm⟩ := ih hrest hr
        exact ⟨x, y, he, .tail _ hx, .tail _ hy, hcm⟩

/-- Introduction: a `cmp`-ordered pair of members lands in
    `newSlashes`. -/
theorem mem_newSlashes {x y : Tree} (hc : Tree.cmp x y = .lt) :
    ∀ {L : List Tree}, List.Pairwise cmpLt L → x ∈ L → y ∈ L →
      Tree.slash x y ∈ newSlashes L := by
  intro L
  induction L with
  | nil => intro _ hx _; exact absurd hx (fun h => nomatch h)
  | cons z rest ih =>
    intro hp hx hy
    cases hp with
    | cons hz hrest =>
      cases hx with
      | head =>
        cases hy with
        | head =>
          rw [Tree.cmp_self_eq] at hc
          exact Ordering.noConfusion hc
        | tail _ hy' =>
          exact E213.Tactic.List213.mem_append_left
            (E213.Tactic.List213.mem_map_of_mem (Tree.slash x) hy')
      | tail _ hx' =>
        cases hy with
        | head =>
          have hgt := Tree.cmp_lt_to_gt_swap _ _ (hz x hx')
          rw [hgt] at hc
          exact Ordering.noConfusion hc
        | tail _ hy' =>
          exact E213.Tactic.List213.mem_append_right _ (ih hrest hx' hy')

theorem pairwise_newSlashes :
    ∀ {L : List Tree}, List.Pairwise cmpLt L →
      List.Pairwise cmpLt (newSlashes L) := by
  intro L
  induction L with
  | nil => intro _; exact .nil
  | cons z rest ih =>
    intro hp
    cases hp with
    | cons hz hrest =>
      refine pairwise_append (pairwise_map ?_ hrest) (ih hrest) ?_
      · intro u v huv
        show Tree.cmp (.slash z u) (.slash z v) = .lt
        rw [cmp_slash_same]
        exact huv
      · intro u hu v hv
        have ⟨y, hy, heu⟩ := map_mem_elim hu
        have ⟨x', y', hev, hx', _, _⟩ := newSlashes_mem_char hrest hv
        rw [heu, hev]
        exact cmp_slash_lt_head (hz x' hx') y y'

private theorem pairwise_atoms :
    List.Pairwise cmpLt [Tree.a, Tree.b] :=
  .cons (fun w hw => match w, hw with
      | _, .head _ => rfl
      | _, .tail _ h => nomatch h)
    (.cons (fun _ hw => nomatch hw) .nil)

/-- ★ The enumeration is strictly `cmp`-ordered at every depth. -/
theorem enum_pairwise : ∀ n, List.Pairwise cmpLt (enumTreeDepth n)
  | 0 => pairwise_atoms
  | n + 1 => by
    have ihp := enum_pairwise n
    refine pairwise_append pairwise_atoms (pairwise_newSlashes ihp) ?_
    intro u hu v hv
    have ⟨x, y, hev, _, _, _⟩ := newSlashes_mem_char ihp hv
    cases hu with
    | head =>
      rw [hev]
      exact rfl
    | tail _ hu' =>
      cases hu' with
      | head =>
        rw [hev]
        exact rfl
      | tail _ h => exact absurd h (fun h => nomatch h)

private theorem max_le_both {u v n : Nat} (hu : u ≤ n) (hv : v ≤ n) :
    Nat.max u v ≤ n :=
  match Nat.lt_or_ge v u with
  | Or.inl h => by
    rw [E213.Tactic.NatHelper.max_eq_left_pure (Nat.le_of_lt h)]
    exact hu
  | Or.inr h => by
    rw [E213.Tactic.NatHelper.max_comm_pure,
        E213.Tactic.NatHelper.max_eq_left_pure h]
    exact hv

/-- ★★ **Soundness**: every member of `enumTreeDepth n` is a
    canonical Tree of depth ≤ n. -/
theorem enum_members : ∀ n, ∀ t, t ∈ enumTreeDepth n →
    t.canonical = true ∧ t.depth ≤ n
  | 0, t, ht => by
    cases ht with
    | head => exact ⟨rfl, Nat.le_refl 0⟩
    | tail _ h =>
      cases h with
      | head => exact ⟨rfl, Nat.le_refl 0⟩
      | tail _ h' => exact absurd h' (fun h => nomatch h)
  | n + 1, t, ht => by
    cases E213.Tactic.List213.mem_append_iff ht with
    | inl h =>
      cases h with
      | head => exact ⟨rfl, Nat.zero_le _⟩
      | tail _ h' =>
        cases h' with
        | head => exact ⟨rfl, Nat.zero_le _⟩
        | tail _ h'' => exact absurd h'' (fun h => nomatch h)
    | inr h =>
      have ⟨x, y, he, hx, hy, hc⟩ :=
        newSlashes_mem_char (enum_pairwise n) h
      have ⟨hxc, hxd⟩ := enum_members n x hx
      have ⟨hyc, hyd⟩ := enum_members n y hy
      subst he
      refine ⟨?_, ?_⟩
      · show (x.canonical && y.canonical &&
            (match Tree.cmp x y with | .lt => true | _ => false)) = true
        rw [hxc, hyc, hc]
        rfl
      · show 1 + Nat.max x.depth y.depth ≤ n + 1
        rw [Nat.add_comm 1 (Nat.max x.depth y.depth)]
        exact Nat.succ_le_succ (max_le_both hxd hyd)

/-- ★★ **Completeness**: every canonical Tree of depth ≤ n is
    listed. -/
theorem enum_complete : ∀ (n : Nat) (t : Tree),
    t.canonical = true → t.depth ≤ n → t ∈ enumTreeDepth n
  | 0, .a, _, _ => .head _
  | 0, .b, _, _ => .tail _ (.head _)
  | 0, .slash x y, _, hd => by
    have hd' : 1 + Nat.max x.depth y.depth ≤ 0 := hd
    rw [Nat.add_comm 1 (Nat.max x.depth y.depth)] at hd'
    exact absurd hd' (Nat.not_succ_le_zero _)
  | n + 1, .a, _, _ => .head _
  | n + 1, .b, _, _ => .tail _ (.head _)
  | n + 1, .slash x y, hc, hd => by
    have ⟨hxy, hcmp'⟩ := Bool.and_eq_true_to_pair hc
    have ⟨hxc, hyc⟩ := Bool.and_eq_true_to_pair hxy
    have hcmp : Tree.cmp x y = .lt := by
      cases hcm : Tree.cmp x y with
      | lt => rfl
      | eq => rw [hcm] at hcmp'; exact Bool.noConfusion hcmp'
      | gt => rw [hcm] at hcmp'; exact Bool.noConfusion hcmp'
    have hmax : Nat.max x.depth y.depth ≤ n := by
      have hd' : 1 + Nat.max x.depth y.depth ≤ n + 1 := hd
      rw [Nat.add_comm 1 (Nat.max x.depth y.depth)] at hd'
      exact Nat.le_of_succ_le_succ hd'
    have hx := enum_complete n x hxc
      (Nat.le_trans (E213.Tactic.NatHelper.le_max_left _ _) hmax)
    have hy := enum_complete n y hyc
      (Nat.le_trans (E213.Tactic.NatHelper.le_max_right _ _) hmax)
    exact E213.Tactic.List213.mem_append_right _
      (mem_newSlashes hcmp (enum_pairwise n) hx hy)

/-- ★★★ **Honest counting capstone**: `enumTreeDepth n` lists
    exactly the canonical Trees of depth ≤ n, without repetition,
    and its length is `rawCount n`.  So the recurrence values
    `2, 3, 5, 12, 68, …` genuinely count the canonical Raw
    population of depth ≤ n — membership, Nodup, and length in one
    bundle. -/
theorem honest_count (n : Nat) :
    (∀ t : Tree, t ∈ enumTreeDepth n ↔ t.canonical = true ∧ t.depth ≤ n)
    ∧ (enumTreeDepth n).Nodup
    ∧ (enumTreeDepth n).length
        = E213.Lib.Math.Foundations.UniverseChain.RawRecurrence.rawCount n := by
  refine ⟨fun t => ⟨enum_members n t,
      fun h => enum_complete n t h.1 h.2⟩, ?_, enumeration_capstone.1 n⟩
  exact pairwise_imp
    (fun u v huv he => by
      have huv' : Tree.cmp u v = .lt := huv
      rw [he, Tree.cmp_self_eq] at huv'
      exact Ordering.noConfusion huv')
    (enum_pairwise n)

end E213.Lib.Math.Foundations.UniverseChain.RawEnumeration
