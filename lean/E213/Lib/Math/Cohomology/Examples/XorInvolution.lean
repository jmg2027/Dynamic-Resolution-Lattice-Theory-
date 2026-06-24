import E213.Meta.Tactic.List213

/-!
# Abstract XOR-fold involution cancellation (∅-axiom)

A `Bool`/ℤ-2 XOR-fold over a `Nodup` list cancels to `false` when the index set
carries a **fixed-point-free involution that preserves the summand**:

    Nodup l → (g closed on l) → (∀ x∈l, g x ≠ x) → (∀ x∈l, g (g x) = x)
            → (∀ x∈l, f (g x) = f x) → xorFold f l = false.

This is "a fixed-point-free involution ⟹ even cardinality" in XOR form.  It is
the reusable engine for the dimension-free `δ²=0`
(`research-notes/frontiers/the_dimension_free_dsquared.md`): the double
coboundary is a XOR over the `(a,b)` removal grid, paired by the simplicial
commutation involution `(a,b) ↦ (b+1,a)` (`ColexRoundTrip.eraseIdx_eraseIdx_comm`).

Proof: strong induction on length, peeling a matched pair `{x, g x}` each step
(via `List.filter`, which is propext-free) and cancelling `f x ⊕ f (g x) = f x ⊕
f x = false`.  Everything ∅-axiom — `List.filter` + the pure `List213` filter
lemmas, no `propext`/`Quot.sound`.
-/

namespace E213.Lib.Math.Cohomology.Examples.XorInvolution

open E213.Tactic.List213 (mem_filter mem_filter_of nodup_filter
  length_filter_le length_filter_lt_of_mem)

/-! ## Bool XOR algebra (propext-free, by case-bashing) -/

private theorem xor_false (b : Bool) : xor b false = b := by cases b <;> rfl
private theorem false_xor (b : Bool) : xor false b = b := by cases b <;> rfl
private theorem xor_self (b : Bool) : xor b b = false := by cases b <;> rfl
private theorem xor_assoc (a b c : Bool) : xor (xor a b) c = xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ## `xorFold` and its structural lemmas -/

/-- XOR of `f` over a list (ℤ/2 sum). -/
def xorFold {α : Type _} (f : α → Bool) : List α → Bool
  | []      => false
  | x :: xs => xor (f x) (xorFold f xs)

/-- `xorFold` of a singleton. -/
private theorem xorFold_single {α : Type _} (f : α → Bool) (a : α) :
    xorFold f [a] = f a := xor_false (f a)

/-- `List.filter` cons reduction, `p x = true`. -/
private theorem filter_cons_true {α : Type _} (p : α → Bool) (x : α) (xs : List α)
    (h : p x = true) : (x :: xs).filter p = x :: xs.filter p := by
  show (match p x with | true => x :: xs.filter p | false => xs.filter p) = x :: xs.filter p
  exact h ▸ rfl

/-- `List.filter` cons reduction, `p x = false`. -/
private theorem filter_cons_false {α : Type _} (p : α → Bool) (x : α) (xs : List α)
    (h : p x = false) : (x :: xs).filter p = xs.filter p := by
  show (match p x with | true => x :: xs.filter p | false => xs.filter p) = xs.filter p
  exact h ▸ rfl

/-- **Partition.**  `xorFold` splits along any Bool predicate `p`. -/
private theorem xorFold_partition {α : Type _} (f : α → Bool) (p : α → Bool) :
    ∀ (l : List α),
      xorFold f l
        = xor (xorFold f (l.filter p)) (xorFold f (l.filter (fun a => !p a)))
  | [] => rfl
  | x :: xs => by
    cases hpx : p x with
    | true =>
      have hf : (x :: xs).filter p = x :: xs.filter p := filter_cons_true p x xs hpx
      have hg : (x :: xs).filter (fun a => !p a) = xs.filter (fun a => !p a) :=
        filter_cons_false (fun a => !p a) x xs (by show (!p x) = false; exact hpx ▸ rfl)
      have eA : xorFold f ((x :: xs).filter p)
                  = xor (f x) (xorFold f (xs.filter p)) := congrArg (xorFold f) hf
      have eB : xorFold f ((x :: xs).filter (fun a => !p a))
                  = xorFold f (xs.filter (fun a => !p a)) := congrArg (xorFold f) hg
      calc xorFold f (x :: xs)
          = xor (f x) (xorFold f xs) := rfl
        _ = xor (f x) (xor (xorFold f (xs.filter p))
                           (xorFold f (xs.filter (fun a => !p a)))) :=
              congrArg (xor (f x)) (xorFold_partition f p xs)
        _ = xor (xor (f x) (xorFold f (xs.filter p)))
                (xorFold f (xs.filter (fun a => !p a))) :=
              (xor_assoc (f x) _ _).symm
        _ = xor (xorFold f ((x :: xs).filter p))
                (xorFold f ((x :: xs).filter (fun a => !p a))) :=
              (congrArg (fun z => xor z (xorFold f (xs.filter (fun a => !p a)))) eA.symm).trans
                (congrArg (xor (xorFold f ((x :: xs).filter p))) eB.symm)
    | false =>
      have hf : (x :: xs).filter p = xs.filter p := filter_cons_false p x xs hpx
      have hg : (x :: xs).filter (fun a => !p a) = x :: xs.filter (fun a => !p a) :=
        filter_cons_true (fun a => !p a) x xs (by show (!p x) = true; exact hpx ▸ rfl)
      have eA : xorFold f ((x :: xs).filter p) = xorFold f (xs.filter p) :=
        congrArg (xorFold f) hf
      have eB : xorFold f ((x :: xs).filter (fun a => !p a))
                  = xor (f x) (xorFold f (xs.filter (fun a => !p a))) :=
        congrArg (xorFold f) hg
      calc xorFold f (x :: xs)
          = xor (f x) (xorFold f xs) := rfl
        _ = xor (f x) (xor (xorFold f (xs.filter p))
                           (xorFold f (xs.filter (fun a => !p a)))) :=
              congrArg (xor (f x)) (xorFold_partition f p xs)
        _ = xor (xorFold f (xs.filter p))
                (xor (f x) (xorFold f (xs.filter (fun a => !p a)))) := by
              cases (f x) <;> cases (xorFold f (xs.filter p)) <;>
                cases (xorFold f (xs.filter (fun a => !p a))) <;> rfl
        _ = xor (xorFold f ((x :: xs).filter p))
                (xorFold f ((x :: xs).filter (fun a => !p a))) :=
              (congrArg (fun z => xor z (xor (f x) (xorFold f (xs.filter (fun a => !p a))))) eA.symm).trans
                (congrArg (xor (xorFold f ((x :: xs).filter p))) eB.symm)

/-! ## Filtering to a single occurrence -/

/-- An absent element filters to nothing. -/
private theorem filter_eq_nil_of_not_mem {α : Type _} [DecidableEq α] (x : α) :
    ∀ (l : List α), x ∉ l → l.filter (fun a => decide (a = x)) = []
  | [],      _   => rfl
  | a :: l', hnm => by
    have hxa : x ≠ a := fun h => hnm (h ▸ List.Mem.head l')
    have hpa : decide (a = x) = false := decide_eq_false (fun h => hxa h.symm)
    have hf : (a :: l').filter (fun a => decide (a = x))
                = l'.filter (fun a => decide (a = x)) :=
      filter_cons_false _ a l' hpa
    have hnm' : x ∉ l' := fun h => hnm (List.Mem.tail a h)
    exact hf.trans (filter_eq_nil_of_not_mem x l' hnm')

/-- In a `Nodup` list, an occurring element filters to exactly `[x]`. -/
private theorem filter_eq_singleton {α : Type _} [DecidableEq α] (x : α) :
    ∀ (l : List α), l.Nodup → x ∈ l → l.filter (fun a => decide (a = x)) = [x]
  | [],      _,      hmem => nomatch hmem
  | a :: l', hnodup, hmem => by
    cases hnodup with
    | cons hrel htail =>
      by_cases hax : a = x
      · -- a = x: head matches, tail has no x (Nodup), so filters to []
        have hpa : decide (a = x) = true := decide_eq_true hax
        have hf : (a :: l').filter (fun a => decide (a = x))
                    = a :: l'.filter (fun a => decide (a = x)) :=
          filter_cons_true _ a l' hpa
        have hxnm : x ∉ l' := fun h => (hrel x h) hax
        have htail_nil : l'.filter (fun a => decide (a = x)) = [] :=
          filter_eq_nil_of_not_mem x l' hxnm
        -- a :: [] = [x] since a = x
        exact hf.trans ((congrArg (a :: ·) htail_nil).trans (congrArg (· :: []) hax))
      · -- a ≠ x: head drops, recurse on tail
        have hpa : decide (a = x) = false := decide_eq_false hax
        have hf : (a :: l').filter (fun a => decide (a = x))
                    = l'.filter (fun a => decide (a = x)) :=
          filter_cons_false _ a l' hpa
        have hxl' : x ∈ l' := by
          cases hmem with
          | head => exact absurd rfl hax
          | tail _ h => exact h
        exact hf.trans (filter_eq_singleton x l' htail hxl')

/-- `xorFold` of the `(= x)`-filter of a `Nodup` list containing `x` is `f x`. -/
private theorem xorFold_filter_eq {α : Type _} [DecidableEq α] (f : α → Bool)
    (x : α) (l : List α) (hnodup : l.Nodup) (hmem : x ∈ l) :
    xorFold f (l.filter (fun a => decide (a = x))) = f x :=
  (congrArg (xorFold f) (filter_eq_singleton x l hnodup hmem)).trans (xorFold_single f x)

/-! ## The involution-cancellation lemma -/

/-- Fuel-bounded core: induction on a length bound `n`. -/
private theorem xorFold_involution_aux {α : Type _} [DecidableEq α]
    (f : α → Bool) (g : α → α) :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.Nodup →
      (∀ x ∈ l, g x ∈ l) → (∀ x ∈ l, g x ≠ x) → (∀ x ∈ l, g (g x) = x) →
      (∀ x ∈ l, f (g x) = f x) → xorFold f l = false
  | 0, l, hlen, _, _, _, _, _ => by
    cases l with
    | nil => rfl
    | cons a as => exact absurd hlen (Nat.not_succ_le_zero as.length)
  | n + 1, l, hlen, hnodup, hclosed, hfpf, hinv, hpres => by
    cases l with
    | nil => rfl
    | cons x xs =>
      -- the partner of x
      have hxmem : x ∈ x :: xs := List.Mem.head xs
      have hgx_mem : g x ∈ x :: xs := hclosed x hxmem
      have hgx_ne : g x ≠ x := hfpf x hxmem
      -- l₁ = l with x removed
      let l₁ := (x :: xs).filter (fun a => !decide (a = x))
      have hgx_in_l₁ : g x ∈ l₁ :=
        mem_filter_of hgx_mem (by
          show (!decide (g x = x)) = true
          exact congrArg (! ·) (decide_eq_false hgx_ne))
      have hnodup₁ : l₁.Nodup := nodup_filter _ hnodup
      -- xorFold over l = f x ⊕ xorFold over l₁
      have hpart1 : xorFold f (x :: xs)
          = xor (xorFold f ((x :: xs).filter (fun a => decide (a = x)))) (xorFold f l₁) :=
        xorFold_partition f (fun a => decide (a = x)) (x :: xs)
      have hfx : xorFold f ((x :: xs).filter (fun a => decide (a = x))) = f x :=
        xorFold_filter_eq f x (x :: xs) hnodup hxmem
      have hstep1 : xorFold f (x :: xs) = xor (f x) (xorFold f l₁) :=
        hpart1.trans (congrArg (fun z => xor z (xorFold f l₁)) hfx)
      -- l₂ = l₁ with g x removed
      let l₂ := l₁.filter (fun a => !decide (a = g x))
      have hnodup₂ : l₂.Nodup := nodup_filter _ hnodup₁
      have hpart2 : xorFold f l₁
          = xor (xorFold f (l₁.filter (fun a => decide (a = g x)))) (xorFold f l₂) :=
        xorFold_partition f (fun a => decide (a = g x)) l₁
      have hfgx : xorFold f (l₁.filter (fun a => decide (a = g x))) = f (g x) :=
        xorFold_filter_eq f (g x) l₁ hnodup₁ hgx_in_l₁
      have hstep2 : xorFold f l₁ = xor (f (g x)) (xorFold f l₂) :=
        hpart2.trans (congrArg (fun z => xor z (xorFold f l₂)) hfgx)
      -- membership facts for l₂: y ∈ l₂ → y ∈ l ∧ y ≠ x ∧ y ≠ g x
      have hmem₂ : ∀ y ∈ l₂, y ∈ (x :: xs) ∧ y ≠ x ∧ y ≠ g x := by
        intro y hy
        obtain ⟨hy₁, hne_gx⟩ := mem_filter hy
        obtain ⟨hy₀, hne_x⟩ := mem_filter hy₁
        refine ⟨hy₀, ?_, ?_⟩
        · exact fun h => Bool.noConfusion (hne_x.symm.trans (congrArg (! ·) (decide_eq_true h)))
        · exact fun h => Bool.noConfusion (hne_gx.symm.trans (congrArg (! ·) (decide_eq_true h)))
      -- l₂ satisfies the involution hypotheses
      have hclosed₂ : ∀ y ∈ l₂, g y ∈ l₂ := by
        intro y hy
        obtain ⟨hy₀, hyx, hygx⟩ := hmem₂ y hy
        have hgy_mem : g y ∈ (x :: xs) := hclosed y hy₀
        have hgy_x : g y ≠ x :=
          fun h => hygx ((hinv y hy₀).symm.trans (congrArg g h))
        have hgy_gx : g y ≠ g x :=
          fun h => hyx ((hinv y hy₀).symm.trans ((congrArg g h).trans (hinv x hxmem)))
        refine mem_filter_of (mem_filter_of hgy_mem ?_) ?_
        · show (!decide (g y = x)) = true
          exact congrArg (! ·) (decide_eq_false hgy_x)
        · show (!decide (g y = g x)) = true
          exact congrArg (! ·) (decide_eq_false hgy_gx)
      have hfpf₂ : ∀ y ∈ l₂, g y ≠ y := fun y hy => hfpf y (hmem₂ y hy).1
      have hinv₂ : ∀ y ∈ l₂, g (g y) = y := fun y hy => hinv y (hmem₂ y hy).1
      have hpres₂ : ∀ y ∈ l₂, f (g y) = f y := fun y hy => hpres y (hmem₂ y hy).1
      -- length bound: l₂.length < l₁.length < l.length ≤ n+1, so l₂.length ≤ n
      have hlt1 : l₁.length < (x :: xs).length :=
        length_filter_lt_of_mem hxmem (by
          show (!decide (x = x)) = false
          exact congrArg (! ·) (decide_eq_true rfl))
      have hle2 : l₂.length ≤ l₁.length := length_filter_le _ l₁
      have hl₂_le : l₂.length ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_le_of_lt hle2 (Nat.lt_of_lt_of_le hlt1 hlen))
      have hC : xorFold f l₂ = false :=
        xorFold_involution_aux f g n l₂ hl₂_le hnodup₂ hclosed₂ hfpf₂ hinv₂ hpres₂
      -- assemble: xorFold l = f x ⊕ (f (g x) ⊕ 0) = (f x ⊕ f (g x)) ⊕ 0 = false
      have hfeq : f (g x) = f x := hpres x hxmem
      calc xorFold f (x :: xs)
          = xor (f x) (xorFold f l₁) := hstep1
        _ = xor (f x) (xor (f (g x)) (xorFold f l₂)) := congrArg (xor (f x)) hstep2
        _ = xor (f x) (xor (f x) (xorFold f l₂)) :=
              congrArg (fun z => xor (f x) (xor z (xorFold f l₂))) hfeq
        _ = xor (xor (f x) (f x)) (xorFold f l₂) := (xor_assoc (f x) (f x) (xorFold f l₂)).symm
        _ = xor false (xorFold f l₂) := congrArg (fun z => xor z (xorFold f l₂)) (xor_self (f x))
        _ = xorFold f l₂ := false_xor _
        _ = false := hC

/-- ★★★ **XOR-fold involution cancellation.**  A ℤ/2 XOR-fold over a `Nodup`
    list is `false` whenever the index set carries a fixed-point-free involution
    `g` that preserves the summand (`f ∘ g = f`).  "A fixed-point-free involution
    has even cardinality", in XOR form — the engine for the `δ²=0` 2-to-1 pairing. -/
theorem xorFold_involution {α : Type _} [DecidableEq α]
    (f : α → Bool) (g : α → α) (l : List α) (hnodup : l.Nodup)
    (hclosed : ∀ x ∈ l, g x ∈ l) (hfpf : ∀ x ∈ l, g x ≠ x)
    (hinv : ∀ x ∈ l, g (g x) = x) (hpres : ∀ x ∈ l, f (g x) = f x) :
    xorFold f l = false :=
  xorFold_involution_aux f g l.length l (Nat.le_refl _) hnodup hclosed hfpf hinv hpres

end E213.Lib.Math.Cohomology.Examples.XorInvolution
