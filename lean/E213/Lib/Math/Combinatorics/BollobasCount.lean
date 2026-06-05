import E213.Lib.Math.Combinatorics.BollobasSetPair

/-!
# The Bollobás favour-count injection (∅-axiom) — discharging the last rung

Builds the geometric lower bound `favourCountTarget n a b ≤ #{orderings
favouring (A,B)}`, the lone remaining rung of `BollobasSetPair.bollobas_of_count`
(its arithmetic is already discharged).  A favouring ordering is built as
`weave mask (σ_A ++ σ_B) σ_R`: interleave an ordering of `A`'s positions then
`B`'s positions into the `mask`-true slots, with an ordering of the rest into the
false slots.  This is the ordering analogue of `SpernerChains.chain_low`.
-/

namespace E213.Lib.Math.Combinatorics.BollobasCount

open E213.Lib.Math.Combinatorics.Sperner (cardB beq_self)
open E213.Lib.Math.Combinatorics.SpernerChains
  (cardB_le_length lperm_cons_append elemNat elemNat_eq_true_of_mem mem_of_elemNat
   truePos idxList)
open E213.Lib.Math.Combinatorics.BollobasSetPair
  (before before_x before_y before_rec favours listAll)
open E213.Tactic.List213 (mem_append_left mem_append_right)
open E213.Lib.Math.Combinatorics.Permutations

/-! ## §1 — `weave` and its permutation property -/

/-- `(a + 1) + b = (a + b) + 1`, propext-free (core `Nat.add_right_comm` carries
    `propext`). -/
theorem succ_add_pure (a b : Nat) : (a + 1) + b = (a + b) + 1 := Nat.succ_add a b

/-- `n + 1 ≠ 0`, propext-free (core `Nat.succ_ne_zero` carries `propext`). -/
theorem succ_ne_zero_pure {n : Nat} : n + 1 ≠ 0 := fun h => Nat.noConfusion h

/-- `weave mask xs ys`: emit the next `xs`-element at each `true` of `mask`, the
    next `ys`-element at each `false`. -/
def weave : List Bool → List Nat → List Nat → List Nat
  | [], _, _ => []
  | true :: m, x :: xs, ys => x :: weave m xs ys
  | false :: m, xs, y :: ys => y :: weave m xs ys
  | true :: m, [], ys => weave m [] ys
  | false :: m, xs, [] => weave m xs []

/-- When the mask's `true`/`false` counts match `|xs|`/`|ys|`, `weave` is a
    rearrangement of `xs ++ ys`. -/
theorem weave_perm :
    ∀ (m : List Bool) (xs ys : List Nat),
      cardB m = xs.length → m.length = xs.length + ys.length →
      LPerm (weave m xs ys) (xs ++ ys)
  | [], xs, ys, ht, hl => by
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons a xs' => exact absurd ht.symm (succ_ne_zero_pure)
      have hys : ys = [] := by
        cases ys with
        | nil => rfl
        | cons b ys' =>
            subst hxs
            exact absurd hl (succ_ne_zero_pure ∘ Eq.symm)
      subst hxs hys
      exact LPerm.nil
  | true :: m, [], ys, ht, _ => absurd ht (succ_ne_zero_pure)
  | false :: m, xs, [], ht, hl => by
      exfalso
      have hl' : m.length + 1 = xs.length := hl
      have ht' : cardB m = xs.length := ht
      have hle : cardB m ≤ m.length := cardB_le_length m
      rw [ht', ← hl'] at hle
      exact Nat.not_succ_le_self _ hle
  | true :: m, x :: xs, ys, ht, hl => by
      have ht' : cardB m = xs.length := Nat.succ.inj ht
      have hl' : m.length = xs.length + ys.length := by
        have h : m.length + 1 = (xs.length + ys.length) + 1 := by
          have hh : m.length + 1 = (xs.length + 1) + ys.length := hl
          rw [succ_add_pure xs.length ys.length] at hh
          exact hh
        exact Nat.succ.inj h
      have ih := weave_perm m xs ys ht' hl'
      show LPerm (x :: weave m xs ys) (x :: (xs ++ ys))
      exact LPerm.cons x ih
  | false :: m, xs, y :: ys, ht, hl => by
      have ht' : cardB m = xs.length := ht
      have hl' : m.length = xs.length + ys.length := Nat.succ.inj hl
      have ih := weave_perm m xs ys ht' hl'
      show LPerm (y :: weave m xs ys) (xs ++ y :: ys)
      exact LPerm.trans (LPerm.cons y ih) (lperm_cons_append y xs ys)

/-! ## §2 — order preservation: the woven ordering is favouring -/

/-- `a ≠ b → Nat.beq a b = false`. -/
theorem bne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

/-- A front-segment element precedes a back-segment one: if `x ∈ p`, `y ∉ p`,
    `y ∈ s`, then `x` is before `y` in `p ++ s`. -/
theorem before_append_mem : ∀ (p s : List Nat) (x y : Nat),
    x ∈ p → y ∉ p → y ∈ s → before (p ++ s) x y = true
  | [], _, x, _, hx, _, _ => absurd hx (List.not_mem_nil x)
  | z :: p', s, x, y, hx, hy, hys => by
      have hyz : y ≠ z := fun h => hy (h ▸ List.Mem.head _)
      have hyp' : y ∉ p' := fun h => hy (List.Mem.tail _ h)
      have hzy : Nat.beq z y = false := bne (fun h => hyz h.symm)
      show before (z :: (p' ++ s)) x y = true
      cases hzx : Nat.beq z x with
      | true =>
          rw [before_x (p' ++ s) hzx]
          exact elemNat_eq_true_of_mem (mem_append_right p' hys)
      | false =>
          have hxp' : x ∈ p' := by
            cases hx with
            | head => rw [beq_self] at hzx; exact Bool.noConfusion hzx
            | tail _ h' => exact h'
          rw [before_rec (p' ++ s) hzx hzy]
          exact before_append_mem p' s x y hxp' hyp' hys

/-- `weave` preserves the order of `xs`: anything before-`xs` is before-`weave`
    (the `ys`-elements, absent from the comparison, do not interfere). -/
theorem weave_preserves_before :
    ∀ (m : List Bool) (xs ys : List Nat) (u v : Nat),
      cardB m = xs.length → m.length = xs.length + ys.length →
      before xs u v = true → u ∉ ys → v ∉ ys →
      before (weave m xs ys) u v = true
  | [], xs, _, u, v, ht, _, hb, _, _ => by
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons a xs' => exact absurd ht.symm (succ_ne_zero_pure)
      rw [hxs] at hb
      exact Bool.noConfusion hb
  | true :: m, [], _, _, _, ht, _, _, _, _ => absurd ht (succ_ne_zero_pure)
  | false :: m, xs, [], _, _, ht, hl, _, _, _ => by
      exfalso
      have hl' : m.length + 1 = xs.length := hl
      have ht' : cardB m = xs.length := ht
      have hle : cardB m ≤ m.length := cardB_le_length m
      rw [ht', ← hl'] at hle
      exact Nat.not_succ_le_self _ hle
  | true :: m, x :: xs, ys, u, v, ht, hl, hb, hu, hv => by
      have ht' : cardB m = xs.length := Nat.succ.inj ht
      have hl' : m.length = xs.length + ys.length := by
        have h : m.length + 1 = (xs.length + ys.length) + 1 := by
          have hh : m.length + 1 = (xs.length + 1) + ys.length := hl
          rw [succ_add_pure xs.length ys.length] at hh; exact hh
        exact Nat.succ.inj h
      show before (x :: weave m xs ys) u v = true
      cases hxu : Nat.beq x u with
      | true =>
          rw [before_x (weave m xs ys) hxu]
          rw [before_x xs hxu] at hb
          have hvxs : v ∈ xs := mem_of_elemNat hb
          exact elemNat_eq_true_of_mem
            (mem_of_lperm (LPerm.symm (weave_perm m xs ys ht' hl')) (mem_append_left hvxs))
      | false =>
          cases hxv : Nat.beq x v with
          | true => rw [before_y xs hxu hxv] at hb; exact Bool.noConfusion hb
          | false =>
              rw [before_rec (weave m xs ys) hxu hxv]
              rw [before_rec xs hxu hxv] at hb
              exact weave_preserves_before m xs ys u v ht' hl' hb hu hv
  | false :: m, xs, y :: ys, u, v, ht, hl, hb, hu, hv => by
      have ht' : cardB m = xs.length := ht
      have hl' : m.length = xs.length + ys.length := Nat.succ.inj hl
      have hyu : Nat.beq y u = false := by
        apply bne; intro h; exact hu (h ▸ List.Mem.head ys)
      have hyv : Nat.beq y v = false := by
        apply bne; intro h; exact hv (h ▸ List.Mem.head ys)
      have hu' : u ∉ ys := fun h => hu (List.Mem.tail _ h)
      have hv' : v ∉ ys := fun h => hv (List.Mem.tail _ h)
      show before (y :: weave m xs ys) u v = true
      rw [before_rec (weave m xs ys) hyu hyv]
      exact weave_preserves_before m xs ys u v ht' hl' hb hu' hv'

/-- `listAll` from a pointwise truth (the introduction dual of
    `BollobasSetPair.listAll_mem`). -/
theorem listAll_intro {p : Nat → Bool} :
    ∀ {l : List Nat}, (∀ x, x ∈ l → p x = true) → listAll p l = true
  | [], _ => rfl
  | a :: l, h => by
      show (p a && listAll p l) = true
      rw [h a (List.Mem.head _)]
      exact listAll_intro (fun x hx => h x (List.Mem.tail _ hx))

/-! ## §3 — `weave_favours`: the construction lands in the favouring set

A woven ordering — orderings of `A`'s then `B`'s positions interleaved (via
`mask`) with an ordering of the rest `R` — favours `(A,B)`: every `A`-position
precedes every `B`-position.  This is the geometric heart of the count; what
remains (a future session) is purely the *enumeration* — that there are exactly
`favourCountTarget` distinct such orderings. -/

/-- ★ **The woven ordering favours `(A,B)`.**  Given orderings `σA, σB, σR` of the
    `A`-, `B`-, `R`-positions (mutually disjoint), and a mask with the matching
    `true`/`false` counts, `weave mask (σA ++ σB) σR` is a favouring ordering. -/
theorem weave_favours {n : Nat} (A B : List Bool) (mask : List Bool)
    (σA σB σR R : List Nat)
    (hσA : σA ∈ perms (truePos A (idxList n)))
    (hσB : σB ∈ perms (truePos B (idxList n)))
    (hσR : σR ∈ perms R)
    (hAB : ∀ z, z ∈ truePos A (idxList n) → z ∈ truePos B (idxList n) → False)
    (hAR : ∀ z, z ∈ truePos A (idxList n) → z ∈ R → False)
    (hBR : ∀ z, z ∈ truePos B (idxList n) → z ∈ R → False)
    (hc1 : cardB mask = (σA ++ σB).length)
    (hc2 : mask.length = (σA ++ σB).length + σR.length) :
    favours n (weave mask (σA ++ σB) σR) A B = true := by
  -- membership transport along the orderings
  have memA : ∀ z, z ∈ truePos A (idxList n) → z ∈ σA :=
    fun z hz => mem_of_lperm (LPerm.symm (perms_sound _ σA hσA)) hz
  have memB : ∀ z, z ∈ truePos B (idxList n) → z ∈ σB :=
    fun z hz => mem_of_lperm (LPerm.symm (perms_sound _ σB hσB)) hz
  have inA' : ∀ z, z ∈ σA → z ∈ truePos A (idxList n) :=
    fun z hz => mem_of_lperm (perms_sound _ σA hσA) hz
  have inR' : ∀ z, z ∈ σR → z ∈ R := fun z hz => mem_of_lperm (perms_sound _ σR hσR) hz
  refine listAll_intro (fun x hx => listAll_intro (fun y hy => ?_))
  -- x ∈ A-pos, y ∈ B-pos; show before (woven) x y
  have hxA : x ∈ σA := memA x hx
  have hyB : y ∈ σB := memB y hy
  have hynA : y ∉ σA := fun hz => hAB y (inA' y hz) hy
  have hbase : before (σA ++ σB) x y = true := before_append_mem σA σB x y hxA hynA hyB
  have hxR : x ∉ σR := fun hz => hAR x hx (inR' x hz)
  have hyR : y ∉ σR := fun hz => hBR y hy (inR' y hz)
  exact weave_preserves_before mask (σA ++ σB) σR x y hc1 hc2 hbase hxR hyR

end E213.Lib.Math.Combinatorics.BollobasCount
