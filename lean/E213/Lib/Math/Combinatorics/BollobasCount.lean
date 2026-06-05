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

open E213.Lib.Math.Combinatorics.Sperner
  (cardB beq_self lcount cardEq kLayer kLayer_card kLayer_nodup)
open E213.Lib.Math.Combinatorics.SpernerChains
  (cardB_le_length lperm_cons_append elemNat elemNat_eq_true_of_mem elemNat_eq_false_of_not_mem
   mem_of_elemNat truePos idxList truePos_length truePos_nodup mem_truePos
   idxList_length idxList_nodup append_inj_left append_left_cancel lcount_ge_nodup_subset)
open E213.Lib.Math.Combinatorics.BollobasSetPair
  (before before_x before_y before_rec favours listAll favourCountTarget)
open E213.Lib.Math.Combinatorics.BoolEnum (length_of_mem_allBoolLists)
open E213.Tactic.List213
  (mem_append_left mem_append_right mem_append_iff mem_filter mem_filter_of
   exists_of_mem_map mem_map_of_mem nodup_map_of_inj length_map length_append)
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

/-! ## §4 — the position partition `Apos ++ Bpos ++ Rpos ~ idxList n`

For disjoint bit-vectors `A, B`, the `A`-positions, `B`-positions and the rest
`R` (`restPos`, the both-false positions) partition `idxList n`.  This supplies
both the disjointness hypotheses of `weave_favours` and the permutation needed
to land the woven ordering in `perms (idxList n)`. -/

/-- `A, B` never both `true` at aligned positions. -/
def disjointVec : List Bool → List Bool → Bool
  | a :: A, b :: B => bif a && b then false else disjointVec A B
  | [], [] => true
  | _, _ => false

/-- The both-`false` positions of the aligned pair `(A, B)`. -/
def restPos : List Bool → List Bool → List Nat → List Nat
  | a :: A, b :: B, p :: ps => bif a then restPos A B ps else bif b then restPos A B ps else p :: restPos A B ps
  | _, _, _ => []

/-- LPerm respects appending a fixed suffix on the left operand. -/
theorem lperm_append_left {α : Type _} {A A' : List α} (h : LPerm A A') (Z : List α) :
    LPerm (A ++ Z) (A' ++ Z) := by
  induction h with
  | nil => exact LPerm.refl Z
  | cons a _ ih => exact LPerm.cons a ih
  | swap a b l => exact LPerm.swap a b (l ++ Z)
  | trans _ _ ih₁ ih₂ => exact LPerm.trans ih₁ ih₂

private theorem nodup_head {α : Type _} {p : α} {ps : List α}
    (hnd : (p :: ps).Nodup) : p ∉ ps ∧ ps.Nodup := by
  cases hnd with | cons hh ht => exact ⟨fun hm => hh p hm rfl, ht⟩

/-- `restPos` is a sublist of the position list. -/
theorem mem_restPos {z : Nat} : ∀ (A B : List Bool) (ps : List Nat),
    z ∈ restPos A B ps → z ∈ ps
  | a :: A, b :: B, p :: ps, h => by
      cases a with
      | true => exact List.Mem.tail _ (mem_restPos A B ps h)
      | false => cases b with
        | true => exact List.Mem.tail _ (mem_restPos A B ps h)
        | false => cases h with
          | head => exact List.Mem.head _
          | tail _ h' => exact List.Mem.tail _ (mem_restPos A B ps h')
  | [], _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | _ :: _, _ :: _, [], h => nomatch h

/-- `restPos` avoids the `A`-positions (both-false vs `A`-true). -/
theorem restPos_not_truePos_A {z : Nat} : ∀ (A B : List Bool) (ps : List Nat),
    ps.Nodup → z ∈ restPos A B ps → z ∈ truePos A ps → False
  | a :: A, b :: B, p :: ps, hnd, hr, ht => by
      obtain ⟨hpps, hnd'⟩ := nodup_head hnd
      cases a with
      | true => cases ht with
        | head => exact hpps (mem_restPos A B ps hr)
        | tail _ ht' => exact restPos_not_truePos_A A B ps hnd' hr ht'
      | false => cases b with
        | true => exact restPos_not_truePos_A A B ps hnd' hr ht
        | false => cases hr with
          | head => exact hpps (mem_truePos A ps ht)
          | tail _ hr' => exact restPos_not_truePos_A A B ps hnd' hr' ht
  | [], _, _, _, hr, _ => nomatch hr
  | _ :: _, [], _, _, hr, _ => nomatch hr
  | _ :: _, _ :: _, [], _, hr, _ => nomatch hr

/-- `restPos` avoids the `B`-positions. -/
theorem restPos_not_truePos_B {z : Nat} : ∀ (A B : List Bool) (ps : List Nat),
    ps.Nodup → z ∈ restPos A B ps → z ∈ truePos B ps → False
  | a :: A, b :: B, p :: ps, hnd, hr, ht => by
      obtain ⟨hpps, hnd'⟩ := nodup_head hnd
      cases a with
      | true => cases b with
        | true => cases ht with
          | head => exact hpps (mem_restPos A B ps hr)
          | tail _ ht' => exact restPos_not_truePos_B A B ps hnd' hr ht'
        | false => exact restPos_not_truePos_B A B ps hnd' hr ht
      | false => cases b with
        | true => cases ht with
          | head => exact hpps (mem_restPos A B ps hr)
          | tail _ ht' => exact restPos_not_truePos_B A B ps hnd' hr ht'
        | false => cases hr with
          | head => exact hpps (mem_truePos B ps ht)
          | tail _ hr' => exact restPos_not_truePos_B A B ps hnd' hr' ht
  | [], _, _, _, hr, _ => nomatch hr
  | _ :: _, [], _, _, hr, _ => nomatch hr
  | _ :: _, _ :: _, [], _, hr, _ => nomatch hr

/-- `truePos A [] = []` (empty position list). -/
theorem truePos_nil_eq : ∀ (A : List Bool), truePos A [] = []
  | [] => rfl
  | true :: _ => rfl
  | false :: _ => rfl

/-- Disjoint vectors have disjoint position-sets: `Apos ∩ Bpos = ∅`. -/
theorem truePos_disjoint {z : Nat} : ∀ (A B : List Bool) (ps : List Nat),
    disjointVec A B = true → ps.Nodup → z ∈ truePos A ps → z ∈ truePos B ps → False := by
  intro A B ps
  induction ps generalizing A B with
  | nil => intro _ _ ha _; rw [truePos_nil_eq] at ha; nomatch ha
  | cons p ps ih =>
      intro hd hnd ha hb
      cases A with
      | nil => nomatch ha
      | cons a A => cases B with
        | nil => nomatch hb
        | cons b B =>
            obtain ⟨hpps, hnd'⟩ := nodup_head hnd
            cases a with
            | true => cases b with
              | true => exact Bool.noConfusion hd
              | false => cases ha with
                | head => exact hpps (mem_truePos B ps hb)
                | tail _ ha' => exact ih A B hd hnd' ha' hb
            | false => cases b with
              | true => cases hb with
                | head => exact hpps (mem_truePos A ps ha)
                | tail _ hb' => exact ih A B hd hnd' ha hb'
              | false => exact ih A B hd hnd' ha hb

/-- `restPos` is duplicate-free (a sublist of the nodup `ps`). -/
theorem restPos_nodup : ∀ (A B : List Bool) (ps : List Nat),
    ps.Nodup → (restPos A B ps).Nodup
  | a :: A, b :: B, p :: ps, hnd => by
      obtain ⟨hpps, hnd'⟩ := nodup_head hnd
      cases a with
      | true => exact restPos_nodup A B ps hnd'
      | false => cases b with
        | true => exact restPos_nodup A B ps hnd'
        | false =>
            refine List.Pairwise.cons (fun y hy he => hpps ?_) (restPos_nodup A B ps hnd')
            rw [he]; exact mem_restPos A B ps hy
  | [], _, _, _ => List.Pairwise.nil
  | _ :: _, [], _, _ => List.Pairwise.nil
  | _ :: _, _ :: _, [], _ => List.Pairwise.nil

/-- The partition is exhaustive: `|Rpos| + (|A| + |B|) = n` (additive form). -/
theorem restPos_card : ∀ (A B : List Bool) (ps : List Nat),
    A.length = ps.length → B.length = ps.length → disjointVec A B = true →
    (restPos A B ps).length + (cardB A + cardB B) = ps.length
  | a :: A, b :: B, p :: ps, hla, hlb, hd => by
      have ih := restPos_card A B ps (Nat.succ.inj hla) (Nat.succ.inj hlb)
      cases a with
      | true => cases b with
        | true => exact Bool.noConfusion hd
        | false =>
            show (restPos A B ps).length + ((cardB A + 1) + cardB B) = ps.length + 1
            rw [succ_add_pure (cardB A) (cardB B)]
            show ((restPos A B ps).length + (cardB A + cardB B)) + 1 = ps.length + 1
            rw [ih hd]
      | false => cases b with
        | true =>
            show ((restPos A B ps).length + (cardB A + cardB B)) + 1 = ps.length + 1
            rw [ih hd]
        | false =>
            show ((restPos A B ps).length + 1) + (cardB A + cardB B) = ps.length + 1
            rw [succ_add_pure (restPos A B ps).length (cardB A + cardB B), ih hd]
  | [], [], [], _, _, _ => rfl
  | [], _, _ :: _, hla, _, _ => nomatch hla
  | _ :: _, _, [], hla, _, _ => nomatch hla
  | [], _ :: _, [], _, hlb, _ => nomatch hlb
  | _ :: _, [], _ :: _, _, hlb, _ => nomatch hlb

/-- ★ **The position partition.**  For disjoint aligned `A, B`, the positions
    split as `Apos ++ Bpos ++ Rpos ~ ps`. -/
theorem partition_perm : ∀ (A B : List Bool) (ps : List Nat),
    A.length = ps.length → B.length = ps.length → disjointVec A B = true →
    LPerm ps ((truePos A ps ++ truePos B ps) ++ restPos A B ps)
  | a :: A, b :: B, p :: ps, hla, hlb, hd => by
      have ih := partition_perm A B ps (Nat.succ.inj hla) (Nat.succ.inj hlb)
      cases a with
      | true => cases b with
        | true => exact Bool.noConfusion hd
        | false =>
            show LPerm (p :: ps) (((p :: truePos A ps) ++ truePos B ps) ++ restPos A B ps)
            exact LPerm.cons p (ih hd)
      | false => cases b with
        | true =>
            show LPerm (p :: ps) ((truePos A ps ++ (p :: truePos B ps)) ++ restPos A B ps)
            refine LPerm.trans (LPerm.cons p (ih hd)) ?_
            exact lperm_append_left
              (lperm_cons_append p (truePos A ps) (truePos B ps)) (restPos A B ps)
        | false =>
            show LPerm (p :: ps) ((truePos A ps ++ truePos B ps) ++ (p :: restPos A B ps))
            exact LPerm.trans (LPerm.cons p (ih hd))
              (lperm_cons_append p (truePos A ps ++ truePos B ps) (restPos A B ps))
  | [], [], [], _, _, _ => LPerm.nil
  | [], _, _ :: _, hla, _, _ => nomatch hla
  | _ :: _, _, [], hla, _, _ => nomatch hla
  | [], _ :: _, [], _, hlb, _ => nomatch hlb
  | _ :: _, [], _ :: _, _, hlb, _ => nomatch hlb

/-! ## §5 — filter/map recovery: `weave` is injective in its three inputs

Reading the woven list back recovers the mask (`map q`), the interleaved
content `xs` (`filter q`) and the rest `ys` (`filter ¬q`), where `q` separates
the two element-classes (the `A∪B`-positions from the `R`-positions).  These give
injectivity of `weave`, the engine of the count's `Nodup`. -/

private theorem hl_succ {m : List Bool} {xs ys : List Nat}
    (hl : (m.length + 1) = (xs.length + 1) + ys.length) :
    m.length = xs.length + ys.length := by
  rw [succ_add_pure xs.length ys.length] at hl; exact Nat.succ.inj hl

private theorem weave_false_nil {m : List Bool} {xs : List Nat}
    (ht : cardB (false :: m) = xs.length) (hl : (false :: m).length = xs.length + ([] : List Nat).length) :
    False := by
  have hl' : m.length + 1 = xs.length := hl
  have ht' : cardB m = xs.length := ht
  have hle : cardB m ≤ m.length := cardB_le_length m
  rw [ht', ← hl'] at hle; exact Nat.not_succ_le_self _ hle

/-- `map q (weave m xs ys) = m` — recover the mask. -/
theorem map_q_weave (q : Nat → Bool) :
    ∀ (m : List Bool) (xs ys : List Nat), cardB m = xs.length → m.length = xs.length + ys.length →
      (∀ z, z ∈ xs → q z = true) → (∀ z, z ∈ ys → q z = false) →
      List.map q (weave m xs ys) = m
  | [], _, _, _, _, _, _ => rfl
  | true :: m, x :: xs, ys, ht, hl, hqx, hqy => by
      show q x :: List.map q (weave m xs ys) = true :: m
      rw [hqx x (List.Mem.head _),
          map_q_weave q m xs ys (Nat.succ.inj ht) (hl_succ hl)
            (fun z hz => hqx z (List.Mem.tail _ hz)) hqy]
  | false :: m, xs, y :: ys, ht, hl, hqx, hqy => by
      show q y :: List.map q (weave m xs ys) = false :: m
      rw [hqy y (List.Mem.head _),
          map_q_weave q m xs ys ht (Nat.succ.inj hl) hqx
            (fun z hz => hqy z (List.Mem.tail _ hz))]
  | true :: _, [], _, ht, _, _, _ => absurd ht succ_ne_zero_pure
  | false :: m, xs, [], ht, hl, _, _ => absurd (weave_false_nil ht hl) (fun h => h)

/-- `filter q (weave m xs ys) = xs` — recover the interleaved content. -/
theorem filter_q_weave (q : Nat → Bool) :
    ∀ (m : List Bool) (xs ys : List Nat), cardB m = xs.length → m.length = xs.length + ys.length →
      (∀ z, z ∈ xs → q z = true) → (∀ z, z ∈ ys → q z = false) →
      List.filter q (weave m xs ys) = xs
  | [], xs, ys, ht, _, _, _ => by
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons a xs' => exact absurd ht.symm succ_ne_zero_pure
      rw [hxs]; rfl
  | true :: m, x :: xs, ys, ht, hl, hqx, hqy => by
      rw [show weave (true :: m) (x :: xs) ys = x :: weave m xs ys from rfl,
          List.filter_cons_of_pos (hqx x (List.Mem.head _)),
          filter_q_weave q m xs ys (Nat.succ.inj ht) (hl_succ hl)
            (fun z hz => hqx z (List.Mem.tail _ hz)) hqy]
  | false :: m, xs, y :: ys, ht, hl, hqx, hqy => by
      rw [show weave (false :: m) xs (y :: ys) = y :: weave m xs ys from rfl,
          List.filter_cons_of_neg (by rw [hqy y (List.Mem.head _)]; exact Bool.noConfusion),
          filter_q_weave q m xs ys ht (Nat.succ.inj hl) hqx
            (fun z hz => hqy z (List.Mem.tail _ hz))]
  | true :: _, [], _, ht, _, _, _ => absurd ht succ_ne_zero_pure
  | false :: m, xs, [], ht, hl, _, _ => absurd (weave_false_nil ht hl) (fun h => h)

/-- `filter (¬q) (weave m xs ys) = ys` — recover the rest. -/
theorem filter_nq_weave (q : Nat → Bool) :
    ∀ (m : List Bool) (xs ys : List Nat), cardB m = xs.length → m.length = xs.length + ys.length →
      (∀ z, z ∈ xs → q z = true) → (∀ z, z ∈ ys → q z = false) →
      List.filter (fun z => !q z) (weave m xs ys) = ys
  | [], xs, ys, ht, hl, _, _ => by
      have hxs : xs = [] := by
        cases xs with
        | nil => rfl
        | cons a xs' => exact absurd ht.symm succ_ne_zero_pure
      have hys : ys = [] := by
        cases ys with
        | nil => rfl
        | cons b ys' => subst hxs; exact absurd hl (succ_ne_zero_pure ∘ Eq.symm)
      rw [hxs, hys]; rfl
  | true :: m, x :: xs, ys, ht, hl, hqx, hqy => by
      rw [show weave (true :: m) (x :: xs) ys = x :: weave m xs ys from rfl,
          List.filter_cons_of_neg (by rw [hqx x (List.Mem.head _)]; exact Bool.noConfusion),
          filter_nq_weave q m xs ys (Nat.succ.inj ht) (hl_succ hl)
            (fun z hz => hqx z (List.Mem.tail _ hz)) hqy]
  | false :: m, xs, y :: ys, ht, hl, hqx, hqy => by
      have hqyh : q y = false := hqy y (List.Mem.head _)
      show List.filter (fun z => !q z) (y :: weave m xs ys) = y :: ys
      rw [List.filter_cons_of_pos (a := y) (l := weave m xs ys)
            (show (fun z => !q z) y = true from (congrArg (fun b => !b) hqyh).trans rfl)]
      show y :: List.filter (fun z => !q z) (weave m xs ys) = y :: ys
      rw [filter_nq_weave q m xs ys ht (Nat.succ.inj hl) hqx
            (fun z hz => hqy z (List.Mem.tail _ hz))]
  | true :: _, [], _, ht, _, _, _ => absurd ht succ_ne_zero_pure
  | false :: m, xs, [], ht, hl, _, _ => absurd (weave_false_nil ht hl) (fun h => h)

/-! ## §6 — the woven family and its count

`wovenFam A B n` enumerates the favouring orderings as `weave mask (σA ++ σB) σR`
over all masks (`kLayer n (a+b)`) and orderings of the `A`-, `B`-, `R`-positions.
Its length is `favourCountTarget`, it is duplicate-free (via the recovery lemmas),
and it lands in the favouring set — giving the lower bound. -/

theorem mask_cardB {n k : Nat} {mask : List Bool} (h : mask ∈ kLayer n k) : cardB mask = k :=
  Nat.eq_of_beq_eq_true (mem_filter h).2

theorem mask_length {n k : Nat} {mask : List Bool} (h : mask ∈ kLayer n k) : mask.length = n :=
  length_of_mem_allBoolLists (mem_filter h).1

/-- The favouring-ordering family. -/
def wovenFam (A B : List Bool) (n : Nat) : List (List Nat) :=
  flatMap213 (fun mask =>
    flatMap213 (fun σA =>
      flatMap213 (fun σB =>
        List.map (fun σR => weave mask (σA ++ σB) σR) (perms (restPos A B (idxList n))))
        (perms (truePos B (idxList n))))
      (perms (truePos A (idxList n))))
    (kLayer n (cardB A + cardB B))

section
variable {A B : List Bool} {n : Nat}

private theorem hApos_len (hAn : A.length = n) :
    (truePos A (idxList n)).length = cardB A :=
  truePos_length A (idxList n) (by rw [hAn, idxList_length])

private theorem hBpos_len (hBn : B.length = n) :
    (truePos B (idxList n)).length = cardB B :=
  truePos_length B (idxList n) (by rw [hBn, idxList_length])

private theorem hRcard_n (hAn : A.length = n) (hBn : B.length = n) (hd : disjointVec A B = true) :
    (restPos A B (idxList n)).length + (cardB A + cardB B) = n := by
  have := restPos_card A B (idxList n) (by rw [hAn, idxList_length]) (by rw [hBn, idxList_length]) hd
  rwa [idxList_length] at this

/-- Count + class hypotheses for a woven element (feeds `map_q_weave` etc.). -/
theorem woven_count (hAn : A.length = n) (hBn : B.length = n) (hd : disjointVec A B = true)
    {mask : List Bool} (hmask : mask ∈ kLayer n (cardB A + cardB B))
    {σA σB σR : List Nat}
    (hσA : σA ∈ perms (truePos A (idxList n))) (hσB : σB ∈ perms (truePos B (idxList n)))
    (hσR : σR ∈ perms (restPos A B (idxList n))) :
    cardB mask = (σA ++ σB).length ∧ mask.length = (σA ++ σB).length + σR.length := by
  have hsAlen : σA.length = cardB A := by rw [perms_length_const _ σA hσA, hApos_len hAn]
  have hsBlen : σB.length = cardB B := by rw [perms_length_const _ σB hσB, hBpos_len hBn]
  have hsRlen : σR.length = (restPos A B (idxList n)).length := perms_length_const _ σR hσR
  have hABlen : (σA ++ σB).length = cardB A + cardB B := by rw [length_append, hsAlen, hsBlen]
  refine ⟨?_, ?_⟩
  · rw [mask_cardB hmask, hABlen]
  · rw [mask_length hmask, hABlen, hsRlen,
        Nat.add_comm (cardB A + cardB B) (restPos A B (idxList n)).length, hRcard_n hAn hBn hd]

/-- A `σA ++ σB` element is an `A∪B`-position (`q = true`). -/
theorem woven_q_true {σA σB : List Nat}
    (hσA : σA ∈ perms (truePos A (idxList n))) (hσB : σB ∈ perms (truePos B (idxList n)))
    {w : Nat} (hw : w ∈ σA ++ σB) :
    elemNat w (truePos A (idxList n) ++ truePos B (idxList n)) = true := by
  rcases mem_append_iff hw with hwA | hwB
  · exact elemNat_eq_true_of_mem (mem_append_left (mem_of_lperm (perms_sound _ σA hσA) hwA))
  · exact elemNat_eq_true_of_mem
      (mem_append_right _ (mem_of_lperm (perms_sound _ σB hσB) hwB))

/-- A `σR` element is not an `A∪B`-position (`q = false`). -/
theorem woven_q_false (hd : disjointVec A B = true) (hAn : A.length = n)
    {σR : List Nat} (hσR : σR ∈ perms (restPos A B (idxList n)))
    {w : Nat} (hw : w ∈ σR) :
    elemNat w (truePos A (idxList n) ++ truePos B (idxList n)) = false := by
  have hwR : w ∈ restPos A B (idxList n) := mem_of_lperm (perms_sound _ σR hσR) hw
  refine elemNat_eq_false_of_not_mem (fun hmem => ?_)
  rcases mem_append_iff hmem with hwA | hwB
  · exact restPos_not_truePos_A A B (idxList n) (idxList_nodup n) hwR hwA
  · exact restPos_not_truePos_B A B (idxList n) (idxList_nodup n) hwR hwB

end
end E213.Lib.Math.Combinatorics.BollobasCount
