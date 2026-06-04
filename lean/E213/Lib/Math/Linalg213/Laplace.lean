import E213.Lib.Math.Linalg213.DetN
import E213.Lib.Math.Linalg213.PermClosure

/-!
# Linalg213 — the cofactor (Laplace) expansion of the Leibniz determinant

Toward integer **Cayley–Hamilton** (and the C-finite Hadamard product): expand `leibDet (n+1)`
along the first row.  The permutation value-lists of `[0,…,n]` whose **first** entry is `j`
biject with the permutations of the `(0,j)`-**minor**'s columns, via the column **relabeling**
`unshift j` (drop the value `j`, pulling larger values down) — the inverse of `DetN.colShift j`
(insert a gap at `j`).  The sign factor `(−1)ʲ` falls out of `PermClosure.psign_cons`
(`psign (j :: rest) = altSign (ltCount j rest) · psign rest`, and `ltCount j rest = j` for a
permutation `rest` of `[0,…,n] ∖ {j}`).

This file builds the relabeling foundation first.  All ∅-axiom.
-/

namespace E213.Lib.Math.Linalg213.Laplace

open E213.Lib.Math.Linalg213.DetN
  (colShift colShift_lt colShift_ge minor altSign altSign_add det cofSum det_congr)
open E213.Lib.Math.Linalg213.Permutation
  (prodDiagFrom psign leibTerm leibDet perms iota LPerm ltCount inversions psign_cons
   ltCount_append sumZ map_lperm sumZ_lperm rowSwapAt rowSwapAt_other rowSwapAt_at rowSwapAt_at1)
open E213.Lib.Math.Linalg213.PermClosure
  (cnt permsOf_sound permsOf_complete lt_of_mem_iota length_iota Nodup cnt_pos_mem cnt_pos_of_mem
   cnt_eq_zero_of_not_mem eq_one_of_le_one_of_pos lperm_of_cnt_eq cnt_lperm add_left_cancel'
   nodup_cons nodup_map nodup_iota nodup_permsOf nodup_flatMap
   mem_map' mem_map_mpr mem_flatMap' mem_flatMap_mpr mem_append_left mem_append_right map_eq_of_mem
   map_map' nodup_of_lperm nodup_head_not_mem sumZ_map_smul LPerm.length_eq LPerm.mem
   leibDet_rows_eq_ne leibDet_setRow_add leibDet_setRow_smul leibDet_rowSwap)

/-! ## §1 — the minor relabeling (`unshift`, inverse of `colShift`) -/

/-- Drop the value `j`: values below `j` stay, values above shift down by one.  The inverse of
    `colShift j` (which inserts a gap at `j`) on `[0,…,n] ∖ {j}`. -/
def unshift (j v : Nat) : Nat := if v < j then v else v - 1

/-- ★ `colShift j ∘ unshift j = id` away from `j` — relabeling then re-inserting the gap. -/
theorem colShift_unshift {j v : Nat} (h : v ≠ j) : colShift j (unshift j v) = v := by
  show colShift j (if v < j then v else v - 1) = v
  by_cases hv : v < j
  · rw [if_pos hv]; show (if v < j then v else v + 1) = v; rw [if_pos hv]
  · rw [if_neg hv]
    have hjv : j < v := Nat.lt_of_le_of_ne (Nat.not_lt.mp hv) (fun e => h e.symm)
    obtain ⟨k, hk⟩ := Nat.le.dest hjv
    have hv1 : v - 1 = j + k := by rw [← hk, Nat.add_right_comm j 1 k]; exact Nat.succ_sub_one _
    rw [hv1]
    show (if j + k < j then j + k else (j + k) + 1) = v
    rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right j k)), ← hk, Nat.add_right_comm j 1 k]

/-- ★ `unshift j ∘ colShift j = id` — re-inserting the gap then relabeling. -/
theorem unshift_colShift (j l : Nat) : unshift j (colShift j l) = l := by
  show unshift j (if l < j then l else l + 1) = l
  by_cases hl : l < j
  · rw [if_pos hl]; show (if l < j then l else l - 1) = l; rw [if_pos hl]
  · rw [if_neg hl]
    show (if l + 1 < j then l + 1 else (l + 1) - 1) = l
    rw [if_neg (fun hlt => hl (Nat.lt_of_succ_lt hlt)), Nat.succ_sub_one]

/-- `colShift j v ≠ j` — the inserted gap is never `j`. -/
theorem colShift_ne (j l : Nat) : colShift j l ≠ j := by
  show (if l < j then l else l + 1) ≠ j
  by_cases hl : l < j
  · rw [if_pos hl]; exact Nat.ne_of_lt hl
  · rw [if_neg hl]
    exact fun e => hl (e ▸ Nat.lt_succ_self l)

/-! ## §2 — the per-term factorization

For `rel ∈ perms n`, the permutation `j :: rel.map (colShift j)` of `[0,…,n]` has
`leibTerm M (j :: rel.map (colShift j)) = altSign j · M 0 j · leibTerm (minor M j) rel`:
the diagonal product gives the minor's (B′), the sign splits via `psign_cons` with the leading
`ltCount = j` (C′) and `psign` preserved under the order-embedding `colShift j` (A′). -/

/-- **B′** — the diagonal product of `M` over the `colShift`-image equals the minor's. -/
theorem prodDiag_minor (M : Nat → Nat → Int) (j : Nat) :
    ∀ (i : Nat) (rel : List Nat),
      prodDiagFrom M (i + 1) (rel.map (colShift j)) = prodDiagFrom (minor M j) i rel
  | _, []      => rfl
  | i, l :: ls => by
    show minor M j i l * prodDiagFrom M (i + 1 + 1) (ls.map (colShift j))
       = minor M j i l * prodDiagFrom (minor M j) (i + 1) ls
    rw [prodDiag_minor M j (i + 1) ls]

/-- `colShift j` is strictly monotone. -/
theorem colShift_lt_mono (j b a : Nat) (h : b < a) : colShift j b < colShift j a := by
  show (if b < j then b else b + 1) < (if a < j then a else a + 1)
  by_cases hb : b < j
  · by_cases ha : a < j
    · rw [if_pos hb, if_pos ha]; exact h
    · rw [if_pos hb, if_neg ha]; exact Nat.lt_succ_of_lt h
  · by_cases ha : a < j
    · exact absurd (Nat.lt_trans h ha) hb
    · rw [if_neg hb, if_neg ha]; exact Nat.succ_lt_succ h

/-- `colShift j` is monotone. -/
theorem colShift_le_mono (j a b : Nat) (h : a ≤ b) : colShift j a ≤ colShift j b := by
  show (if a < j then a else a + 1) ≤ (if b < j then b else b + 1)
  by_cases ha : a < j
  · by_cases hb : b < j
    · rw [if_pos ha, if_pos hb]; exact h
    · rw [if_pos ha, if_neg hb]; exact Nat.le_succ_of_le h
  · have hb : ¬ b < j := fun hbj => ha (Nat.lt_of_le_of_lt h hbj)
    rw [if_neg ha, if_neg hb]; exact Nat.succ_le_succ h

/-- **A′ (count)** — `ltCount` is preserved under the order-embedding `colShift j`. -/
theorem ltCount_map_colShift (j a : Nat) : ∀ (rel : List Nat),
    ltCount (colShift j a) (rel.map (colShift j)) = ltCount a rel
  | []      => rfl
  | b :: bs => by
    show (if colShift j b < colShift j a then 1 else 0) + ltCount (colShift j a) (bs.map (colShift j))
       = (if b < a then 1 else 0) + ltCount a bs
    rw [ltCount_map_colShift j a bs]
    by_cases h : b < a
    · rw [if_pos h, if_pos (colShift_lt_mono j b a h)]
    · rw [if_neg h, if_neg (Nat.not_lt.mpr (colShift_le_mono j a b (Nat.not_lt.mp h)))]

/-- **A′ (inversions)** — `inversions` is preserved under `colShift j`. -/
theorem inversions_map_colShift (j : Nat) : ∀ (rel : List Nat),
    inversions (rel.map (colShift j)) = inversions rel
  | []      => rfl
  | a :: as => by
    show ltCount (colShift j a) (as.map (colShift j)) + inversions (as.map (colShift j))
       = ltCount a as + inversions as
    rw [ltCount_map_colShift j a as, inversions_map_colShift j as]

/-- **A′** — `psign` is preserved under `colShift j`. -/
theorem psign_map_colShift (j : Nat) (rel : List Nat) :
    psign (rel.map (colShift j)) = psign rel := by
  show altSign (inversions (rel.map (colShift j))) = altSign (inversions rel)
  rw [inversions_map_colShift]

/-! ## §2 (C′) — the leading inversion count is `j` -/

/-- `ltCount` is `LPerm`-invariant. -/
theorem ltCount_lperm {a : Nat} {L1 L2 : List Nat} (h : LPerm L1 L2) : ltCount a L1 = ltCount a L2 := by
  induction h with
  | nil => rfl
  | cons x _ ih => show (if x < a then 1 else 0) + ltCount a _ = (if x < a then 1 else 0) + ltCount a _; rw [ih]
  | swap x y l =>
    show (if y < a then 1 else 0) + ((if x < a then 1 else 0) + ltCount a l)
       = (if x < a then 1 else 0) + ((if y < a then 1 else 0) + ltCount a l)
    exact Nat.add_left_comm _ _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- If every entry is `< j`, the inversion-count is the length. -/
theorem ltCount_all (j : Nat) : ∀ {L : List Nat}, (∀ v ∈ L, v < j) → ltCount j L = L.length
  | [],     _ => rfl
  | a :: l, h => by
    show (if a < j then 1 else 0) + ltCount j l = l.length + 1
    rw [if_pos (h a (List.Mem.head _)), ltCount_all j (fun v hv => h v (List.Mem.tail _ hv)),
        Nat.add_comm]

/-- `iota n` has all entries `< j` when `n ≤ j`, so its inversion-count is `n`. -/
theorem ltCount_iota_all {n j : Nat} (h : n ≤ j) : ltCount j (iota n) = n := by
  rw [ltCount_all j (fun v hv => Nat.lt_of_lt_of_le (lt_of_mem_iota hv) h), length_iota]

/-- `ltCount` of a singleton. -/
theorem ltCount_singleton (j n : Nat) : ltCount j [n] = if n < j then 1 else 0 := by
  show (if n < j then 1 else 0) + ltCount j ([] : List Nat) = if n < j then 1 else 0
  exact Nat.add_zero _

/-- ★ **`ltCount j (iota n) = j`** for `j ≤ n` (exactly `j` of `[0,…,n-1]` are `< j`). -/
theorem ltCount_iota : ∀ (n j : Nat), j ≤ n → ltCount j (iota n) = j
  | 0,     j, hj => (Nat.le_antisymm hj (Nat.zero_le j)).symm
  | n + 1, j, hj => by
    show ltCount j (iota n ++ [n]) = j
    rw [ltCount_append j (iota n) [n], ltCount_singleton]
    by_cases hjn : j ≤ n
    · rw [ltCount_iota n j hjn, if_neg (Nat.not_lt.mpr hjn), Nat.add_zero]
    · have hje : j = n + 1 :=
        Nat.le_antisymm hj (Nat.succ_le_of_lt (Nat.lt_of_not_le hjn))
      subst hje
      rw [ltCount_iota_all (Nat.le_succ n), if_pos (Nat.lt_succ_self n)]

/-- `ltCount j` against `j` is unchanged by the `colShift j` embedding (it preserves `< j`). -/
theorem ltCount_colShift_self (j : Nat) : ∀ (rel : List Nat),
    ltCount j (rel.map (colShift j)) = ltCount j rel
  | []      => rfl
  | l :: ls => by
    show (if colShift j l < j then 1 else 0) + ltCount j (ls.map (colShift j))
       = (if l < j then 1 else 0) + ltCount j ls
    rw [ltCount_colShift_self j ls]
    have hif : (if colShift j l < j then (1 : Nat) else 0) = (if l < j then 1 else 0) := by
      by_cases hl : l < j
      · rw [colShift_lt hl]
      · rw [colShift_ge (Nat.not_lt.mp hl), if_neg hl,
            if_neg (Nat.not_lt.mpr (Nat.le_succ_of_le (Nat.not_lt.mp hl)))]
    rw [hif]

/-- ★ **C′** — the leading inversion count of `j :: rel.map (colShift j)` is `j`
    (for `rel ∈ perms n`, `j ≤ n`). -/
theorem ltCount_perm_colShift {n j : Nat} (hj : j ≤ n) {rel : List Nat} (hrel : rel ∈ perms n) :
    ltCount j (rel.map (colShift j)) = j := by
  rw [ltCount_colShift_self, ltCount_lperm (permsOf_sound (iota n) rel hrel), ltCount_iota n j hj]

/-! ## §2 — the per-term cofactor factorization -/

/-- ★ **Per-term cofactor identity**: the Leibniz term of `j :: rel.map (colShift j)` (a
    permutation of `[0,…,n]` with first entry `j`) factors as `(−1)ʲ · M 0 j · (minor term)`. -/
theorem leibTerm_cons_colShift (M : Nat → Nat → Int) (n j : Nat) (hj : j ≤ n) {rel : List Nat}
    (hrel : rel ∈ perms n) :
    leibTerm M (j :: rel.map (colShift j)) = altSign j * M 0 j * leibTerm (minor M j) rel := by
  show psign (j :: rel.map (colShift j)) * prodDiagFrom M 0 (j :: rel.map (colShift j))
     = altSign j * M 0 j * (psign rel * prodDiagFrom (minor M j) 0 rel)
  rw [psign_cons, ltCount_perm_colShift hj hrel, psign_map_colShift]
  show (altSign j * psign rel) * (M 0 j * prodDiagFrom M 1 (rel.map (colShift j)))
     = altSign j * M 0 j * (psign rel * prodDiagFrom (minor M j) 0 rel)
  rw [prodDiag_minor M j 0 rel]
  ring_intZ

/-! ## §2 (D) — the `perms (n+1)` head-decomposition reindex -/

/-- Two `Nodup` lists with the same membership are `LPerm` (the set-equality ⟹ multiset-equality
    bridge, via the count engine). -/
theorem lperm_of_nodup_mem_iff {α : Type} [DecidableEq α] {L1 L2 : List α}
    (h1 : Nodup L1) (h2 : Nodup L2) (hm : ∀ q, q ∈ L1 ↔ q ∈ L2) : LPerm L1 L2 := by
  apply lperm_of_cnt_eq
  intro q
  cases Nat.eq_zero_or_pos (cnt q L1) with
  | inl h0 =>
    have hq1 : q ∉ L1 := fun hmem => absurd (h0 ▸ cnt_pos_of_mem hmem) (Nat.lt_irrefl 0)
    rw [h0, cnt_eq_zero_of_not_mem (fun hmem => hq1 ((hm q).mpr hmem))]
  | inr hp =>
    rw [eq_one_of_le_one_of_pos (h1 q) hp,
        eq_one_of_le_one_of_pos (h2 q) (cnt_pos_of_mem ((hm q).mp (cnt_pos_mem hp)))]

/-- `v < n → v ∈ iota n`. -/
theorem mem_iota_of_lt : ∀ {n v : Nat}, v < n → v ∈ iota n
  | n + 1, v, h => by
    show v ∈ iota n ++ [n]
    by_cases hv : v < n
    · exact mem_append_left _ (mem_iota_of_lt hv)
    · have hvn : v = n := Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.mp hv)
      rw [hvn]; exact mem_append_right _ (List.Mem.head _)

/-- `colShift j` is injective (from strict monotonicity). -/
theorem colShift_inj (j a b : Nat) (h : colShift j a = colShift j b) : a = b := by
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (colShift_lt_mono j a b hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (colShift_lt_mono j b a hgt))

/-- `colShift j l ≤ l + 1`. -/
theorem colShift_le_succ (j l : Nat) : colShift j l ≤ l + 1 := by
  show (if l < j then l else l + 1) ≤ l + 1
  by_cases hl : l < j
  · rw [if_pos hl]; exact Nat.le_succ l
  · rw [if_neg hl]; exact Nat.le_refl _

/-- `unshift j v < n` for `v ≤ n`, `v ≠ j`, `j ≤ n`. (helper) -/
theorem unshift_lt {n j v : Nat} (hvn : v ≤ n) (hvj : v ≠ j) (hjn : j ≤ n) : unshift j v < n := by
  show (if v < j then v else v - 1) < n
  by_cases hv : v < j
  · rw [if_pos hv]; exact Nat.lt_of_lt_of_le hv hjn
  · rw [if_neg hv]
    have hjv : j < v := Nat.lt_of_le_of_ne (Nat.not_lt.mp hv) (fun e => hvj e.symm)
    obtain ⟨k, hk⟩ := Nat.le.dest hjv
    have hv1 : v - 1 = j + k := by rw [← hk, Nat.add_right_comm j 1 k]; exact Nat.succ_sub_one _
    rw [← hk, Nat.add_right_comm j 1 k] at hvn
    rw [hv1]; exact hvn

/-- ★ **Canonical decomposition LPerm**: `j :: (iota n).map (colShift j)` is a permutation of
    `iota (n+1)` (insert `j`, shift the rest up past the gap). -/
theorem canonical_lperm (n j : Nat) (hj : j ≤ n) :
    LPerm (j :: (iota n).map (colShift j)) (iota (n + 1)) := by
  apply lperm_of_nodup_mem_iff
  · apply nodup_cons
    · intro hmem
      rcases mem_map' _ hmem with ⟨l, _, hl⟩
      exact colShift_ne j l hl
    · exact nodup_map (colShift_inj j) (nodup_iota n)
  · exact nodup_iota (n + 1)
  · intro v
    constructor
    · intro hv
      apply mem_iota_of_lt
      cases hv with
      | head => exact Nat.lt_succ_of_le hj
      | tail _ hmem =>
        rcases mem_map' _ hmem with ⟨l, hl, he⟩
        rw [← he]
        exact Nat.lt_succ_of_le (Nat.le_trans (colShift_le_succ j l)
          (Nat.succ_le_of_lt (lt_of_mem_iota hl)))
    · intro hv
      by_cases hvj : v = j
      · rw [hvj]; exact List.Mem.head _
      · refine List.Mem.tail _ ?_
        rw [← colShift_unshift hvj]
        exact mem_map_mpr (colShift j)
          (mem_iota_of_lt (unshift_lt (Nat.le_of_lt_succ (lt_of_mem_iota hv)) hvj hj))

/-- `LPerm` cons-cancellation. -/
theorem lperm_cons_inv {α : Type} [DecidableEq α] {x : α} {L1 L2 : List α}
    (h : LPerm (x :: L1) (x :: L2)) : LPerm L1 L2 := by
  apply lperm_of_cnt_eq
  intro w
  exact add_left_cancel' (if x = w then 1 else 0) (cnt_lperm (a := w) h)

/-- `map (fun x => x) = id` (clean). -/
theorem map_id' {α : Type} : ∀ (L : List α), L.map (fun x => x) = L
  | []     => rfl
  | a :: l => by show a :: l.map (fun x => x) = a :: l; rw [map_id' l]

/-- `List.map f` is injective when `f` is. -/
theorem map_inj_list {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b) :
    ∀ {L1 L2 : List α}, L1.map f = L2.map f → L1 = L2
  | [],      [],      _ => rfl
  | [],      _ :: _,  h => by cases h
  | _ :: _,  [],      h => by cases h
  | a :: l1, b :: l2, h => by
    rw [hf a b (List.cons.inj h).1, map_inj_list f hf (List.cons.inj h).2]

/-- ★★ **The head-decomposition reindex**: `perms (n+1)` is the disjoint union over `j ≤ n` of
    the `j`-headed permutations `j :: rel.map (colShift j)` (`rel ∈ perms n`). -/
theorem perms_succ_lperm (n : Nat) :
    LPerm (perms (n + 1))
      ((iota (n + 1)).flatMap (fun j => (perms n).map (fun rel => j :: rel.map (colShift j)))) := by
  apply lperm_of_nodup_mem_iff (nodup_permsOf (nodup_iota (n + 1)))
  · refine nodup_flatMap (fun j => (perms n).map (fun rel => j :: rel.map (colShift j)))
      (fun q => q.headD 0) (iota (n + 1)) (nodup_iota (n + 1)) ?_ ?_
    · exact fun j _ => nodup_map (fun r r' he =>
        map_inj_list (colShift j) (colShift_inj j) (List.cons.inj he).2) (nodup_permsOf (nodup_iota n))
    · intro j _ q hq
      rcases mem_map' _ hq with ⟨rel, _, he⟩
      have he' : j :: rel.map (colShift j) = q := he
      exact (congrArg (fun l => List.headD l 0) he').symm
  · intro q
    constructor
    · intro hq
      have hlp : LPerm q (iota (n + 1)) := permsOf_sound (iota (n + 1)) q hq
      cases q with
      | nil => exact Nat.noConfusion ((LPerm.length_eq hlp).trans (length_iota (n + 1)))
      | cons jj tail =>
        have hjj : jj ∈ iota (n + 1) := LPerm.mem hlp (List.Mem.head _)
        have hjn : jj ≤ n := Nat.le_of_lt_succ (lt_of_mem_iota hjj)
        have hnd : Nodup (jj :: tail) := nodup_of_lperm hlp (nodup_iota (n + 1))
        have hne : ∀ v ∈ tail, v ≠ jj := fun v hv e => nodup_head_not_mem hnd (e ▸ hv)
        have htc : LPerm tail ((iota n).map (colShift jj)) :=
          lperm_cons_inv (LPerm.trans hlp (LPerm.symm (canonical_lperm n jj hjn)))
        have hrel : tail.map (unshift jj) ∈ perms n := by
          refine permsOf_complete (iota n) _ (LPerm.trans (map_lperm (unshift jj) htc) ?_)
          rw [map_map',
              map_eq_of_mem (fun l => unshift jj (colShift jj l)) (fun l => l)
                (fun l _ => unshift_colShift jj l), map_id']
          exact LPerm.refl _
        have htail : (tail.map (unshift jj)).map (colShift jj) = tail := by
          rw [map_map',
              map_eq_of_mem (fun v => colShift jj (unshift jj v)) (fun v => v)
                (fun v hv => colShift_unshift (hne v hv)), map_id']
        have hmem2 : (jj :: (tail.map (unshift jj)).map (colShift jj))
            ∈ (perms n).map (fun rel => jj :: rel.map (colShift jj)) :=
          mem_map_mpr (fun rel => jj :: rel.map (colShift jj)) hrel
        rw [htail] at hmem2
        exact mem_flatMap_mpr _ hjj hmem2
    · intro hq
      rcases mem_flatMap' _ hq with ⟨j, hj, hqj⟩
      rcases mem_map' _ hqj with ⟨rel, hrel, he⟩
      refine permsOf_complete (iota (n + 1)) q ?_
      rw [← he]
      exact LPerm.trans (LPerm.cons j (map_lperm (colShift j) (permsOf_sound (iota n) rel hrel)))
        (canonical_lperm n j (Nat.le_of_lt_succ (lt_of_mem_iota hj)))

/-! ## §2 — assembly: the row-0 cofactor expansion -/

/-- `sumZ` over append. -/
theorem sumZ_append : ∀ (L M : List Int), sumZ (L ++ M) = sumZ L + sumZ M
  | [],     M => by show sumZ M = 0 + sumZ M; rw [E213.Meta.Int213.zero_add]
  | a :: l, M => by
    show a + sumZ (l ++ M) = (a + sumZ l) + sumZ M
    rw [sumZ_append l M, E213.Meta.Int213.add_assoc]

/-- `map` over append. -/
theorem map_append' {α β : Type} (f : α → β) : ∀ (L M : List α),
    (L ++ M).map f = L.map f ++ M.map f
  | [],     _ => rfl
  | a :: l, M => by show f a :: (l ++ M).map f = f a :: (l.map f ++ M.map f); rw [map_append' f l M]

/-- `map` over `flatMap`. -/
theorem map_flatMap {α β γ : Type} (f : β → γ) (g : α → List β) : ∀ (L : List α),
    (L.flatMap g).map f = L.flatMap (fun x => (g x).map f)
  | []     => rfl
  | a :: l => by
    show (g a ++ l.flatMap g).map f = (g a).map f ++ l.flatMap (fun x => (g x).map f)
    rw [map_append' f (g a) (l.flatMap g), map_flatMap f g l]

/-- `sumZ` over `flatMap` = sum of the inner sums. -/
theorem sumZ_flatMap {α : Type} (h : α → List Int) : ∀ (L : List α),
    sumZ (L.flatMap h) = sumZ (L.map (fun x => sumZ (h x)))
  | []     => rfl
  | a :: l => by
    show sumZ (h a ++ l.flatMap h) = sumZ (h a) + sumZ (l.map (fun x => sumZ (h x)))
    rw [sumZ_append (h a) (l.flatMap h), sumZ_flatMap h l]

/-- The `j`-headed block sums to the cofactor term `(−1)ʲ · M 0 j · det (minor M j)`. -/
theorem cofactor_term (M : Nat → Nat → Int) (n j : Nat) (hj : j ≤ n) :
    sumZ (((perms n).map (fun rel => j :: rel.map (colShift j))).map (leibTerm M))
      = altSign j * M 0 j * leibDet n (minor M j) := by
  show sumZ (((perms n).map (fun rel => j :: rel.map (colShift j))).map (leibTerm M))
     = altSign j * M 0 j * sumZ ((perms n).map (leibTerm (minor M j)))
  rw [map_map',
      map_eq_of_mem (fun rel => leibTerm M (j :: rel.map (colShift j)))
        (fun rel => altSign j * M 0 j * leibTerm (minor M j) rel)
        (fun rel hrel => leibTerm_cons_colShift M n j hj hrel),
      sumZ_map_smul (altSign j * M 0 j) (leibTerm (minor M j)) (perms n)]

/-- ★★★ **Cofactor (Laplace) expansion along row 0**:
    `det (n+1) M = Σⱼ (−1)ʲ · M 0 j · det n (minor M j)`. -/
theorem cofactor_row0 (M : Nat → Nat → Int) (n : Nat) :
    leibDet (n + 1) M
      = sumZ ((iota (n + 1)).map (fun j => altSign j * M 0 j * leibDet n (minor M j))) := by
  show sumZ ((perms (n + 1)).map (leibTerm M)) = _
  rw [sumZ_lperm (map_lperm (leibTerm M) (perms_succ_lperm n)), map_flatMap, sumZ_flatMap,
      map_eq_of_mem
        (fun j => sumZ (((perms n).map (fun rel => j :: rel.map (colShift j))).map (leibTerm M)))
        (fun j => altSign j * M 0 j * leibDet n (minor M j))
        (fun j hj => cofactor_term M n j (Nat.le_of_lt_succ (lt_of_mem_iota hj)))]

/-! ## §3 — bridge to the recursive determinant `DetN.det` -/

/-- `a + 0 = a` over `ℤ` (propext-free). -/
private theorem add_zero' (a : Int) : a + 0 = a :=
  (E213.Meta.Int213.add_comm a 0).trans (E213.Meta.Int213.zero_add a)

/-- `DetN.cofSum` (the left-fold cofactor sum) equals the `sumZ`-over-`iota` form. -/
theorem cofSum_eq_sumZ_iota (g : (Nat → Nat → Int) → Int) (M : Nat → Nat → Int) : ∀ c,
    cofSum g M c = sumZ ((iota c).map (fun j => altSign j * M 0 j * g (minor M j)))
  | 0     => rfl
  | c + 1 => by
    show cofSum g M c + altSign c * M 0 c * g (minor M c)
       = sumZ ((iota c ++ [c]).map (fun j => altSign j * M 0 j * g (minor M j)))
    rw [map_append', sumZ_append, cofSum_eq_sumZ_iota g M c]
    show sumZ ((iota c).map (fun j => altSign j * M 0 j * g (minor M j)))
           + altSign c * M 0 c * g (minor M c)
       = sumZ ((iota c).map (fun j => altSign j * M 0 j * g (minor M j)))
           + (altSign c * M 0 c * g (minor M c) + 0)
    rw [add_zero']

/-- `cofSum` respects a pointwise-equal inner determinant. -/
theorem cofSum_congr {g g' : (Nat → Nat → Int) → Int} (M : Nat → Nat → Int)
    (h : ∀ M', g M' = g' M') : ∀ c, cofSum g M c = cofSum g' M c
  | 0     => rfl
  | c + 1 => by
    show cofSum g M c + altSign c * M 0 c * g (minor M c)
       = cofSum g' M c + altSign c * M 0 c * g' (minor M c)
    rw [cofSum_congr M h c, h (minor M c)]

/-- ★★ **The Leibniz determinant equals the cofactor (recursive) determinant `DetN.det`.** -/
theorem leibDet_eq_det : ∀ (n : Nat) (M : Nat → Nat → Int), leibDet n M = det n M
  | 0,     _ => by show (1 : Int) * 1 + 0 = 1; rw [E213.Meta.Int213.mul_one, add_zero']
  | n + 1, M => by
    rw [cofactor_row0, ← cofSum_eq_sumZ_iota (leibDet n) M (n + 1),
        cofSum_congr M (fun M' => leibDet_eq_det n M') (n + 1)]
    rfl

/-! ## §3 — determinant properties transferred to `DetN.det` (via the bridge) -/

open E213.Lib.Math.Linalg213.PermClosure (setRow)

/-- ★ **`DetN.det`: two equal rows ⟹ 0** (any distinct positions). -/
theorem det_rows_eq_ne (M : Nat → Nat → Int) (n i j : Nat) (hij : i ≠ j) (hi : i < n) (hj : j < n)
    (hrows : ∀ c, M i c = M j c) : det n M = 0 := by
  rw [← leibDet_eq_det]; exact leibDet_rows_eq_ne M n i j hij hi hj hrows

/-- ★ **`DetN.det` is additive in any row.** -/
theorem det_setRow_add (n i : Nat) (hi : i < n) (r1 r2 : Nat → Int) (M : Nat → Nat → Int) :
    det n (setRow i (fun c => r1 c + r2 c) M) = det n (setRow i r1 M) + det n (setRow i r2 M) := by
  rw [← leibDet_eq_det, ← leibDet_eq_det, ← leibDet_eq_det]
  exact leibDet_setRow_add n i hi r1 r2 M

/-- ★ **`DetN.det` is scalar-homogeneous in any row.** -/
theorem det_setRow_smul (n i : Nat) (hi : i < n) (a : Int) (r : Nat → Int) (M : Nat → Nat → Int) :
    det n (setRow i (fun c => a * r c) M) = a * det n (setRow i r M) := by
  rw [← leibDet_eq_det, ← leibDet_eq_det]
  exact leibDet_setRow_smul n i hi a r M

/-- ★ **`DetN.det`: an adjacent row swap negates** (for `k+1 < n`). -/
theorem det_rowSwap (M : Nat → Nat → Int) (n k : Nat) (hk : k + 1 < n) :
    det n (rowSwapAt k M) = - det n M := by
  rw [← leibDet_eq_det, ← leibDet_eq_det]; exact leibDet_rowSwap M n k hk

/-! ## §4 — row-`i` cofactor expansion (move row `i` to the top) -/

/-- Move row `i` to the top: rows `0,…,i-1` shift down to `1,…,i`. -/
def cyc (i : Nat) (M : Nat → Nat → Int) : Nat → Nat → Int := fun r c =>
  if r = 0 then M i c else if r ≤ i then M (r - 1) c else M r c

/-- `cyc 0 = id`. -/
theorem cyc0 (M : Nat → Nat → Int) (r c : Nat) : cyc 0 M r c = M r c := by
  show (if r = 0 then M 0 c else if r ≤ 0 then M (r - 1) c else M r c) = M r c
  by_cases hr : r = 0
  · rw [if_pos hr, hr]
  · rw [if_neg hr, if_neg (fun h => hr (Nat.le_antisymm h (Nat.zero_le r)))]

/-- One bubble step: `cyc (i+1) M = cyc i (rowSwapAt i M)`. -/
theorem cyc_succ_eq (i : Nat) (M : Nat → Nat → Int) : ∀ (r c : Nat),
    cyc (i + 1) M r c = cyc i (rowSwapAt i M) r c
  | 0,     c => by show M (i + 1) c = rowSwapAt i M i c; rw [rowSwapAt_at]
  | s + 1, c => by
    show (if s + 1 ≤ i + 1 then M ((s + 1) - 1) c else M (s + 1) c)
       = (if s + 1 ≤ i then rowSwapAt i M ((s + 1) - 1) c else rowSwapAt i M (s + 1) c)
    by_cases h1 : s + 1 ≤ i + 1
    · rw [if_pos h1]
      by_cases h2 : s + 1 ≤ i
      · rw [if_pos h2]
        have hsi : s < i := Nat.lt_of_succ_le h2
        show M s c = rowSwapAt i M s c
        rw [rowSwapAt_other i M (Nat.ne_of_lt hsi) (Nat.ne_of_lt (Nat.lt_succ_of_lt hsi))]
      · rw [if_neg h2]
        have hsi : s = i := Nat.le_antisymm (Nat.le_of_succ_le_succ h1)
          (Nat.le_of_lt_succ (Nat.lt_of_not_le h2))
        rw [hsi]
        show M i c = rowSwapAt i M (i + 1) c
        rw [rowSwapAt_at1]
    · rw [if_neg h1, if_neg (fun h => h1 (Nat.le_succ_of_le h))]
      have hgt : i < s := Nat.lt_of_succ_lt_succ (Nat.lt_of_not_le h1)
      rw [rowSwapAt_other i M (Ne.symm (Nat.ne_of_lt (Nat.lt_succ_of_lt hgt)))
        (Ne.symm (Nat.ne_of_lt (Nat.succ_lt_succ hgt)))]

/-- ★ **Moving row `i` to the top multiplies the determinant by `(−1)ⁱ`.** -/
theorem det_cyc (n : Nat) : ∀ (i : Nat) (M : Nat → Nat → Int), i < n →
    det n (cyc i M) = altSign i * det n M
  | 0,     M, _  => by
    rw [det_congr n (cyc0 M)]; show det n M = 1 * det n M; rw [Int.one_mul]
  | i + 1, M, hi => by
    rw [det_congr n (cyc_succ_eq i M), det_cyc n i (rowSwapAt i M) (Nat.lt_of_succ_lt hi),
        det_rowSwap M n i hi]
    show altSign i * -det n M = -(altSign i) * det n M
    rw [E213.Meta.Int213.mul_neg, E213.Meta.Int213.neg_mul]

end E213.Lib.Math.Linalg213.Laplace
