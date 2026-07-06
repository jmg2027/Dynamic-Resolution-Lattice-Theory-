/-
Rederive/Grading.lean — the grading obstruction core, finitized (SPEC Q2;
task L3; theory counterpart: rederive/theory/grading_obstruction.md §3–§5).

Contents:

1. The ℕ-folds on `Tree`: `depth` (= level, = lockstep generation),
   `size` (leaf count), and the lockstep-generation predicate `inGen`,
   with the theorem `gen_eq_depth` (minimal generation = depth,
   grading_obstruction.md Proposition 5.1 — so the third fold adds
   nothing, for ALL trees, not just the enumerator's 44).

2. The fold-divergence witness at level 3 (Theorem 5.3): the folds form
   one ladder `size = depth + 1` on all five level-≤2 objects of
   ORIGIN_RAW §9, and break at `w = ((ab)(a(ab)))` (size 5, depth 3);
   plus the first strict order-reversal (Theorem 5.4): the folds
   eventually order trees oppositely, so no monotone rescaling
   reconciles them.

3. The no-rank theorem, finitized (Theorem 4.1): the nine concrete
   events of D surrounding the witness `E* = link{(a(ab)),(a(b(ab)))}`,
   with the nine cover pairs of the two saturated chains C₁ (length 4)
   and C₂ (length 6) listed explicitly; NO function `rank : Elem → ℕ`
   satisfies `rank upper = rank lower + 1` on all listed covers — a
   theorem over ALL candidate rank functions (`no_rank`).  The cover
   list is exactly the hand-verified list of grading_obstruction.md
   Theorem 4.1 (each step checked as a genuine cover of D there, via
   the cover classification Lemma 2.4).

4. The positive half (Proposition 3.4 / Theorem 4.2 restricted): on the
   level-≤2 zone Z (six events, five covers) the height IS a rank
   function, and every rank function on Z is forced to be
   `rank ⊥ + height` (uniqueness up to the constant).

Zero dependencies: Lean 4 core only, zero axioms (see AxiomCheck.lean).
-/

import Rederive.Object1

namespace Rederive

/-! ## 0. Axiom-free Nat mini-toolkit

The core-library lemmas `Nat.max_le`, `Nat.le_max_left/right`,
`Nat.add_left_cancel` (and the `omega` tactic) carry `propext` /
`Quot.sound` in their proofs, which the program's zero-axiom contract
forbids.  The few arithmetic facts needed are re-proved here from
scratch; all verified axiom-free in AxiomCheck.lean. -/

/-- Recursive binary maximum (extensionally `Nat.max`; defined
recursively so that all its laws are provable without any axiom). -/
def maxN : Nat → Nat → Nat
  | 0, n => n
  | m + 1, 0 => m + 1
  | m + 1, n + 1 => maxN m n + 1

theorem le_maxN_left : ∀ (m n : Nat), m ≤ maxN m n
  | 0, n => Nat.zero_le n
  | _ + 1, 0 => Nat.le_refl _
  | m + 1, n + 1 => Nat.succ_le_succ (le_maxN_left m n)

theorem le_maxN_right : ∀ (m n : Nat), n ≤ maxN m n
  | 0, n => Nat.le_refl n
  | _ + 1, 0 => Nat.zero_le _
  | m + 1, n + 1 => Nat.succ_le_succ (le_maxN_right m n)

theorem maxN_le : ∀ (m n c : Nat), m ≤ c → n ≤ c → maxN m n ≤ c
  | 0, _, _, _, h2 => h2
  | _ + 1, 0, _, h1, _ => h1
  | m + 1, n + 1, 0, h1, _ => absurd h1 (Nat.not_succ_le_zero m)
  | m + 1, n + 1, c + 1, h1, h2 =>
    Nat.succ_le_succ
      (maxN_le m n c (Nat.le_of_succ_le_succ h1) (Nat.le_of_succ_le_succ h2))

theorem zero_addN : ∀ n : Nat, 0 + n = n
  | 0 => rfl
  | n + 1 => congrArg Nat.succ (zero_addN n)

theorem succ_addN : ∀ (n m : Nat), n + 1 + m = (n + m) + 1
  | _, 0 => rfl
  | n, m + 1 => congrArg Nat.succ (succ_addN n m)

/-- Left cancellation of addition, axiom-free. -/
theorem add_left_cancelN : ∀ (n : Nat) {m k : Nat}, n + m = n + k → m = k
  | 0, m, k, h => (zero_addN m).symm.trans (h.trans (zero_addN k))
  | n + 1, m, k, h =>
    add_left_cancelN n
      (Nat.succ.inj ((succ_addN n m).symm.trans (h.trans (succ_addN n k))))

namespace Tree

/-! ## 1. The ℕ-folds -/

/-- Depth fold: `depth atom = 0`, `depth (xy) = 1 + max`.  ORIGIN_RAW §5's
"level" of an object (Proposition `gen_eq_depth` below makes this the raw
text's own stratum where it is defined). -/
def depth : Tree → Nat
  | .a => 0
  | .b => 0
  | .node l r => maxN (depth l) (depth r) + 1

/-- Size fold: leaf count (`λ` of grading_obstruction.md §1.1). -/
def size : Tree → Nat
  | .a => 1
  | .b => 1
  | .node l r => size l + size r

/-- Lockstep-generation membership: `inGen k t` ⟺ `t ∈ G_k` where
`G₀ = {a,b}` and `G_{k+1} = G_k ∪ {pair{x,y} : x, y ∈ G_k}` (ORIGIN_RAW §5's
stage-`k` population, read on the ordered carrier; the distinctness
side-condition of the pairing does not affect stage membership). -/
def inGen (k : Nat) : Tree → Bool
  | .a => true
  | .b => true
  | .node l r =>
    match k with
    | 0 => false
    | k' + 1 => inGen k' l && inGen k' r
termination_by structural t => t

/-- Boolean-`and` split, proved by cases (no simp, no Classical). -/
theorem and_eq_true_split {x y : Bool} (h : (x && y) = true) :
    x = true ∧ y = true := by
  cases x with
  | true => exact ⟨rfl, h⟩
  | false => exact Bool.noConfusion h

theorem and_eq_true_join {x y : Bool} (h₁ : x = true) (h₂ : y = true) :
    (x && y) = true := by
  subst h₁; exact h₂

/-- Stage membership is exactly the depth bound: `t ∈ G_k ⟺ depth t ≤ k`. -/
theorem inGen_iff : ∀ (t : Tree) (k : Nat), inGen k t = true ↔ depth t ≤ k := by
  intro t
  induction t with
  | a => exact fun k => ⟨fun _ => Nat.zero_le k, fun _ => rfl⟩
  | b => exact fun k => ⟨fun _ => Nat.zero_le k, fun _ => rfl⟩
  | node l r ihl ihr =>
    intro k
    cases k with
    | zero =>
      constructor
      · intro h; exact Bool.noConfusion h
      · intro h; exact absurd h (Nat.not_succ_le_zero _)
    | succ k =>
      constructor
      · intro h
        have hs := and_eq_true_split h
        exact Nat.succ_le_succ
          (maxN_le _ _ _ ((ihl k).mp hs.1) ((ihr k).mp hs.2))
      · intro h
        have hm : maxN (depth l) (depth r) ≤ k := Nat.le_of_succ_le_succ h
        exact and_eq_true_join
          ((ihl k).mpr (Nat.le_trans (le_maxN_left _ _) hm))
          ((ihr k).mpr (Nat.le_trans (le_maxN_right _ _) hm))

/-- **Minimal generation = depth** (grading_obstruction.md Proposition 5.1,
for ALL trees): `t` appears at stage `depth t` and at no earlier stage.
The lockstep fold is therefore not a third stratum — the operative
divergence is depth vs size. -/
theorem gen_eq_depth (t : Tree) :
    inGen (depth t) t = true ∧ ∀ k, inGen k t = true → depth t ≤ k :=
  ⟨(inGen_iff t (depth t)).mpr (Nat.le_refl _),
   fun k h => (inGen_iff t k).mp h⟩

end Tree

namespace Grading

open Tree

/-! ## 2. The concrete trees: the five level-≤2 objects and the witnesses -/

/-- `(ab)` — the first reified difference. -/
def ab : Tree := pairing .a .b
/-- `(a(ab))` — level 2. -/
def aab : Tree := pairing .a ab
/-- `(b(ab))` — level 2. -/
def bab : Tree := pairing .b ab
/-- `w = ((ab)(a(ab)))` — the first tree past the five level-≤2 objects
that links two composites; the fold-divergence witness (Theorem 5.3) and
the composite of the stratification witness `ℓ*` (Theorem 3.5). -/
def w : Tree := pairing ab aab
/-- `(a(b(ab)))` — the depth-3 comb over `(b(ab))`. -/
def abab : Tree := pairing .a bab
/-- `(a(a(a(ab))))` — the depth-4 comb (Theorem 5.4's `t₁`). -/
def comb4 : Tree := pairing .a (pairing .a aab)
/-- `((a(ab))(b(ab)))` — Theorem 5.4's `t₂`. -/
def t2 : Tree := pairing aab bab
/-- `((a(ab))(a(b(ab))))` — the composite of the no-rank witness `E*`
(Theorem 4.1): λ = 7, δ = 4. -/
def eStarTree : Tree := pairing aab abab

/-- **The lockstep ladder on the level-≤2 zone** (Proposition 5.2 on the
five objects of ORIGIN_RAW §9): `size = depth + 1` on `a, b, (ab),
(a(ab)), (b(ab))` — the folds coincide as one bijective ladder. -/
theorem ladder_level2 :
    size Tree.a = depth Tree.a + 1 ∧
    size Tree.b = depth Tree.b + 1 ∧
    size ab = depth ab + 1 ∧
    size aab = depth aab + 1 ∧
    size bab = depth bab + 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **First fold divergence at level 3** (Theorem 5.3, decidable form):
`w = ((ab)(a(ab)))` has depth 3 (a level-3 object) but size 5 — the
ladder `size = depth + 1` breaks exactly here. -/
theorem witness_diverges :
    depth w = 3 ∧ size w = 5 ∧ size w ≠ depth w + 1 :=
  ⟨rfl, rfl, by decide⟩

/-- The generation fold agrees with depth at the witness: `w` first
appears at lockstep stage 3, not at stage 2 (instance of
`gen_eq_depth`, decidably). -/
theorem gen_witness : inGen 3 w = true ∧ inGen 2 w = false :=
  ⟨rfl, rfl⟩

/-- **Order reversal** (Theorem 5.4): `t₁ = (a(a(a(ab))))` and
`t₂ = ((a(ab))(b(ab)))` are ordered oppositely by the two folds
(`depth t₁ > depth t₂` but `size t₁ < size t₂`), so no strictly
increasing `θ : ℕ → ℕ` carries one fold to the other. -/
theorem reversal : depth comb4 > depth t2 ∧ size comb4 < size t2 := by
  decide

/-- The no-rank witness composite: 7 leaves, depth 4 (Theorem 4.1). -/
theorem eStar_tree_facts : depth eStarTree = 4 ∧ size eStarTree = 7 :=
  ⟨rfl, rfl⟩

/-! ## 3. The no-rank theorem, finitized (Theorem 4.1)

The nine events of `D` lying on the two saturated chains from the
minimum `⊥ = link{a,b}` to `E* = link{(a(ab)),(a(b(ab)))}`:

    C₁ : link{a,b} ⋖ resolve{a,b} ⋖ link{a,(ab)} ⋖ resolve{a,(ab)} ⋖ E*
         (length 4)
    C₂ : link{a,b} ⋖ resolve{a,b} ⋖ link{b,(ab)} ⋖ resolve{b,(ab)}
         ⋖ link{a,(b(ab))} ⋖ resolve{a,(b(ab))} ⋖ E*
         (length 6)

Every step is a genuine cover of `D` — verified by hand in
grading_obstruction.md Theorem 4.1 via the cover classification
(Lemma 2.4); in particular BOTH `resolve{a,(ab)}` and
`resolve{a,(b(ab))}` are lower covers of `E*` because the endpoints
`(a(ab))` and `(a(b(ab)))` are subterm-incomparable. -/

/-- The finite fragment of `D` surrounding the no-rank witness: one
constructor per event.  `elemTree` (below) ties each constructor to the
composite tree whose line it draws/resolves. -/
inductive Elem : Type where
  /-- `link{a,b}` — the minimum `⊥` of D. -/
  | linkAB : Elem
  /-- `resolve{a,b}` — reifies `(ab)`. -/
  | resAB : Elem
  /-- `link{a,(ab)}`. -/
  | linkA_AB : Elem
  /-- `resolve{a,(ab)}` — reifies `(a(ab))`; a lower cover of `E*`. -/
  | resA_AB : Elem
  /-- `link{b,(ab)}`. -/
  | linkB_AB : Elem
  /-- `resolve{b,(ab)}` — reifies `(b(ab))`. -/
  | resB_AB : Elem
  /-- `link{a,(b(ab))}`. -/
  | linkA_BAB : Elem
  /-- `resolve{a,(b(ab))}` — reifies `(a(b(ab)))`; the other lower cover of `E*`. -/
  | resA_BAB : Elem
  /-- `E* = link{(a(ab)),(a(b(ab)))}` — the no-rank witness (λ = 7). -/
  | eStar : Elem
  deriving DecidableEq

/-- The composite tree of each event (`tree(e)` of grading_obstruction.md
§1.2): the pair a link draws is the pair its resolve reifies. -/
def elemTree : Elem → Tree
  | .linkAB | .resAB => ab
  | .linkA_AB | .resA_AB => aab
  | .linkB_AB | .resB_AB => bab
  | .linkA_BAB | .resA_BAB => abab
  | .eStar => eStarTree

/-- Event kind: `true` = link, `false` = resolve. -/
def isLink : Elem → Bool
  | .linkAB | .linkA_AB | .linkB_AB | .linkA_BAB | .eStar => true
  | _ => false

/-- Height in `D` of each listed event (grading_obstruction.md Lemma 2.5:
`h(link) = 2δ − 2`, `h(resolve) = 2δ − 1`). -/
def heightOf : Elem → Nat
  | .linkAB => 0
  | .resAB => 1
  | .linkA_AB => 2
  | .resA_AB => 3
  | .linkB_AB => 2
  | .resB_AB => 3
  | .linkA_BAB => 4
  | .resA_BAB => 5
  | .eStar => 6

/-- The height values are the Lemma 2.5 formula evaluated on the
composite trees — the finite fragment is consistently embedded in `D`. -/
theorem heightOf_formula (e : Elem) :
    heightOf e = if isLink e then 2 * depth (elemTree e) - 2
                 else 2 * depth (elemTree e) - 1 := by
  cases e <;> rfl

/-- The nine cover pairs `(lower, upper)` of the chains `C₁` and `C₂` —
the explicit finite cover list (each verified as a cover of `D` in
grading_obstruction.md Theorem 4.1). -/
def coverList : List (Elem × Elem) :=
  [ (.linkAB,    .resAB),                          -- shared bottom step
    (.resAB,     .linkA_AB),                       -- C₁ …
    (.linkA_AB,  .resA_AB),
    (.resA_AB,   .eStar),                          -- height jump 3 → 6
    (.resAB,     .linkB_AB),                       -- C₂ …
    (.linkB_AB,  .resB_AB),
    (.resB_AB,   .linkA_BAB),
    (.linkA_BAB, .resA_BAB),
    (.resA_BAB,  .eStar) ]

/-- A rank function on the fragment: unit increment along every listed
cover. -/
abbrev IsRank (rank : Elem → Nat) : Prop :=
  ∀ p ∈ coverList, rank p.2 = rank p.1 + 1

/-- **No rank function exists** (Theorem 4.1, finitized) — for EVERY
candidate `rank : Elem → ℕ`: walking `C₁` forces
`rank E* = rank ⊥ + 4`, walking `C₂` forces `rank E* = rank ⊥ + 6`;
linear arithmetic refutes. -/
theorem no_rank (rank : Elem → Nat) : ¬ IsRank rank := by
  intro h
  -- Explicit `List.Mem` chains (position in `coverList`), not `decide`:
  -- the core decidable-membership instance carries `propext`.
  have c1 : rank .resAB = rank .linkAB + 1 :=
    h ((.linkAB, .resAB) : Elem × Elem) (List.Mem.head _)
  have c2 : rank .linkA_AB = rank .resAB + 1 :=
    h ((.resAB, .linkA_AB) : Elem × Elem) (.tail _ (.head _))
  have c3 : rank .resA_AB = rank .linkA_AB + 1 :=
    h ((.linkA_AB, .resA_AB) : Elem × Elem) (.tail _ (.tail _ (.head _)))
  have c4 : rank .eStar = rank .resA_AB + 1 :=
    h ((.resA_AB, .eStar) : Elem × Elem)
      (.tail _ (.tail _ (.tail _ (.head _))))
  have c5 : rank .linkB_AB = rank .resAB + 1 :=
    h ((.resAB, .linkB_AB) : Elem × Elem)
      (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have c6 : rank .resB_AB = rank .linkB_AB + 1 :=
    h ((.linkB_AB, .resB_AB) : Elem × Elem)
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have c7 : rank .linkA_BAB = rank .resB_AB + 1 :=
    h ((.resB_AB, .linkA_BAB) : Elem × Elem)
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  have c8 : rank .resA_BAB = rank .linkA_BAB + 1 :=
    h ((.linkA_BAB, .resA_BAB) : Elem × Elem)
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
        (.head _))))))))
  have c9 : rank .eStar = rank .resA_BAB + 1 :=
    h ((.resA_BAB, .eStar) : Elem × Elem)
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
        (.tail _ (.head _)))))))))
  -- Walk C₁: rank E* = rank ⊥ + 4.
  have e1 : rank .eStar = rank .linkAB + 4 := by rw [c4, c3, c2, c1]
  -- Walk C₂: rank E* = rank ⊥ + 6.
  have e2 : rank .eStar = rank .linkAB + 6 := by rw [c9, c8, c7, c6, c5, c1]
  -- 4 = 6 by left cancellation: contradiction.
  exact absurd (add_left_cancelN (rank .linkAB) (e1.symm.trans e2))
    (by decide : (4 : Nat) ≠ 6)

/-- Existential form: there is no rank function on the fragment. -/
theorem no_rank_exists : ¬ ∃ rank : Elem → Nat, IsRank rank :=
  fun ⟨rank, h⟩ => no_rank rank h

/-- The height is strictly monotone with unit steps on every listed
cover EXCEPT the skew cover `resolve{a,(ab)} ⋖ E*` (decidable check of
grading_obstruction.md Theorem 4.2's case analysis on this fragment). -/
theorem covers_unit_except :
    ∀ p ∈ coverList,
      heightOf p.2 = heightOf p.1 + 1 ∨ p = (.resA_AB, .eStar) := by
  decide

/-- The height's cover-defect at the witness: the cover
`resolve{a,(ab)} ⋖ E*` jumps height by 3 (Theorem 4.1's final clause). -/
theorem height_jump : heightOf .eStar = heightOf .resA_AB + 3 := rfl

/-- In particular the height itself is not a rank function on the
fragment (also an instance of `no_rank`). -/
theorem height_not_rank : ¬ IsRank heightOf := by decide

/-! ## 4. The positive half: the level-≤2 zone is graded

The zone `Z = D₃` (grading_obstruction.md Proposition 3.4) restricted to
this fragment: six events, five covers, Hasse diagram a tree.  All five
covers are among the nine above. -/

/-- The five cover pairs of the level-≤2 zone `Z`. -/
def coverListZ : List (Elem × Elem) :=
  [ (.linkAB,   .resAB),
    (.resAB,    .linkA_AB),
    (.resAB,    .linkB_AB),
    (.linkA_AB, .resA_AB),
    (.linkB_AB, .resB_AB) ]

/-- A rank function on the zone: unit increment along every `Z`-cover. -/
abbrev IsRankZ (rank : Elem → Nat) : Prop :=
  ∀ p ∈ coverListZ, rank p.2 = rank p.1 + 1

/-- **The positive half** (Proposition 3.4): on the level-≤2 zone the
height IS a rank function — natural-number strata exist there, with
values 0, 1, 2, 3, 2, 3. -/
theorem height_is_rank_on_Z : IsRankZ heightOf := by decide

/-- **Uniqueness up to the constant** (Theorem 4.2 restricted to the
zone): every rank function on `Z` equals `rank ⊥ + height` at each of
the six zone events — the natural-number strata of the level-≤2 zone
are the height strata and nothing else. -/
theorem rank_on_Z_unique (rank : Elem → Nat) (h : IsRankZ rank) :
    rank .linkAB = rank .linkAB + heightOf .linkAB ∧
    rank .resAB = rank .linkAB + heightOf .resAB ∧
    rank .linkA_AB = rank .linkAB + heightOf .linkA_AB ∧
    rank .resA_AB = rank .linkAB + heightOf .resA_AB ∧
    rank .linkB_AB = rank .linkAB + heightOf .linkB_AB ∧
    rank .resB_AB = rank .linkAB + heightOf .resB_AB := by
  have h1 : rank .resAB = rank .linkAB + 1 :=
    h ((.linkAB, .resAB) : Elem × Elem) (List.Mem.head _)
  have h2 : rank .linkA_AB = rank .resAB + 1 :=
    h ((.resAB, .linkA_AB) : Elem × Elem) (.tail _ (.head _))
  have h3 : rank .linkB_AB = rank .resAB + 1 :=
    h ((.resAB, .linkB_AB) : Elem × Elem) (.tail _ (.tail _ (.head _)))
  have h4 : rank .resA_AB = rank .linkA_AB + 1 :=
    h ((.linkA_AB, .resA_AB) : Elem × Elem)
      (.tail _ (.tail _ (.tail _ (.head _))))
  have h5 : rank .resB_AB = rank .linkB_AB + 1 :=
    h ((.linkB_AB, .resB_AB) : Elem × Elem)
      (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  refine ⟨rfl, h1, ?_, ?_, ?_, ?_⟩
  · rw [h2, h1]; exact rfl
  · rw [h4, h2, h1]; exact rfl
  · rw [h3, h1]; exact rfl
  · rw [h5, h3, h1]; exact rfl

end Grading

end Rederive
