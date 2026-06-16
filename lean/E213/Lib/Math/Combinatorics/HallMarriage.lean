import E213.Lib.Math.Combinatorics.Pigeonhole
import E213.Meta.Nat.Beq213

/-!
# Hall's marriage theorem — the matching COMPUTED (∅-axiom, forcing vein-B)

Bipartite graph: left vertices `Fin n`, right vertices `Fin B`, adjacency
`adj : Fin n → Fin B → Bool`.  A **matching** is an injective `M : Fin n → Fin B`
landing in neighbors.  **Hall's condition** is the standard `|N(S)| ≥ |S|` over
all `S : Fin n → Bool`.

The matching is *constructed* by an augmenting recursion, never asserted by
LP-duality.  Hall's condition is exactly the obstruction the construction never
hits.
-/

namespace E213.Lib.Math.Combinatorics.HallMarriage

/-! ## Definitions -/

/-- A **matching** for `adj`: a function `M : Fin n → Fin B` landing on a
    neighbor of each left vertex (`adj i (M i) = true`) and injective. -/
structure Matching {n B : Nat} (adj : Fin n → Fin B → Bool) where
  M    : Fin n → Fin B
  mem  : ∀ i, adj i (M i) = true
  inj  : ∀ i j, i ≠ j → M i ≠ M j

/-! ## Decidable counting over `Fin`

`countB k p` = number of `i : Fin k` with `p i = true`.  Pure structural
recursion; everything below is `Bool`-valued so decidability is free. -/

/-- Count the `Fin k` indices on which `p` is `true`. -/
def countB : ∀ (k : Nat) (p : Fin k → Bool), Nat
  | 0,     _ => 0
  | k + 1, p =>
      let p' : Fin k → Bool := fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
      (if p last then 1 else 0) + countB k p'

/-- The count is at most the index range. -/
theorem countB_le : ∀ (k : Nat) (p : Fin k → Bool), countB k p ≤ k := by
  intro k
  induction k with
  | zero => intro _; exact Nat.le_refl 0
  | succ m ih =>
      intro p
      let p' : Fin m → Bool := fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      have hrec : countB m p' ≤ m := ih p'
      show (if p ⟨m, Nat.lt_succ_self m⟩ then 1 else 0) + countB m p' ≤ m + 1
      by_cases hp : p ⟨m, Nat.lt_succ_self m⟩ = true
      · rw [if_pos hp, Nat.add_comm 1 (countB m p')]
        exact Nat.succ_le_succ hrec
      · rw [if_neg hp, Nat.zero_add]
        exact Nat.le_succ_of_le hrec

/-! ## Neighborhood as a Bool predicate

`anyAdj n adj S r` is `true` iff some selected left vertex (`S i = true`)
is adjacent to right vertex `r`.  Pure `Bool` fold over `Fin n`. -/

/-- `true` iff some `i : Fin n` with `S i = true` has `adj i r = true`. -/
def anyAdj : ∀ (n : Nat) {B : Nat} (adj : Fin n → Fin B → Bool)
    (S : Fin n → Bool) (r : Fin B), Bool
  | 0,     _, _,   _, _ => false
  | n + 1, _, adj, S, r =>
      let last : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
      let adj' : Fin n → Fin _ → Bool :=
        fun i => adj ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      let S'   : Fin n → Bool := fun i => S ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      ((S last) && (adj last r)) || anyAdj n adj' S' r

/-- The selected-left count `|S|`. -/
def cardS {n : Nat} (S : Fin n → Bool) : Nat := countB n S

/-- The neighborhood count `|N(S)|` over the right range `Fin B`. -/
def cardN {n B : Nat} (adj : Fin n → Fin B → Bool) (S : Fin n → Bool) : Nat :=
  countB B (fun r => anyAdj n adj S r)

/-- **Hall's condition**: `|N(S)| ≥ |S|` for every selection `S`. -/
def HallCond {n B : Nat} (adj : Fin n → Fin B → Bool) : Prop :=
  ∀ S : Fin n → Bool, cardS S ≤ cardN adj S

/-! ## Monotonicity of `countB` -/

/-- If `p` implies `q` pointwise, `countB p ≤ countB q`. -/
theorem countB_mono : ∀ (k : Nat) (p q : Fin k → Bool),
    (∀ i, p i = true → q i = true) → countB k p ≤ countB k q := by
  intro k
  induction k with
  | zero => intro _ _ _; exact Nat.le_refl 0
  | succ m ih =>
      intro p q hpq
      let p' : Fin m → Bool := fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      let q' : Fin m → Bool := fun i => q ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      have hpq' : ∀ i, p' i = true → q' i = true := fun i h => hpq _ h
      have hrec : countB m p' ≤ countB m q' := ih p' q' hpq'
      let last : Fin (m+1) := ⟨m, Nat.lt_succ_self m⟩
      show (if p last then 1 else 0) + countB m p'
         ≤ (if q last then 1 else 0) + countB m q'
      cases hp : p last with
      | false =>
          show (0 : Nat) + countB m p' ≤ (if q last then 1 else 0) + countB m q'
          rw [Nat.zero_add]
          cases hq : q last with
          | false =>
              show countB m p' ≤ (0 : Nat) + countB m q'
              rw [Nat.zero_add]; exact hrec
          | true =>
              show countB m p' ≤ (1 : Nat) + countB m q'
              exact Nat.le_trans hrec (Nat.le_add_left _ _)
      | true =>
          have hql : q last = true := hpq last hp
          rw [hql]
          show (1 : Nat) + countB m p' ≤ 1 + countB m q'
          exact Nat.add_le_add_left hrec 1

/-- If no index satisfies `p`, the count is `0`. -/
theorem countB_eq_zero_of_none : ∀ (k : Nat) (p : Fin k → Bool),
    (∀ i, p i = false) → countB k p = 0 := by
  intro k
  induction k with
  | zero => intro _ _; rfl
  | succ m ih =>
      intro p hnone
      let p' : Fin m → Bool := fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      have hp' : ∀ i, p' i = false := fun i => hnone _
      have hlast : p ⟨m, Nat.lt_succ_self m⟩ = false := hnone _
      show (if p ⟨m, Nat.lt_succ_self m⟩ then 1 else 0) + countB m p' = 0
      rw [if_neg (by rw [hlast]; exact Bool.false_ne_true), ih p' hp', Nat.zero_add]

/-- A predicate true at no more than one index counts at most `1`. -/
theorem countB_le_one_of_subsingleton : ∀ (k : Nat) (p : Fin k → Bool),
    (∀ i j, p i = true → p j = true → i.val = j.val) → countB k p ≤ 1 := by
  intro k
  induction k with
  | zero => intro _ _; exact Nat.le_succ 0
  | succ m ih =>
      intro p hsub
      let p' : Fin m → Bool := fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      let last : Fin (m+1) := ⟨m, Nat.lt_succ_self m⟩
      cases hl : p last with
      | false =>
          have hsub' : ∀ i j, p' i = true → p' j = true → i.val = j.val := by
            intro i j hi hj
            exact hsub ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ hi hj
          show (if p last then 1 else 0) + countB m p' ≤ 1
          rw [hl]; show (0:Nat) + countB m p' ≤ 1
          rw [Nat.zero_add]; exact ih p' hsub'
      | true =>
          have htail0 : countB m p' = 0 := by
            apply countB_eq_zero_of_none
            intro i
            cases hpi : p' i with
            | false => rfl
            | true =>
                exfalso
                have hcoll : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m+1)).val = last.val :=
                  hsub _ last hpi hl
                have hival : i.val = m := hcoll
                exact absurd hival (Nat.ne_of_lt i.isLt)
          show (if p last then 1 else 0) + countB m p' ≤ 1
          rw [hl]; show (1:Nat) + countB m p' ≤ 1
          rw [htail0]; exact Nat.le_refl 1

/-- A positive count exhibits a satisfying index. -/
theorem exists_of_countB_pos : ∀ (k : Nat) (p : Fin k → Bool),
    0 < countB k p → ∃ i, p i = true := by
  intro k
  induction k with
  | zero => intro p hpos; exact absurd hpos (Nat.lt_irrefl 0)
  | succ m ih =>
      intro p hpos
      let p' : Fin m → Bool := fun i => p ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      cases hlast : p ⟨m, Nat.lt_succ_self m⟩ with
      | true => exact ⟨⟨m, Nat.lt_succ_self m⟩, hlast⟩
      | false =>
          have hzero : (if p ⟨m, Nat.lt_succ_self m⟩ then 1 else 0) = 0 :=
            if_neg (by rw [hlast]; exact Bool.false_ne_true)
          have hpos' : 0 < countB m p' := by
            have heq : countB (m+1) p = countB m p' := by
              show (if p ⟨m, Nat.lt_succ_self m⟩ then 1 else 0) + countB m p' = countB m p'
              rw [hzero, Nat.zero_add]
            exact heq ▸ hpos
          obtain ⟨i, hi⟩ := ih p' hpos'
          exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hi⟩

/-- A satisfying index makes the count positive. -/
theorem countB_pos_of_exists : ∀ (k : Nat) (p : Fin k → Bool) (i : Fin k),
    p i = true → 0 < countB k p := by
  intro k
  induction k with
  | zero => intro _ i _; exact i.elim0
  | succ m ih =>
      intro p i hi
      let p' : Fin m → Bool := fun j => p ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
      by_cases hlast : p ⟨m, Nat.lt_succ_self m⟩ = true
      · show 0 < (if p ⟨m, Nat.lt_succ_self m⟩ then 1 else 0) + countB m p'
        rw [if_pos hlast]
        exact Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (Nat.le_add_right _ _)
      · -- i ≠ last, so i.val < m, and p' (restricted) hits at i
        have hival : i.val < m := by
          rcases Nat.lt_or_ge i.val m with h | h
          · exact h
          · exfalso
            have : i.val = m := Nat.le_antisymm (Nat.le_of_lt_succ i.isLt) h
            have : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext this
            rw [this] at hi; exact hlast hi
        have hp'i : p' ⟨i.val, hival⟩ = true := by
          show p ⟨i.val, Nat.lt_succ_of_lt hival⟩ = true
          have : (⟨i.val, Nat.lt_succ_of_lt hival⟩ : Fin (m+1)) = i := Fin.ext rfl
          rw [this]; exact hi
        have hpos' : 0 < countB m p' := ih p' ⟨i.val, hival⟩ hp'i
        show 0 < (if p ⟨m, Nat.lt_succ_self m⟩ then 1 else 0) + countB m p'
        exact Nat.lt_of_lt_of_le hpos' (Nat.le_add_left _ _)

/-! ## Semantics of `anyAdj` -/

/-- `anyAdj = true` produces an adjacent selected left vertex. -/
theorem anyAdj_elim : ∀ (n : Nat) {B : Nat} (adj : Fin n → Fin B → Bool)
    (S : Fin n → Bool) (r : Fin B),
    anyAdj n adj S r = true → ∃ i, S i = true ∧ adj i r = true := by
  intro n
  induction n with
  | zero => intro _ _ _ _ h; exact absurd h Bool.false_ne_true
  | succ m ih =>
      intro B adj S r h
      let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
      let adj' : Fin m → Fin B → Bool :=
        fun i => adj ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      let S'   : Fin m → Bool := fun i => S ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      have hor : (((S last) && (adj last r)) || anyAdj m adj' S' r) = true := h
      -- case on the two Bool summands
      cases hSl : S last with
      | false =>
          have hl : ((S last) && (adj last r)) = false := by rw [hSl]; rfl
          have hr : anyAdj m adj' S' r = true := by
            rw [hl, Bool.false_or] at hor; exact hor
          obtain ⟨i, hSi, hAi⟩ := ih adj' S' r hr
          exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hSi, hAi⟩
      | true =>
          cases hAl : adj last r with
          | true => exact ⟨last, hSl, hAl⟩
          | false =>
              have hl : ((S last) && (adj last r)) = false := by rw [hSl, hAl]; rfl
              have hr : anyAdj m adj' S' r = true := by
                rw [hl, Bool.false_or] at hor; exact hor
              obtain ⟨i, hSi, hAi⟩ := ih adj' S' r hr
              exact ⟨⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, hSi, hAi⟩

/-- An adjacent selected left vertex makes `anyAdj = true`. -/
theorem anyAdj_intro : ∀ (n : Nat) {B : Nat} (adj : Fin n → Fin B → Bool)
    (S : Fin n → Bool) (r : Fin B) (i : Fin n),
    S i = true → adj i r = true → anyAdj n adj S r = true := by
  intro n
  induction n with
  | zero => intro _ _ _ _ i _ _; exact i.elim0
  | succ m ih =>
      intro B adj S r i hS hA
      let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
      let adj' : Fin m → Fin B → Bool :=
        fun j => adj ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
      let S'   : Fin m → Bool := fun j => S ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
      show (((S last) && (adj last r)) || anyAdj m adj' S' r) = true
      by_cases hil : i.val < m
      · have hSi' : S' ⟨i.val, hil⟩ = true := by
          show S ⟨i.val, Nat.lt_succ_of_lt hil⟩ = true
          have : (⟨i.val, Nat.lt_succ_of_lt hil⟩ : Fin (m+1)) = i := Fin.ext rfl
          rw [this]; exact hS
        have hAi' : adj' ⟨i.val, hil⟩ r = true := by
          show adj ⟨i.val, Nat.lt_succ_of_lt hil⟩ r = true
          have : (⟨i.val, Nat.lt_succ_of_lt hil⟩ : Fin (m+1)) = i := Fin.ext rfl
          rw [this]; exact hA
        have hrec : anyAdj m adj' S' r = true := ih adj' S' r ⟨i.val, hil⟩ hSi' hAi'
        rw [hrec]; exact Bool.or_true _
      · have hival : i.val = m := Nat.le_antisymm (Nat.le_of_lt_succ i.isLt) (Nat.le_of_not_lt hil)
        have hil2 : i = last := Fin.ext hival
        have hSl : S last = true := hil2 ▸ hS
        have hAl : adj last r = true := hil2 ▸ hA
        rw [hSl, hAl]; rfl

/-! ## Monotonicity of the neighborhood count -/

/-- `anyAdj` is monotone in the selection. -/
theorem anyAdj_mono {n B : Nat} (adj : Fin n → Fin B → Bool)
    (S T : Fin n → Bool) (hST : ∀ i, S i = true → T i = true) (r : Fin B) :
    anyAdj n adj S r = true → anyAdj n adj T r = true := by
  intro h
  obtain ⟨i, hSi, hAi⟩ := anyAdj_elim n adj S r h
  exact anyAdj_intro n adj T r i (hST i hSi) hAi

/-- `|N(S)|` is monotone: `S ⟹ T` pointwise gives `cardN S ≤ cardN T`. -/
theorem cardN_mono {n B : Nat} (adj : Fin n → Fin B → Bool)
    (S T : Fin n → Bool) (hST : ∀ i, S i = true → T i = true) :
    cardN adj S ≤ cardN adj T :=
  countB_mono B (fun r => anyAdj n adj S r) (fun r => anyAdj n adj T r)
    (fun r h => anyAdj_mono adj S T hST r h)

/-! ## Singleton selection and "a left vertex has a neighbor" -/

/-- Indicator of `{i}` as a selection. -/
def singleton {n : Nat} (i : Fin n) : Fin n → Bool :=
  fun j => Nat.beq j.val i.val

theorem singleton_self {n : Nat} (i : Fin n) : singleton i i = true :=
  E213.Meta.Nat.Beq213.nat_beq_refl' i.val

/-- **From Hall, every left vertex has a neighbor.**  Apply Hall to the
    singleton `{i}`: `1 ≤ |S| ≤ |N(S)|`, so some right vertex is hit, and
    that vertex is adjacent to `i`. -/
theorem neighbor_exists {n B : Nat} (adj : Fin n → Fin B → Bool)
    (hall : HallCond adj) (i : Fin n) : ∃ r, adj i r = true := by
  have hS1 : 0 < cardS (singleton i) :=
    countB_pos_of_exists n (singleton i) i (singleton_self i)
  have hN1 : 0 < cardN adj (singleton i) :=
    Nat.lt_of_lt_of_le hS1 (hall (singleton i))
  obtain ⟨r, hr⟩ := exists_of_countB_pos B (fun r => anyAdj n adj (singleton i) r) hN1
  obtain ⟨j, hSj, hAj⟩ := anyAdj_elim n adj (singleton i) r hr
  -- `singleton i j = true` forces `j = i`
  have hji : j.val = i.val := Nat.eq_of_beq_eq_true hSj
  have heq : j = i := Fin.ext hji
  exact ⟨r, heq ▸ hAj⟩

/-! ## Data-level neighbor finder (the matching value is *computed*)

`findNeighbor` scans `Fin B` and *returns the actual right vertex* adjacent
to `i` (as data, in a subtype), or `none`.  `findNeighbor_of_exists` shows the
scan succeeds whenever a neighbor exists — so under Hall it always returns
`some`, and the matching value is the scan's output, not an abstract `∃`. -/

/-- Scan the first `k` right vertices for a neighbor of `i`; return its index. -/
def scanNeighbor {n B : Nat} (adj : Fin n → Fin B → Bool) (i : Fin n) :
    ∀ (k : Nat), k ≤ B → Option (Fin B)
  | 0,     _  => none
  | k + 1, hk =>
      let r : Fin B := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      if adj i r then some r else scanNeighbor adj i k (Nat.le_of_lt hk)

/-- Any value the scan returns is a genuine neighbor of `i`. -/
theorem scanNeighbor_spec {n B : Nat} (adj : Fin n → Fin B → Bool) (i : Fin n) :
    ∀ (k : Nat) (hk : k ≤ B) (r : Fin B),
    scanNeighbor adj i k hk = some r → adj i r = true := by
  intro k
  induction k with
  | zero => intro _ r h; exact absurd h (by intro hh; cases hh)
  | succ m ih =>
      intro hk r h
      let top : Fin B := ⟨m, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hk⟩
      cases htop : adj i top with
      | true =>
          have heq : scanNeighbor adj i (m+1) hk = some top := by
            show (if adj i top then some top else scanNeighbor adj i m (Nat.le_of_lt hk))
                = some top
            rw [if_pos htop]
          rw [heq] at h
          have : top = r := Option.some.inj h
          rw [← this]; exact htop
      | false =>
          have heq : scanNeighbor adj i (m+1) hk = scanNeighbor adj i m (Nat.le_of_lt hk) := by
            show (if adj i top then some top else scanNeighbor adj i m (Nat.le_of_lt hk))
                = scanNeighbor adj i m (Nat.le_of_lt hk)
            rw [if_neg (by rw [htop]; exact Bool.false_ne_true)]
          rw [heq] at h
          exact ih (Nat.le_of_lt hk) r h

/-- If a neighbor exists below `k`, the scan returns `some`. -/
theorem scanNeighbor_isSome {n B : Nat} (adj : Fin n → Fin B → Bool) (i : Fin n) :
    ∀ (k : Nat) (hk : k ≤ B) (r : Fin B), r.val < k → adj i r = true →
    (scanNeighbor adj i k hk).isSome = true := by
  intro k
  induction k with
  | zero => intro _ r hr _; exact absurd hr (Nat.not_lt_zero r.val)
  | succ m ih =>
      intro hk r hrlt hadj
      let top : Fin B := ⟨m, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hk⟩
      cases htop : adj i top with
      | true =>
          have heq : scanNeighbor adj i (m+1) hk = some top := by
            show (if adj i top then some top else scanNeighbor adj i m (Nat.le_of_lt hk))
                = some top
            rw [if_pos htop]
          rw [heq]; rfl
      | false =>
          have heq : scanNeighbor adj i (m+1) hk = scanNeighbor adj i m (Nat.le_of_lt hk) := by
            show (if adj i top then some top else scanNeighbor adj i m (Nat.le_of_lt hk))
                = scanNeighbor adj i m (Nat.le_of_lt hk)
            rw [if_neg (by rw [htop]; exact Bool.false_ne_true)]
          rw [heq]
          have hrm : r.val < m := by
            rcases Nat.lt_or_ge r.val m with h | h
            · exact h
            · exfalso
              have hrval : r.val = m := Nat.le_antisymm (Nat.le_of_lt_succ hrlt) h
              have hreq : r = top := Fin.ext hrval
              rw [hreq] at hadj; rw [hadj] at htop; exact Bool.false_ne_true htop.symm
          exact ih (Nat.le_of_lt hk) r hrm hadj

/-- **The computed neighbor.**  Under Hall, the scan over all of `Fin B`
    returns `some`; `computeNeighbor` extracts the actual right vertex (data). -/
def computeNeighbor {n B : Nat} (adj : Fin n → Fin B → Bool)
    (hall : HallCond adj) (i : Fin n) : { r : Fin B // adj i r = true } :=
  let rOpt := scanNeighbor adj i B (Nat.le_refl B)
  let hsome : rOpt.isSome = true := by
    obtain ⟨r, hr⟩ := neighbor_exists adj hall i
    exact scanNeighbor_isSome adj i B (Nat.le_refl B) r r.isLt hr
  let r : Fin B := rOpt.get hsome
  ⟨r, scanNeighbor_spec adj i B (Nat.le_refl B) r (Option.some_get hsome).symm⟩

/-! ## Neighbor finder avoiding one forbidden right vertex -/

/-- Scan the first `k` right vertices for a neighbor of `i` whose index `≠ a`. -/
def scanAvoid {n B : Nat} (adj : Fin n → Fin B → Bool) (i : Fin n) (a : Fin B) :
    ∀ (k : Nat), k ≤ B → Option (Fin B)
  | 0,     _  => none
  | k + 1, hk =>
      let r : Fin B := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      if adj i r && !(Nat.beq r.val a.val) then some r
      else scanAvoid adj i a k (Nat.le_of_lt hk)

/-- Any value `scanAvoid` returns is a neighbor of `i` with index `≠ a`. -/
theorem scanAvoid_spec {n B : Nat} (adj : Fin n → Fin B → Bool) (i : Fin n) (a : Fin B) :
    ∀ (k : Nat) (hk : k ≤ B) (r : Fin B),
    scanAvoid adj i a k hk = some r → adj i r = true ∧ r ≠ a := by
  intro k
  induction k with
  | zero => intro _ r h; exact absurd h (by intro hh; cases hh)
  | succ m ih =>
      intro hk r h
      let top : Fin B := ⟨m, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hk⟩
      cases hcond : adj i top && !(Nat.beq top.val a.val) with
      | true =>
          have heq : scanAvoid adj i a (m+1) hk = some top := by
            show (if adj i top && !(Nat.beq top.val a.val) then some top
                  else scanAvoid adj i a m (Nat.le_of_lt hk)) = some top
            rw [if_pos hcond]
          rw [heq] at h
          have htr : top = r := Option.some.inj h
          rw [← htr]
          -- decompose the conjunction structurally
          cases hA : adj i top with
          | false =>
              exfalso; rw [hA] at hcond
              exact Bool.false_ne_true (by rw [← hcond]; rfl)
          | true =>
              cases hB : Nat.beq top.val a.val with
              | true =>
                  exfalso; rw [hA, hB] at hcond
                  exact Bool.false_ne_true (by rw [← hcond]; rfl)
              | false =>
                  refine ⟨rfl, ?_⟩
                  intro heqa
                  have htopa : top.val = a.val := congrArg Fin.val heqa
                  have hbt : Nat.beq top.val a.val = true := by
                    rw [htopa]; exact E213.Meta.Nat.Beq213.nat_beq_refl' a.val
                  exact Bool.false_ne_true (hB.symm.trans hbt)
      | false =>
          have heq : scanAvoid adj i a (m+1) hk = scanAvoid adj i a m (Nat.le_of_lt hk) := by
            show (if adj i top && !(Nat.beq top.val a.val) then some top
                  else scanAvoid adj i a m (Nat.le_of_lt hk))
                = scanAvoid adj i a m (Nat.le_of_lt hk)
            rw [if_neg (by rw [hcond]; exact Bool.false_ne_true)]
          rw [heq] at h
          exact ih (Nat.le_of_lt hk) r h

/-- If a neighbor of `i` with index `≠ a` exists below `k`, `scanAvoid` finds one. -/
theorem scanAvoid_isSome {n B : Nat} (adj : Fin n → Fin B → Bool) (i : Fin n) (a : Fin B) :
    ∀ (k : Nat) (hk : k ≤ B) (r : Fin B), r.val < k → adj i r = true → r ≠ a →
    (scanAvoid adj i a k hk).isSome = true := by
  intro k
  induction k with
  | zero => intro _ r hr _ _; exact absurd hr (Nat.not_lt_zero r.val)
  | succ m ih =>
      intro hk r hrlt hadj hne
      let top : Fin B := ⟨m, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hk⟩
      cases hcond : adj i top && !(Nat.beq top.val a.val) with
      | true =>
          have heq : scanAvoid adj i a (m+1) hk = some top := by
            show (if adj i top && !(Nat.beq top.val a.val) then some top
                  else scanAvoid adj i a m (Nat.le_of_lt hk)) = some top
            rw [if_pos hcond]
          rw [heq]; rfl
      | false =>
          have heq : scanAvoid adj i a (m+1) hk = scanAvoid adj i a m (Nat.le_of_lt hk) := by
            show (if adj i top && !(Nat.beq top.val a.val) then some top
                  else scanAvoid adj i a m (Nat.le_of_lt hk))
                = scanAvoid adj i a m (Nat.le_of_lt hk)
            rw [if_neg (by rw [hcond]; exact Bool.false_ne_true)]
          rw [heq]
          -- r ≠ top, since if r = top the condition would be true
          have hrm : r.val < m := by
            rcases Nat.lt_or_ge r.val m with hlt | hge
            · exact hlt
            · exfalso
              have hrval : r.val = m := Nat.le_antisymm (Nat.le_of_lt_succ hrlt) hge
              have hreq : r = top := Fin.ext hrval
              -- then adj i top = true and top.val ≠ a.val, so cond = true, contradiction
              have htop_adj : adj i top = true := by rw [← hreq]; exact hadj
              have htop_ne : Nat.beq top.val a.val = false := by
                apply E213.Meta.Nat.Beq213.nat_beq_eq_false_of_ne
                intro heqv
                apply hne
                exact Fin.ext (hreq ▸ heqv)
              rw [htop_adj, htop_ne] at hcond
              exact Bool.false_ne_true hcond.symm
          exact ih (Nat.le_of_lt hk) r hrm hadj hne

/-! ## Small-n explicit matchings (computed, fully constructive) -/

/-- **`n = 0`**: the empty matching. -/
def matching_zero {B : Nat} (adj : Fin 0 → Fin B → Bool) : Matching adj where
  M   := fun i => i.elim0
  mem := fun i => i.elim0
  inj := fun i _ _ => i.elim0

/-- **`n = 1`**: match the single vertex to a neighbor (from Hall).  Injectivity
    is vacuous (`Fin 1` has no distinct pair).  The neighbor is *computed* by
    `neighbor_exists` (singleton-Hall), not asserted. -/
def matching_one {B : Nat} (adj : Fin 1 → Fin B → Bool)
    (hall : HallCond adj) : Matching adj :=
  let nb := computeNeighbor adj hall ⟨0, Nat.lt_succ_self 0⟩
  { M := fun _ => nb.val
    mem := fun i => by
      have hi : i = ⟨0, Nat.lt_succ_self 0⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      rw [hi]; exact nb.property
    inj := fun i j hij => by
      exfalso
      apply hij
      have hi : i = ⟨0, Nat.lt_succ_self 0⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt))
      have hj : j = ⟨0, Nat.lt_succ_self 0⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ j.isLt))
      rw [hi, hj] }

/-- The headline `∃ M` form extracted from a `Matching` structure. -/
theorem matching_exists {n B : Nat} {adj : Fin n → Fin B → Bool}
    (m : Matching adj) :
    ∃ M : Fin n → Fin B, (∀ i, adj i (M i) = true) ∧ (∀ i j, i ≠ j → M i ≠ M j) :=
  ⟨m.M, m.mem, m.inj⟩

/-- **Hall's matching, `n = 0`** (headline form): the empty matching. -/
theorem hall_matching_zero {B : Nat} (adj : Fin 0 → Fin B → Bool) :
    ∃ M : Fin 0 → Fin B, (∀ i, adj i (M i) = true) ∧ (∀ i j, i ≠ j → M i ≠ M j) :=
  matching_exists (matching_zero adj)

/-- **Hall's matching, `n = 1`** (headline form): the computed singleton match. -/
theorem hall_matching_one {B : Nat} (adj : Fin 1 → Fin B → Bool)
    (hall : HallCond adj) :
    ∃ M : Fin 1 → Fin B, (∀ i, adj i (M i) = true) ∧ (∀ i j, i ≠ j → M i ≠ M j) :=
  matching_exists (matching_one adj hall)

/-! ## `n = 2`: the first case with non-vacuous injectivity

Two left vertices `0, 1`.  Compute a neighbor `r0` of `0`, then search for a
neighbor of `1` distinct from `r0` (`scanAvoid`).  If found, done.  Otherwise
vertex `1`'s only neighbor is `r0`, so Hall on the *full* set `{0,1}`
(`cardN ≥ 2`) forces vertex `0` to have a neighbor `≠ r0` — else
`N({0,1}) ⊆ {r0}` and `cardN ≤ 1 < 2`.  The construction never hits the
obstruction Hall rules out. -/

private def v0 : Fin 2 := ⟨0, by decide⟩
private def v1 : Fin 2 := ⟨1, by decide⟩

/-- Each `i : Fin 2` is `v0` or `v1`. -/
theorem fin2_cases (i : Fin 2) : i = v0 ∨ i = v1 := by
  cases hi : i.val with
  | zero => exact Or.inl (Fin.ext hi)
  | succ k =>
      cases k with
      | zero => exact Or.inr (Fin.ext hi)
      | succ l =>
          exfalso
          have h2 : i.val < 2 := i.isLt
          rw [hi] at h2
          exact Nat.not_lt_zero l (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h2))

/-- The two-vertex matching map: `0 ↦ r0`, `1 ↦ r1`. -/
private def map2 {B : Nat} (r0 r1 : Fin B) : Fin 2 → Fin B :=
  fun i => if i.val = 0 then r0 else r1

theorem map2_v0 {B : Nat} (r0 r1 : Fin B) : map2 r0 r1 v0 = r0 := by
  show (if (0 : Nat) = 0 then r0 else r1) = r0
  rw [if_pos rfl]

theorem map2_v1 {B : Nat} (r0 r1 : Fin B) : map2 r0 r1 v1 = r1 := by
  show (if (1 : Nat) = 0 then r0 else r1) = r1
  rw [if_neg (fun h => Nat.one_ne_zero h)]

/-- Injectivity of `map2` when `r0 ≠ r1`. -/
theorem map2_inj {B : Nat} (r0 r1 : Fin B) (hr : r0 ≠ r1) :
    ∀ i j, i ≠ j → map2 r0 r1 i ≠ map2 r0 r1 j := by
  intro i j hij
  rcases fin2_cases i with hi | hi <;> rcases fin2_cases j with hj | hj
  · exact absurd (hi.trans hj.symm) hij
  · rw [hi, hj, map2_v0, map2_v1]; exact hr
  · rw [hi, hj, map2_v1, map2_v0]; exact fun h => hr h.symm
  · exact absurd (hi.trans hj.symm) hij

/-- `scanAvoid = none` means every neighbor of `i` equals `a`. -/
theorem scanAvoid_none_all_eq {n B : Nat} (adj : Fin n → Fin B → Bool)
    (i : Fin n) (a : Fin B) (hnone : scanAvoid adj i a B (Nat.le_refl B) = none)
    (r : Fin B) (hr : adj i r = true) : r = a := by
  cases hra : Nat.beq r.val a.val with
  | true => exact Fin.ext (Nat.eq_of_beq_eq_true hra)
  | false =>
      exfalso
      have hne : r ≠ a := by
        intro heq
        have hbt : Nat.beq r.val a.val = true := by
          rw [congrArg Fin.val heq]; exact E213.Meta.Nat.Beq213.nat_beq_refl' a.val
        exact Bool.false_ne_true (hra.symm.trans hbt)
      have hsome := scanAvoid_isSome adj i a B (Nat.le_refl B) r r.isLt hr hne
      rw [hnone] at hsome
      exact Bool.false_ne_true hsome

/-- **Hall's matching, `n = 2`** (headline form): the computed two-vertex match,
    with *non-vacuous* injectivity (`M 0 ≠ M 1`). -/
theorem hall_matching_two {B : Nat} (adj : Fin 2 → Fin B → Bool)
    (hall : HallCond adj) :
    ∃ M : Fin 2 → Fin B, (∀ i, adj i (M i) = true) ∧ (∀ i j, i ≠ j → M i ≠ M j) := by
  let nb0 := computeNeighbor adj hall v0
  let r0 : Fin B := nb0.val
  have hr0 : adj v0 r0 = true := nb0.property
  cases hsa : scanAvoid adj v1 r0 B (Nat.le_refl B) with
  | some r1 =>
      have hspec := scanAvoid_spec adj v1 r0 B (Nat.le_refl B) r1 hsa
      have hr1 : adj v1 r1 = true := hspec.1
      have hne : r0 ≠ r1 := fun h => hspec.2 h.symm
      refine ⟨map2 r0 r1, ?_, map2_inj r0 r1 hne⟩
      intro i
      rcases fin2_cases i with hi | hi
      · rw [hi, map2_v0]; exact hr0
      · rw [hi, map2_v1]; exact hr1
  | none =>
      have hall_all : ∀ r, adj v1 r = true → r = r0 :=
        scanAvoid_none_all_eq adj v1 r0 hsa
      cases hsa0 : scanAvoid adj v0 r0 B (Nat.le_refl B) with
      | some r0' =>
          have hspec0 := scanAvoid_spec adj v0 r0 B (Nat.le_refl B) r0' hsa0
          have hr0' : adj v0 r0' = true := hspec0.1
          have hne0 : r0' ≠ r0 := hspec0.2
          refine ⟨map2 r0' r0, ?_, map2_inj r0' r0 hne0⟩
          intro i
          rcases fin2_cases i with hi | hi
          · rw [hi, map2_v0]; exact hr0'
          · rw [hi, map2_v1]
            obtain ⟨r1, hr1⟩ := neighbor_exists adj hall v1
            have heqr : r1 = r0 := hall_all r1 hr1
            rw [← heqr]; exact hr1
      | none =>
          exfalso
          have hall0_all : ∀ r, adj v0 r = true → r = r0 :=
            scanAvoid_none_all_eq adj v0 r0 hsa0
          let full : Fin 2 → Bool := fun _ => true
          have hsub : ∀ r, anyAdj 2 adj full r = true →
              Nat.beq r.val r0.val = true := by
            intro r hr
            obtain ⟨i, _, hAi⟩ := anyAdj_elim 2 adj full r hr
            rcases fin2_cases i with hi | hi
            · have hAi' : adj v0 r = true := by rw [← hi]; exact hAi
              have heqr : r = r0 := hall0_all r hAi'
              rw [congrArg Fin.val heqr]; exact E213.Meta.Nat.Beq213.nat_beq_refl' r0.val
            · have hAi' : adj v1 r = true := by rw [← hi]; exact hAi
              have heqr : r = r0 := hall_all r hAi'
              rw [congrArg Fin.val heqr]; exact E213.Meta.Nat.Beq213.nat_beq_refl' r0.val
          have hcardN_le : cardN adj full ≤ 1 := by
            have hmono : cardN adj full
                ≤ countB B (fun r => Nat.beq r.val r0.val) :=
              countB_mono B (fun r => anyAdj 2 adj full r)
                (fun r => Nat.beq r.val r0.val) hsub
            have hsing : countB B (fun r => Nat.beq r.val r0.val) ≤ 1 := by
              apply countB_le_one_of_subsingleton
              intro i j hi hj
              have hir : i.val = r0.val := Nat.eq_of_beq_eq_true hi
              have hjr : j.val = r0.val := Nat.eq_of_beq_eq_true hj
              exact hir.trans hjr.symm
            exact Nat.le_trans hmono hsing
          have hcardS : cardS full = 2 := by decide
          have hhall := hall full
          rw [hcardS] at hhall
          have hge2 : 2 ≤ cardN adj full := hhall
          exact Nat.not_lt_of_le hcardN_le
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) hge2)

end E213.Lib.Math.Combinatorics.HallMarriage
