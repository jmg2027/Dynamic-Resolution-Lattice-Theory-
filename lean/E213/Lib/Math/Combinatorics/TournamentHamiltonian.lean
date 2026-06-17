/-!
# Redei's theorem, ∅-axiom: every tournament has a Hamiltonian path, COMPUTED by insertion

A **tournament** on `n` players is `beats : Nat → Nat → Bool`, total + antisymmetric
on `[0,n)`.  **Redei's theorem**: every tournament has a Hamiltonian path — an ordering
of `{0,…,n-1}` with `beats vₖ vₖ₊₁` for all `k`.

Classically a non-constructive existence (or a "longest path is Hamiltonian" extremal
argument).  ∅-axiom forces the **insertion algorithm**: the path is assembled
vertex-by-vertex, each insertion a decidable scan placing `x` at the seam where it flips
from loser to winner (totality guarantees the seam exists).  The Hamiltonian path is an
**insertion-sort output** — computed, not extracted.

Everything is `List Nat` + structural `Bool`/`List`-recursion (no `List.get`, no
`List.mem`, no `propext`).  PURE: `#print axioms` → "does not depend on any axioms".
-/

namespace E213.Lib.Math.Combinatorics.TournamentHamiltonian

/-! ## Chain predicate: consecutive `beats` along a list -/

/-- `chainBeats beats l = true` iff every consecutive pair in `l` satisfies `beats`.
    Structural recursion on the list shape — no indexing, no `propext`. -/
def chainBeats (beats : Nat → Nat → Bool) : List Nat → Bool
  | []           => true
  | [_]          => true
  | a :: b :: rest => beats a b && chainBeats beats (b :: rest)

/-- Structural membership: `memN x l = true` iff `x` occurs in `l`. -/
def memN (x : Nat) : List Nat → Bool
  | []      => false
  | a :: as => (x == a) || memN x as

/-- Structural "all elements `< n`". -/
def allLt (n : Nat) : List Nat → Bool
  | []      => true
  | a :: as => (a < n) && allLt n as

/-- Structural nodup. -/
def nodupN : List Nat → Bool
  | []      => true
  | a :: as => (! memN a as) && nodupN as

/-! ## The insertion engine

Scan `l` for the first element the newcomer `x` beats; insert `x` *before* it.
If `x` is beaten by every element, append `x` at the end. -/

/-- Insert `x` into `l` at the first place `x` beats the current head; else append. -/
def insertHam (beats : Nat → Nat → Bool) (x : Nat) : List Nat → List Nat
  | []      => [x]
  | a :: as => if beats x a then x :: a :: as else a :: insertHam beats x as

/-! ### PURE Bool `&&` decomposition (no `propext`)

`Bool.and_eq_true` is an `Iff`, so it leaks `propext`.  These structural
case-splits on the two Bools are ∅-axiom. -/

/-- `p && q = true → p = true`.  Term-mode case on `p`. -/
theorem and_left {p q : Bool} (h : (p && q) = true) : p = true := by
  cases p with
  | false => exact (Bool.noConfusion h)
  | true  => rfl

/-- `p && q = true → q = true`.  Term-mode case on `p`. -/
theorem and_right {p q : Bool} (h : (p && q) = true) : q = true := by
  cases p with
  | false => exact (Bool.noConfusion h)
  | true  => exact h

/-- `p = true → q = true → p && q = true`.  Term-mode. -/
theorem and_intro {p q : Bool} (hp : p = true) (hq : q = true) : (p && q) = true := by
  cases p with
  | false => exact (Bool.noConfusion hp)
  | true  => exact hq

/-- `a || (b || c) = b || (a || c)`, PURE.  Full Bool case split. -/
theorem or_left_comm (a b c : Bool) : (a || (b || c)) = (b || (a || c)) := by
  cases a with
  | false => cases b with
             | false => rfl
             | true  => rfl
  | true  => cases b with
             | false => rfl
             | true  => rfl

/-! ### `chainBeats` of a `cons` unfolds to head-edge `&&` tail-chain -/

theorem chainBeats_cons_cons (beats : Nat → Nat → Bool) (a b : Nat) (rest : List Nat) :
    chainBeats beats (a :: b :: rest) = (beats a b && chainBeats beats (b :: rest)) := rfl

/-- The head edge holds when the chain holds (on a `≥ 2` list). -/
theorem head_edge_of_chain {beats : Nat → Nat → Bool} {a b : Nat} {rest : List Nat}
    (h : chainBeats beats (a :: b :: rest) = true) : beats a b = true :=
  and_left (chainBeats_cons_cons beats a b rest ▸ h)

/-- The tail chain holds when the chain holds. -/
theorem tail_chain_of_chain {beats : Nat → Nat → Bool} {a b : Nat} {rest : List Nat}
    (h : chainBeats beats (a :: b :: rest) = true) : chainBeats beats (b :: rest) = true :=
  and_right (chainBeats_cons_cons beats a b rest ▸ h)

/-- Rebuild a chain from a head edge + a tail chain. -/
theorem chain_cons_of {beats : Nat → Nat → Bool} {a b : Nat} {rest : List Nat}
    (he : beats a b = true) (ht : chainBeats beats (b :: rest) = true) :
    chainBeats beats (a :: b :: rest) = true :=
  (chainBeats_cons_cons beats a b rest).symm ▸ and_intro he ht

/-! ## Tournament property -/

/-- `beats` is a tournament on `[0,n)`: total + antisymmetric.  For distinct
    `i, j < n`, exactly one of `beats i j`, `beats j i` is `true`. -/
def IsTournament (n : Nat) (beats : Nat → Nat → Bool) : Prop :=
  ∀ i j, i < n → j < n → i ≠ j → (beats i j = true ↔ beats j i = false)

/-- **Totality at the seam.**  From the tournament law, if `x` does *not* beat `a`
    (both `< n`, distinct), then `a` beats `x`.  This is the fact that makes the
    seam stay valid: a non-edge in one direction is an edge in the other. -/
theorem beats_of_not_beats {n : Nat} {beats : Nat → Nat → Bool}
    (T : IsTournament n beats) {x a : Nat} (hx : x < n) (ha : a < n) (hne : x ≠ a)
    (h : beats x a = false) : beats a x = true := by
  -- Tournament law on (a, x): `beats a x = true ↔ beats x a = false`.
  have hiff := T a x ha hx (fun e => hne e.symm)
  exact hiff.mpr h

/-! ## The insertion lemma (★ the constructive engine)

`insertHam` places `x` at the first seam where it flips from loser to winner.
We prove `chainBeats` is preserved.  The seam argument: when the scan steps past
`a` (because `beats x a = false`, i.e. `x` loses to `a`), totality gives
`beats a x = true`, so the edge `a → (head of the inserted tail)` is recovered. -/

/-- `Nat.beq x x = true`, PURE (Lean-core `beq_self_eq_true` is an `Iff` →
    `propext`).  Structural induction on `x`. -/
theorem beq_self (x : Nat) : (x == x) = true := by
  show decide (x = x) = true
  exact decide_eq_true rfl

/-- `memN x (x :: as) = true`. -/
theorem memN_head (x : Nat) (as : List Nat) : memN x (x :: as) = true := by
  show ((x == x) || memN x as) = true
  rw [beq_self x]; rfl

/-- `memN x as = true → memN x (a :: as) = true`. -/
theorem memN_tail {x a : Nat} {as : List Nat} (h : memN x as = true) :
    memN x (a :: as) = true := by
  show ((x == a) || memN x as) = true
  rw [h]; exact Bool.or_true _

/-- **Seam lemma.**  Prepending `c` to `insertHam beats x l` keeps the chain,
    given the chain on `insertHam beats x l`, that `c` beats `x` (`hcx`), and
    that `c` beats `l`'s old head (`hcb`).  Cases on `l`:
    * `l = []`: `insertHam = [x]`, edge `c → x` is `hcx`.
    * `l = b :: bs`: head of `insertHam` is `x` (if `beats x b`) — edge `hcx`;
      else `b` — edge `hcb`. -/
theorem cons_insert {beats : Nat → Nat → Bool} {x c : Nat} :
    ∀ (l : List Nat),
      chainBeats beats (insertHam beats x l) = true →
      beats c x = true →
      (∀ b bs, l = b :: bs → beats c b = true) →
      chainBeats beats (c :: insertHam beats x l) = true
  | [], _, hcx, _ =>
      -- insertHam x [] = [x]; chain (c :: [x]) = beats c x && true
      chain_cons_of hcx rfl
  | b :: bs, hins, hcx, hcb => by
      show chainBeats beats (c :: (if beats x b then x :: b :: bs else b :: insertHam beats x bs)) = true
      cases hxb : beats x b with
      | true =>
          rw [if_pos rfl]
          have hins' : chainBeats beats (x :: b :: bs) = true := by
            have e : insertHam beats x (b :: bs) = x :: b :: bs := by
              show (if beats x b then x :: b :: bs else b :: insertHam beats x bs) = x :: b :: bs
              rw [hxb, if_pos rfl]
            rw [e] at hins; exact hins
          exact chain_cons_of hcx hins'
      | false =>
          rw [if_neg (fun h => Bool.noConfusion h)]
          have hcb' : beats c b = true := hcb b bs rfl
          have hins' : chainBeats beats (b :: insertHam beats x bs) = true := by
            have e : insertHam beats x (b :: bs) = b :: insertHam beats x bs := by
              show (if beats x b then x :: b :: bs else b :: insertHam beats x bs) = b :: insertHam beats x bs
              rw [hxb, if_neg (fun h => Bool.noConfusion h)]
            rw [e] at hins; exact hins
          exact chain_cons_of hcb' hins'

/-- **`insert_into_path` (★).**  Inserting `x` into a Hamiltonian chain `l`
    preserves the chain, *provided* `x` is comparable to every element of `l`
    (`hcomp`: each `e ∈ l` has `beats x e = true ∨ beats e x = true` — exactly what
    tournament totality delivers).  By induction on `l`.

    The seam: at `a :: as`, if `beats x a` we prepend `x` (edge `x → a` direct); else
    `x` loses to `a`, so `beats a x = true` (comparability), and the recursion
    `a :: insertHam beats x as` needs the edge `a → head(insertHam beats x as)`,
    recovered (via `cons_insert`) because `a` beats `x` *and* `a` beats `as`'s old
    head (the original chain edge). -/
theorem insert_into_path {beats : Nat → Nat → Bool} (x : Nat) :
    ∀ (l : List Nat),
      chainBeats beats l = true →
      (∀ e, memN e l = true → (beats x e = true ∨ beats e x = true)) →
      chainBeats beats (insertHam beats x l) = true
  | [], _, _ => rfl
  | a :: as, hchain, hcomp => by
      show chainBeats beats (if beats x a then x :: a :: as else a :: insertHam beats x as) = true
      cases hxa : beats x a with
      | true =>
          rw [if_pos rfl]
          exact chain_cons_of hxa hchain
      | false =>
          rw [if_neg (fun h => Bool.noConfusion h)]
          have hcompa : beats x a = true ∨ beats a x = true := hcomp a (memN_head a as)
          have hax : beats a x = true := by
            cases hcompa with
            | inl h => rw [h] at hxa; exact Bool.noConfusion hxa
            | inr h => exact h
          have hchain_as : chainBeats beats as = true := by
            cases as with
            | nil => rfl
            | cons b bs => exact tail_chain_of_chain hchain
          have hcomp_as : ∀ e, memN e as = true → (beats x e = true ∨ beats e x = true) :=
            fun e he => hcomp e (memN_tail he)
          have hins : chainBeats beats (insertHam beats x as) = true :=
            insert_into_path x as hchain_as hcomp_as
          have hcb : ∀ b bs, as = b :: bs → beats a b = true := by
            intro b bs hbs
            have hc2 : chainBeats beats (a :: b :: bs) = true := by rw [← hbs]; exact hchain
            exact head_edge_of_chain hc2
          exact cons_insert as hins hax hcb

/-! ## Bookkeeping: `insertHam` adds exactly one vertex

`length`, membership (cover), and bound preservation under a single insertion. -/

/-- `insertHam` adds exactly one element to the length. -/
theorem length_insertHam (beats : Nat → Nat → Bool) (x : Nat) :
    ∀ (l : List Nat), (insertHam beats x l).length = l.length + 1
  | [] => rfl
  | a :: as => by
      show (if beats x a then x :: a :: as else a :: insertHam beats x as).length
        = (a :: as).length + 1
      cases hxa : beats x a with
      | true => rw [if_pos rfl]; rfl
      | false =>
          rw [if_neg (fun h => Bool.noConfusion h)]
          show (insertHam beats x as).length + 1 = (as.length + 1) + 1
          rw [length_insertHam beats x as]

/-- **Cover step.**  `y` is a member of `insertHam beats x l` iff `y = x` or `y ∈ l`.
    The insertion neither drops nor duplicates membership. -/
theorem memN_insertHam (beats : Nat → Nat → Bool) (x : Nat) (y : Nat) :
    ∀ (l : List Nat), memN y (insertHam beats x l) = ((y == x) || memN y l)
  | [] => by
      show memN y [x] = ((y == x) || memN y [])
      show ((y == x) || memN y []) = ((y == x) || false)
      rfl
  | a :: as => by
      show memN y (if beats x a then x :: a :: as else a :: insertHam beats x as)
        = ((y == x) || memN y (a :: as))
      cases hxa : beats x a with
      | true =>
          rw [if_pos rfl]
          show ((y == x) || memN y (a :: as)) = ((y == x) || memN y (a :: as))
          rfl
      | false =>
          rw [if_neg (fun h => Bool.noConfusion h)]
          show ((y == a) || memN y (insertHam beats x as))
            = ((y == x) || ((y == a) || memN y as))
          rw [memN_insertHam beats x y as]
          -- (y==a) || ((y==x) || memN y as) = (y==x) || ((y==a) || memN y as)
          exact or_left_comm (y == a) (y == x) (memN y as)

/-- `allLt` step: if all of `l < n` and `x < n`, then all of `insertHam x l < n`. -/
theorem allLt_insertHam {n : Nat} (beats : Nat → Nat → Bool) {x : Nat} (hx : x < n) :
    ∀ (l : List Nat), allLt n l = true → allLt n (insertHam beats x l) = true
  | [], _ => by
      show (decide (x < n) && allLt n []) = true
      exact and_intro (decide_eq_true hx) rfl
  | a :: as, hl => by
      show allLt n (if beats x a then x :: a :: as else a :: insertHam beats x as) = true
      have hl' : (decide (a < n) && allLt n as) = true := hl
      have hla : decide (a < n) = true := and_left hl'
      have hlas : allLt n as = true := and_right hl'
      cases hxa : beats x a with
      | true =>
          rw [if_pos rfl]
          show (decide (x < n) && allLt n (a :: as)) = true
          exact and_intro (decide_eq_true hx) hl
      | false =>
          rw [if_neg (fun h => Bool.noConfusion h)]
          show (decide (a < n) && allLt n (insertHam beats x as)) = true
          exact and_intro hla (allLt_insertHam beats hx as hlas)

/-! ## `redei` (★★ headline)

Build the Hamiltonian path over `[0,n)` by folding `insertHam` over `0,1,…,n-1`:
`buildPath beats 0 = []`, `buildPath beats (k+1) = insertHam beats k (buildPath beats k)`.
Each insertion of `k` into the path on `[0,k)` is valid because every existing element
`e < k ≤ n` is distinct from `k < n`, so tournament totality supplies comparability. -/

/-- The growing path: insert `0, 1, …, k-1` in order. -/
def buildPath (beats : Nat → Nat → Bool) : Nat → List Nat
  | 0     => []
  | k + 1 => insertHam beats k (buildPath beats k)

/-- `buildPath` invariants, maintained by induction on `k` (with `k ≤ n`):
    chain, length `= k`, every element `< n`, and the cover `memN x ↔ x < k`. -/
theorem buildPath_spec {n : Nat} {beats : Nat → Nat → Bool}
    (T : IsTournament n beats) :
    ∀ k, k ≤ n →
      chainBeats beats (buildPath beats k) = true
      ∧ (buildPath beats k).length = k
      ∧ allLt n (buildPath beats k) = true
      ∧ (∀ x, memN x (buildPath beats k) = true ↔ x < k)
  | 0, _ => by
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro x
      constructor
      · intro h; exact Bool.noConfusion h
      · intro h; exact absurd h (Nat.not_lt_zero x)
  | k + 1, hk => by
      have hkn : k < n := hk
      have hk_le : k ≤ n := Nat.le_of_lt hkn
      obtain ⟨hchain, hlen, hall, hcover⟩ := buildPath_spec T k hk_le
      -- comparability of `k` with every element of `buildPath k`
      have hcomp : ∀ e, memN e (buildPath beats k) = true →
          (beats k e = true ∨ beats e k = true) := by
        intro e he
        have helt : e < k := (hcover e).mp he
        have hen : e < n := Nat.lt_trans helt hkn
        have hne : k ≠ e := fun heq => Nat.lt_irrefl e (heq ▸ helt)
        -- comparability: either `k` beats `e`, or (by totality) `e` beats `k`.
        match hb : beats k e with
        | true  => exact Or.inl rfl
        | false => exact Or.inr (beats_of_not_beats T hkn hen hne hb)
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- chain preserved
        show chainBeats beats (insertHam beats k (buildPath beats k)) = true
        exact insert_into_path k (buildPath beats k) hchain hcomp
      · -- length k+1
        show (insertHam beats k (buildPath beats k)).length = k + 1
        rw [length_insertHam beats k (buildPath beats k), hlen]
      · -- all < n
        show allLt n (insertHam beats k (buildPath beats k)) = true
        exact allLt_insertHam beats hkn (buildPath beats k) hall
      · -- cover: memN x (buildPath (k+1)) ↔ x < k+1
        intro x
        show memN x (insertHam beats k (buildPath beats k)) = true ↔ x < k + 1
        rw [memN_insertHam beats k x (buildPath beats k)]
        constructor
        · intro h
          cases hxk : (x == k) with
          | true =>
              have hxeq : x = k := of_decide_eq_true hxk
              exact hxeq ▸ Nat.lt_succ_self k
          | false =>
              have hmem : memN x (buildPath beats k) = true := by
                have : ((x == k) || memN x (buildPath beats k)) = true := h
                rw [hxk] at this; exact this
              exact Nat.lt_succ_of_lt ((hcover x).mp hmem)
        · intro h
          -- x < k+1 → x = k ∨ x < k
          cases Nat.lt_or_ge x k with
          | inl hlt =>
              have hmem : memN x (buildPath beats k) = true := (hcover x).mpr hlt
              rw [hmem]; exact Bool.or_true _
          | inr hge =>
              have hxk : x = k := Nat.le_antisymm (Nat.le_of_lt_succ h) hge
              have : (x == k) = true := by rw [hxk]; exact beq_self k
              rw [this]; rfl

/-- **Redei's theorem (∅-axiom, computed by insertion).**  Every tournament on
    `[0,n)` has a Hamiltonian path: an explicit `List Nat` of length `n`, covering
    exactly `{0,…,n-1}`, with `chainBeats` (consecutive `beats`) holding.  The list
    is the insertion-sort output `buildPath beats n` — assembled, not extracted. -/
theorem redei {n : Nat} {beats : Nat → Nat → Bool} (T : IsTournament n beats) :
    ∃ l : List Nat, l.length = n ∧ (∀ x, memN x l = true ↔ x < n)
      ∧ chainBeats beats l = true := by
  obtain ⟨hchain, hlen, _, hcover⟩ := buildPath_spec T n (Nat.le_refl n)
  exact ⟨buildPath beats n, hlen, hcover, hchain⟩

/-! ## Smoke: a concrete 3-cycle tournament

`beats3 0 1 = beats3 1 2 = beats3 2 0 = true`, all else `false`.  This is the
directed 3-cycle.  Its Hamiltonian path is `[0,1,2]` (edges `0→1`, `1→2`). -/

/-- The directed 3-cycle on `{0,1,2}`. -/
def beats3 (i j : Nat) : Bool :=
  (i == 0 && j == 1) || (i == 1 && j == 2) || (i == 2 && j == 0)

/-- `[0,1,2]` is a Hamiltonian path of the 3-cycle — checked by `rfl` on `chainBeats`. -/
theorem smoke_3cycle_chain : chainBeats beats3 [0, 1, 2] = true := rfl

/-- And it covers exactly `{0,1,2}` with length 3. -/
theorem smoke_3cycle_cover : [0, 1, 2].length = 3
    ∧ memN 0 [0,1,2] = true ∧ memN 1 [0,1,2] = true ∧ memN 2 [0,1,2] = true
    ∧ memN 3 [0,1,2] = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end E213.Lib.Math.Combinatorics.TournamentHamiltonian
