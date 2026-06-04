import E213.Lib.Math.Combinatorics.BoolEnum
import E213.Meta.Tactic.Omega213
import E213.Meta.Tactic.NatHelper

/-!
# COUNT — the deficit-existence instruction (∅-axiom)

Compiling the **probabilistic method** (Erdős 1947) down the proof-ISA
(`seed/PROOF_ISA.md`) surfaces one move that is *not* among the eight named
instructions.  Where `DIAGONALIZE` forces an object by **distinction from
all** (Cantor) and the structural `GAP` exhibits an *un-covered* surplus by a
qualitative reason ("not every function is a fold"), the probabilistic method
forces an object by **counting**: if the bad events together occupy fewer than
all `2ⁿ` colourings, a good colouring is left over — and, the carrier being
finite and badness decidable, it can be **found** (no `Classical`, no LEM).

So the compilation verdict is *not* "already in the ISA": it is a new witness
of the `GAP` family — a **quantitative GAP** keyed on a cardinality
comparison.  The repo already *uses* this everywhere as `pigeonhole`
(≈25 Lean files) without naming it an instruction — the abstract forms
`Combinatorics.Pigeonhole.no_inj_lt` (no injection `Fin k → Fin N`, `N < k`) and
`Tactic.List213.nodup_length_le_of_subset` (the cardinality form, reused in
`LinearDependence`); the probabilistic method is what makes the missing
primitive explicit.  Name it **COUNT** (deficit ⟹ existence).  (`deficit_exists`
below is the `Bool`-list deficit form, a direct finite search.)

Built over the `BoolEnum` carrier (`allBoolLists n` = the `2ⁿ`
2-colourings of `n` edges):

  · `cond_or_le`        — per-element subadditivity of the count over `||`;
  · `bcount_or_le`      — the same over a whole list;
  · `union_bound`       — `bcount (anyBad preds) ≤ Σ bcount predᵢ` (union bound);
  · `deficit_exists`    — `bcount bad L < |L| → ∃ l ∈ L, bad l = false`
                          (the constructive extraction = finite search);
  · ★ `count_existence` — the instruction: `Σ bcount predᵢ < 2ⁿ
                          → ∃ colouring avoiding every predᵢ`;
  · ★ `erdos_schema`    — the uniform-bound form Erdős uses: `t` bad events,
                          each on ≤ `c` of the `2ⁿ` colourings, with
                          `t·c < 2ⁿ`, force a colouring dodging all.  Erdős'
                          Ramsey bound `R(k,k) > N` is the instance
                          `n = C(N,2)`, `t = C(N,k)`, `c = 2·2^{n−C(k,2)}`,
                          whose hypothesis is `2·C(N,k) < 2^{C(k,2)}`.
-/

namespace E213.Lib.Math.Combinatorics.CountExistence

open E213.Lib.Math.Combinatorics.BoolEnum

/-- `anyBad preds l` — some bad event fires on colouring `l`. -/
def anyBad : List (List Bool → Bool) → List Bool → Bool
  | [], _ => false
  | p :: ps, l => p l || anyBad ps l

/-- `totalCount preds L` — `Σᵢ bcount predᵢ L`, the union-bound right side. -/
def totalCount : List (List Bool → Bool) → List (List Bool) → Nat
  | [], _ => 0
  | p :: ps, L => bcount p L + totalCount ps L

/-! ## The union bound -/

/-- Middle-four shuffle, `(a+b)+(c+d) = (a+c)+(b+d)`, core-`Nat` only. -/
private theorem shuffle4 (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc a b (c + d), Nat.add_left_comm b c d, ← Nat.add_assoc a c (b + d)]

/-- Per-element subadditivity: an `||`-event contributes no more than the sum
    of its disjuncts. -/
theorem cond_or_le (a b : Bool) :
    (bif (a || b) then 1 else 0)
      ≤ (bif a then 1 else 0) + (bif b then 1 else 0) := by
  cases a <;> cases b <;> decide

/-- `bcount` is subadditive over a pointwise `||`. -/
theorem bcount_or_le (p q : List Bool → Bool) :
    ∀ (L : List (List Bool)),
      bcount (fun l => p l || q l) L ≤ bcount p L + bcount q L
  | [] => Nat.le_refl 0
  | a :: rest => by
      have ih := bcount_or_le p q rest
      have hhead := cond_or_le (p a) (q a)
      show (bif (p a || q a) then 1 else 0) + bcount (fun l => p l || q l) rest
            ≤ ((bif p a then 1 else 0) + bcount p rest)
              + ((bif q a then 1 else 0) + bcount q rest)
      calc (bif (p a || q a) then 1 else 0) + bcount (fun l => p l || q l) rest
            ≤ ((bif p a then 1 else 0) + (bif q a then 1 else 0))
                + (bcount p rest + bcount q rest) := Nat.add_le_add hhead ih
        _ = ((bif p a then 1 else 0) + bcount p rest)
              + ((bif q a then 1 else 0) + bcount q rest) :=
            shuffle4 _ _ _ _

/-- **Union bound.**  The count of colourings hit by *some* bad event is at
    most the sum of the per-event counts. -/
theorem union_bound :
    ∀ (preds : List (List Bool → Bool)) (L : List (List Bool)),
      bcount (anyBad preds) L ≤ totalCount preds L
  | [], L => by
      have h0 : bcount (anyBad []) L = 0 := by
        rw [bcount_congr (p := anyBad []) (q := fun _ => false) (fun _ => rfl) L,
            bcount_false]
      rw [h0]
      exact Nat.le_refl _
  | p :: ps, L => by
      have ih := union_bound ps L
      have h1 : bcount (anyBad (p :: ps)) L ≤ bcount p L + bcount (anyBad ps) L := by
        show bcount (fun l => p l || anyBad ps l) L ≤ bcount p L + bcount (anyBad ps) L
        exact bcount_or_le p (anyBad ps) L
      exact Nat.le_trans h1 (Nat.add_le_add (Nat.le_refl _) ih)

/-! ## The deficit-existence extraction -/

/-- **Deficit ⟹ existence (constructive).**  If `bad` holds on fewer than all
    of `L`, then `L` contains an element on which `bad` is `false` — exhibited
    by finite search, no choice. -/
theorem deficit_exists (bad : List Bool → Bool) :
    ∀ (L : List (List Bool)), bcount bad L < L.length → ∃ l, l ∈ L ∧ bad l = false
  | [], h => absurd h (Nat.lt_irrefl 0)
  | a :: rest, h => by
      cases hb : bad a with
      | false => exact ⟨a, List.Mem.head rest, hb⟩
      | true =>
          have e1 : bcount bad (a :: rest)
                      = (bif bad a then 1 else 0) + bcount bad rest := rfl
          rw [e1, hb] at h
          -- `h` is now defeq to `1 + bcount bad rest < rest.length + 1`
          have h' : 1 + bcount bad rest < rest.length + 1 := h
          rw [Nat.add_comm 1 (bcount bad rest)] at h'
          have hlen : bcount bad rest < rest.length := Nat.lt_of_succ_lt_succ h'
          rcases deficit_exists bad rest hlen with ⟨l, hmem, hbl⟩
          exact ⟨l, List.Mem.tail a hmem, hbl⟩

/-! ## The COUNT instruction -/

/-- ★ **COUNT — the deficit-existence instruction.**  If the bad events
    together cover fewer than all `2ⁿ` colourings, a colouring avoiding every
    bad event exists (and is found by finite search). -/
theorem count_existence (preds : List (List Bool → Bool)) (n : Nat)
    (h : totalCount preds (allBoolLists n) < 2 ^ n) :
    ∃ l, l ∈ allBoolLists n ∧ anyBad preds l = false := by
  have hub : bcount (anyBad preds) (allBoolLists n)
              ≤ totalCount preds (allBoolLists n) :=
    union_bound preds (allBoolLists n)
  have hlt : bcount (anyBad preds) (allBoolLists n) < (allBoolLists n).length := by
    rw [allBoolLists_length n]
    exact Nat.lt_of_le_of_lt hub h
  exact deficit_exists (anyBad preds) (allBoolLists n) hlt

/-- `anyBad preds l = false` un-bundles to "every event misses `l`". -/
theorem anyBad_false_elim :
    ∀ (preds : List (List Bool → Bool)) (l : List Bool),
      anyBad preds l = false → ∀ p, p ∈ preds → p l = false
  | [], _, _, p, hp => absurd hp (List.not_mem_nil p)
  | q :: ps, l, h, p, hp => by
      have hsplit : q l = false ∧ anyBad ps l = false := by
        have hor : (q l || anyBad ps l) = false := h
        cases hh : q l with
        | true => rw [hh, Bool.true_or] at hor; exact Bool.noConfusion hor
        | false =>
            rw [hh, Bool.false_or] at hor
            exact ⟨rfl, hor⟩
      cases hp with
      | head => exact hsplit.1
      | tail _ hp' => exact anyBad_false_elim ps l hsplit.2 p hp'

/-- Uniform per-event bound ⟹ `totalCount ≤ t·c`. -/
theorem totalCount_le_uniform (c : Nat) :
    ∀ (preds : List (List Bool → Bool)) (L : List (List Bool)),
      (∀ p, p ∈ preds → bcount p L ≤ c) →
      totalCount preds L ≤ preds.length * c
  | [], L, _ => by
      show (0 : Nat) ≤ ([] : List (List Bool → Bool)).length * c
      rw [List.length_nil, Nat.zero_mul]
      exact Nat.le_refl 0
  | p :: ps, L, hb => by
      have hph : bcount p L ≤ c := hb p (List.Mem.head ps)
      have ih : totalCount ps L ≤ ps.length * c :=
        totalCount_le_uniform c ps L (fun q hq => hb q (List.Mem.tail p hq))
      have hmul : (ps.length + 1) * c = ps.length * c + c := by
        rw [E213.Tactic.NatHelper.add_mul, Nat.one_mul]
      show bcount p L + totalCount ps L ≤ (p :: ps).length * c
      rw [List.length_cons]
      calc bcount p L + totalCount ps L
            ≤ c + ps.length * c := Nat.add_le_add hph ih
        _ = ps.length * c + c := Nat.add_comm _ _
        _ = (ps.length + 1) * c := hmul.symm

/-- ★ **The probabilistic-method schema (Erdős 1947).**  `t = |preds|` bad
    events, each on at most `c` of the `2ⁿ` colourings, with `t·c < 2ⁿ`, force
    a colouring dodging every event.  Instantiated with `n = C(N,2)`,
    `t = C(N,k)`, `c = 2·2^{n−C(k,2)}` the hypothesis is `2·C(N,k) < 2^{C(k,2)}`
    and the conclusion is a 2-colouring of `K_N` with no monochromatic `K_k`,
    i.e. `R(k,k) > N` — the bound `R(k,k) > 2^{k/2}`. -/
theorem erdos_schema (preds : List (List Bool → Bool)) (n c : Nat)
    (hc : ∀ p, p ∈ preds → bcount p (allBoolLists n) ≤ c)
    (h : preds.length * c < 2 ^ n) :
    ∃ l, l ∈ allBoolLists n ∧ ∀ p, p ∈ preds → p l = false := by
  have htot : totalCount preds (allBoolLists n) < 2 ^ n :=
    Nat.lt_of_le_of_lt (totalCount_le_uniform c preds (allBoolLists n) hc) h
  rcases count_existence preds n htot with ⟨l, hmem, hany⟩
  exact ⟨l, hmem, anyBad_false_elim preds l hany⟩

end E213.Lib.Math.Combinatorics.CountExistence
