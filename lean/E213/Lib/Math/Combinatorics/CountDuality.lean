import E213.Lib.Math.Combinatorics.CountExistence
import E213.Lib.Math.Combinatorics.Sperner

/-!
# COUNT-duality — the union bound and LYM are one incidence double-count (∅-axiom)

`seed/PROOF_ISA.md` and the Sperner / Erdős chapters state, **in prose**, that the
two faces of the `COUNT` instruction —

  · the **union bound** (Erdős' probabilistic method, `CountExistence.union_bound`):
    *bad events cover few colourings, so a good one is left over* — the **row read**;
  · the **LYM inequality** (Sperner, `Sperner.lym_double_count`): *each chain meets
    the antichain ≤ once, so the chains-through-`A` total is ≤ the chain total* — the
    **column read**;

are *"one move — Fubini on a 0/1 incidence matrix, read once by rows and once by
columns."*  But that unity was **narrated, not proven**: in the corpus the union
bound is discharged by per-element subadditivity (`CountExistence.bcount_or_le`,
`cond_or_le`), while LYM is discharged by the double-count swap
(`Sperner.sumOver_swap`).  Two *different* proofs.  A cross-domain unification
claim is licensed only when the shared structure is **exhibited as a theorem**:
no value-coincidence, no `: True` headline — a proven map.

This file supplies it.  Both bounds are re-derived from the **single** identity

  `incidence_balance` :  Σ_A Σ_c ⟦g A c⟧  =  Σ_c Σ_A ⟦g A c⟧            (= `Sperner.sumOver_swap`)

— the Bool incidence matrix `g : α → γ → Bool` summed by rows = summed by columns —
with the *only* difference being which marginal is bounded:

  · **rows → union bound**: the row-indicator of a disjunction is ≤ the row sum of
    indicators (`ind_anyBad_le`, an `||`-collapse), so the colourings hit by *some*
    bad event are ≤ the column total Σ_p #{l : p l} = `totalCount` (`union_bound_via_balance`);
  · **columns → LYM**: each column (chain) carries ≤ 1 incidence (`hcap`), so the
    row total Σ_A #{chains through A} is ≤ #columns = #chains (`lym_via_balance`).

`count_duality` packages both as one proof object: *the same `sumOver_swap`, two
marginals.*  This is the operational content of "no exterior" (`05_no_exterior.md`
§5.1) made checkable — two independently-built combinatorial domains (Erdős /
Ramsey over `allBoolLists`, Sperner over `perms`) shown to be one residue read
under two Lenses, ∅-axiom, with the bridge a theorem rather than a sentence.

Companion essay: `theory/essays/proof_isa/count_duality.md`.
-/

namespace E213.Lib.Math.Combinatorics.CountDuality

open E213.Lib.Math.Combinatorics

/-! ## §1 — the count primitives as one `sumOver`

`BoolEnum.bcount` (Erdős side) and `Sperner.lcount` (Sperner side) are the *same*
0/1 count; both equal `Sperner.sumOver` of the indicator.  Bridging them is what
lets one `sumOver_swap` serve both chapters. -/

/-- `BoolEnum.bcount` is `sumOver` of the `0/1` indicator (the Erdős-side count is
    the engine's `sumOver`). -/
theorem bcount_eq_sumOver (p : List Bool → Bool) :
    ∀ (L : List (List Bool)),
      BoolEnum.bcount p L = Sperner.sumOver (fun l => bif p l then 1 else 0) L
  | [] => rfl
  | a :: rest => by
      show (bif p a then 1 else 0) + BoolEnum.bcount p rest
            = (bif p a then 1 else 0) + Sperner.sumOver (fun l => bif p l then 1 else 0) rest
      rw [bcount_eq_sumOver p rest]

/-- `CountExistence.totalCount` (the union-bound right side) is `sumOver` of the
    per-event count — the *row* total Σ_p #{l : p l}. -/
theorem totalCount_eq_sumOver :
    ∀ (preds : List (List Bool → Bool)) (L : List (List Bool)),
      CountExistence.totalCount preds L
        = Sperner.sumOver (fun p => BoolEnum.bcount p L) preds
  | [], _ => rfl
  | p :: ps, L => by
      show BoolEnum.bcount p L + CountExistence.totalCount ps L
            = BoolEnum.bcount p L + Sperner.sumOver (fun p => BoolEnum.bcount p L) ps
      rw [totalCount_eq_sumOver ps L]

/-! ## §2 — the shared engine: one incidence double-count -/

/-- ★ **Incidence balance (the shared move).**  A `Bool` incidence matrix `g`,
    summed by rows (`Σ_A Σ_c`), equals it summed by columns (`Σ_c Σ_A`).  This is
    `Sperner.sumOver_swap` named as the single engine both `COUNT` faces run on. -/
theorem incidence_balance {α γ : Type _} (g : α → γ → Bool)
    (F : List α) (C : List γ) :
    Sperner.sumOver (fun A => Sperner.sumOver (fun c => bif g A c then 1 else 0) C) F
      = Sperner.sumOver (fun c => Sperner.sumOver (fun A => bif g A c then 1 else 0) F) C :=
  Sperner.sumOver_swap (fun A c => bif g A c then 1 else 0) F C

/-! ## §3 — the row read: the union bound, through the swap

The `||`-collapse: the row indicator of a disjunction of events is at most the row
sum of the individual indicators.  This is the *only* extra ingredient the union
bound needs over the bare balance. -/

/-- The indicator of `anyBad preds l` (some event fires on `l`) is ≤ the sum of the
    individual event-indicators on `l` — the per-row `||`-collapse. -/
theorem ind_anyBad_le (l : List Bool) :
    ∀ (preds : List (List Bool → Bool)),
      (bif CountExistence.anyBad preds l then 1 else 0)
        ≤ Sperner.sumOver (fun p => bif p l then 1 else 0) preds
  | [] => by
      show (bif CountExistence.anyBad [] l then 1 else 0)
            ≤ Sperner.sumOver (fun (p : List Bool → Bool) => bif p l then 1 else 0) []
      exact Nat.zero_le _
  | p :: ps => by
      show (bif (p l || CountExistence.anyBad ps l) then 1 else 0)
            ≤ (bif p l then 1 else 0)
              + Sperner.sumOver (fun p => bif p l then 1 else 0) ps
      exact Nat.le_trans (CountExistence.cond_or_le (p l) (CountExistence.anyBad ps l))
        (Nat.add_le_add (Nat.le_refl _) (ind_anyBad_le l ps))

/-- ★★ **Union bound via the balance** (Erdős' probabilistic method, row read).
    The colourings hit by *some* bad event number at most `totalCount` — re-derived
    *through* `incidence_balance` (rows = events, columns = colourings), where the
    original `CountExistence.union_bound` used per-element subadditivity instead.
    Same statement, now factored through the shared Fubini engine. -/
theorem union_bound_via_balance (preds : List (List Bool → Bool))
    (L : List (List Bool)) :
    BoolEnum.bcount (CountExistence.anyBad preds) L
      ≤ CountExistence.totalCount preds L := by
  have step3 :
      Sperner.sumOver (fun l => Sperner.sumOver (fun p => bif p l then 1 else 0) preds) L
        = Sperner.sumOver (fun p => Sperner.sumOver (fun l => bif p l then 1 else 0) L) preds :=
    (incidence_balance (fun (p : List Bool → Bool) (l : List Bool) => p l) preds L).symm
  have step4 :
      Sperner.sumOver (fun p => Sperner.sumOver (fun l => bif p l then 1 else 0) L) preds
        = CountExistence.totalCount preds L := by
    rw [totalCount_eq_sumOver]
    exact Sperner.sumOver_congr (fun p _ => (bcount_eq_sumOver p L).symm)
  calc BoolEnum.bcount (CountExistence.anyBad preds) L
      = Sperner.sumOver (fun l => bif CountExistence.anyBad preds l then 1 else 0) L :=
        bcount_eq_sumOver _ L
    _ ≤ Sperner.sumOver (fun l => Sperner.sumOver (fun p => bif p l then 1 else 0) preds) L :=
        Sperner.sumOver_le (fun l _ => ind_anyBad_le l preds)
    _ = Sperner.sumOver (fun p => Sperner.sumOver (fun l => bif p l then 1 else 0) L) preds :=
        step3
    _ = CountExistence.totalCount preds L := step4

/-! ## §4 — the column read: LYM, through the same swap

The dual marginal: each column (chain) carries ≤ 1 incidence (`hcap`), so the row
total is bounded by the number of columns.  This is `Sperner.lym_double_count`
re-exhibited as the *column* read of the *same* `incidence_balance`. -/

/-- ★★ **LYM via the balance** (Sperner, column read).  If each column `c` (chain)
    is incident to ≤ 1 row (antichain member), the row total
    `Σ_A #{chains through A}` is ≤ the number of columns `#chains`.  The same
    `incidence_balance`, with the *column* marginal capped at `1`. -/
theorem lym_via_balance {α γ : Type _}
    (F : List α) (chains : List γ) (inc : α → γ → Bool)
    (hcap : ∀ c, c ∈ chains → Sperner.lcount (fun A => inc A c) F ≤ 1) :
    Sperner.sumOver (fun A => Sperner.lcount (inc A) chains) F ≤ chains.length := by
  have e1 :
      Sperner.sumOver (fun A => Sperner.lcount (inc A) chains) F
        = Sperner.sumOver
            (fun A => Sperner.sumOver (fun c => bif inc A c then 1 else 0) chains) F :=
    Sperner.sumOver_congr (fun A _ => Sperner.lcount_eq_sumOver (inc A) chains)
  have ebal :
      Sperner.sumOver
          (fun A => Sperner.sumOver (fun c => bif inc A c then 1 else 0) chains) F
        = Sperner.sumOver
            (fun c => Sperner.sumOver (fun A => bif inc A c then 1 else 0) F) chains :=
    incidence_balance inc F chains
  have ecap : ∀ c, c ∈ chains →
      Sperner.sumOver (fun A => bif inc A c then 1 else 0) F ≤ 1 :=
    fun c hc => (Sperner.lcount_eq_sumOver (fun A => inc A c) F) ▸ hcap c hc
  have ebound :
      Sperner.sumOver (fun c => Sperner.sumOver (fun A => bif inc A c then 1 else 0) F) chains
        ≤ Sperner.sumOver (fun _ => 1) chains :=
    Sperner.sumOver_le ecap
  rw [e1, ebal]
  rwa [Sperner.sumOver_const_one] at ebound

/-! ## §5 — the capstone: both faces, one engine -/

/-- ★★★ **COUNT-duality.**  One proof object exhibiting *both* faces of the `COUNT`
    instruction as the two marginals of a single Bool incidence double-count
    (`incidence_balance` = `Sperner.sumOver_swap`):

      · row read  → the Erdős **union bound** (`union_bound_via_balance`);
      · column read → the Sperner **LYM** bound (`lym_via_balance`).

    The narrated "one move, two readings" of `seed/PROOF_ISA.md` is now a theorem:
    two independently-built combinatorial domains are one residue under two Lenses,
    bridged by a proof, not a sentence. -/
theorem count_duality
    (preds : List (List Bool → Bool)) (L : List (List Bool))
    {α γ : Type _} (F : List α) (chains : List γ) (inc : α → γ → Bool)
    (hcap : ∀ c, c ∈ chains → Sperner.lcount (fun A => inc A c) F ≤ 1) :
    (BoolEnum.bcount (CountExistence.anyBad preds) L
        ≤ CountExistence.totalCount preds L)
    ∧ (Sperner.sumOver (fun A => Sperner.lcount (inc A) chains) F ≤ chains.length) :=
  ⟨union_bound_via_balance preds L, lym_via_balance F chains inc hcap⟩

end E213.Lib.Math.Combinatorics.CountDuality
