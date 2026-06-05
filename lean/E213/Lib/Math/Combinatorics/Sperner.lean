import E213.Lib.Math.Combinatorics.BoolEnum
import E213.Lib.Math.Combinatorics.Binomial

/-!
# Sperner's theorem, compiled down the proof-ISA (∅-axiom)

**The problem (L3).**  The largest *antichain* in the Boolean lattice `2^[n]`
— a family of subsets of `[n]` none containing another — has size
`C(n, ⌊n/2⌋)`.  (Sperner 1928.)

**The compilation (`seed/PROOF_ISA.md`).**  Sperner's *number* and its *upper
bound* are two different ISA moves, and separating them is the content:

  · the **number** `C(n, ⌊n/2⌋)` is the largest single layer — a
    **READ** (the layer-size = binomial) followed by the unimodality of the
    Pascal recursion (`binom n k ≤ binom n (n/2)`);
  · the extremal antichain **exists** — the middle layer itself, an antichain
    because equal-size distinct sets are incomparable (a **SEPARATE**: the
    subset reading separates same-size sets only at equality);
  · the **upper bound** is the LYM (Lubell–Yamamoto–Meshalkin) inequality — the
    **double-counting / dual-union-bound** face of the `COUNT` instruction:
    each maximal chain meets the antichain at most once, so summing
    "chains through `A`" over the antichain cannot exceed the chain total.

This file closes everything except the *named* general upper bound's chain
arithmetic (the permutation counts `|A|!·(n−|A|)!` and `n!`), which — exactly
as Erdős' named Ramsey bound left a `K_N`-bookkeeping rung over a built engine
(`RamseyLowerBound`) — is the one honest rung over the LYM engine here.

## What is closed (general, ∅-axiom)

  · `layer_size` — `#{A ⊆ [n] : |A| = k} = C(n, k)` (the **READ**: layer = binomial).
  · `middle_layer_isAntichain` + `lower_bound` — the middle layer is an antichain
    of size `C(n, ⌊n/2⌋)`; the bound is **tight** (existence half of Sperner).
  · `binom_le_binom_mid` — binomial **unimodality**: `C(n,k) ≤ C(n, ⌊n/2⌋)`; the
    middle layer is the largest layer (*why* the Sperner number is `C(n,⌊n/2⌋)`).
  · `uniform_antichain_le` — Sperner for **uniform** (single-size) antichains,
    fully general: any antichain whose members share a size has `≤ C(n,⌊n/2⌋)`.
  · `lym_double_count` — the LYM **engine**: the dual-union-bound, the
    cross-layer upper bound's heart, abstract and ∅-axiom.

Companion essay: `theory/essays/proof_isa/sperner_double_counting.md`.
-/

namespace E213.Lib.Math.Combinatorics.Sperner

open E213.Lib.Math.Combinatorics.BoolEnum
open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## §1 — the model: subsets of `[n]` as length-`n` `Bool` lists

`List Bool` is chosen over `Fin n → Bool` for the same reason as `BoolEnum`:
equality is decidable list equality (no `funext`) and a family's size is a
`List.length` / `bcount` (no `Fintype`).  `allBoolLists n` already enumerates
all `2^n` subsets. -/

/-- Cardinality of a subset = number of `true` entries. -/
def cardB : List Bool → Nat
  | [] => 0
  | true :: l => cardB l + 1
  | false :: l => cardB l

/-- The size-`k` membership predicate (`Bool`-valued, for `bcount`).  Uses
    `Nat.beq` directly — it reduces structurally on `succ` (unlike `==`, which
    on `Nat` is `instBEqOfDecidableEq` and neither reduces nor stays
    propext-clean). -/
def cardEq (k : Nat) (l : List Bool) : Bool := Nat.beq (cardB l) k

@[simp] theorem cardB_false (l : List Bool) : cardB (false :: l) = cardB l := rfl
@[simp] theorem cardB_true (l : List Bool) : cardB (true :: l) = cardB l + 1 := rfl

/-! ## §2 — Theorem A: layer sizes are binomial coefficients (the READ)

`#{A ⊆ [n] : |A| = k} = C(n, k)`.  The count recursion *is* the Pascal
recursion: a length-`(n+1)` set either omits the new point (a size-`k` set of
the first `n` — `binom n k`) or includes it (a size-`(k−1)` set — `binom n (k−1)`),
and `binom (n+1) k = binom n (k−1) + binom n k`. -/

/-- ★ **Layer size = binomial.**  Exactly `C(n, k)` of the `2^n` subsets of
    `[n]` have size `k`.  This is the count-Lens READ of the Sperner setting:
    the Boolean lattice's `k`-th layer has `binom n k` elements. -/
theorem layer_size : ∀ (n k : Nat),
    bcount (cardEq k) (allBoolLists n) = binom n k
  | 0, k => by
      cases k with
      | zero => rfl
      | succ k => rfl
  | n + 1, k => by
      rw [bcount_allBoolLists_succ]
      -- `false :: x` keeps the size; `true :: x` raises it by one.
      have hfalse : (fun x => cardEq k (false :: x)) = cardEq k := rfl
      cases k with
      | zero =>
          -- size-0 sets never contain the new point: the `true` block is empty.
          rw [hfalse,
              bcount_congr (p := fun x => cardEq 0 (true :: x)) (q := fun _ => false)
                (fun x => rfl),
              bcount_false, layer_size n 0, Nat.add_zero,
              Binomial.binom_n_0 n, Binomial.binom_n_0 (n + 1)]
      | succ k =>
          rw [hfalse,
              bcount_congr (p := fun x => cardEq (k + 1) (true :: x)) (q := cardEq k)
                (fun x => rfl),
              layer_size n (k + 1), layer_size n k]
          -- `binom (n+1) (k+1) = binom n k + binom n (k+1)`
          show binom n (k + 1) + binom n k = binom n k + binom n (k + 1)
          exact Nat.add_comm _ _

/-! ## §3 — the inclusion order and the SEPARATE lemma

`A ⊆ B` on equal-length `Bool` lists is the pointwise implication `aᵢ → bᵢ`.
The key fact — equal-size distinct sets are **incomparable** — is the
`SEPARATE` move: the subset reading collapses two same-size sets *only at
equality*, so any antichain may freely take a whole size-layer. -/

/-- Boolean implication `a → b`. -/
def impl (a b : Bool) : Bool := !a || b

/-- Subset on length-matched `Bool` lists: pointwise `aᵢ → bᵢ` (`false` on a
    length mismatch). -/
def subseteqB : List Bool → List Bool → Bool
  | [], [] => true
  | a :: as, b :: bs => impl a b && subseteqB as bs
  | _, _ => false

/-- Comparability: one contains the other. -/
def comparable (A B : List Bool) : Bool := subseteqB A B || subseteqB B A

/-- A subset has no more elements: `A ⊆ B → |A| ≤ |B|`. -/
theorem card_le_of_subseteq :
    ∀ (A B : List Bool), subseteqB A B = true → cardB A ≤ cardB B
  | [], [], _ => Nat.le_refl 0
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | false :: as, b :: bs, h => by
      -- `subseteqB (false :: as) (b :: bs) = subseteqB as bs` (defeq)
      have ih := card_le_of_subseteq as bs h
      have hb : cardB bs ≤ cardB (b :: bs) := by
        cases b
        · exact Nat.le_refl _
        · exact Nat.le_succ _
      exact Nat.le_trans ih hb
  | true :: as, b :: bs, h => by
      cases b with
      | false => exact Bool.noConfusion h
      | true => exact Nat.succ_le_succ (card_le_of_subseteq as bs h)

/-- ★ **SEPARATE.**  Distinct sets of the *same size* are incomparable: if
    `A ⊆ B` and `|A| = |B|` then `A = B`.  (The inclusion order separates a
    size-layer into singletons.) -/
theorem eq_of_subseteq_card_eq :
    ∀ (A B : List Bool), subseteqB A B = true → cardB A = cardB B → A = B
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => Bool.noConfusion h
  | _ :: _, [], h, _ => Bool.noConfusion h
  | false :: as, b :: bs, h, hc => by
      cases b with
      | true =>
          exfalso
          have hle := card_le_of_subseteq as bs h
          have hc' : cardB as = cardB bs + 1 := hc
          have hcontra : cardB bs + 1 ≤ cardB bs := hc' ▸ hle
          exact Nat.not_succ_le_self (cardB bs) hcontra
      | false =>
          have hcc : cardB as = cardB bs := hc
          rw [eq_of_subseteq_card_eq as bs h hcc]
  | true :: as, b :: bs, h, hc => by
      cases b with
      | false => exact Bool.noConfusion h
      | true =>
          have hcc : cardB as = cardB bs := Nat.succ.inj hc
          rw [eq_of_subseteq_card_eq as bs h hcc]

/-- Equal-size distinct sets are incomparable (`comparable = false`). -/
theorem comparable_eq_false_of_card_eq {A B : List Bool}
    (hcard : cardB A = cardB B) (hne : A ≠ B) : comparable A B = false := by
  have h1 : subseteqB A B = false := by
    cases hsab : subseteqB A B with
    | false => rfl
    | true => exact absurd (eq_of_subseteq_card_eq A B hsab hcard) hne
  have h2 : subseteqB B A = false := by
    cases hsba : subseteqB B A with
    | false => rfl
    | true => exact absurd (eq_of_subseteq_card_eq B A hsba hcard.symm) (fun h => hne h.symm)
  show (subseteqB A B || subseteqB B A) = false
  rw [h1, h2]
  rfl

/-! ## §4 — antichains and the tight lower bound

An antichain is a family no two distinct members of which are comparable.  The
size-`k` layer is an antichain (§3), and its size is `binom n k` (§2).  Taking
`k = ⌊n/2⌋` gives an antichain of size `binom n ⌊n/2⌋` — the **lower** half of
Sperner: the bound is achieved. -/

/-- A family of subsets, no two distinct members comparable. -/
def IsAntichain (L : List (List Bool)) : Prop :=
  ∀ A, A ∈ L → ∀ B, B ∈ L → A ≠ B → comparable A B = false

/-- The size-`k` layer of the Boolean lattice `2^[n]`. -/
def kLayer (n k : Nat) : List (List Bool) := (allBoolLists n).filter (cardEq k)

open E213.Tactic.List213 (mem_filter mem_filter_of nodup_filter)

/-- `|kLayer n k| = binom n k`. -/
theorem kLayer_card (n k : Nat) : (kLayer n k).length = binom n k := by
  rw [kLayer, filter_length_eq_bcount, layer_size]

/-- The layer is duplicate-free. -/
theorem kLayer_nodup (n k : Nat) : (kLayer n k).Nodup :=
  nodup_filter (cardEq k) (nodup_allBoolLists n)

/-- ★ Every size-layer is an antichain. -/
theorem kLayer_isAntichain (n k : Nat) : IsAntichain (kLayer n k) := by
  intro A hA B hB hne
  have hcA : cardB A = k := Nat.eq_of_beq_eq_true (mem_filter hA).2
  have hcB : cardB B = k := Nat.eq_of_beq_eq_true (mem_filter hB).2
  exact comparable_eq_false_of_card_eq (hcA.trans hcB.symm) hne

/-- ★ **Lower bound (tight).**  The Boolean lattice `2^[n]` has an antichain of
    size `binom n ⌊n/2⌋` — the middle layer.  So Sperner's bound is achieved;
    the content of the theorem is the matching *upper* bound. -/
theorem lower_bound (n : Nat) :
    ∃ L, IsAntichain L ∧ L.Nodup ∧ L.length = binom n (n / 2) :=
  ⟨kLayer n (n / 2), kLayer_isAntichain n (n / 2),
   kLayer_nodup n (n / 2), kLayer_card n (n / 2)⟩

end E213.Lib.Math.Combinatorics.Sperner
