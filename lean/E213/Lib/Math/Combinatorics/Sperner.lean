import E213.Lib.Math.Combinatorics.BoolEnum
import E213.Lib.Math.Combinatorics.Binomial
import E213.Lib.Math.Combinatorics.Permutations
import E213.Meta.Tactic.NatHelper

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
open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Tactic.NatHelper (add_sub_of_le le_sub_of_add_le add_sub_cancel_right sub_add_cancel)
open E213.Tactic.NatHelper renaming mul_assoc → nmul_assoc, mul_left_comm → nmul_left_comm

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

/-- `half n = ⌊n/2⌋`, defined structurally so its spec lemmas are propext-free
    (core `Nat.div_add_mod` carries `propext`).  Verifiably `half n = ⌊n/2⌋`
    (`example : half 7 = 3 := rfl`). -/
def half : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => half n + 1

/-- `2·⌊n/2⌋ ≤ n`. -/
theorem half_le : ∀ n, 2 * half n ≤ n
  | 0 => Nat.le_refl 0
  | 1 => Nat.zero_le 1
  | n + 2 => by
      show 2 * (half n + 1) ≤ n + 2
      rw [Nat.mul_add, Nat.mul_one]
      exact Nat.add_le_add_right (half_le n) 2

/-- `n ≤ 2·⌊n/2⌋ + 1`. -/
theorem le_half : ∀ n, n ≤ 2 * half n + 1
  | 0 => Nat.zero_le _
  | 1 => Nat.le_refl _
  | n + 2 => by
      show n + 2 ≤ 2 * (half n + 1) + 1
      rw [Nat.mul_add, Nat.mul_one]
      have h := Nat.add_le_add_right (le_half n) 2
      rwa [Nat.add_right_comm (2 * half n) 1 2] at h

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

open E213.Tactic.List213 (mem_filter mem_filter_of nodup_filter nodup_length_le_of_subset)

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
    ∃ L, IsAntichain L ∧ L.Nodup ∧ L.length = binom n (half n) :=
  ⟨kLayer n (half n), kLayer_isAntichain n (half n),
   kLayer_nodup n (half n), kLayer_card n (half n)⟩

/-! ## §5 — binomial unimodality: the middle layer is the largest

*Why* the Sperner number is `binom n ⌊n/2⌋` rather than any other layer: the
binomial row is **unimodal**, peaking at the middle.  The engine is the
absorption identity `(k+1)·C(n,k+1) = (n−k)·C(n,k)` — the Pascal recursion's
multiplicative shadow — which makes the ratio cross `1` exactly at `k = n/2`. -/

/-- Above the diagonal the binomial vanishes: `n < k → C(n,k) = 0`. -/
theorem binom_zero_of_lt : ∀ (n k : Nat), n < k → binom n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
      have hn : n < k := Nat.lt_of_succ_lt_succ h
      show binom n k + binom n (k + 1) = 0
      rw [binom_zero_of_lt n k hn, binom_zero_of_lt n (k + 1) (Nat.lt_succ_of_lt hn)]

/-- On the diagonal `C(n,n) = 1`. -/
theorem binom_n_n : ∀ n, binom n n = 1
  | 0 => rfl
  | n + 1 => by
      show binom n n + binom n (n + 1) = 1
      rw [binom_n_n n, binom_zero_of_lt n (n + 1) (Nat.lt_succ_self n)]

/-- ★ **The absorption identity** `(k+1)·C(n,k+1) = (n−k)·C(n,k)` — the
    multiplicative form of Pascal's recursion.  Holds for all `n, k` (the
    `Nat`-truncated `n − k` makes the degenerate `k ≥ n` cases vanish). -/
theorem absorb : ∀ (n k : Nat), (k + 1) * binom n (k + 1) = (n - k) * binom n k
  | 0, k => by
      rw [show binom 0 (k + 1) = 0 from rfl, Nat.mul_zero, Nat.zero_sub, Nat.zero_mul]
  | n + 1, k => by
      cases k with
      | zero =>
          rw [Nat.zero_add, Nat.one_mul, Binomial.binom_n_1, Nat.sub_zero,
              Binomial.binom_n_0, Nat.mul_one]
      | succ j =>
          have hIHj := absorb n j
          have hIHj1 := absorb n (j + 1)
          have hp2 : binom (n + 1) (j + 1 + 1) = binom n (j + 1) + binom n (j + 1 + 1) := rfl
          have hp1 : binom (n + 1) (j + 1) = binom n j + binom n (j + 1) := rfl
          rw [hp2, hp1, Nat.succ_sub_succ, Nat.mul_add, Nat.mul_add, hIHj1, ← hIHj,
              ← Binomial.add_mul_pure, ← Binomial.add_mul_pure]
          rcases Nat.lt_or_ge n (j + 1) with hnj | hjn
          · rw [binom_zero_of_lt n (j + 1) hnj, Nat.mul_zero, Nat.mul_zero]
          · have hj : j ≤ n := Nat.le_of_succ_le hjn
            have hc : (j + 1 + 1) + (n - (j + 1)) = (j + 1) + (n - j) := by
              rw [Nat.add_right_comm (j + 1) 1 (n - (j + 1)), add_sub_of_le hjn,
                  Nat.add_right_comm j 1 (n - j), add_sub_of_le hj]
            rw [hc]

/-- **Monotone up to the middle.**  `2k+1 ≤ n → C(n,k) ≤ C(n,k+1)`: below the
    middle the ratio `(n−k)/(k+1) ≥ 1`, so the binomial increases. -/
theorem binom_mono_up {n k : Nat} (h : 2 * k + 1 ≤ n) :
    binom n k ≤ binom n (k + 1) := by
  have hab := absorb n k
  have hadd : (k + 1) + k ≤ n := by
    have he : (k + 1) + k = 2 * k + 1 := by rw [Nat.add_right_comm k 1 k, Nat.two_mul]
    rw [he]; exact h
  have hge : k + 1 ≤ n - k := le_sub_of_add_le hadd
  have hstep : (k + 1) * binom n k ≤ (n - k) * binom n k :=
    Nat.mul_le_mul_right (binom n k) hge
  rw [← hab] at hstep
  exact Nat.le_of_mul_le_mul_left hstep (Nat.succ_pos k)

/-- **Monotone past the middle.**  `n ≤ 2k+1 → C(n,k+1) ≤ C(n,k)`: at and beyond
    the middle the ratio `(n−k)/(k+1) ≤ 1`, so the binomial decreases. -/
theorem binom_mono_down {n k : Nat} (h : n ≤ 2 * k + 1) :
    binom n (k + 1) ≤ binom n k := by
  have hab := absorb n k
  have hle : n - k ≤ k + 1 := by
    have he : (k + 1) + k = 2 * k + 1 := by rw [Nat.add_right_comm k 1 k, Nat.two_mul]
    have h1 : n ≤ (k + 1) + k := by rw [he]; exact h
    have h2 : n - k ≤ ((k + 1) + k) - k := Nat.sub_le_sub_right h1 k
    rwa [add_sub_cancel_right] at h2
  have hstep : (n - k) * binom n k ≤ (k + 1) * binom n k :=
    Nat.mul_le_mul_right (binom n k) hle
  rw [← hab] at hstep
  exact Nat.le_of_mul_le_mul_left hstep (Nat.succ_pos k)

/-- Climb up to the middle: `C(n,a) ≤ C(n,a+d)` while `2(a+d) ≤ n`. -/
theorem binom_climb_up (n : Nat) :
    ∀ (d a : Nat), 2 * (a + d) ≤ n → binom n a ≤ binom n (a + d)
  | 0, a, _ => Nat.le_of_eq (by rw [Nat.add_zero])
  | d + 1, a, h => by
      have hassoc : a + (d + 1) = (a + d) + 1 := (Nat.add_assoc a d 1).symm
      rw [hassoc] at h ⊢
      have hexp : 2 * ((a + d) + 1) = 2 * (a + d) + 2 := by rw [Nat.mul_add, Nat.mul_one]
      have h2 : 2 * (a + d) + 2 ≤ n := hexp ▸ h
      have hb : 2 * (a + d) ≤ n := Nat.le_trans (Nat.le_add_right _ 2) h2
      have hs : 2 * (a + d) + 1 ≤ n := Nat.le_trans (Nat.le_succ (2 * (a + d) + 1)) h2
      exact Nat.le_trans (binom_climb_up n d a hb) (binom_mono_up hs)

/-- Climb down from the middle: `C(n,a+d) ≤ C(n,a)` while `n ≤ 2a+1`. -/
theorem binom_climb_down (n : Nat) :
    ∀ (d a : Nat), n ≤ 2 * a + 1 → binom n (a + d) ≤ binom n a
  | 0, a, _ => Nat.le_of_eq (by rw [Nat.add_zero])
  | d + 1, a, h => by
      have hassoc : a + (d + 1) = (a + d) + 1 := (Nat.add_assoc a d 1).symm
      rw [hassoc]
      have hmono : n ≤ 2 * (a + d) + 1 :=
        Nat.le_trans h (Nat.succ_le_succ (Nat.mul_le_mul_left 2 (Nat.le_add_right a d)))
      exact Nat.le_trans (binom_mono_down hmono) (binom_climb_down n d a h)

/-- ★ **Binomial unimodality** — the middle layer is the largest:
    `C(n,k) ≤ C(n, ⌊n/2⌋)` for every `k`.  *This is why the Sperner number is
    `C(n,⌊n/2⌋)`*: among the `n+1` layers, the middle one is the biggest. -/
theorem binom_le_binom_mid (n k : Nat) : binom n k ≤ binom n (half n) := by
  have hle : 2 * half n ≤ n := half_le n
  have hge1 : n ≤ 2 * half n + 1 := le_half n
  rcases Nat.lt_or_ge (half n) k with hk | hk
  · rcases Nat.lt_or_ge n k with hkn | hkn
    · rw [binom_zero_of_lt n k hkn]; exact Nat.zero_le _
    · have hsplit : (half n) + (k - half n) = k := add_sub_of_le (Nat.le_of_lt hk)
      have hd := binom_climb_down n (k - half n) (half n) hge1
      rw [hsplit] at hd; exact hd
  · have hsplit : k + (half n - k) = half n := add_sub_of_le hk
    have hu := binom_climb_up n (half n - k) k (by rw [hsplit]; exact hle)
    rw [hsplit] at hu; exact hu

/-- AC helper: `a·(b·c·d) = a·b·(c·d)`. -/
private theorem m4 (a b c d : Nat) : a * (b * c * d) = a * b * (c * d) := by
  rw [nmul_assoc a b (c * d), nmul_assoc b c d]

/-- AC helper: `M·C·(Fk·Fd) = C·(Fk·(M·Fd))`. -/
private theorem m4b (M C Fk Fd : Nat) : M * C * (Fk * Fd) = C * (Fk * (M * Fd)) := by
  rw [Nat.mul_comm M C, nmul_assoc C M (Fk * Fd), nmul_left_comm M Fk Fd]

/-- ★ **The factorial form of the binomial** — `C(n,k) · k!·(n−k)! = n!` for
    `k ≤ n`.  The bridge from the chain count (`k!·(n−k)!` chains through a
    size-`k` set) to the binomial: it converts the LYM sum into the Sperner
    bound.  Proved from the absorption identity (`absorb`), inducting on `k`. -/
theorem binom_mul_fact :
    ∀ (n k : Nat), k ≤ n → binom n k * (fact k * fact (n - k)) = fact n
  | n, 0, _ => by
      rw [Binomial.binom_n_0, Nat.sub_zero, Nat.one_mul]
      show fact 0 * fact n = fact n
      rw [show fact 0 = 1 from rfl, Nat.one_mul]
  | n, k + 1, hk => by
      have hkn : k ≤ n := Nat.le_of_succ_le hk
      have ih := binom_mul_fact n k hkn
      have hfk : fact (k + 1) = (k + 1) * fact k := rfl
      have h1 : 1 ≤ n - k := le_sub_of_add_le (by rw [Nat.add_comm]; exact hk)
      have hsub : n - k = (n - (k + 1)) + 1 := by
        rw [Nat.sub_succ]; exact (sub_add_cancel h1).symm
      have hfnk : fact (n - k) = (n - k) * fact (n - (k + 1)) := by rw [hsub]; rfl
      have hab := absorb n k   -- (k+1) * binom n (k+1) = (n-k) * binom n k
      calc binom n (k + 1) * (fact (k + 1) * fact (n - (k + 1)))
          = binom n (k + 1) * (k + 1) * (fact k * fact (n - (k + 1))) := by
              rw [hfk]; exact m4 _ _ _ _
        _ = (n - k) * binom n k * (fact k * fact (n - (k + 1))) := by
              rw [Nat.mul_comm (binom n (k + 1)) (k + 1), hab]
        _ = binom n k * (fact k * fact (n - k)) := by
              rw [hfnk]; exact m4b _ _ _ _
        _ = fact n := ih

/-! ## §6 — Sperner for uniform (single-size) antichains

The easy half of the upper bound: an antichain *within one layer* cannot beat
that layer, hence cannot beat the middle layer.  This is fully general
(∅-axiom): the genuine content of Sperner is the **cross-layer** bound (§7),
that even mixing sizes cannot beat the single best layer. -/

/-- `Nat.beq k k = true` (propext-free; core `Nat.beq_refl` carries propext). -/
theorem beq_self : ∀ k, Nat.beq k k = true
  | 0 => rfl
  | k + 1 => beq_self k

/-- ★ **Uniform Sperner.**  Any duplicate-free family of size-`k` subsets of
    `[n]` has at most `binom n ⌊n/2⌋` members.  (A single-layer antichain is
    bounded by its layer, and no layer beats the middle — §5.) -/
theorem uniform_antichain_le {n k : Nat} {L : List (List Bool)}
    (hnd : L.Nodup) (hlen : ∀ A, A ∈ L → A.length = n) (hk : ∀ A, A ∈ L → cardB A = k) :
    L.length ≤ binom n (half n) := by
  have hsub : ∀ A, A ∈ L → A ∈ kLayer n k := by
    intro A hA
    refine mem_filter_of ?_ ?_
    · have hm := mem_allBoolLists A
      rwa [hlen A hA] at hm
    · show Nat.beq (cardB A) k = true
      rw [hk A hA]; exact beq_self k
  have hbound := nodup_length_le_of_subset hnd hsub
  rw [kLayer_card] at hbound
  exact Nat.le_trans hbound (binom_le_binom_mid n k)

/-! ## §7 — the LYM double-counting engine (the cross-layer upper bound)

The heart of Sperner's *upper* bound is the **LYM (Lubell–Yamamoto–Meshalkin)
inequality**, compiled here to the **double-counting / dual-union-bound** face
of the `COUNT` instruction (`seed/PROOF_ISA.md`).  Where the union bound (Erdős,
`CountExistence.union_bound`) says *bad events cover few colourings, so a good
one is left over*, its dual says: if a family of **chains** each meets the
antichain at most once, then summing "chains through `A`" over the antichain
cannot exceed the chain total.  Both are one move — Fubini on a 0/1 incidence
matrix, read once by rows and once by columns.

The engine is abstract and ∅-axiom.  Instantiating it to the *named* Sperner
bound needs the chain model's two counts — `#chains = n!` and
`#chains through A = |A|!·(n−|A|)!` — the permutation arithmetic that, exactly
as Erdős' named Ramsey bound left a `K_N`-bookkeeping rung over its built engine
(`RamseyLowerBound`), is the one honest rung here. -/

/-- Generic `Bool`-predicate count (propext-free; core `List.countP` carries it). -/
def lcount {β : Type _} (p : β → Bool) : List β → Nat
  | [] => 0
  | a :: l => (bif p a then 1 else 0) + lcount p l

/-- Sum of `f` over a list. -/
def sumOver {β : Type _} (f : β → Nat) : List β → Nat
  | [] => 0
  | a :: l => f a + sumOver f l

theorem sumOver_zero {β : Type _} : ∀ (L : List β), sumOver (fun _ => 0) L = 0
  | [] => rfl
  | _ :: l => by show 0 + sumOver (fun _ => (0 : Nat)) l = 0; rw [Nat.zero_add, sumOver_zero l]

theorem sumOver_const_one {β : Type _} : ∀ (L : List β), sumOver (fun _ => 1) L = L.length
  | [] => rfl
  | _ :: l => by
      show 1 + sumOver (fun _ => 1) l = l.length + 1
      rw [sumOver_const_one l, Nat.add_comm]

theorem sumOver_add {β : Type _} (f g : β → Nat) :
    ∀ (L : List β), sumOver (fun x => f x + g x) L = sumOver f L + sumOver g L
  | [] => rfl
  | a :: l => by
      show (f a + g a) + sumOver (fun x => f x + g x) l = (f a + sumOver f l) + (g a + sumOver g l)
      rw [sumOver_add f g l, Nat.add_add_add_comm]

theorem sumOver_le {β : Type _} {f g : β → Nat} :
    ∀ {L : List β}, (∀ x, x ∈ L → f x ≤ g x) → sumOver f L ≤ sumOver g L
  | [], _ => Nat.le_refl 0
  | a :: l, h => by
      show f a + sumOver f l ≤ g a + sumOver g l
      exact Nat.add_le_add (h a (List.Mem.head _))
              (sumOver_le (fun x hx => h x (List.Mem.tail _ hx)))

theorem sumOver_congr {β : Type _} {f g : β → Nat} :
    ∀ {L : List β}, (∀ x, x ∈ L → f x = g x) → sumOver f L = sumOver g L
  | [], _ => rfl
  | a :: l, h => by
      show f a + sumOver f l = g a + sumOver g l
      rw [h a (List.Mem.head _), sumOver_congr (fun x hx => h x (List.Mem.tail _ hx))]

/-- `lcount` is `sumOver` of the `0/1` indicator — the bridge between the
    user-facing count and the double-sum engine. -/
theorem lcount_eq_sumOver {β : Type _} (p : β → Bool) :
    ∀ (L : List β), lcount p L = sumOver (fun a => bif p a then 1 else 0) L
  | [] => rfl
  | a :: l => by
      show (bif p a then 1 else 0) + lcount p l
            = (bif p a then 1 else 0) + sumOver (fun a => bif p a then 1 else 0) l
      rw [lcount_eq_sumOver p l]

/-- ★ **Fubini / double-count swap.**  A `0/1` (or any) incidence matrix summed
    by rows equals it summed by columns — the engine of every double count. -/
theorem sumOver_swap {α γ : Type _} (g : α → γ → Nat) :
    ∀ (F : List α) (C : List γ),
      sumOver (fun A => sumOver (fun c => g A c) C) F
        = sumOver (fun c => sumOver (fun A => g A c) F) C
  | [], C => (sumOver_zero C).symm
  | A :: F, C => by
      show sumOver (fun c => g A c) C + sumOver (fun A' => sumOver (fun c => g A' c) C) F
            = sumOver (fun c => g A c + sumOver (fun A' => g A' c) F) C
      rw [sumOver_swap g F C, sumOver_add (fun c => g A c) (fun c => sumOver (fun A' => g A' c) F) C]

/-- ★ **The LYM inequality (engine form).**  If each chain `c ∈ chains` is
    incident (`inc · c`) to at most one antichain member, then the total of
    "chains through `A`" over the antichain `F` is at most `#chains`.  This is
    the dual of the union bound: the double count, read by columns, is bounded
    by `1` per chain. -/
theorem lym_double_count {α γ : Type _}
    (F : List α) (chains : List γ) (inc : α → γ → Bool)
    (h : ∀ c, c ∈ chains → lcount (fun A => inc A c) F ≤ 1) :
    sumOver (fun A => lcount (inc A) chains) F ≤ chains.length := by
  have e1 : sumOver (fun A => lcount (inc A) chains) F
      = sumOver (fun A => sumOver (fun c => bif inc A c then 1 else 0) chains) F :=
    sumOver_congr (fun A _ => lcount_eq_sumOver (inc A) chains)
  have key := sumOver_swap (fun A c => bif inc A c then 1 else 0) F chains
  rw [e1, key]
  have h' : ∀ c, c ∈ chains → sumOver (fun A => bif inc A c then 1 else 0) F ≤ 1 :=
    fun c hc => (lcount_eq_sumOver (fun A => inc A c) F) ▸ h c hc
  have hb : sumOver (fun c => sumOver (fun A => bif inc A c then 1 else 0) F) chains
      ≤ sumOver (fun _ => 1) chains := sumOver_le h'
  rwa [sumOver_const_one] at hb

/-! ## §8 — the named Sperner numbers (confirmation)

The Sperner number `C(n,⌊n/2⌋)` for small `n` is `1, 2, 3, 6, 10, 20, …`.  Each
is *realised* by the middle layer (`lower_bound`) and *bounds* every uniform
antichain (`uniform_antichain_le`); unimodality (`binom_le_binom_mid`) makes it
the largest layer. -/

/-- `C(n,⌊n/2⌋)` for `n = 1..6`. -/
theorem sperner_numbers :
    binom 1 (half 1) = 1 ∧ binom 2 (half 2) = 2 ∧ binom 3 (half 3) = 3
    ∧ binom 4 (half 4) = 6 ∧ binom 5 (half 5) = 10 ∧ binom 6 (half 6) = 20 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end E213.Lib.Math.Combinatorics.Sperner
