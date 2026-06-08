import E213.Lib.Math.Algebra.Linalg213.Laplace
import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Tactic.NatHelper

/-!
# Linalg213 — inversions of an append, and the reversal sign

General inversion-count combinatorics the sign theory needs beyond the adjacent-swap engine:

* `inversions_append` — `inversions (L ++ M) = inversions L + crossInv L M + inversions M`,
  where `crossInv L M = Σ_{x∈L} ltCount x M` is the count of cross pairs out of order.
* `psign_append` — the `altSign` shadow: `psign (L ++ M) = psign L · altSign (crossInv L M) · psign M`.

These feed the **reversal sign** (`psign_revL`) and the block-doubling parity used by Zolotarev's
converse.  A propext-free reversal `revL` is used throughout (`List.reverse` lemmas pull `propext`).
All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.InversionsAppend

open E213.Lib.Math.Algebra.Linalg213.Permutation
  (inversions ltCount psign ltCount_append psign_cons LPerm)
open E213.Lib.Math.Algebra.Linalg213.DetN (altSign altSign_add)
open E213.Lib.Math.Algebra.Linalg213.Laplace (ltCount_lperm)
open E213.Tactic.NatHelper (sub_le_sub_left sub_sub_self)
open E213.Meta.Int213 (mul_one mul_comm)

/-! ## §1 — cross inversions and the append law -/

/-- Cross inversions of an appended pair: `Σ_{x∈L}` (entries of `M` strictly below `x`). -/
def crossInv : List Nat → List Nat → Nat
  | [],     _ => 0
  | a :: L, M => ltCount a M + crossInv L M

/-- ★ **Inversions of an append.**  `inversions (L ++ M) = inversions L + crossInv L M + inversions M`. -/
theorem inversions_append : ∀ (L M : List Nat),
    inversions (L ++ M) = inversions L + crossInv L M + inversions M
  | [],     M => (Nat.zero_add (inversions M)).symm
  | a :: L, M => by
      show ltCount a (L ++ M) + inversions (L ++ M)
         = (ltCount a L + inversions L) + (ltCount a M + crossInv L M) + inversions M
      rw [ltCount_append a L M, inversions_append L M]; ring_nat

/-- ★ **Sign of an append** — the `altSign` shadow of `inversions_append`. -/
theorem psign_append (L M : List Nat) :
    psign (L ++ M) = psign L * altSign (crossInv L M) * psign M := by
  show altSign (inversions (L ++ M))
     = altSign (inversions L) * altSign (crossInv L M) * altSign (inversions M)
  rw [inversions_append L M, altSign_add, altSign_add]

/-! ## §2 — a propext-free reversal and the sign of `(c−·) ∘ reverse` -/

/-- Reversal (propext-free; `List.reverse` lemmas pull `propext`). -/
def revL : List Nat → List Nat
  | []     => []
  | a :: t => revL t ++ [a]

/-- `map` over a snoc (own proof; `List.map_append` pulls `propext`). -/
theorem map_snoc (f : Nat → Nat) :
    ∀ (L : List Nat) (x : Nat), (L ++ [x]).map f = L.map f ++ [f x]
  | [],     x => rfl
  | a :: t, x => by
      show f a :: (t ++ [x]).map f = f a :: (t.map f ++ [f x]); rw [map_snoc f t x]

/-- Bubble the head to the back, up to `LPerm`. -/
theorem lperm_cons_to_back : ∀ (a : Nat) (M : List Nat), LPerm (a :: M) (M ++ [a])
  | _, []     => LPerm.refl _
  | a, b :: M => LPerm.trans (LPerm.swap b a M) (LPerm.cons b (lperm_cons_to_back a M))

/-- `revL` is a permutation of its input. -/
theorem revL_lperm : ∀ (L : List Nat), LPerm L (revL L)
  | []     => LPerm.nil
  | a :: t => LPerm.trans (LPerm.cons a (revL_lperm t)) (lperm_cons_to_back a (revL t))

/-- `ltCount` is `revL`-invariant (multiset-invariant). -/
theorem ltCount_revL (a : Nat) (L : List Nat) : ltCount a (revL L) = ltCount a L :=
  (ltCount_lperm (revL_lperm L)).symm

/-- `c − a < c − b ↔ b < a` for `a, b ≤ c` (value-negation reverses order). -/
theorem csub_lt_iff {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) : (c - a < c - b) ↔ (b < a) := by
  constructor
  · intro h
    rcases Nat.lt_or_ge b a with h1 | h1
    · exact h1
    · exact absurd h (Nat.not_lt.mpr (sub_le_sub_left c h1))
  · intro h
    have hle : c - a ≤ c - b := sub_le_sub_left c (Nat.le_of_lt h)
    have hne : c - a ≠ c - b := fun heq => by
      have hab : a = b := by rw [← sub_sub_self ha, heq, sub_sub_self hb]
      exact Nat.lt_irrefl b (hab ▸ h)
    exact Nat.lt_of_le_of_ne hle hne

/-- Cross count of `map(c−·)L` against the singleton `[c−a]` equals `ltCount a L`. -/
theorem crossInv_map_csub (a c : Nat) (ha : a ≤ c) :
    ∀ (L : List Nat), (∀ x ∈ L, x ≤ c) → crossInv (L.map (fun v => c - v)) [c - a] = ltCount a L
  | [],     _  => rfl
  | b :: t, hb => by
    have hbc : b ≤ c := hb b (List.Mem.head t)
    have ht : ∀ x ∈ t, x ≤ c := fun x hx => hb x (List.Mem.tail b hx)
    show ltCount (c - b) [c - a] + crossInv ((t.map (fun v => c - v))) [c - a]
       = (if b < a then 1 else 0) + ltCount a t
    rw [crossInv_map_csub a c ha t ht]
    show (if c - a < c - b then (1 : Nat) else 0) + ltCount a t
       = (if b < a then 1 else 0) + ltCount a t
    rcases Nat.lt_or_ge b a with hba | hba
    · rw [if_pos ((csub_lt_iff ha hbc).mpr hba), if_pos hba]
    · rw [if_neg (fun hca => absurd ((csub_lt_iff ha hbc).mp hca) (Nat.not_lt.mpr hba)),
          if_neg (Nat.not_lt.mpr hba)]

/-- ★★ **The sign of `(c−·) ∘ revL` is trivial:** `psign ((revL L).map (c − ·)) = psign L`
    for `L` with all entries `≤ c`.  Value-negation `c−·` and the reversal each flip every
    pairwise comparison; composed they cancel pair-by-pair — no inversion-count change.  (This is
    the block-doubling parity behind Zolotarev: the two halves of `σ_a`'s block part have equal
    sign.) -/
theorem psign_csub_revL (c : Nat) :
    ∀ (L : List Nat), (∀ x ∈ L, x ≤ c) → psign ((revL L).map (fun v => c - v)) = psign L
  | [],     _  => rfl
  | a :: t, hb => by
    have hac : a ≤ c := hb a (List.Mem.head t)
    have ht : ∀ x ∈ t, x ≤ c := fun x hx => hb x (List.Mem.tail a hx)
    have hmemt : ∀ x ∈ revL t, x ≤ c :=
      fun x hx => ht x (E213.Lib.Math.Algebra.Linalg213.PermClosure.LPerm.mem
        (E213.Lib.Math.Algebra.Linalg213.Permutation.LPerm.symm (revL_lperm t)) hx)
    show psign ((revL t ++ [a]).map (fun v => c - v)) = psign (a :: t)
    rw [map_snoc (fun v => c - v) (revL t) a, psign_append, psign_csub_revL c t ht,
        show psign ([c - a] : List Nat) = 1 from rfl, mul_one,
        crossInv_map_csub a c hac (revL t) hmemt, ltCount_revL a t, psign_cons]
    exact mul_comm (psign t) (altSign (ltCount a t))

end E213.Lib.Math.Algebra.Linalg213.InversionsAppend
