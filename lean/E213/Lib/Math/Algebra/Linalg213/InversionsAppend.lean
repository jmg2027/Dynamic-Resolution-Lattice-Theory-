import E213.Lib.Math.Algebra.Linalg213.Laplace
import E213.Lib.Math.Algebra.Linalg213.PermSign
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
open E213.Lib.Math.Algebra.Linalg213.PermSign (ltCount_zero_of_all_ge altSign_self)
open E213.Tactic.NatHelper (sub_le_sub_left sub_sub_self le_sub_of_add_le sub_add_cancel)
open E213.Tactic.List213 (exists_of_mem_map)
open E213.Meta.Int213 (mul_one mul_comm mul_assoc)

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

/-! ## §3 — block-doubling has trivial sign -/

/-- `crossInv L M = 0` when every `M`-entry is at least every `L`-entry (no cross inversions). -/
theorem crossInv_eq_zero : ∀ (L M : List Nat), (∀ x ∈ L, ltCount x M = 0) → crossInv L M = 0
  | [],     _, _ => rfl
  | a :: L, M, h => by
      show ltCount a M + crossInv L M = 0
      rw [h a (List.Mem.head L), Nat.zero_add,
          crossInv_eq_zero L M (fun x hx => h x (List.Mem.tail a hx))]

/-- ★★★ **The block form's sign is its cross-inversion count.**  For any `L` with entries `≤ p`,
    the `±`-paired "block" list `0 :: L ++ (revL L).map (p − ·)` has
    `psign = altSign (crossInv L ((revL L).map (p − ·)))`.  The leading `0` contributes no
    inversions and the two halves carry **equal** sign (`psign_csub_revL`, `psign L · psign L = 1`),
    so only the cross term survives.  This is exactly the shape of `σ_a` (since
    `σ_a(p−x) = p − σ_a(x)`): `psign σ_a` reduces to a single cross-inversion count. -/
theorem psign_blockForm (p : Nat) (L : List Nat) (hL : ∀ x ∈ L, x ≤ p) :
    psign (0 :: (L ++ (revL L).map (fun v => p - v)))
      = altSign (crossInv L ((revL L).map (fun v => p - v))) := by
  rw [psign_cons, ltCount_zero_of_all_ge 0 _ (fun v _ => Nat.zero_le v),
      psign_append, psign_csub_revL p L hL]
  show (1 : Int) * (psign L * altSign (crossInv L ((revL L).map (fun v => p - v))) * psign L)
     = altSign (crossInv L ((revL L).map (fun v => p - v)))
  rw [Int.one_mul, mul_comm (psign L) (altSign (crossInv L ((revL L).map (fun v => p - v)))),
      mul_assoc, show psign L * psign L = 1 from altSign_self (inversions L), mul_one]

/-- ★★★ **Block-doubling has trivial sign.**  For `g` with all entries `≤ m` and `2m+1 ≤ p`, the
    orientation-preserving "doubling" `0 :: g ++ (revL g).map (p − ·)` has `psign = 1`: every cross
    pair vanishes (first half `⊆ [1,m]` strictly below second half `⊆ [m+1,2m]`), so the surviving
    cross-inversion count is `0`. -/
theorem psign_blockLift (g : List Nat) (p m : Nat) (hpm : 2 * m + 1 ≤ p) (hg : ∀ x ∈ g, x ≤ m) :
    psign (0 :: (g ++ (revL g).map (fun v => p - v))) = 1 := by
  have hmp : m ≤ p :=
    Nat.le_trans (Nat.le_trans (Nat.le_mul_of_pos_left m (by decide)) (Nat.le_succ (2 * m))) hpm
  have hmp1 : m + 1 ≤ p - m :=
    le_sub_of_add_le (by rw [show m + 1 + m = 2 * m + 1 from by ring_nat]; exact hpm)
  have hsh_ge : ∀ y ∈ (revL g).map (fun v => p - v), m + 1 ≤ y := by
    intro y hy
    obtain ⟨x', hx', hyx'⟩ := exists_of_mem_map hy
    have hx'g : x' ∈ g :=
      E213.Lib.Math.Algebra.Linalg213.PermClosure.LPerm.mem
        (E213.Lib.Math.Algebra.Linalg213.Permutation.LPerm.symm (revL_lperm g)) hx'
    rw [← hyx']
    exact Nat.le_trans hmp1 (sub_le_sub_left p (hg x' hx'g))
  have hcross : crossInv g ((revL g).map (fun v => p - v)) = 0 :=
    crossInv_eq_zero g _ (fun x hx => ltCount_zero_of_all_ge x _
      (fun y hy => Nat.le_trans (hg x hx) (Nat.le_trans (Nat.le_succ m) (hsh_ge y hy))))
  rw [psign_blockForm p g (fun x hx => Nat.le_trans (hg x hx) hmp), hcross]
  rfl

/-! ## §4 — symmetric cross-count parity: `psign σ_a` is `(−1)^μ` -/

/-- `p − w < a ↔ p < a + w` for `w ≤ p`. -/
private theorem sub_lt_iff_lt_add' {p w a : Nat} (h : w ≤ p) : (p - w < a) ↔ (p < a + w) := by
  constructor
  · intro hlt
    have h2 : (p - w) + w < a + w := Nat.add_lt_add_right hlt w
    rwa [sub_add_cancel h] at h2
  · intro hlt
    have h2 : (p - w) + w < a + w := by rw [sub_add_cancel h]; exact hlt
    exact Nat.lt_of_add_lt_add_right h2

/-- The cross relation `p − w < a` is symmetric in `(a, w)` for `a, w ≤ p`. -/
theorem psub_lt_symm {p w a : Nat} (hw : w ≤ p) (ha : a ≤ p) : (p - w < a) ↔ (p - a < w) := by
  constructor
  · intro h; exact (sub_lt_iff_lt_add' ha).mpr (by rw [Nat.add_comm]; exact (sub_lt_iff_lt_add' hw).mp h)
  · intro h; exact (sub_lt_iff_lt_add' hw).mpr (by rw [Nat.add_comm]; exact (sub_lt_iff_lt_add' ha).mp h)

/-- `colLt c L = #{x ∈ L : c < x}` (the "column" count against a fixed lower value `c`). -/
def colLt (c : Nat) : List Nat → Nat
  | []     => 0
  | x :: t => (if c < x then 1 else 0) + colLt c t

/-- `diagCount p L = #{x ∈ L : p − x < x}` (the diagonal of the symmetric cross relation). -/
def diagCount (p : Nat) : List Nat → Nat
  | []     => 0
  | x :: t => (if p - x < x then 1 else 0) + diagCount p t

/-- `altSign` of a doubled count is trivial. -/
theorem altSign_double (k : Nat) : altSign (k + k) = 1 := by rw [altSign_add]; exact altSign_self k

/-- Peel a head from the *second* argument of `crossInv`. -/
theorem crossInv_cons_right (c : Nat) :
    ∀ (L M : List Nat), crossInv L (c :: M) = colLt c L + crossInv L M
  | [],     _ => rfl
  | a :: t, M => by
      show ltCount a (c :: M) + crossInv t (c :: M) = colLt c (a :: t) + crossInv (a :: t) M
      rw [crossInv_cons_right c t M]
      show ((if c < a then 1 else 0) + ltCount a M) + (colLt c t + crossInv t M)
         = ((if c < a then 1 else 0) + colLt c t) + (ltCount a M + crossInv t M)
      ring_nat

/-- Symmetry rewrite: `colLt (p−b) F = ltCount b (F.map (p−·))` for `b ≤ p`, `F ≤ p`. -/
theorem colLt_eq_ltCount_map (p b : Nat) (hb : b ≤ p) :
    ∀ (F : List Nat), (∀ w ∈ F, w ≤ p) → colLt (p - b) F = ltCount b (F.map (fun w => p - w))
  | [],      _  => rfl
  | w :: F', hw => by
      have hwp : w ≤ p := hw w (List.Mem.head F')
      have hF' : ∀ z ∈ F', z ≤ p := fun z hz => hw z (List.Mem.tail w hz)
      show (if p - b < w then 1 else 0) + colLt (p - b) F'
         = (if p - w < b then 1 else 0) + ltCount b (F'.map (fun w => p - w))
      rw [colLt_eq_ltCount_map p b hb F' hF']
      rcases Nat.lt_or_ge (p - b) w with hlt | hge
      · rw [if_pos hlt, if_pos ((psub_lt_symm hb hwp).mp hlt)]
      · rw [if_neg (Nat.not_lt.mpr hge),
            if_neg (fun h => absurd ((psub_lt_symm hb hwp).mpr h) (Nat.not_lt.mpr hge))]

/-- ★★★★ **Symmetric cross-count parity.**  `altSign (crossInv F (F.map (p − ·))) =
    altSign (diagCount p F)` for `F` with entries `≤ p`.  The cross count
    `crossInv F (F.map(p−·)) = #{(x,w)∈F² : x+w>p}` is symmetric, so off-diagonal pairs come in
    twos (`altSign_double`) and only the diagonal `#{x : p−x<x}` survives mod 2.  Applied to
    `σ_a`'s first half, the diagonal is exactly Gauss's `μ`. -/
theorem altSign_crossInv_map_psub (p : Nat) :
    ∀ (F : List Nat), (∀ x ∈ F, x ≤ p) →
      altSign (crossInv F (F.map (fun w => p - w))) = altSign (diagCount p F)
  | [],      _  => rfl
  | b :: F', hb => by
      have hbp : b ≤ p := hb b (List.Mem.head F')
      have hF' : ∀ z ∈ F', z ≤ p := fun z hz => hb z (List.Mem.tail b hz)
      show altSign (crossInv (b :: F') ((p - b) :: F'.map (fun w => p - w)))
         = altSign (diagCount p (b :: F'))
      rw [crossInv_cons_right (p - b) (b :: F') (F'.map (fun w => p - w))]
      show altSign (((if p - b < b then 1 else 0) + colLt (p - b) F')
            + (ltCount b (F'.map (fun w => p - w)) + crossInv F' (F'.map (fun w => p - w))))
         = altSign ((if p - b < b then 1 else 0) + diagCount p F')
      rw [colLt_eq_ltCount_map p b hbp F' hF']
      have hrw : ((if p - b < b then 1 else 0) + ltCount b (F'.map (fun w => p - w)))
            + (ltCount b (F'.map (fun w => p - w)) + crossInv F' (F'.map (fun w => p - w)))
          = (if p - b < b then 1 else 0)
            + ((ltCount b (F'.map (fun w => p - w)) + ltCount b (F'.map (fun w => p - w)))
               + crossInv F' (F'.map (fun w => p - w))) := by ring_nat
      rw [hrw, altSign_add, altSign_add, altSign_double, Int.one_mul,
          altSign_crossInv_map_psub p F' hF', ← altSign_add]

end E213.Lib.Math.Algebra.Linalg213.InversionsAppend
