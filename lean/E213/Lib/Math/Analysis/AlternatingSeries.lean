import E213.Lib.Math.Analysis.ModulusConvergence
import E213.Lib.Math.Analysis.UniformLimitContinuous
import E213.Meta.Nat.Max213
import E213.Meta.Int213

/-!
# Leibniz alternating series test, ∅-axiom force-the-modulus (scratch)

The partial sums of an alternating series `a0 - a1 + a2 - ...` with terms
`a : Nat → Nat` non-increasing and `→ 0` with a modulus form a **Cauchy
sequence whose modulus IS the term-decay modulus** — the convergence rate is
*computed*, not asserted by completeness.

Tractable, signed-free formulation: the alternating tail
`altTail a j len` (= |a j − a(j+1) + a(j+2) − …|, the absolute alternating
sum of `len` terms from index `j`) satisfies the **bracketing inequality**

    altTail a j len ≤ a j        (the tail is bounded by the first term)

and equals the `distN`-distance between two partial sums.  Hence for
`p, q ≥ r m` the two partial sums are `closeN`-within `1/2^m`.
-/

namespace E213.Lib.Math.Analysis.AlternatingSeries

open E213.Lib.Math.Analysis.UniformLimitContinuous
  (distN distN_symm distN_self closeN distMet le_sub_add sub_le_of_le_add)
open E213.Lib.Math.Analysis.ModulusConvergence (ConvergesWith)

/-! ## 0. Pure truncated-subtraction helper (`Nat.sub_eq_zero_of_le` pulls
       `propext`; this additive-form replacement is ∅-axiom) -/

/-- `y − (y + k) = 0` unconditionally (∅-axiom; induction on `y`). -/
theorem sub_add_self_zero : ∀ (y k : Nat), y - (y + k) = 0 := by
  intro y
  induction y with
  | zero => intro k; show (0 : Nat) - (0 + k) = 0; rw [Nat.zero_sub]
  | succ y ih =>
      intro k
      show (y + 1) - ((y + 1) + k) = 0
      rw [Nat.succ_add, Nat.succ_sub_succ]
      exact ih k

/-- `y ≤ x → y − x = 0` — ∅-axiom twin of `Nat.sub_eq_zero_of_le`
    (which pulls `propext`).  Via `Nat.le.dest` (additive form). -/
theorem sub_eq_zero_p {y x : Nat} (h : y ≤ x) : y - x = 0 := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  rw [← hk]; exact sub_add_self_zero y k

/-! ## 1. The alternating tail and its bracketing bound -/

/-- `altTail a j len` — the **absolute alternating sum** of `len` terms of `a`
    starting at index `j`:  `|a j − a(j+1) + a(j+2) − … ± a(j+len−1)|`.

    Built parity-free by the nesting recursion
    `altTail a j (len+1) = | a j − altTail a (j+1) len |`
    (`distN _ 0` is `id`, `distN (a j) X` is `|a j − X|`).  This is exactly the
    Leibniz bracket: the alternating tail is the first term minus the (smaller)
    alternating tail of the rest. -/
def altTail (a : Nat → Nat) : Nat → Nat → Nat
  | _, 0       => 0
  | j, len + 1 => distN (a j) (altTail a (j + 1) len)

/-- `distN x 0 = x`. -/
theorem distN_zero (x : Nat) : distN x 0 = x := by
  show (x - 0) + (0 - x) = x
  rw [Nat.sub_zero, Nat.zero_sub, Nat.add_zero]

/-- `distN x y ≤ x` when `y ≤ x` (the gap below the larger value).
    `distN x y = (x − y) + (y − x) = (x − y) + 0 ≤ x`. -/
theorem distN_le_left {x y : Nat} (h : y ≤ x) : distN x y ≤ x := by
  show (x - y) + (y - x) ≤ x
  have h0 : y - x = 0 := sub_eq_zero_p h
  rw [h0, Nat.add_zero]
  exact Nat.sub_le x y

/-- **★ Bracketing bound.**  If `a` is non-increasing, the absolute alternating
    tail is bounded by its first term:  `altTail a j len ≤ a j`.

    Induction on `len`, *generalised over the start index* `j` (so the IH
    applies at `j+1`).  The nesting step:
    `altTail a j (len+1) = |a j − altTail a (j+1) len| ≤ a j` because the inner
    tail `altTail a (j+1) len ≤ a (j+1) ≤ a j` (IH + non-increasing). -/
theorem altTail_le (a : Nat → Nat) (hmono : ∀ k, a (k + 1) ≤ a k) :
    ∀ len j, altTail a j len ≤ a j := by
  intro len
  induction len with
  | zero => intro j; show (0 : Nat) ≤ a j; exact Nat.zero_le _
  | succ len ih =>
      intro j
      show distN (a j) (altTail a (j + 1) len) ≤ a j
      -- inner tail ≤ a(j+1) ≤ a j
      have hinner : altTail a (j + 1) len ≤ a (j + 1) := ih (j + 1)
      have hstep : a (j + 1) ≤ a j := hmono j
      have hle : altTail a (j + 1) len ≤ a j := Nat.le_trans hinner hstep
      exact distN_le_left hle

/-! ## 2. Genuine partial sums over `Int` and the distance identity

To certify `altTail` really is the gap between two partial sums (not a
free-standing definition), we exhibit the genuine signed partial sums
`S n = a 0 − a 1 + a 2 − … ± a (n−1)` over `Int` and prove

    (S p − S q).natAbs = altTail a p (q − p)      (for p ≤ q).

`diff a j len` is the *signed* alternating tail (front-peeling recursion,
matching `altTail`); `signPow j = (−1)^j`. -/

/-- `signPow j = (−1)^j : Int`. -/
def signPow : Nat → Int
  | 0     => 1
  | j + 1 => - signPow j

/-- `(−1)^(j+1) = −(−1)^j`. -/
theorem signPow_succ (j : Nat) : signPow (j + 1) = - signPow j := rfl

/-- `|(−1)^j| = 1`. -/
theorem signPow_natAbs (j : Nat) : (signPow j).natAbs = 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show (- signPow j).natAbs = 1
      rw [Int.natAbs_neg]; exact ih

/-- Signed alternating tail: `diff a j len = a j − a(j+1) + a(j+2) − …`
    (front-peeling, `len` terms).  Matches `altTail`'s recursion shape. -/
def diff (a : Nat → Nat) : Nat → Nat → Int
  | _, 0       => 0
  | j, len + 1 => (a j : Int) - diff a (j + 1) len

/-- ∅-axiom bridge: `(↑x − ↑y : Int) = subNatNat x y` (core `Int.sub` unfolds
    to `ofNat x + negOfNat y`, definitionally `subNatNat x y` for `y` succ; the
    `y = 0` case via `subNatNat_zero`). -/
theorem sub_eq_subNatNat (x y : Nat) : (x : Int) - (y : Int) = Int.subNatNat x y := by
  show Int.ofNat x + Int.negOfNat y = Int.subNatNat x y
  cases y with
  | zero =>
      show Int.ofNat x + 0 = Int.subNatNat x 0
      rw [Int.add_zero, E213.Meta.Int213.subNatNat_zero]
  | succ k => rfl

/-- `distN x y = x − y` (in `Int`) when `y ≤ x`.  ∅-axiom — through the pure
    `subNatNat_of_le` (avoids `Int.ofNat_sub`, which pulls `propext`). -/
theorem distN_cast_of_le {x y : Nat} (h : y ≤ x) :
    ((distN x y : Nat) : Int) = (x : Int) - (y : Int) := by
  show (((x - y) + (y - x) : Nat) : Int) = (x : Int) - (y : Int)
  rw [sub_eq_subNatNat, E213.Meta.Int213.subNatNat_of_le h]
  have h0 : y - x = 0 := sub_eq_zero_p h
  rw [h0, Nat.add_zero]
  rfl

/-- **The signed tail is the non-negative `altTail`**:
    `diff a j len = (altTail a j len : Int)` for non-increasing `a`.
    The signed alternating tail (starting on `+`) is genuinely non-negative,
    and its magnitude is exactly `altTail`.  Induction on `len` (gen. `j`):
    the front-peel `a j − diff a(j+1) len = a j − altTail a(j+1) len`, and since
    `altTail a(j+1) len ≤ a(j+1) ≤ a j` this equals `(distN (a j) … : Int)`. -/
theorem diff_eq_altTail (a : Nat → Nat) (hmono : ∀ k, a (k + 1) ≤ a k) :
    ∀ len j, diff a j len = (altTail a j len : Int) := by
  intro len
  induction len with
  | zero => intro j; rfl
  | succ len ih =>
      intro j
      -- diff a j (len+1) = a j − diff a (j+1) len
      show (a j : Int) - diff a (j + 1) len = (altTail a j (len + 1) : Int)
      rw [ih (j + 1)]
      -- now: (a j) − (altTail a (j+1) len) = (distN (a j) (altTail a (j+1) len))
      show (a j : Int) - (altTail a (j + 1) len : Int)
        = ((distN (a j) (altTail a (j + 1) len) : Nat) : Int)
      have hinner : altTail a (j + 1) len ≤ a (j + 1) := altTail_le a hmono len (j + 1)
      have hstep : a (j + 1) ≤ a j := hmono j
      have hle : altTail a (j + 1) len ≤ a j := Nat.le_trans hinner hstep
      rw [distN_cast_of_le hle]

/-! ## 3. The partial sums `S` and the gap identity -/

/-- The genuine signed partial sum `S n = a 0 − a 1 + a 2 − … ± a (n−1)`
    (`n` terms), over `Int`.  `S 0 = 0`; `S (n+1) = S n + (−1)^n · a n`. -/
def S (a : Nat → Nat) : Nat → Int
  | 0     => 0
  | n + 1 => S a n + signPow n * (a n : Int)

/-- **Gap identity.**  `S (j + len) − S j = (−1)^j · diff a j len`: the gap
    between two partial sums is, up to the global sign `(−1)^j`, the signed
    alternating tail.  Front-peel induction on `len` (generalised over `j`):
    `S(j+len) − S j = (S(j+len) − S(j+1)) + (S(j+1) − S j)`, the first piece is
    the IH at `j+1` and the second is `(−1)^j a j`; `(−1)^(j+1) = −(−1)^j`
    flips the inner sign exactly into `diff a j (len+1) = a j − diff a(j+1) len`. -/
theorem S_gap (a : Nat → Nat) :
    ∀ len j, S a (j + len) - S a j = signPow j * diff a j len := by
  intro len
  induction len with
  | zero =>
      intro j
      show S a (j + 0) - S a j = signPow j * diff a j 0
      -- diff a j 0 = 0; S a (j+0) = S a j
      show S a j - S a j = signPow j * (0 : Int)
      rw [Int.mul_zero]
      -- S a j − S a j = 0  (pure, via add_left_neg)
      show S a j + (- S a j) = 0
      rw [E213.Meta.Int213.add_comm]
      exact E213.Meta.Int213.add_left_neg (S a j)
  | succ len ih =>
      intro j
      -- j + (len+1) = (j+1) + len  (defeq: both (j+len).succ)
      -- inner: S ((j+1)+len) - S (j+1) = signPow (j+1) * diff a (j+1) len
      have hin : S a ((j + 1) + len) - S a (j + 1)
          = signPow (j + 1) * diff a (j + 1) len := ih (j + 1)
      -- step: S (j+1) - S j = signPow j * a j
      have hstep : S a (j + 1) - S a j = signPow j * (a j : Int) := by
        show (S a j + signPow j * (a j : Int)) - S a j = signPow j * (a j : Int)
        rw [show (S a j + signPow j * (a j : Int)) - S a j
              = signPow j * (a j : Int) by ring_intZ]
      -- assemble; rewrite index  j + (len+1) = (j+1) + len
      have hidx : j + (len + 1) = (j + 1) + len := by
        rw [Nat.succ_add, Nat.add_succ]
      rw [hidx]
      -- S ((j+1)+len) - S j = (S ((j+1)+len) - S (j+1)) + (S (j+1) - S j)
      have hsplit : S a ((j + 1) + len) - S a j
          = (S a ((j + 1) + len) - S a (j + 1)) + (S a (j + 1) - S a j) := by
        ring_intZ
      rw [hsplit, hin, hstep, signPow_succ]
      -- (−signPow j)·diff a(j+1) len + signPow j · a j = signPow j · diff a j (len+1)
      show (- signPow j) * diff a (j + 1) len + signPow j * (a j : Int)
        = signPow j * diff a j (len + 1)
      -- diff a j (len+1) = a j − diff a (j+1) len
      show (- signPow j) * diff a (j + 1) len + signPow j * (a j : Int)
        = signPow j * ((a j : Int) - diff a (j + 1) len)
      ring_intZ

/-- `|(−1)^j · x| = |x|` (∅-axiom; `Int.natAbs_mul` pulls `propext`, so we case
    on the sign through `Int.natAbs_neg`). -/
theorem signPow_mul_natAbs (j : Nat) (x : Int) :
    (signPow j * x).natAbs = x.natAbs := by
  induction j with
  | zero =>
      show ((1 : Int) * x).natAbs = x.natAbs
      rw [show (1 : Int) * x = x by ring_intZ]
  | succ j ih =>
      show ((- signPow j) * x).natAbs = x.natAbs
      rw [show (- signPow j) * x = -(signPow j * x) by ring_intZ, Int.natAbs_neg]
      exact ih

/-- **★★ Distance identity.**  `|S (j+len) − S j| = altTail a j len` for
    non-increasing `a`: the magnitude of the partial-sum gap is exactly the
    bracketing tail.  `|(−1)^j · diff| = |diff| = altTail` (`S_gap`,
    `signPow_mul_natAbs`, `diff_eq_altTail`). -/
theorem S_gap_natAbs (a : Nat → Nat) (hmono : ∀ k, a (k + 1) ≤ a k) (len j : Nat) :
    (S a (j + len) - S a j).natAbs = altTail a j len := by
  rw [S_gap a len j, signPow_mul_natAbs]
  rw [diff_eq_altTail a hmono len j, Int.natAbs_ofNat]

/-! ## 4. The bracketing inequality and the headline Cauchy modulus -/

/-- `(p + k) − p = k` — ∅-axiom truncated subtraction (Lean-core form pulls
    `propext`). -/
theorem add_sub_self_left : ∀ (p k : Nat), (p + k) - p = k := by
  intro p
  induction p with
  | zero => intro k; show (0 + k) - 0 = k; rw [Nat.zero_add, Nat.sub_zero]
  | succ p ih =>
      intro k
      show ((p + 1) + k) - (p + 1) = k
      rw [Nat.succ_add, Nat.succ_sub_succ]; exact ih k

/-- **★ The bracketing inequality** (`|S n − S m| ≤ a (min n m)`, ordered form).
    For `p ≤ q`, the alternating tail between the two partial sums is bounded by
    the first omitted term:  `|S p − S q| ≤ a p`.  (`S_gap_natAbs` rewrites the
    gap to `altTail a p (q−p)`, then `altTail_le`.) -/
theorem brackets_le (a : Nat → Nat) (hmono : ∀ k, a (k + 1) ≤ a k)
    {p q : Nat} (hpq : p ≤ q) :
    (S a p - S a q).natAbs ≤ a p := by
  -- write q = p + (q − p)
  obtain ⟨k, hk⟩ := Nat.le.dest hpq
  -- hk : p + k = q
  have hgap : (S a (p + k) - S a p).natAbs = altTail a p k :=
    S_gap_natAbs a hmono k p
  have hb : altTail a p k ≤ a p := altTail_le a hmono k p
  -- |S p − S q| = |S q − S p| = altTail a p k ≤ a p
  have hsymm : (S a p - S a q).natAbs = (S a (p + k) - S a p).natAbs := by
    rw [hk]
    rw [show S a p - S a q = -(S a q - S a p) by ring_intZ, Int.natAbs_neg]
  rw [hsymm, hgap]; exact hb

/-- The dyadic scaling step: from the term bound `2^m · a p < 2^(L0+1)` and
    `d ≤ a p`, conclude `2^m · d < 2^(L0+1)` (monotonicity of `2^m · _`). -/
theorem scale_lt {L0 m d ap : Nat}
    (hd : d ≤ ap) (hap : 2 ^ m * ap < 2 ^ (L0 + 1)) :
    2 ^ m * d < 2 ^ (L0 + 1) :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ hd) hap

/-- **★★★ `leibniz_cauchy` — the headline (∅-axiom, modulus computed).**

    Let `a : Nat → Nat` be non-increasing with a decay modulus `r` to `0` on
    the denominator `2^(L0+1)`:  `∀ m, ∀ k ≥ r m, 2^m · a k < 2^(L0+1)`
    (i.e. `a k` is `closeN`-within `1/2^m` of `0`).  Then the alternating
    partial sums `S a` are **Cauchy with the *same* modulus** `r`: for any
    `p, q ≥ r m`,

        2^m · |S a p − S a q| < 2^(L0+1)        (closeN-within 1/2^m).

    The convergence rate IS the term-decay modulus — forced into the open, no
    completeness, no monotone-bracketing existence claim.  Proof: order `p, q`;
    the bracketing inequality bounds the gap by the first term at the *smaller*
    index, which already lies past `r m` and is therefore `1/2^m`-small. -/
theorem leibniz_cauchy {L0 : Nat} (a : Nat → Nat) (hmono : ∀ k, a (k + 1) ≤ a k)
    {r : Nat → Nat} (hr : ∀ m, ∀ k, r m ≤ k → 2 ^ m * a k < 2 ^ (L0 + 1))
    (m : Nat) {p q : Nat} (hp : r m ≤ p) (hq : r m ≤ q) :
    2 ^ m * (S a p - S a q).natAbs < 2 ^ (L0 + 1) := by
  -- order p, q so the smaller index carries the bound
  cases Nat.le_total p q with
  | inl hpq =>
      -- p ≤ q : gap ≤ a p, and a p is 1/2^m-small (p ≥ r m)
      have hb : (S a p - S a q).natAbs ≤ a p := brackets_le a hmono hpq
      exact scale_lt hb (hr m p hp)
  | inr hqp =>
      -- q ≤ p : symmetrise, gap ≤ a q, a q is 1/2^m-small (q ≥ r m)
      have hb : (S a q - S a p).natAbs ≤ a q := brackets_le a hmono hqp
      have hsymm : (S a p - S a q).natAbs = (S a q - S a p).natAbs := by
        rw [show S a p - S a q = -(S a q - S a p) by ring_intZ, Int.natAbs_neg]
      rw [hsymm]
      exact scale_lt hb (hr m q hq)

/-! ## 5. Non-vacuous: an eventually-zero alternating series -/

/-- The eventually-zero, non-increasing magnitude sequence:
    `evZero N k = (if k < N then 1 else 0)` realised purely as
    `1` for `k < N` and `0` afterwards, via truncated subtraction
    `evZero N k = N − k` capped... — we use the clean witness `a k = N − k`
    truncated, which is non-increasing and `0` for `k ≥ N`. -/
def evZero (N : Nat) (k : Nat) : Nat := N - k

/-- `n.pred ≤ n` (∅-axiom). -/
theorem pred_le (n : Nat) : n.pred ≤ n := by
  cases n with
  | zero => exact Nat.le_refl 0
  | succ k => exact Nat.le_succ k

/-- `evZero N` is non-increasing (∅-axiom; `N − (k+1) = (N−k).pred ≤ N−k`,
    avoiding `Nat.sub_le_sub_left` which pulls `propext`). -/
theorem evZero_mono (N : Nat) : ∀ k, evZero N (k + 1) ≤ evZero N k := by
  intro k
  show N - (k + 1) ≤ N - k
  show (N - k).pred ≤ N - k
  exact pred_le (N - k)

/-- `evZero N` decays to `0` with modulus `r m = N`: for `k ≥ N`,
    `evZero N k = N − k = 0`, so `2^m · 0 = 0 < 2^(L0+1)`. -/
theorem evZero_modulus (L0 N : Nat) :
    ∀ m, ∀ k, N ≤ k → 2 ^ m * evZero N k < 2 ^ (L0 + 1) := by
  intro m k hk
  show 2 ^ m * (N - k) < 2 ^ (L0 + 1)
  have h0 : N - k = 0 := sub_eq_zero_p hk
  rw [h0, Nat.mul_zero]
  exact Nat.pos_pow_of_pos (L0 + 1) (by decide)

/-- **Non-vacuous instance.**  The alternating series with eventually-zero,
    non-increasing magnitudes `evZero N` has Cauchy partial sums with the
    (constant) modulus `r m = N` — the alternating sum stabilises, and
    `leibniz_cauchy` certifies the Cauchy bound on a concrete sequence. -/
theorem leibniz_cauchy_evZero (L0 N : Nat) (m : Nat) {p q : Nat}
    (hp : N ≤ p) (hq : N ≤ q) :
    2 ^ m * (S (evZero N) p - S (evZero N) q).natAbs < 2 ^ (L0 + 1) :=
  leibniz_cauchy (L0 := L0) (evZero N) (evZero_mono N)
    (r := fun _ => N) (evZero_modulus L0 N) m hp hq

#print axioms E213.Lib.Math.Analysis.AlternatingSeries.altTail_le
#print axioms E213.Lib.Math.Analysis.AlternatingSeries.diff_eq_altTail
#print axioms E213.Lib.Math.Analysis.AlternatingSeries.signPow_natAbs
#print axioms E213.Lib.Math.Analysis.AlternatingSeries.S_gap
#print axioms E213.Lib.Math.Analysis.AlternatingSeries.S_gap_natAbs
#print axioms E213.Lib.Math.Analysis.AlternatingSeries.brackets_le
#print axioms E213.Lib.Math.Analysis.AlternatingSeries.leibniz_cauchy
#print axioms E213.Lib.Math.Analysis.AlternatingSeries.leibniz_cauchy_evZero
