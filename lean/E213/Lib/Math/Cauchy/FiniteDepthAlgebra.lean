import E213.Lib.Math.Cauchy.NewtonGregory

/-!
# FiniteDepthAlgebra — the finite-difference-depth sequences form a ring

The `ℤ`-sequences of finite faithful divergence depth (`NewtonGregory.polyDepthZ`)
are closed under addition, scalar multiplication, shift, depth-weakening, and
**pointwise product** with **additive depths**:

> ★★★ `polyDepthZ_mul` : `polyDepthZ d s → polyDepthZ e t → polyDepthZ (d+e) (s·t)`.

The product law is the discrete Leibniz rule `Δ(s·t) = (E s)·(Δ t) + (Δ s)·t`
(`diffZ_mul`) driven through a strong induction on `d + e`.  It turns the
hand-counted depth arithmetic of `DivergenceDepth` (e.g. π's "degree-4 ratio =
product of two degree-2 coefficients") into a theorem about the ring of
finite-depth sequences.

All ∅-axiom (over `Int213`).
-/

namespace E213.Lib.Math.Cauchy.FiniteDepthAlgebra

open E213.Lib.Math.Cauchy.NewtonGregory
  (diffZ liftKZ isConstZ polyDepthZ diffZ_isConstZ_zero add_add_add_comm
   add_sub_cancel_left' mul_zero')
open E213.Meta.Int213
  (add_comm add_assoc add_left_comm add_right_comm mul_comm mul_add add_mul
   mul_sub sub_mul add_neg_cancel add_left_neg neg_add zero_mul zero_add
   mul_eq_zero sub_add_cancel_int)

/-! ## §0 — ℤ rearrangement helpers -/

/-- `(a + b) − (c + d) = (a − c) + (b − d)` (pure). -/
theorem add_sub_add (a b c d : Int) : (a + b) - (c + d) = (a - c) + (b - d) := by
  rw [Int.sub_eq_add_neg, neg_add, Int.sub_eq_add_neg, Int.sub_eq_add_neg,
      add_add_add_comm]

/-- Telescoping: `(X − Y) + (Y − Z) = X − Z` (pure). -/
theorem sub_add_sub (X Y Z : Int) : (X - Y) + (Y - Z) = X - Z := by
  rw [Int.sub_eq_add_neg, Int.sub_eq_add_neg, Int.sub_eq_add_neg,
      add_assoc X (-Y) (Y + -Z), ← add_assoc (-Y) Y (-Z),
      show -Y + Y = 0 from by rw [add_comm, add_neg_cancel], zero_add]

/-! ## §1 — `liftKZ` is additive; `isConstZ` / `polyDepthZ` closed under `+` -/

/-- Iterated forward difference is additive: `Δᵏ(u+v) = Δᵏu + Δᵏv` (pointwise). -/
theorem liftKZ_add (u v : Nat → Int) : ∀ k n,
    liftKZ k (fun m => u m + v m) n = liftKZ k u n + liftKZ k v n
  | 0,   n => rfl
  | k+1, n => by
    show liftKZ k (fun m => u m + v m) (n+1) - liftKZ k (fun m => u m + v m) n
       = (liftKZ k u (n+1) - liftKZ k u n) + (liftKZ k v (n+1) - liftKZ k v n)
    rw [liftKZ_add u v k (n+1), liftKZ_add u v k n, add_sub_add]

/-- `Δᵏ(c·s) = c·Δᵏs` (pointwise scalar). -/
theorem liftKZ_smul (c : Int) (s : Nat → Int) : ∀ k n,
    liftKZ k (fun m => c * s m) n = c * liftKZ k s n
  | 0,   n => rfl
  | k+1, n => by
    show liftKZ k (fun m => c * s m) (n+1) - liftKZ k (fun m => c * s m) n
       = c * (liftKZ k s (n+1) - liftKZ k s n)
    rw [liftKZ_smul c s k (n+1), liftKZ_smul c s k n, mul_sub]

/-- Sum of two constant `ℤ`-sequences is constant. -/
theorem isConstZ_add {u v : Nat → Int} (hu : isConstZ u) (hv : isConstZ v) :
    isConstZ (fun n => u n + v n) := fun n => by
  show u n + v n = u 0 + v 0
  rw [hu n, hv n]

/-- ★ **Depth is closed under addition** (same depth). -/
theorem polyDepthZ_add {d : Nat} {s t : Nat → Int}
    (hs : polyDepthZ d s) (ht : polyDepthZ d t) : polyDepthZ d (fun n => s n + t n) := by
  intro n
  show liftKZ d (fun m => s m + t m) n = liftKZ d (fun m => s m + t m) 0
  rw [liftKZ_add s t d n, liftKZ_add s t d 0, hs n, ht n]

/-- ★ **Depth is closed under scalar multiplication.** -/
theorem polyDepthZ_smul {d : Nat} {s : Nat → Int} (c : Int)
    (hs : polyDepthZ d s) : polyDepthZ d (fun n => c * s n) := by
  intro n
  show liftKZ d (fun m => c * s m) n = liftKZ d (fun m => c * s m) 0
  rw [liftKZ_smul c s d n, liftKZ_smul c s d 0, hs n]

/-! ## §2 — the vanishing view: `vanishZ k s := Δᵏs ≡ 0`, equivalent to depth -/

/-- `Δᵏ s` is identically zero. -/
def vanishZ (k : Nat) (s : Nat → Int) : Prop := ∀ n, liftKZ k s n = 0

/-- `polyDepthZ d s ↔ Δ^{d+1}s ≡ 0`.  (`isConstZ u ↔ Δu ≡ 0`.) -/
theorem polyDepthZ_iff_vanish {d : Nat} {s : Nat → Int} :
    polyDepthZ d s ↔ vanishZ (d + 1) s := by
  constructor
  · intro h n
    show liftKZ (d+1) s n = 0
    exact diffZ_isConstZ_zero h n
  · intro h n
    -- Δ^{d+1}s ≡ 0 ⟹ liftKZ d s constant (induct: diffZ ≡ 0 ⟹ isConstZ)
    show liftKZ d s n = liftKZ d s 0
    induction n with
    | zero => rfl
    | succ n ih =>
      have hstep : liftKZ d s (n+1) - liftKZ d s n = 0 := h n
      have heq : liftKZ d s (n+1) = liftKZ d s n := by
        rw [← sub_add_cancel_int (liftKZ d s (n+1)) (liftKZ d s n), hstep, zero_add]
      rw [heq]; exact ih

/-- `vanishZ` is monotone in the order: `Δᵏs ≡ 0 ⟹ Δ^{k+1}s ≡ 0`. -/
theorem vanishZ_succ {k : Nat} {s : Nat → Int} (h : vanishZ k s) : vanishZ (k + 1) s := by
  intro n
  show liftKZ k s (n+1) - liftKZ k s n = 0
  rw [h (n+1), h n, Int.sub_eq_add_neg, add_neg_cancel]

/-- The zero sequence vanishes at every order. -/
theorem vanishZ_of_zero {u : Nat → Int} (h : ∀ n, u n = 0) : ∀ k, vanishZ k u
  | 0,   n => h n
  | k+1, n => by
    show liftKZ k u (n+1) - liftKZ k u n = 0
    rw [vanishZ_of_zero h k (n+1), vanishZ_of_zero h k n, Int.sub_eq_add_neg, add_neg_cancel]

/-- `vanishZ` closed under `+`. -/
theorem vanishZ_add {k : Nat} {u v : Nat → Int} (hu : vanishZ k u) (hv : vanishZ k v) :
    vanishZ k (fun n => u n + v n) := fun n => by
  rw [liftKZ_add u v k n, hu n, hv n, Int.add_zero]

/-- `vanishZ` closed under scalar multiplication. -/
theorem vanishZ_smul {k : Nat} {s : Nat → Int} (c : Int) (h : vanishZ k s) :
    vanishZ k (fun n => c * s n) := fun n => by
  rw [liftKZ_smul c s k n, h n, mul_zero']

/-- `liftKZ` respects pointwise equality (no `funext`). -/
theorem liftKZ_congrZ {u v : Nat → Int} (h : ∀ m, u m = v m) : ∀ k n,
    liftKZ k u n = liftKZ k v n
  | 0,   n => h n
  | k+1, n => by
    show liftKZ k u (n+1) - liftKZ k u n = liftKZ k v (n+1) - liftKZ k v n
    rw [liftKZ_congrZ h k (n+1), liftKZ_congrZ h k n]

/-- `vanishZ` respects pointwise equality. -/
theorem vanishZ_congr {k : Nat} {u v : Nat → Int} (h : ∀ m, u m = v m)
    (hu : vanishZ k u) : vanishZ k v := fun n => by
  rw [← liftKZ_congrZ h k n]; exact hu n

/-! ## §3 — shift / difference commutation -/

/-- `Δᵏ` commutes with the shift `E`: `Δᵏ(E s) n = (Δᵏ s)(n+1)`. -/
theorem liftKZ_shift (s : Nat → Int) : ∀ k n,
    liftKZ k (fun m => s (m + 1)) n = liftKZ k s (n + 1)
  | 0,   n => rfl
  | k+1, n => by
    show liftKZ k (fun m => s (m + 1)) (n+1) - liftKZ k (fun m => s (m + 1)) n
       = liftKZ k s (n + 1 + 1) - liftKZ k s (n + 1)
    rw [liftKZ_shift s k (n+1), liftKZ_shift s k n]

/-- `vanishZ` is shift-invariant. -/
theorem vanishZ_shift {k : Nat} {s : Nat → Int} (h : vanishZ k s) :
    vanishZ k (fun m => s (m + 1)) := fun n => by
  rw [liftKZ_shift s k n]; exact h (n + 1)

/-- `Δᵏ(Δ s) n = Δ^{k+1} s n` (the difference commutes with its iterate). -/
theorem liftKZ_diffZ_comm (s : Nat → Int) : ∀ k n,
    liftKZ k (diffZ s) n = liftKZ (k + 1) s n
  | 0,   n => rfl
  | k+1, n => by
    show liftKZ k (diffZ s) (n+1) - liftKZ k (diffZ s) n
       = liftKZ (k+1) s (n+1) - liftKZ (k+1) s n
    rw [liftKZ_diffZ_comm s k (n+1), liftKZ_diffZ_comm s k n]

/-- `Δ^{k+1}s ≡ 0 ⟹ Δᵏ(Δs) ≡ 0`: peel one difference. -/
theorem vanishZ_diff {k : Nat} {s : Nat → Int} (h : vanishZ (k + 1) s) :
    vanishZ k (diffZ s) := fun n => by rw [liftKZ_diffZ_comm s k n]; exact h n

/-! ## §4 — the discrete Leibniz rule and multiplicative depth-additivity -/

/-- ★ **Discrete Leibniz rule.**  `Δ(s·t) n = s(n+1)·(Δt n) + (Δs n)·t n` — the
    product rule with one factor shifted (telescoping `s(n+1)t(n+1) − s n·t n`). -/
theorem diffZ_mul (s t : Nat → Int) (n : Nat) :
    diffZ (fun m => s m * t m) n
      = s (n + 1) * diffZ t n + diffZ s n * t n := by
  show s (n + 1) * t (n + 1) - s n * t n
     = s (n + 1) * (t (n + 1) - t n) + (s (n + 1) - s n) * t n
  rw [mul_sub, sub_mul, sub_add_sub]

/-- The vanishing form of depth-additivity, by induction on the degree bound `N`. -/
theorem mul_vanish : ∀ (N d e : Nat) (s t : Nat → Int), d + e ≤ N →
    vanishZ (d + 1) s → vanishZ (e + 1) t → vanishZ (d + e + 1) (fun n => s n * t n)
  | 0, d, e, s, t, hN, hs, ht => by
    have hd0 : d = 0 := Nat.le_zero.mp (Nat.le_trans (Nat.le_add_right d e) hN)
    have he0 : e = 0 := Nat.le_zero.mp (Nat.le_trans (Nat.le_add_left e d) hN)
    subst hd0; subst he0
    intro n
    show diffZ (fun m => s m * t m) n = 0
    have hds : diffZ s n = 0 := vanishZ_diff hs n
    have hdt : diffZ t n = 0 := vanishZ_diff ht n
    rw [diffZ_mul s t n, hdt, hds, mul_zero', zero_mul, Int.add_zero]
  | N+1, d, e, s, t, hN, hs, ht => by
    have hreduce : vanishZ (d + e) (diffZ (fun m => s m * t m))
        → vanishZ (d + e + 1) (fun n => s n * t n) := fun hd n => by
      rw [show liftKZ (d + e + 1) (fun m => s m * t m) n
            = liftKZ (d + e) (diffZ (fun m => s m * t m)) n from
            (liftKZ_diffZ_comm (fun m => s m * t m) (d + e) n).symm]
      exact hd n
    apply hreduce
    apply vanishZ_congr (u := fun n => s (n + 1) * diffZ t n + diffZ s n * t n)
      (fun n => (diffZ_mul s t n).symm)
    apply vanishZ_add
    · -- (E s)·(Δ t)
      cases e with
      | zero =>
        refine vanishZ_of_zero (fun n => ?_) (d + 0)
        have hdt : diffZ t n = 0 := vanishZ_diff ht n
        show s (n + 1) * diffZ t n = 0
        rw [hdt, mul_zero']
      | succ e' =>
        have hbd : d + e' ≤ N := Nat.le_of_succ_le_succ hN
        exact mul_vanish N d e' (fun m => s (m + 1)) (diffZ t) hbd
          (vanishZ_shift hs) (vanishZ_diff ht)
    · -- (Δ s)·t
      cases d with
      | zero =>
        refine vanishZ_of_zero (fun n => ?_) (0 + e)
        have hds : diffZ s n = 0 := vanishZ_diff hs n
        show diffZ s n * t n = 0
        rw [hds, zero_mul]
      | succ d' =>
        have h' : d' + e + 1 ≤ N + 1 := by rw [← Nat.add_right_comm d' 1 e]; exact hN
        have hbd : d' + e ≤ N := Nat.le_of_succ_le_succ h'
        rw [Nat.add_right_comm d' 1 e]
        exact mul_vanish N d' e (diffZ s) t hbd (vanishZ_diff hs) ht

/-- ★★★ **Depth-additivity — finite-depth `ℤ`-sequences form a ring.**
    `polyDepthZ d s → polyDepthZ e t → polyDepthZ (d+e) (s·t)`.  Turns the
    hand-counted depth arithmetic of `DivergenceDepth` (a product of a degree-`d`
    and a degree-`e` discrete polynomial is degree `d+e`) into a theorem.  Via the
    discrete Leibniz rule and the vanishing form `mul_vanish`. -/
theorem polyDepthZ_mul {d e : Nat} {s t : Nat → Int}
    (hs : polyDepthZ d s) (ht : polyDepthZ e t) :
    polyDepthZ (d + e) (fun n => s n * t n) :=
  polyDepthZ_iff_vanish.mpr
    (mul_vanish (d + e) d e s t (Nat.le_refl _)
      (polyDepthZ_iff_vanish.mp hs) (polyDepthZ_iff_vanish.mp ht))

/-! ## §5 — the boundary marker: periodic ∩ finite-depth = constant

A periodic continued fraction (quadratic irrational, Lagrange) is bounded but
*not* polynomial unless constant.  So the Newton-reconstructible (finite-depth)
sector and the periodic (Markov/quadratic) sector meet only at the constants —
the boundary of the divergence-depth classification. -/

/-- `s` has period `p` over `ℤ`. -/
def PeriodicZ (p : Nat) (s : Nat → Int) : Prop := ∀ n, s (n + p) = s n

/-- The forward difference of a periodic sequence is periodic. -/
theorem diffZ_periodic {p : Nat} {s : Nat → Int} (h : PeriodicZ p s) :
    PeriodicZ p (diffZ s) := fun n => by
  show s (n + p + 1) - s (n + p) = s (n + 1) - s n
  rw [h n, show n + p + 1 = (n + 1) + p from by rw [Nat.add_right_comm], h (n + 1)]

/-- `a + x = a ⟹ x = 0`. -/
theorem add_right_eq_self {a x : Int} (h : a + x = a) : x = 0 := by
  have h2 : -a + (a + x) = 0 := by rw [h, add_left_neg]
  rwa [← add_assoc, add_left_neg, zero_add] at h2

/-- A sequence with constant first difference `c` is affine: `s k = s 0 + k·c`. -/
theorem affine_of_diff_const (s : Nat → Int) (c : Int) (hc : ∀ k, diffZ s k = c) :
    ∀ k, s k = s 0 + (k : Int) * c
  | 0 => by show s 0 = s 0 + (0 : Int) * c; rw [zero_mul, Int.add_zero]
  | k+1 => by
    have hstep : s (k + 1) = c + s k := by
      show s (k + 1) = c + s k
      rw [← hc k]; show s (k + 1) = (s (k + 1) - s k) + s k; rw [sub_add_cancel_int]
    rw [hstep, affine_of_diff_const s c hc k]
    show c + (s 0 + (k : Int) * c) = s 0 + ((k : Int) + 1) * c
    rw [add_mul, Int.one_mul, add_left_comm, add_comm c ((k : Int) * c)]

/-- ★★★ **Periodic ∩ finite-depth = constant.**  A periodic `ℤ`-sequence of finite
    faithful divergence depth is constant.  So the finite-depth (Newton-
    reconstructible) class and the periodic (quadratic-irrational / Markov) class are
    disjoint apart from the constants — the boundary of the depth classification. -/
theorem periodic_finite_depth_const {p : Nat} (hp : 0 < p) {s : Nat → Int} :
    ∀ d, PeriodicZ p s → polyDepthZ d s → isConstZ s
  | 0,   _,    h => h
  | d+1, hper, h => by
    have hdpd : polyDepthZ d (diffZ s) :=
      polyDepthZ_iff_vanish.mpr (vanishZ_diff (polyDepthZ_iff_vanish.mp h))
    have hdconst : isConstZ (diffZ s) :=
      periodic_finite_depth_const hp d (diffZ_periodic hper) hdpd
    have hc0 : diffZ s 0 = 0 := by
      have haff := affine_of_diff_const s (diffZ s 0) hdconst
      have hsp : s p = s 0 := by have := hper 0; rwa [Nat.zero_add] at this
      have hpc : (p : Int) * diffZ s 0 = 0 := by
        have heq := haff p
        rw [hsp] at heq
        exact add_right_eq_self heq.symm
      rcases mul_eq_zero hpc with hp0 | hc
      · have hp00 : p = 0 := Int.ofNat.inj hp0
        rw [hp00] at hp; exact absurd hp (Nat.lt_irrefl 0)
      · exact hc
    exact fun n => by
      show liftKZ 0 s n = liftKZ 0 s 0
      have hdz : ∀ m, diffZ s m = 0 := fun m => by rw [hdconst m, hc0]
      exact (polyDepthZ_iff_vanish (d := 0) (s := s)).mpr hdz n

end E213.Lib.Math.Cauchy.FiniteDepthAlgebra
