import E213.Lib.Physics.Simplex.Counts
import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Nat.NatRing213

/-!
# Combinatorics — binomial coefficients (Pascal recursion)

Reuses `binom` from `Lib/Physics/Simplex/Counts.lean` (defined
for the Δⁿ⁻¹ cohomology setup).  Extends with Pascal-level
identities and the Vandermonde-2 split for `binom (a+b) 2`.

Atomic content:
  * `binom n 0 = 1`, `binom n 1 = n` (defeq-blocked at level 0
    for free `n`; case-split forces reduction).
  * Pascal step at level 2: `binom (n+1) 2 = n + binom n 2`.
  * Vandermonde-2: `binom (a+b) 2 = binom a 2 + binom b 2 + a·b`.
  * Pascal's row 5 values; small-n Pascal step.

All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.Binomial

open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## Pascal-level identities -/

/-- `binom n 0 = 1` for any `n`.  Although the first pattern of
    `binom` reads `binom _ 0 = 1`, Lean does not eagerly reduce
    `binom n 0` when `n` is a free variable — case-splitting
    forces the reduction. -/
theorem binom_n_0 (n : Nat) : binom n 0 = 1 := by
  cases n <;> rfl

/-- `binom p m ≤ binom (p+1) m` — Pascal monotonicity in the
    first argument.  For `m = 0` both sides are `1` (via
    `binom_n_0`); for `m = succ k` the Pascal recursion gives
    `binom (p+1) (k+1) = binom p k + binom p (k+1)`, so
    `binom p (k+1) ≤ binom p k + binom p (k+1)` by
    `Nat.le_add_left`. -/
theorem binom_le_binom_succ (p m : Nat) :
    binom p m ≤ binom (p+1) m := by
  cases m with
  | zero => rw [binom_n_0 p, binom_n_0 (p+1)]; exact Nat.le_refl 1
  | succ k => exact Nat.le_add_left _ _

/-- `binom n 1 = n` by Nat-induction via Pascal recursion.  Used
    as the first ingredient in the Vandermonde-2 identity. -/
theorem binom_n_1 : ∀ n : Nat, binom n 1 = n
  | 0     => rfl
  | n + 1 => by
    show binom n 0 + binom n 1 = n + 1
    rw [binom_n_0 n, binom_n_1 n]
    exact Nat.add_comm 1 n

/-- Pascal step at level 2: `binom (n+1) 2 = n + binom n 2`.
    Combines the `binom` definition with `binom n 1 = n`. -/
theorem binom_succ_2 (n : Nat) : binom (n + 1) 2 = n + binom n 2 := by
  show binom n 1 + binom n 2 = n + binom n 2
  rw [binom_n_1]

/-! ## Vandermonde-2 -/

/-- Helper: reposition `b` from the second slot to the last slot
    in a left-associated 5-term `Nat` sum.  Internal to
    `binom_add_2`. -/
private theorem move_b_to_tail (a b X Y Z : Nat) :
    a + b + X + Y + Z = a + X + Y + Z + b := by
  rw [Nat.add_right_comm a b X,
      Nat.add_right_comm (a + X) b Y,
      Nat.add_right_comm (a + X + Y) b Z]

/-- Propext-free right distribution `(a + b) * c = a * c + b * c`.
    Re-derived from `Nat.mul_succ` + `Nat.add_assoc` +
    `Nat.add_right_comm` to avoid the `propext` dependency in
    `Nat.right_distrib`. -/
theorem add_mul_pure : ∀ (a b c : Nat), (a + b) * c = a * c + b * c
  | _, _, 0     => rfl
  | a, b, c + 1 => by
    show (a + b) * (c + 1) = a * (c + 1) + b * (c + 1)
    rw [Nat.mul_succ (a + b) c, Nat.mul_succ a c, Nat.mul_succ b c,
        add_mul_pure a b c]
    rw [← Nat.add_assoc (a * c + b * c) a b,
        ← Nat.add_assoc (a * c + a) (b * c) b,
        Nat.add_right_comm (a * c) (b * c) a]

/-- ★ **Vandermonde-2 identity**:
        `binom (a + b) 2 = binom a 2 + binom b 2 + a · b`.

    2-subsets of `a + b` split into intra-a (`binom a 2`),
    intra-b (`binom b 2`), and cross-ab (`a · b`).  Used by the
    mediant cohomology functor to decompose K_{a+c, *} S-pair
    counts; the same identity governs T-pairs. -/
theorem binom_add_2 : ∀ a b : Nat,
    binom (a + b) 2 = binom a 2 + binom b 2 + a * b
  | 0,     b => by
    show binom (0 + b) 2 = binom 0 2 + binom b 2 + 0 * b
    rw [Nat.zero_add, Nat.zero_mul, Nat.add_zero]
    show binom b 2 = 0 + binom b 2
    rw [Nat.zero_add]
  | a + 1, b => by
    have ih := binom_add_2 a b
    show binom (a + 1 + b) 2
        = binom (a + 1) 2 + binom b 2 + (a + 1) * b
    have h_assoc : a + 1 + b = (a + b) + 1 := Nat.add_right_comm a 1 b
    rw [h_assoc, binom_succ_2, ih, binom_succ_2, Nat.succ_mul]
    rw [← Nat.add_assoc (a + b) (binom a 2 + binom b 2) (a * b),
        ← Nat.add_assoc (a + b) (binom a 2) (binom b 2)]
    rw [← Nat.add_assoc (a + binom a 2 + binom b 2) (a * b) b]
    exact move_b_to_tail a b (binom a 2) (binom b 2) (a * b)

/-- Diagonal Pascal monotonicity: `binom p m ≤ binom (p+1) (m+1)` — the other Pascal
    summand (`binom (p+1) (m+1) = binom p m + binom p (m+1)`). -/
theorem binom_le_binom_succ_succ (p m : Nat) :
    binom p m ≤ binom (p + 1) (m + 1) := by
  show binom p m ≤ binom p m + binom p (m + 1)
  exact Nat.le_add_right _ _

/-! ## Vanishing, absorption, log-concavity -/

/-- `binom n k = 0` above the row: `n < k ⟹ C(n,k) = 0`. -/
theorem binom_vanish : ∀ n k : Nat, n < k → binom n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    show binom n k + binom n (k + 1) = 0
    rw [binom_vanish n k (Nat.lt_of_succ_lt_succ h),
        binom_vanish n (k + 1) (Nat.lt_of_succ_lt h)]

/-- ★★★ **Absorption identity**, subtraction-free form:

      `(k+1)·C(n,k+1) + k·C(n,k) = n·C(n,k)`

    (equivalently `(k+1)·C(n,k+1) = (n−k)·C(n,k)`, valid for all `n, k` — both sides
    vanish above the row).  Pure double induction on the Pascal recursion. -/
theorem binom_absorption : ∀ n k : Nat,
    (k + 1) * binom n (k + 1) + k * binom n k = n * binom n k
  | 0, 0 => rfl
  | 0, k + 1 => by
    show (k + 2) * binom 0 (k + 2) + (k + 1) * binom 0 (k + 1) = 0 * binom 0 (k + 1)
    rw [show binom 0 (k + 2) = 0 from rfl, show binom 0 (k + 1) = 0 from rfl,
        Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | n + 1, 0 => by
    show 1 * binom (n + 1) 1 + 0 * binom (n + 1) 0 = (n + 1) * binom (n + 1) 0
    rw [binom_n_1, binom_n_0]
    ring_nat
  | n + 1, k + 1 => by
    have ih1 : (k + 2) * binom n (k + 2) + (k + 1) * binom n (k + 1)
        = n * binom n (k + 1) := binom_absorption n (k + 1)
    have ih2 := binom_absorption n k
    show (k + 2) * (binom n (k + 1) + binom n (k + 2))
          + (k + 1) * (binom n k + binom n (k + 1))
        = (n + 1) * (binom n k + binom n (k + 1))
    rw [show (k + 2) * (binom n (k + 1) + binom n (k + 2))
            + (k + 1) * (binom n k + binom n (k + 1))
          = ((k + 2) * binom n (k + 2) + (k + 1) * binom n (k + 1))
            + ((k + 1) * binom n (k + 1) + k * binom n k)
            + binom n k + binom n (k + 1) from by ring_nat,
        ih1, ih2]
    ring_nat

/-- ★★★★★ **Binomial log-concavity** (division-free):

      `C(n,k) · C(n,k+2) ≤ C(n,k+1)²`.

    The discrete **Li–Yau gradient estimate** for the binomial heat kernel: spatial
    log-concavity of `u(t,·)` is the cleared form of `Δ log u ≤ 0` / the `|∇log u|²`
    bound (no `Real213` division, no `log` — the nonlinearity is carried by the
    cross-multiplied products).  Proof: two absorption identities convert
    `(e+2)(k+2)·C(n,k)C(n,k+2)` into `(e+1)(k+1)·C(n,k+1)²` (`n = k+2+e`), and
    `(e+1)(k+1) ≤ (e+2)(k+2)` plus positive cancellation closes; above the row the
    left side vanishes. -/
theorem binom_log_concave (n k : Nat) :
    binom n k * binom n (k + 2) ≤ binom n (k + 1) * binom n (k + 1) := by
  rcases Nat.lt_or_ge n (k + 2) with hlt | hge
  · rw [binom_vanish n (k + 2) hlt, Nat.mul_zero]
    exact Nat.zero_le _
  · obtain ⟨e, he⟩ := Nat.le.dest hge
    have habs1 : (k + 2) * binom n (k + 2) + (k + 1) * binom n (k + 1)
        = n * binom n (k + 1) := binom_absorption n (k + 1)
    have habs2 := binom_absorption n k
    generalize hA : binom n k = A at habs2 ⊢
    generalize hB : binom n (k + 1) = B at habs1 habs2 ⊢
    generalize hD : binom n (k + 2) = D at habs1 ⊢
    rw [← he] at habs1 habs2
    -- habs1 : (k+2)·D + (k+1)·B = (k+2+e)·B;  habs2 : (k+1)·B + k·A = (k+2+e)·A
    have h1 : (k + 2) * D = (e + 1) * B := by
      rw [show (k + 2 + e) * B = (e + 1) * B + (k + 1) * B from by ring_nat] at habs1
      exact E213.Meta.Nat.NatRing213.nat_add_right_cancel habs1
    have h2 : (k + 1) * B = (e + 2) * A := by
      rw [show (k + 2 + e) * A = (e + 2) * A + k * A from by ring_nat] at habs2
      exact E213.Meta.Nat.NatRing213.nat_add_right_cancel habs2
    have h3 : ((e + 2) * (k + 2)) * (A * D) = ((e + 1) * (k + 1)) * (B * B) := by
      rw [show ((e + 2) * (k + 2)) * (A * D) = ((k + 2) * D) * ((e + 2) * A) from by
            ring_nat,
          h1, ← h2]
      ring_nat
    have h4 : ((e + 1) * (k + 1)) * (B * B) ≤ ((e + 2) * (k + 2)) * (B * B) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_succ (e + 1)) (Nat.le_succ (k + 1)))
        (Nat.le_refl (B * B))
    have h5 : ((e + 2) * (k + 2)) * (A * D) ≤ ((e + 2) * (k + 2)) * (B * B) := by
      rw [h3]; exact h4
    have hpos : 0 < (e + 2) * (k + 2) :=
      Nat.lt_of_lt_of_le (by decide)
        (Nat.mul_le_mul (Nat.succ_le_succ (Nat.zero_le (e + 1)))
          (Nat.succ_le_succ (Nat.zero_le (k + 1))))
    exact Nat.le_of_mul_le_mul_left h5 hpos

/-! ## Unimodality (rising/falling halves + central dominance) -/

/-- Rising half (division-free, via absorption): `2k+1 ≤ n ⟹ C(n,k) ≤ C(n,k+1)` —
    the kernel increases up to the middle. -/
theorem binom_le_succ_of_le_half (n k : Nat) (h : 2 * k + 1 ≤ n) :
    binom n k ≤ binom n (k + 1) := by
  obtain ⟨e, he⟩ := Nat.le.dest h
  have habs := binom_absorption n k
  generalize hA : binom n k = A at habs ⊢
  generalize hB : binom n (k + 1) = B at habs ⊢
  rw [← he] at habs
  have h1 : (k + 1) * B = (k + 1 + e) * A := by
    rw [show (2 * k + 1 + e) * A = (k + 1 + e) * A + k * A from by ring_nat] at habs
    exact E213.Meta.Nat.NatRing213.nat_add_right_cancel habs
  have h2 : (k + 1) * A ≤ (k + 1) * B := by
    rw [h1]
    exact Nat.mul_le_mul (Nat.le_add_right (k + 1) e) (Nat.le_refl A)
  exact Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos k)

/-- Falling half: `n ≤ 2k+1 ⟹ C(n,k+1) ≤ C(n,k)` — the kernel decreases past the
    middle. -/
theorem binom_succ_le_of_half_le (n k : Nat) (h : n ≤ 2 * k + 1) :
    binom n (k + 1) ≤ binom n k := by
  obtain ⟨e, he⟩ := Nat.le.dest h
  have habs := binom_absorption n k
  generalize hA : binom n k = A at habs ⊢
  generalize hB : binom n (k + 1) = B at habs ⊢
  have h2 : ((k + 1) * B + e * A) + k * A = ((k + 1) * A) + k * A := by
    rw [show ((k + 1) * B + e * A) + k * A = ((k + 1) * B + k * A) + e * A from by
          ring_nat,
        habs, ← add_mul_pure n e A, he]
    ring_nat
  have h1 : (k + 1) * B + e * A = (k + 1) * A :=
    E213.Meta.Nat.NatRing213.nat_add_right_cancel h2
  have h3 : (k + 1) * B ≤ (k + 1) * A :=
    Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq h1)
  exact Nat.le_of_mul_le_mul_left h3 (Nat.succ_pos k)

/-- ★★★★ **Central dominance / unimodality**: `C(2n,k) ≤ C(2n,n)` for *every* `k` — the
    even-time kernel peaks at its centre.  Rising + falling halves chained; with
    `binom_log_concave` this is the full unimodal profile. -/
theorem binom_le_central (n : Nat) : ∀ k, binom (2 * n) k ≤ binom (2 * n) n := by
  have up : ∀ g k, k + g = n → binom (2 * n) k ≤ binom (2 * n) n := by
    intro g
    induction g with
    | zero =>
      intro k h
      have hk : k = n := h
      subst hk
      exact Nat.le_refl _
    | succ g ih =>
      intro k h
      have hk1 : k + 1 + g = n := by
        rw [show k + 1 + g = k + (g + 1) from by ring_nat]
        exact h
      have hstep : binom (2 * n) k ≤ binom (2 * n) (k + 1) := by
        apply binom_le_succ_of_le_half
        have hle : k + 1 ≤ n := Nat.le.intro hk1
        have hmul : 2 * (k + 1) ≤ 2 * n := Nat.mul_le_mul (Nat.le_refl 2) hle
        exact Nat.le_trans
          (Nat.le.intro (show 2 * k + 1 + 1 = 2 * (k + 1) from by ring_nat)) hmul
      exact Nat.le_trans hstep (ih (k + 1) hk1)
  have down : ∀ d, binom (2 * n) (n + d) ≤ binom (2 * n) n := by
    intro d
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih =>
      have hstep : binom (2 * n) (n + d + 1) ≤ binom (2 * n) (n + d) := by
        apply binom_succ_le_of_half_le
        exact Nat.le.intro (show 2 * n + (2 * d + 1) = 2 * (n + d) + 1 from by ring_nat)
      exact Nat.le_trans hstep ih
  intro k
  rcases Nat.le_total k n with h | h
  · obtain ⟨g, hg⟩ := Nat.le.dest h
    exact up g k hg
  · obtain ⟨d, hd⟩ := Nat.le.dest h
    rw [← hd]
    exact down d

/-! ## Small-n concrete identities -/

/-- ★ Pascal's row 5: 1, 5, 10, 10, 5, 1 — the d=5 simplex
    grade dimensions for K_{3,2}^{(c=2)} ↪ Δ⁴.  Symmetric:
    C(5, k) = C(5, 5−k).  Row sum 2⁵ = 32. -/
theorem binom_5_row :
    binom 5 0 = 1 ∧ binom 5 1 = 5 ∧ binom 5 2 = 10
    ∧ binom 5 3 = 10 ∧ binom 5 4 = 5 ∧ binom 5 5 = 1
    ∧ binom 5 0 + binom 5 1 + binom 5 2
        + binom 5 3 + binom 5 4 + binom 5 5 = 32
    ∧ binom 5 6 = 0  -- vanishes above grade d
    := by decide

/-- ★ Atomic Pascal step at (5, 2): C(5, 2) = C(4, 1) + C(4, 2)
    = 4 + 6 = 10. -/
theorem pascal_5_2 : binom 5 2 = binom 4 1 + binom 4 2 := by decide

end E213.Lib.Math.Combinatorics.Binomial
