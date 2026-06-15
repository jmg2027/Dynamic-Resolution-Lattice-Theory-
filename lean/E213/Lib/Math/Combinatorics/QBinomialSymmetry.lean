import E213.Meta.Int213.Core
import E213.Meta.Int213.PolyIntMTactic
import E213.Lib.Math.Combinatorics.QBinomial
import E213.Meta.Tactic.NatHelper

/-!
# Dual q-Pascal (form B) + general q-binomial symmetry (∅-axiom)

Closes the open follow-up of `Combinatorics/QBinomial.lean`.

`QBinomial.qbinom` is defined by form A:
  `[n+1,k+1]_q = q^(k+1)·[n,k+1]_q + [n,k]_q`  (power on the *upper* index).

* `qbinom_rel` — adjacent-column relation `(q^(n-k)-1)·[n,k] = (q^(k+1)-1)·[n,k+1]`
  (the algebraic heart; induction on `n` using form A + the column lemma + above-diagonal
  vanishing).
* `qbinom_pascal_dual` — **dual q-Pascal (form B)**:
  `[n+1,k+1]_q = q^(n-k)·[n,k]_q + [n,k+1]_q`.
  NOTE the power rides the *lower* index `[n,k]` (the partner of form A's *upper* index).
  The prompt's draft put `q^(n-k)` on `[n,k+1]` — that is FALSE for this `qbinom`
  convention (verified numerically: it would require `q^(k+1)=q^(n-k)` on the support of
  `[n,k+1]`).  The corrected statement above is the true dual and holds for all `q,n,k`.
* `qbinom_symm` — **general symmetry** `[n,k]_q = [n,n-k]_q` (the ★★★ goal),
  induction on `n` using form A + `qbinom_rel` + `qbinom_diag`.

Auxiliaries: `qpow_add`, `qpow_combine1/2` (power bookkeeping), `qbinom_above`
(above-diagonal vanishing), `qbinom_col1` (q-integer column), `qbinom_diag`,
`rel_step`/`symm_step` (isolated `ring_intZ` algebra).  All `#print axioms`-clean.
-/

namespace E213.Lib.Math.Combinatorics.QBinomialSymmetry

open E213.Lib.Math.Combinatorics.QBinomial
open E213.Tactic.NatHelper

/-- qpow additivity: `qpow q (a + b) = qpow q a * qpow q b`. -/
theorem qpow_add (q : Int) (a : Nat) : ∀ b, qpow q (a + b) = qpow q a * qpow q b
  | 0 => by
    show qpow q a = qpow q a * 1
    generalize qpow q a = x; ring_intZ
  | k + 1 => by
    have ih : qpow q (a + k) = qpow q a * qpow q k := qpow_add q a k
    show qpow q (a + k) * q = qpow q a * (qpow q k * q)
    rw [ih]; generalize qpow q a = x; generalize qpow q k = y; ring_intZ

/-- Above-diagonal vanishing: `qbinom q n k = 0` when `n < k`. -/
theorem qbinom_above : ∀ (n k : Nat), n < k → qbinom q n k = 0
  | n, 0, h => absurd h (Nat.not_lt_zero n)
  | 0, k+1, _ => qbinom_zero_succ q k
  | n+1, k+1, h => by
    have hlt : n < k := Nat.lt_of_succ_lt_succ h
    rw [qbinom_pascal, qbinom_above n (k+1) (Nat.lt_succ_of_lt hlt),
        qbinom_above n k hlt, Int.mul_zero, Int.add_zero]

/-- Column `k = 1` value (q-integer): `(q - 1) · [m,1]_q = q^m - 1`. -/
theorem qbinom_col1 (q : Int) : ∀ m, (q - 1) * qbinom q m 1 = qpow q m - 1
  | 0 => by
    show (q - 1) * qbinom q 0 1 = qpow q 0 - 1
    rw [qbinom_zero_succ]
    show (q - 1) * 0 = (1 : Int) - 1
    rw [Int.mul_zero]; decide
  | m + 1 => by
    have ih : (q - 1) * qbinom q m 1 = qpow q m - 1 := qbinom_col1 q m
    -- [m+1,1] = q^1 * [m,1] + [m,0] = q * [m,1] + 1  (form A, k=0)
    have hA : qbinom q (m+1) 1 = qpow q 1 * qbinom q m 1 + qbinom q m 0 :=
      qbinom_pascal q m 0
    rw [hA, qbinom_zero_right]
    show (q - 1) * (qpow q 1 * qbinom q m 1 + 1) = qpow q (m+1) - 1
    have hq1 : qpow q 1 = q := by show qpow q 0 * q = q; rw [show qpow q 0 = (1:Int) from rfl]; ring_intZ
    have hqs : qpow q (m+1) = qpow q m * q := rfl
    rw [hq1, hqs]
    -- goal: (q-1)*(q * [m,1] + 1) = qpow q m * q - 1
    -- = q*(q-1)*[m,1] + (q-1) = q*(qpow q m - 1) + (q-1) = qpow q m * q - 1
    have key : (q - 1) * (q * qbinom q m 1 + 1)
             = q * ((q - 1) * qbinom q m 1) + (q - 1) := by
      generalize qbinom q m 1 = b; ring_intZ
    rw [key, ih]
    generalize qpow q m = p; ring_intZ

/-- Power-combine: `m ≤ n → qpow q (m+1) * qpow q (n-m) = qpow q (n+1)`. -/
theorem qpow_combine1 (q : Int) {n m : Nat} (h : m ≤ n) :
    qpow q (m + 1) * qpow q (n - m) = qpow q (n + 1) := by
  rw [← qpow_add]
  have he : (m + 1) + (n - m) = n + 1 := by
    rw [Nat.add_comm m 1, Nat.add_assoc, add_sub_of_le h, Nat.add_comm 1 n]
  rw [he]

/-- Power-combine: `m+1 ≤ n → qpow q (m+2) * qpow q (n-m-1) = qpow q (n+1)`. -/
theorem qpow_combine2 (q : Int) {n m : Nat} (h : m + 1 ≤ n) :
    qpow q (m + 2) * qpow q (n - m - 1) = qpow q (n + 1) := by
  rw [← qpow_add]
  have hmn : m ≤ n := Nat.le_of_succ_le h
  -- t := n - m; m + t = n, and 1 ≤ t.
  have hmt : m + (n - m) = n := add_sub_of_le hmn
  have h1t : 1 ≤ n - m := by
    have : m + 1 ≤ m + (n - m) := by rw [hmt]; exact h
    exact le_of_add_le_add_left this
  have htne : (n - m) ≠ 0 := fun hz => absurd (hz ▸ h1t) (by decide)
  -- (m+2) + (n-m-1) = n+1
  have he : (m + 2) + (n - m - 1) = n + 1 := by
    -- 1 + (n-m-1) = n-m  via sub_one_add_one
    have hs : (n - m - 1) + 1 = n - m := sub_one_add_one htne
    -- (m+2)+(n-m-1) = m + (2 + (n-m-1)) = m + ((n-m-1)+1 + 1) = m + ((n-m)+1)
    have step : (m + 2) + (n - m - 1) = m + ((n - m - 1 + 1) + 1) := by
      generalize (n - m - 1) = x
      rw [Nat.add_assoc m 2 x, Nat.add_comm 2 x, ← Nat.add_assoc x 1 1]
    rw [step, hs, ← Nat.add_assoc, hmt]
  rw [he]

/-- Abstract algebraic core of the relation induction step.
    With `(Pnm-1)·a = (P1-1)·b`, `(Pnm1-1)·b = (P2-1)·c`,
    `P1·Pnm = Pn1`, `P2·Pnm1 = Pn1`, we get
    `(Pnm-1)·(P1·b + a) = (P2-1)·(P2·c + b)` (both equal `(Pn1-1)·b`). -/
theorem rel_step (P1 Pnm Pn1 P2 Pnm1 a b c : Int)
    (hR0 : (Pnm - 1) * a = (P1 - 1) * b)
    (hR1 : (Pnm1 - 1) * b = (P2 - 1) * c)
    (hc1 : P1 * Pnm = Pn1)
    (hc2 : P2 * Pnm1 = Pn1) :
    (Pnm - 1) * (P1 * b + a) = (P2 - 1) * (P2 * c + b) := by
  have hL : (Pnm - 1) * (P1 * b + a) = (Pn1 - 1) * b := by
    have e1 : (Pnm - 1) * (P1 * b + a)
            = P1 * ((Pnm - 1) * b) + (Pnm - 1) * a := by ring_intZ
    rw [e1, hR0]
    have e2 : P1 * ((Pnm - 1) * b) + (P1 - 1) * b = (P1 * Pnm - 1) * b := by ring_intZ
    rw [e2, hc1]
  have hR : (P2 - 1) * (P2 * c + b) = (Pn1 - 1) * b := by
    have e3 : (P2 - 1) * (P2 * c + b)
            = P2 * ((P2 - 1) * c) + (P2 - 1) * b := by ring_intZ
    rw [e3, ← hR1]
    have e4 : P2 * ((Pnm1 - 1) * b) + (P2 - 1) * b = (P2 * Pnm1 - 1) * b := by ring_intZ
    rw [e4, hc2]
  rw [hL, hR]

/-- **Adjacent-column relation** `R(n,k)`:
    `(q^(n-k) - 1) · [n,k]_q = (q^(k+1) - 1) · [n,k+1]_q` for `k ≤ n`.
    The algebraic heart linking form A and the dual recurrence. -/
theorem qbinom_rel (q : Int) : ∀ (n k : Nat), k ≤ n →
    (qpow q (n - k) - 1) * qbinom q n k = (qpow q (k + 1) - 1) * qbinom q n (k + 1)
  | 0, 0, _ => by
    show (qpow q 0 - 1) * qbinom q 0 0 = (qpow q 1 - 1) * qbinom q 0 1
    rw [qbinom_zero_right, qbinom_zero_succ, Int.mul_zero,
        show qpow q 0 = (1:Int) from rfl]
    show ((1:Int) - 1) * 1 = 0
    decide
  | 0, _ + 1, h => absurd h (Nat.not_succ_le_zero _)
  | n + 1, 0, _ => by
    show (qpow q (n + 1 - 0) - 1) * qbinom q (n+1) 0
       = (qpow q 1 - 1) * qbinom q (n+1) 1
    rw [Nat.sub_zero, qbinom_zero_right,
        show qpow q 1 = q from
          (by show qpow q 0 * q = q; rw [show qpow q 0 = (1:Int) from rfl]; ring_intZ)]
    -- goal: (qpow q (n+1) - 1) * 1 = (q - 1) * qbinom q (n+1) 1
    rw [show (qpow q (n+1) - 1) * 1 = qpow q (n+1) - 1 from by
          generalize qpow q (n+1) = P; ring_intZ]
    exact (qbinom_col1 q (n + 1)).symm
  | n + 1, m + 1, h => by
    have hmn : m ≤ n := Nat.le_of_succ_le_succ h
    -- normalise (n+1)-(m+1) = n-m
    have hsub : (n + 1) - (m + 1) = n - m := Nat.succ_sub_succ_eq_sub n m
    -- form A expansions
    have hA1 : qbinom q (n+1) (m+1) = qpow q (m+1) * qbinom q n (m+1) + qbinom q n m :=
      qbinom_pascal q n m
    have hA2 : qbinom q (n+1) (m+2) = qpow q (m+2) * qbinom q n (m+2) + qbinom q n (m+1) :=
      qbinom_pascal q n (m+1)
    rw [hsub, hA1, hA2]
    -- now goal: (q^(n-m)-1)*(q^(m+1)*[n,m+1]+[n,m])
    --         = (q^(m+2)-1)*(q^(m+2)*[n,m+2]+[n,m+1])
    rcases Nat.lt_or_ge m n with hlt | hge
    · -- m < n : both IHs available
      have hm1n : m + 1 ≤ n := hlt
      have hR0 : (qpow q (n - m) - 1) * qbinom q n m
               = (qpow q (m + 1) - 1) * qbinom q n (m + 1) :=
        qbinom_rel q n m hmn
      have hR1 : (qpow q (n - (m+1)) - 1) * qbinom q n (m + 1)
               = (qpow q (m + 2) - 1) * qbinom q n (m + 2) :=
        qbinom_rel q n (m + 1) hm1n
      -- n - (m+1) = n - m - 1 (definitional: Nat.sub recurses on 2nd arg)
      have hnm1 : n - (m + 1) = n - m - 1 := rfl
      rw [hnm1] at hR1
      have hc1 : qpow q (m + 1) * qpow q (n - m) = qpow q (n + 1) :=
        qpow_combine1 q hmn
      have hc2 : qpow q (m + 2) * qpow q (n - m - 1) = qpow q (n + 1) :=
        qpow_combine2 q hm1n
      exact rel_step (qpow q (m+1)) (qpow q (n-m)) (qpow q (n+1))
        (qpow q (m+2)) (qpow q (n-m-1)) (qbinom q n m) (qbinom q n (m+1))
        (qbinom q n (m+2)) hR0 hR1 hc1 hc2
    · -- m = n (since m ≤ n and m ≥ n)
      have hmeq : m = n := Nat.le_antisymm hmn hge
      subst hmeq
      -- m - m = 0; [m,m+2] = above diagonal = 0
      have hz : m - m = 0 := Nat.sub_self m
      rw [hz, show qpow q 0 = (1:Int) from rfl]
      have habove : qbinom q m (m + 2) = 0 :=
        qbinom_above m (m + 2) (Nat.lt_of_lt_of_le (Nat.lt_succ_self m)
          (Nat.le_succ (m + 1)))
      have habove2 : qbinom q m (m + 1) = 0 :=
        qbinom_above m (m + 1) (Nat.lt_succ_self m)
      rw [habove, habove2]
      -- goal: (1-1)*(qpow q (m+1)*0 + [m,m]) = (qpow q (m+2)-1)*(qpow q (m+2)*0 + 0)
      generalize qpow q (m+1) = P1
      generalize qpow q (m+1+1) = P2
      generalize qbinom q m m = X
      show ((1:Int) - 1) * (P1 * 0 + X) = (P2 - 1) * (P2 * 0 + 0)
      rw [show (1:Int) - 1 = 0 from rfl, E213.Meta.Int213.zero_mul,
          Int.mul_zero, Int.add_zero, Int.mul_zero]

/-- Diagonal value: `[n,n]_q = 1`. -/
theorem qbinom_diag (q : Int) : ∀ n, qbinom q n n = 1
  | 0 => rfl
  | n + 1 => by
    -- [n+1,n+1] = q^(n+1)*[n,n+1] + [n,n]; [n,n+1]=0, [n,n]=1
    rw [qbinom_pascal q n n, qbinom_above n (n+1) (Nat.lt_succ_self n),
        Int.mul_zero, E213.Meta.Int213.zero_add, qbinom_diag q n]

/-- ★★ **Dual q-Pascal (form B)**: for `k ≤ n`,
    `[n+1,k+1]_q = q^(n-k)·[n,k]_q + [n,k+1]_q`.
    (Partner of form A `[n+1,k+1]_q = q^(k+1)·[n,k+1]_q + [n,k]_q`;
    the power rides the *lower* index `[n,k]` here.) -/
theorem qbinom_pascal_dual (q : Int) (n k : Nat) (hk : k ≤ n) :
    qbinom q (n + 1) (k + 1) = qpow q (n - k) * qbinom q n k + qbinom q n (k + 1) := by
  -- form A:  [n+1,k+1] = q^(k+1)*[n,k+1] + [n,k]
  rw [qbinom_pascal q n k]
  -- goal: q^(k+1)*[n,k+1] + [n,k] = q^(n-k)*[n,k] + [n,k+1]
  -- equivalent to R(n,k): (q^(n-k)-1)*[n,k] = (q^(k+1)-1)*[n,k+1]
  have hR : (qpow q (n - k) - 1) * qbinom q n k
          = (qpow q (k + 1) - 1) * qbinom q n (k + 1) := qbinom_rel q n k hk
  -- rearrange: bring everything to a ring identity using hR
  generalize hA : qpow q (k + 1) = A at hR ⊢
  generalize hB : qpow q (n - k) = B at hR ⊢
  generalize qbinom q n k = x at hR ⊢
  generalize qbinom q n (k + 1) = y at hR ⊢
  -- goal: A*y + x = B*x + y ; hR: (B-1)*x = (A-1)*y
  -- rewrite hR into the additive form B*x - x = A*y - y
  have hR' : B * x - x = A * y - y := by
    have e : (B - 1) * x = B * x - x := by ring_intZ
    have f : (A - 1) * y = A * y - y := by ring_intZ
    rw [← e, ← f]; exact hR
  -- goal A*y + x = B*x + y.  Add the chain.
  have goal_eq : A * y + x = B * x + y := by
    have h2 : (B * x - x) + (x + y) = (A * y - y) + (x + y) := congrArg (· + (x + y)) hR'
    rw [show (B * x - x) + (x + y) = B * x + y from by ring_intZ,
        show (A * y - y) + (x + y) = A * y + x from by ring_intZ] at h2
    exact h2.symm
  exact goal_eq

/-- Abstract algebraic core of the symmetry induction step.
    Given form-A expansions `L = A·v + u` and `Rt = Bp·u + v` and the
    relation `(A - 1)·v = (Bp - 1)·u`, conclude `L = Rt`. -/
theorem symm_step (A Bp u v L Rt : Int)
    (hL : L = A * v + u) (hRt : Rt = Bp * u + v)
    (hrel : (A - 1) * v = (Bp - 1) * u) : L = Rt := by
  rw [hL, hRt]
  -- A*v + u = Bp*u + v  ⟺ (A-1)*v = (Bp-1)*u
  -- rewrite hrel additively: A*v - v = Bp*u - u
  have hrel' : A * v - v = Bp * u - u := by
    have e : (A - 1) * v = A * v - v := by ring_intZ
    have f : (Bp - 1) * u = Bp * u - u := by ring_intZ
    rw [← e, ← f]; exact hrel
  -- (A*v - v) + (u + v) = A*v + u ; (Bp*u - u) + (u + v) = Bp*u + v
  have h2 : (A * v - v) + (u + v) = (Bp * u - u) + (u + v) :=
    congrArg (· + (u + v)) hrel'
  rw [show (A * v - v) + (u + v) = A * v + u from by ring_intZ,
      show (Bp * u - u) + (u + v) = Bp * u + v from by ring_intZ] at h2
  exact h2

/-- ★★★ **General q-binomial symmetry**: `[n,k]_q = [n,n-k]_q` for `k ≤ n`. -/
theorem qbinom_symm (q : Int) : ∀ (n k : Nat), k ≤ n →
    qbinom q n k = qbinom q n (n - k)
  | 0, 0, _ => rfl
  | 0, _ + 1, h => absurd h (Nat.not_succ_le_zero _)
  | n + 1, 0, _ => by
    -- [n+1,0] = 1 = [n+1,n+1] = [n+1, (n+1)-0]
    rw [Nat.sub_zero, qbinom_zero_right, qbinom_diag q (n + 1)]
  | n + 1, k + 1, h => by
    have hjn : k ≤ n := Nat.le_of_succ_le_succ h
    rcases Nat.lt_or_ge k n with hlt | hge
    · -- interior: k < n, write j := k.  target index (n+1)-(k+1) = n-k.
      have hkn : k + 1 ≤ n := hlt
      -- n - k ≥ 1
      have h1nk : 1 ≤ n - k := by
        have : k + 1 ≤ k + (n - k) := by rw [add_sub_of_le hjn]; exact hkn
        exact le_of_add_le_add_left this
      have hnkne : (n - k) ≠ 0 := fun hz => absurd (hz ▸ h1nk) (by decide)
      -- target = [n+1, (n+1)-(k+1)] = [n+1, n-k]
      have htsub : (n + 1) - (k + 1) = n - k := Nat.succ_sub_succ_eq_sub n k
      rw [htsub]
      -- form A on LHS [n+1,k+1]
      have hL : qbinom q (n+1) (k+1)
              = qpow q (k+1) * qbinom q n (k+1) + qbinom q n k := qbinom_pascal q n k
      -- write n-k = (n-k-1)+1 to apply form A on [n+1,n-k]
      have hnk_eq : n - k = (n - k - 1) + 1 := (sub_one_add_one hnkne).symm
      have hRt0 : qbinom q (n+1) (n - k)
                = qpow q ((n - k - 1) + 1) * qbinom q n ((n - k - 1) + 1)
                  + qbinom q n (n - k - 1) := by
        rw [hnk_eq]; exact qbinom_pascal q n (n - k - 1)
      -- (n-k-1)+1 = n-k ; n - (k+1) = n-k-1 (defeq)
      have hback : (n - k - 1) + 1 = n - k := sub_one_add_one hnkne
      rw [hback] at hRt0
      -- IH: [n,k] = [n,n-k];  [n,k+1] = [n, n-(k+1)] = [n, n-k-1]
      have hIH0 : qbinom q n k = qbinom q n (n - k) := qbinom_symm q n k hjn
      have hIH1 : qbinom q n (k + 1) = qbinom q n (n - (k + 1)) :=
        qbinom_symm q n (k + 1) hkn
      have hnk1 : n - (k + 1) = n - k - 1 := rfl
      rw [hnk1] at hIH1
      -- relation R(n, n-k-1):
      --   (q^(n-(n-k-1)) - 1)*[n,n-k-1] = (q^((n-k-1)+1) - 1)*[n, (n-k-1)+1]
      have hnkk : n - k - 1 ≤ n := Nat.le_trans (Nat.sub_le (n - k) 1) (Nat.sub_le n k)
      have hrelR : (qpow q (n - (n - k - 1)) - 1) * qbinom q n (n - k - 1)
                 = (qpow q ((n - k - 1) + 1) - 1) * qbinom q n ((n - k - 1) + 1) :=
        qbinom_rel q n (n - k - 1) hnkk
      -- simplify powers: n - (n-k-1) = k+1 ;  (n-k-1)+1 = n-k
      have hexp1 : n - (n - k - 1) = k + 1 := by
        -- n-k-1 = n-(k+1) (defeq); use sub_sub_self with k+1 ≤ n
        exact sub_sub_self hkn
      rw [hexp1, hback] at hrelR
      -- now hrelR : (q^(k+1)-1)*[n,n-k-1] = (q^(n-k)-1)*[n,n-k]
      -- Apply symm_step with A=q^(k+1), Bp=q^(n-k), u=[n,n-k], v=[n,n-k-1]
      -- L = [n+1,k+1] = q^(k+1)*[n,k+1] + [n,k] = q^(k+1)*[n,n-k-1] + [n,n-k]  (IH)
      have hL' : qbinom q (n+1) (k+1)
               = qpow q (k+1) * qbinom q n (n - k - 1) + qbinom q n (n - k) := by
        rw [hL, hIH1, hIH0]
      -- Rt = [n+1,n-k] = q^(n-k)*[n,n-k] + [n,n-k-1]
      exact symm_step (qpow q (k+1)) (qpow q (n - k))
        (qbinom q n (n - k)) (qbinom q n (n - k - 1))
        (qbinom q (n+1) (k+1)) (qbinom q (n+1) (n - k))
        hL' hRt0 hrelR
    · -- k = n : top of row.  [n+1,n+1] = [n+1, (n+1)-(n+1)] = [n+1,0]
      have hkeq : k = n := Nat.le_antisymm hjn hge
      subst hkeq
      -- now row index is (k+1), goal [k+1, k+1] = [k+1, (k+1)-(k+1)]
      have htsub : (k + 1) - (k + 1) = 0 := Nat.sub_self (k + 1)
      rw [htsub, qbinom_zero_right, qbinom_diag q (k + 1)]

/-- Sanity: the general theorem reproduces the corpus symmetry table. -/
theorem qbinom_symm_check :
    qbinom 2 4 1 = qbinom 2 4 3 ∧ qbinom 3 4 1 = qbinom 3 4 3 := by
  refine ⟨?_, ?_⟩
  · have := qbinom_symm 2 4 1 (by decide); rw [this]
  · have := qbinom_symm 3 4 1 (by decide); rw [this]

end E213.Lib.Math.Combinatorics.QBinomialSymmetry
