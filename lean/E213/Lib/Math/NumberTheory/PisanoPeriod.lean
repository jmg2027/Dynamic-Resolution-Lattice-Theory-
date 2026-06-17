import E213.Lib.Math.Combinatorics.Pigeonhole
import E213.Meta.Nat.EncodePair213
import E213.Meta.Nat.AddMod213

/-!
# Pisano period — Fibonacci mod m is periodic (∅-axiom)

The state at step `n` is the consecutive pair `(fib n % m, fib (n+1) % m)`,
living in a set of size `m²`.  `exists_collision_lt` on `Fin (m²+1) → Fin (m²)`
RETURNS two distinct indices with the same state; their gap is the (computed)
Pisano period, propagated forward by the recurrence mod m.
-/

namespace E213.Lib.Math.NumberTheory.PisanoPeriod

open E213.Lib.Math.Combinatorics.Pigeonhole (exists_collision_lt)
open E213.Meta.Nat.EncodePair213 (encode_div encode_mod)
open E213.Meta.Nat.AddMod213 (add_mod_gen)
open E213.Tactic.NatHelper (add_sub_of_le sub_pos_of_lt)

/-- Standard Fibonacci (corpus convention; reuses the recurrence). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem fib_rec (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

/-! ## Forward propagation of an equal consecutive-pair state -/

/-- If states agree at `n` and `n+1` (i.e. `fib` agrees mod m at `n, n+1, n+1, n+2`
    is the same as agreeing at `n` and `n+1`), the next residue agrees too.
    This is the heart: the next term is determined by the current pair mod m. -/
theorem step_propagate {m : Nat} (a b : Nat)
    (h0 : fib a % m = fib b % m)
    (h1 : fib (a + 1) % m = fib (b + 1) % m) :
    fib (a + 2) % m = fib (b + 2) % m := by
  rw [fib_rec a, fib_rec b]
  rw [add_mod_gen (fib a) (fib (a + 1)) m]
  rw [add_mod_gen (fib b) (fib (b + 1)) m]
  rw [h0, h1]

/-! ## State encoding and the pigeonhole collision -/

/-- Pack the consecutive-pair state at step `n` into `Fin (m*m)`.
    `state n = (fib n % m) * m + (fib (n+1) % m)`, which is `< m*m`. -/
def stateVal (m n : Nat) : Nat := (fib n % m) * m + (fib (n + 1) % m)

/-- `stateVal m n < m * m` when `0 < m`. -/
theorem stateVal_lt {m : Nat} (hm : 0 < m) (n : Nat) : stateVal m n < m * m := by
  show (fib n % m) * m + (fib (n + 1) % m) < m * m
  have hb : fib (n + 1) % m < m := Nat.mod_lt _ hm
  have ha : fib n % m < m := Nat.mod_lt _ hm
  -- (a)*m + b < (a+1)*m ≤ m*m  since a < m ⟹ a+1 ≤ m.
  have hstep : (fib n % m) * m + (fib (n + 1) % m) < (fib n % m) * m + m :=
    Nat.add_lt_add_left hb _
  have hle : (fib n % m) * m + m ≤ m * m := by
    have : (fib n % m + 1) * m ≤ m * m :=
      Nat.mul_le_mul_right m (Nat.succ_le_of_lt ha)
    have e : (fib n % m + 1) * m = (fib n % m) * m + m := by
      rw [Nat.succ_mul]
    rw [e] at this; exact this
  exact Nat.lt_of_lt_of_le hstep hle

/-- The collision: two distinct indices `i, j < m*m+1` with the same encoded state,
    hence equal residues at both `i, i+1` and `j, j+1`. -/
theorem state_collision {m : Nat} (hm : 0 < m) :
    ∃ i j : Nat, i ≠ j ∧
      fib i % m = fib j % m ∧ fib (i + 1) % m = fib (j + 1) % m := by
  let g : Fin (m * m + 1) → Fin (m * m) :=
    fun k => ⟨stateVal m k.val, stateVal_lt hm k.val⟩
  have hlt : m * m < m * m + 1 := Nat.lt_succ_self _
  obtain ⟨i, j, hij, hg⟩ := exists_collision_lt hlt g
  -- equal encoded state values
  have hval : stateVal m i.val = stateVal m j.val := congrArg Fin.val hg
  -- decode via encode_div / encode_mod
  have hbi : fib (i.val + 1) % m < m := Nat.mod_lt _ hm
  have hbj : fib (j.val + 1) % m < m := Nat.mod_lt _ hm
  have hdiv : fib i.val % m = fib j.val % m := by
    have li : stateVal m i.val / m = fib i.val % m :=
      encode_div hm (fib i.val % m) (fib (i.val + 1) % m) hbi
    have lj : stateVal m j.val / m = fib j.val % m :=
      encode_div hm (fib j.val % m) (fib (j.val + 1) % m) hbj
    rw [← li, ← lj, hval]
  have hmod : fib (i.val + 1) % m = fib (j.val + 1) % m := by
    have li : stateVal m i.val % m = fib (i.val + 1) % m :=
      encode_mod hm (fib i.val % m) (fib (i.val + 1) % m) hbi
    have lj : stateVal m j.val % m = fib (j.val + 1) % m :=
      encode_mod hm (fib j.val % m) (fib (j.val + 1) % m) hbj
    rw [← li, ← lj, hval]
  refine ⟨i.val, j.val, ?_, hdiv, hmod⟩
  intro h
  exact hij (Fin.ext h)

/-! ## Forward extension from the anchor pair to all later indices -/

/-- If the period-`p` shift preserves the residue at both `a` and `a+1`, it
    preserves it at every `a + t`.  Two-step induction carrying the pair. -/
theorem extend_forward {m p : Nat}
    (h0 : ∀ a, fib (a + p) % m = fib a % m → fib (a + 1 + p) % m = fib (a + 1) % m →
            fib (a + 2 + p) % m = fib (a + 2) % m) :
    ∀ (a : Nat), fib (a + p) % m = fib a % m → fib (a + 1 + p) % m = fib (a + 1) % m →
      ∀ t, fib (a + t + p) % m = fib (a + t) % m := by
  intro a ha ha1 t
  refine Nat.strongRecOn t
    (motive := fun t => fib (a + t + p) % m = fib (a + t) % m) ?_
  intro t ih
  match t with
    | 0 =>
        have e : a + 0 = a := Nat.add_zero a
        rw [e]; exact ha
    | 1 => exact ha1
    | k + 2 =>
        have hk : fib (a + k + p) % m = fib (a + k) % m :=
          ih k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k)
            (Nat.le_succ_of_le (Nat.le_refl _)))
        have hk1 : fib (a + (k + 1) + p) % m = fib (a + (k + 1)) % m :=
          ih (k + 1) (Nat.lt_succ_self (k + 1))
        -- rewrite (a + (k+1)) as (a+k)+1 so h0 applies at a+k
        have hk1' : fib (a + k + 1 + p) % m = fib (a + k + 1) % m := by
          have e1 : a + (k + 1) = a + k + 1 := by rw [Nat.add_assoc]
          rw [e1] at hk1; exact hk1
        have hstep := h0 (a + k) hk hk1'
        -- hstep : fib (a+k+2+p) % m = fib (a+k+2) % m ; rewrite to a+(k+2)
        have e2 : a + k + 2 = a + (k + 2) := by
          rw [Nat.add_assoc]
        rw [e2] at hstep
        exact hstep

/-- `step_propagate` packaged as the `h0` hypothesis of `extend_forward`
    (with the period `p` as the shift, applied on both sides). -/
theorem step_shift {m p : Nat} (a : Nat)
    (h0 : fib (a + p) % m = fib a % m)
    (h1 : fib (a + 1 + p) % m = fib (a + 1) % m) :
    fib (a + 2 + p) % m = fib (a + 2) % m := by
  have h1' : fib (a + p + 1) % m = fib (a + 1) % m := by
    have e : a + p + 1 = a + 1 + p := by rw [Nat.add_right_comm]
    rw [e]; exact h1
  have key := step_propagate (m := m) (a + p) a h0 h1'
  -- key : fib (a+p+2) % m = fib (a+2) % m ; rewrite a+p+2 = a+2+p
  have e : a + p + 2 = a + 2 + p := by
    rw [Nat.add_right_comm]
  rw [e] at key
  exact key

/-! ## Modular additive cancellation (for backward propagation) -/

open E213.Tactic.NatHelper (sub_add_cancel)

/-- Right-cancellation in `ℤ/m`: `(x + c) % m = (y + c) % m → x % m = y % m`.
    ∅-axiom.  Add the additive inverse `m - c % m`; `c%m + (m - c%m) = m`,
    and `(z + m) % m = z % m`. -/
theorem mod_add_right_cancel {m : Nat} (hm : 0 < m) {x y c : Nat}
    (h : (x + c) % m = (y + c) % m) : x % m = y % m := by
  -- Reduce c to C = c % m on both sides.
  have hxC : (x + c) % m = (x % m + c % m) % m := add_mod_gen x c m
  have hyC : (y + c) % m = (y % m + c % m) % m := add_mod_gen y c m
  have hXY : (x % m + c % m) % m = (y % m + c % m) % m := by
    rw [← hxC, ← hyC]; exact h
  -- Let C = c % m, d = m - C.  C + d = m.
  have hClt : c % m < m := Nat.mod_lt _ hm
  have hd : c % m + (m - c % m) = m := add_sub_of_le (Nat.le_of_lt hClt)
  -- Add d on the right of both sides (under %m), giving (x%m + m)%m = (y%m + m)%m.
  have step : ((x % m + c % m) % m + (m - c % m)) % m
            = ((y % m + c % m) % m + (m - c % m)) % m :=
    congrArg (fun z => (z + (m - c % m)) % m) hXY
  -- collapse the inner %m: ((A)%m + d)%m = (A + d)%m  via add_mod_left
  have collapseX : ((x % m + c % m) % m + (m - c % m)) % m
                 = (x % m + c % m + (m - c % m)) % m :=
    (E213.Meta.Nat.AddMod213.add_mod_left hm (x % m + c % m) (m - c % m)).symm
  have collapseY : ((y % m + c % m) % m + (m - c % m)) % m
                 = (y % m + c % m + (m - c % m)) % m :=
    (E213.Meta.Nat.AddMod213.add_mod_left hm (y % m + c % m) (m - c % m)).symm
  rw [collapseX, collapseY] at step
  -- x%m + c%m + (m - c%m) = x%m + m
  have eX : x % m + c % m + (m - c % m) = x % m + m := by
    rw [Nat.add_assoc, hd]
  have eY : y % m + c % m + (m - c % m) = y % m + m := by
    rw [Nat.add_assoc, hd]
  rw [eX, eY] at step
  -- (x%m + m) % m = x%m : drop the +m via add_mod_left_pure (commuted)
  have fX : (x % m + m) % m = x % m := by
    rw [Nat.add_comm (x % m) m, E213.Meta.Nat.AddMod213.add_mod_left_pure m (x % m),
        E213.Meta.Nat.AddMod213.mod_mod]
  have fY : (y % m + m) % m = y % m := by
    rw [Nat.add_comm (y % m) m, E213.Meta.Nat.AddMod213.add_mod_left_pure m (y % m),
        E213.Meta.Nat.AddMod213.mod_mod]
  rw [fX, fY] at step
  exact step

/-! ## Backward propagation (one step down) -/

/-- The period-`p` shift, if it preserves the residue at `n+1` and `n+2`,
    preserves it at `n`.  Uses `fib (n+2) = fib n + fib (n+1)` and cancels the
    common `fib (n+1+p)` term in `ℤ/m`. -/
theorem step_back {m p : Nat} (hm : 0 < m) (n : Nat)
    (h1 : fib (n + 1 + p) % m = fib (n + 1) % m)
    (h2 : fib (n + 2 + p) % m = fib (n + 2) % m) :
    fib (n + p) % m = fib n % m := by
  -- expand both fib(n+2) via the recurrence
  have eL : fib (n + 2) % m = (fib n + fib (n + 1)) % m := by rw [fib_rec n]
  have eR : fib (n + 2 + p) % m = (fib (n + p) + fib (n + 1 + p)) % m := by
    have er : n + 2 + p = (n + p) + 2 := by rw [Nat.add_right_comm]
    rw [er, fib_rec (n + p)]
    have e1 : (n + p) + 1 = n + 1 + p := by rw [Nat.add_right_comm]
    rw [e1]
  -- combine with h2
  have hcomb : (fib (n + p) + fib (n + 1 + p)) % m = (fib n + fib (n + 1)) % m := by
    rw [← eR, ← eL]; exact h2
  -- replace fib(n+1) by fib(n+1+p) on the RHS using h1 (mod equality)
  have hRHS : (fib n + fib (n + 1)) % m = (fib n + fib (n + 1 + p)) % m := by
    rw [add_mod_gen (fib n) (fib (n + 1)) m,
        add_mod_gen (fib n) (fib (n + 1 + p)) m, h1]
  have hfinal : (fib (n + p) + fib (n + 1 + p)) % m
              = (fib n + fib (n + 1 + p)) % m := by
    rw [hcomb, hRHS]
  -- cancel the common +fib(n+1+p)
  exact mod_add_right_cancel hm hfinal

/-- Downward extension: if the period-`p` relation `Q` holds at `N` and `N+1`,
    it holds at every `n` with `n ≤ N` — proved by induction on the gap `g`
    with the equation `n + g = N` carried explicitly (no saturating subtraction).
    `Q n` abbreviates `fib (n + p) % m = fib n % m`. -/
theorem extend_back {m p : Nat} (hm : 0 < m) (N : Nat)
    (hN : fib (N + p) % m = fib N % m)
    (hN1 : fib (N + 1 + p) % m = fib (N + 1) % m) :
    ∀ (g n : Nat), n + g = N → fib (n + p) % m = fib n % m := by
  intro g
  induction g using Nat.strongRecOn with
  | _ g ih =>
    intro n hgn
    match g with
    | 0 =>
        -- n = N
        have hn : n = N := by rw [← hgn, Nat.add_zero]
        rw [hn]; exact hN
    | 1 =>
        -- n + 1 = N, so Q n from step_back needing Q(n+1)=Q N and Q(n+2)=Q(N+1)
        have hn1 : n + 1 = N := hgn
        have q1 : fib (n + 1 + p) % m = fib (n + 1) % m := by rw [hn1]; exact hN
        have q2 : fib (n + 2 + p) % m = fib (n + 2) % m := by
          have e : n + 2 = N + 1 := by rw [← hn1, Nat.add_assoc]
          rw [e]; exact hN1
        exact step_back hm n q1 q2
    | k + 2 =>
        -- n + (k+2) = N.  Q(n+1) from gap k+1, Q(n+2) from gap k.
        have q1 : fib (n + 1 + p) % m = fib (n + 1) % m :=
          ih (k + 1) (Nat.lt_succ_self (k + 1)) (n + 1)
            (by rw [Nat.add_right_comm, ← Nat.add_assoc]; exact hgn)
        have q2 : fib (n + 2 + p) % m = fib (n + 2) % m :=
          ih k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k)
                  (Nat.le_succ_of_le (Nat.le_refl _))) (n + 2)
            (by rw [Nat.add_right_comm n 2 k]; exact hgn)
        exact step_back hm n q1 q2

/-! ## Anchor extraction from the collision -/

/-- The pigeonhole collision, normalized: a positive period `p` and an anchor
    `a` at which the period-`p` shift preserves the residue at both `a` and
    `a+1`.  (The smaller of the two colliding indices is the anchor; their gap
    is `p`.) -/
theorem anchor_of_collision {m : Nat} (hm : 0 < m) :
    ∃ p, 0 < p ∧ ∃ a,
      fib (a + p) % m = fib a % m ∧ fib (a + 1 + p) % m = fib (a + 1) % m := by
  obtain ⟨i, j, hij, hdi, hmi⟩ := state_collision hm
  rcases Nat.lt_or_ge i j with hlt | hge
  · refine ⟨j - i, sub_pos_of_lt hlt, i, ?_, ?_⟩
    · have hp : i + (j - i) = j := by rw [add_sub_of_le (Nat.le_of_lt hlt)]
      rw [hp]; exact hdi.symm
    · have e : i + 1 + (j - i) = j + 1 := by
        rw [Nat.add_right_comm, add_sub_of_le (Nat.le_of_lt hlt)]
      rw [e]; exact hmi.symm
  · have hlt : j < i := Nat.lt_of_le_of_ne hge (fun e => hij e.symm)
    refine ⟨i - j, sub_pos_of_lt hlt, j, ?_, ?_⟩
    · have hp : j + (i - j) = i := by rw [add_sub_of_le (Nat.le_of_lt hlt)]
      rw [hp]; exact hdi
    · have e : j + 1 + (i - j) = i + 1 := by
        rw [Nat.add_right_comm, add_sub_of_le (Nat.le_of_lt hlt)]
      rw [e]; exact hmi

/-! ## Eventually-periodic form (∀ n ≥ anchor) -/

/-- **Fibonacci mod m is eventually periodic** with a *computed* period.
    There is a positive period `p` and an anchor `N` such that for all `n ≥ N`,
    `fib (n+p) % m = fib n % m`.  `p` and `N` come from the pigeonhole collision
    on consecutive-pair states. -/
theorem fib_eventually_periodic {m : Nat} (hm : 0 < m) :
    ∃ p, 0 < p ∧ ∃ N, ∀ n, N ≤ n → fib (n + p) % m = fib n % m := by
  obtain ⟨p, hp, a, ha, ha1⟩ := anchor_of_collision hm
  refine ⟨p, hp, a, ?_⟩
  intro n hn
  have ht : a + (n - a) = n := add_sub_of_le hn
  have hgen := extend_forward (m := m) (p := p)
    (fun b h h1 => step_shift b h h1) a ha ha1 (n - a)
  rw [ht] at hgen
  exact hgen

/-! ## Pure periodicity from 0 (∀ n) — backward + forward propagation -/

/-- **Pisano period.**  Fibonacci mod `m` is *purely* periodic: there is a
    positive period `p` with `fib (n + p) % m = fib n % m` for **every** `n`.
    The period is the gap of the pigeonhole collision on consecutive-pair
    states; forward propagation covers `n ≥ anchor`, backward propagation
    (the recurrence inverted, `fib n = fib (n+2) − fib (n+1)` in `ℤ/m`) covers
    `n ≤ anchor`. -/
theorem pisano_period {m : Nat} (hm : 0 < m) :
    ∃ p, 0 < p ∧ ∀ n, fib (n + p) % m = fib n % m := by
  obtain ⟨p, hp, a, ha, ha1⟩ := anchor_of_collision hm
  refine ⟨p, hp, ?_⟩
  intro n
  rcases Nat.lt_or_ge n a with hlt | hge
  · -- n < a: use downward extension from the anchor pair (a, a+1)
    exact extend_back hm a ha ha1 (a - n) n (add_sub_of_le (Nat.le_of_lt hlt))
  · -- n ≥ a: forward extension
    have ht : a + (n - a) = n := add_sub_of_le hge
    have hgen := extend_forward (m := m) (p := p)
      (fun b h h1 => step_shift b h h1) a ha ha1 (n - a)
    rw [ht] at hgen
    exact hgen

/-! ## Smoke tests — the classical Pisano periods (closed numerals) -/

-- π(2) = 3 : fib mod 2 has period 3 and not 1 or 2.
example : ∀ k, k < 3 → fib (k + 3) % 2 = fib k % 2 := by decide
example : fib (0 + 1) % 2 ≠ fib 0 % 2 := by decide        -- not period 1
example : fib (0 + 2) % 2 ≠ fib 0 % 2 := by decide        -- not period 2

-- π(3) = 8.
example : ∀ k, k < 8 → fib (k + 8) % 3 = fib k % 3 := by decide
example : fib (1 + 4) % 3 ≠ fib 1 % 3 := by decide          -- 8 is not 4 (a divisor probe)

-- π(10) = 60.
example : ∀ k, k < 60 → fib (k + 60) % 10 = fib k % 10 := by decide

#print axioms pisano_period
#print axioms fib_eventually_periodic

end E213.Lib.Math.NumberTheory.PisanoPeriod
