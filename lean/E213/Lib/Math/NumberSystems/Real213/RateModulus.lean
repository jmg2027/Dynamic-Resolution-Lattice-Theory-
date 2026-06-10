import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.PowBasic
import E213.Meta.Nat.RootFloor

/-!
# RateModulus — the "rate-carrying ⟹ total modulus" generator, graded by probe schedule

A monotone convergent cut-sequence `a_i/d_i` whose margin `e_i + 1/(ρ_i·d_i)` is
non-increasing — `ρ : Nat → Nat` a **probe schedule** — completes with a
*constructed* total modulus: the cut is constant past any layer `i₀` at which the
schedule admits the probe denominator (`k ≤ ρ i₀`), uniformly in `(m,k)`, with no
recurrence, no LEM, no irrationality measure.  The whole argument turns on one
fact — the scheduled margin is non-increasing (`HtelS`) — and is then pure
transitivity; nothing is specific to any individual real or any individual
schedule.

`HtelS a d ρ` is the **graded rate certificate** — the cross-multiplied form of
"the margin sequence `e_i + 1/(ρ_i·d_i)` decreases".  An instance supplies
`(a, d, ρ)` plus:

  * `hd`     — positive denominators;
  * `hρ`     — positive schedule (from layer 1);
  * `htel`   — the scheduled margin is non-increasing (the convergence rate);
  * `hmono`  — convergents increasing (gives `false`-forward nesting);
  * `hmonoS` — convergents *strictly* increasing (handles the `m/k = e_{i₀}` edge);
  * a base layer `i₀ ≥ 1` with `k ≤ ρ i₀` — the layer admitting the probe

and gets `rateS_cut_const`: the cut constant past `i₀ + 1`.  Two schedules are
the named rungs of the modulus-degree ladder:

  * ★ `rate_total_modulus` — the identity schedule: `Htel a d` (definitionally
    `HtelS a d (·)`) yields `N(m,k) = k+2`.  The degree-1 generator behind
    `eHolonomicReal`.
  * ★★★ `graded_total_modulus` — the degree-`s` root schedule `ρ = rootFloor s`:
    `N(m,k) = k^s + 1`.  The slack the presentation must defend per layer drops
    from `1/(i·d_i)` to `1/(⌊i^{1/s}⌋·d_i)`; measured at the layer `i = r^s`
    where probe denominator `r` is admitted, the identity schedule defends
    `1/(r^s·d_i)` where the graded one defends `1/(r·d_i)` — an `r^{s-1}` factor
    of overtake forgiven, paid for by a degree-`s` modulus.  This makes "rescue"
    graded the way `CompletabilityGrade` grades "break"; the per-layer
    comparison form is `RateStratification.DominatesS`.

Narrative: `theory/math/analysis/holonomic_modulus.md`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.RateModulus

open E213.Tactic.NatHelper
  (add_mul mul_assoc le_of_mul_le_mul_right add_sub_of_le lt_of_lt_le mul_mul_mul_comm_213)
open E213.Meta.Nat.PowBasic (one_le_pow self_le_pow)
open E213.Meta.Nat.RootFloor (rootFloor rootFloor_pos rootFloor_pow)

/-- The convergent cut: `e_i ≤ m/k`, i.e. `a i · k ≤ d i · m`. -/
abbrev rcut (a d : Nat → Nat) (i m k : Nat) : Bool := decide (a i * k ≤ d i * m)

/-- The scheduled margin invariant `e_i + 1/(ρ_i·d_i) ≤ m/k`, cross-multiplied
    to `Nat`. -/
abbrev RInvS (a d ρ : Nat → Nat) (m k i : Nat) : Prop :=
  (a i * ρ i + 1) * k ≤ m * (ρ i * d i)

/-- The **graded rate certificate**: the scheduled margin `e_i + 1/(ρ_i·d_i)` is
    non-increasing.  Its cross-multiplied form, for `i ≥ 1`. -/
def HtelS (a d ρ : Nat → Nat) : Prop :=
  ∀ i, 1 ≤ i →
    (a (i+1) * ρ (i+1) + 1) * (ρ i * d i) ≤ (a i * ρ i + 1) * (ρ (i+1) * d (i+1))

/-- The identity-schedule rate certificate: the margin `e_i + 1/(i·d_i)` is
    non-increasing.  Definitionally `HtelS a d (·)`. -/
def Htel (a d : Nat → Nat) : Prop :=
  ∀ i, 1 ≤ i → (a (i+1)*(i+1)+1)*(i * d i) ≤ (a i * i + 1)*((i+1)*d (i+1))

variable {a d ρ : Nat → Nat}

/-- `Htel` is the identity-schedule instance of `HtelS` (definitional). -/
theorem htelS_of_htel (h : Htel a d) : HtelS a d (fun i => i) := h

private theorem swap_kr (P k i : Nat) : (P*k)*i = (P*i)*k := by
  rw [mul_assoc, Nat.mul_comm k i, ← mul_assoc]

private theorem L_base (x k r : Nat) (hkr : k ≤ r) : (x*r+1)*k ≤ (x*k+1)*r := by
  have l1 : (x*r+1)*k = x*r*k + k := by rw [add_mul, Nat.one_mul]
  have l2 : (x*k+1)*r = x*r*k + r := by
    rw [add_mul, Nat.one_mul]; congr 1
    rw [mul_assoc, Nat.mul_comm k r, ← mul_assoc]
  rw [l1, l2]; exact Nat.add_le_add_left hkr _

private theorem rinvS_step (hd : ∀ i, 1 ≤ d i) (hρ : ∀ i, 1 ≤ i → 1 ≤ ρ i)
    (htel : HtelS a d ρ) (m k i : Nat) (hi1 : 1 ≤ i)
    (ih : RInvS a d ρ m k i) : RInvS a d ρ m k (i+1) := by
  have hpos : 0 < ρ i * d i := Nat.mul_pos (hρ i hi1) (hd i)
  have hki : ((a (i+1)*ρ (i+1)+1)*k)*(ρ i*d i)
      ≤ (m*(ρ (i+1)*d (i+1)))*(ρ i*d i) :=
    calc ((a (i+1)*ρ (i+1)+1)*k)*(ρ i*d i)
        = ((a (i+1)*ρ (i+1)+1)*(ρ i*d i))*k := swap_kr _ k (ρ i*d i)
      _ ≤ ((a i*ρ i+1)*(ρ (i+1)*d (i+1)))*k := Nat.mul_le_mul_right k (htel i hi1)
      _ = ((a i*ρ i+1)*k)*(ρ (i+1)*d (i+1)) := swap_kr _ (ρ (i+1)*d (i+1)) k
      _ ≤ (m*(ρ i*d i))*(ρ (i+1)*d (i+1)) := Nat.mul_le_mul_right _ ih
      _ = (m*(ρ (i+1)*d (i+1)))*(ρ i*d i) := by
            rw [mul_assoc m (ρ i*d i) (ρ (i+1)*d (i+1)),
                Nat.mul_comm (ρ i*d i) (ρ (i+1)*d (i+1)), ← mul_assoc]
  exact le_of_mul_le_mul_right hpos hki

private theorem rinvS (hd : ∀ i, 1 ≤ d i) (hρ : ∀ i, 1 ≤ i → 1 ≤ ρ i)
    (htel : HtelS a d ρ) (m k i₀ : Nat) (hi₀ : 1 ≤ i₀) (hkρ : k ≤ ρ i₀)
    (hstrict : a i₀ * k + 1 ≤ d i₀ * m) :
    ∀ i, i₀ ≤ i → RInvS a d ρ m k i := by
  have aux : ∀ t, RInvS a d ρ m k (i₀+t) := by
    intro t
    induction t with
    | zero =>
      show (a i₀*ρ i₀+1)*k ≤ m*(ρ i₀*d i₀)
      have e2 : (a i₀*k+1)*(ρ i₀) ≤ (d i₀*m)*(ρ i₀) :=
        Nat.mul_le_mul_right (ρ i₀) hstrict
      have e3 : (d i₀*m)*(ρ i₀) = m*(ρ i₀*d i₀) := by
        rw [Nat.mul_comm (d i₀) m, mul_assoc, Nat.mul_comm (d i₀) (ρ i₀)]
      exact Nat.le_trans (L_base (a i₀) k (ρ i₀) hkρ) (e3 ▸ e2)
    | succ t ih =>
      have hi1 : 1 ≤ i₀+t := Nat.le_trans hi₀ (Nat.le_add_right i₀ t)
      exact rinvS_step hd hρ htel m k (i₀+t) hi1 ih
  intro i hi; rw [← add_sub_of_le hi]; exact aux (i - i₀)

private theorem rinvS_cut (m k i : Nat) (hk : 1 ≤ k)
    (hinv : RInvS a d ρ m k i) : rcut a d i m k = true := by
  apply decide_eq_true
  have h1 : (a i*ρ i)*k + k ≤ m*(ρ i*d i) := by
    have e : (a i*ρ i+1)*k = (a i*ρ i)*k + k := by rw [add_mul, Nat.one_mul]
    rw [← e]; exact hinv
  have h2 : (a i*ρ i)*k + 1 ≤ m*(ρ i*d i) := Nat.le_trans (Nat.add_le_add_left hk _) h1
  have el : (a i*ρ i)*k = ρ i*(a i*k) := by rw [Nat.mul_comm (a i) (ρ i), mul_assoc]
  have er : m*(ρ i*d i) = ρ i*(m*d i) := by
    rw [← mul_assoc, Nat.mul_comm m (ρ i), mul_assoc]
  rw [el, er] at h2
  have h4 : a i*k < m*d i := by
    rcases Nat.lt_or_ge (a i*k) (m*d i) with h | h
    · exact h
    · exact absurd (lt_of_lt_le h2 (Nat.mul_le_mul_left (ρ i) h)) (Nat.lt_irrefl _)
  rw [Nat.mul_comm (d i) m]; exact Nat.le_of_lt h4

private theorem false_fwd (hd : ∀ i, 1 ≤ d i)
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (m k N : Nat) (hN : rcut a d N m k = false) (i : Nat) (hi : N ≤ i) :
    rcut a d i m k = false := by
  apply decide_eq_false
  have hneg : ¬(a N * k ≤ d N * m) := of_decide_eq_false hN
  have hNlt : d N * m < a N * k := by
    rcases Nat.lt_or_ge (d N * m) (a N * k) with h | h
    · exact h
    · exact absurd h hneg
  intro hle
  have c1 : d N * m * d i < a N * k * d i := Nat.mul_lt_mul_of_pos_right hNlt (hd i)
  have c2 : a N * k * d i ≤ a i * d N * k := by
    calc a N * k * d i = (a N * d i) * k := by
            rw [mul_assoc, Nat.mul_comm k (d i), ← mul_assoc]
      _ ≤ (a i * d N) * k := Nat.mul_le_mul_right k (hmono N i hi)
  have c3 : d N * (m * d i) < d N * (a i * k) := by
    calc d N * (m * d i) = d N * m * d i := (mul_assoc (d N) m (d i)).symm
      _ < a i * d N * k := lt_of_lt_le c1 c2
      _ = d N * (a i * k) := by rw [Nat.mul_comm (a i) (d N), mul_assoc]
  have c4 : m * d i < a i * k := by
    rcases Nat.lt_or_ge (m * d i) (a i * k) with h | h
    · exact h
    · exact absurd (lt_of_lt_le c3 (Nat.mul_le_mul_left (d N) h)) (Nat.lt_irrefl _)
  rw [Nat.mul_comm (d i) m] at hle
  exact absurd hle (Nat.not_le.mpr c4)

private theorem eq_false_at (m k j : Nat) (hk : 1 ≤ k)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (heq : a j * k = d j * m) : rcut a d (j+1) m k = false := by
  apply decide_eq_false
  intro hle
  have key : d j * (m * d (j+1)) < d j * (a (j+1) * k) := by
    calc d j * (m * d (j+1))
        = a j * k * d (j+1) := by rw [← mul_assoc, ← heq]
      _ = a j * d (j+1) * k := by rw [mul_assoc, Nat.mul_comm k (d (j+1)), ← mul_assoc]
      _ < a (j+1) * d j * k := Nat.mul_lt_mul_of_pos_right (hmonoS j) hk
      _ = d j * (a (j+1) * k) := by rw [Nat.mul_comm (a (j+1)) (d j), mul_assoc]
  have c : m * d (j+1) < a (j+1) * k := by
    rcases Nat.lt_or_ge (m * d (j+1)) (a (j+1) * k) with h | h
    · exact h
    · exact absurd (lt_of_lt_le key (Nat.mul_le_mul_left (d j) h)) (Nat.lt_irrefl _)
  rw [Nat.mul_comm (d (j+1)) m] at hle
  exact absurd hle (Nat.not_le.mpr c)

/-- ★★★ **Graded rate-carrying ⟹ total modulus (constant form).**  A monotone
    convergent cut-sequence `a_i/d_i` with a non-increasing scheduled margin
    `e_i + 1/(ρ_i·d_i)` (`HtelS`) has its cut constant past any layer `i₀ ≥ 1`
    at which the schedule admits the probe denominator (`k ≤ ρ i₀`):
    `rcut a d i m k = rcut a d j m k` for all `i, j ≥ i₀+1` (`k ≥ 1`).  No LEM,
    no irrationality measure — the graded certificate plus one admitted layer
    suffice. -/
theorem rateS_cut_const (hd : ∀ i, 1 ≤ d i) (hρ : ∀ i, 1 ≤ i → 1 ≤ ρ i)
    (htel : HtelS a d ρ)
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (m k : Nat) (hk : 1 ≤ k)
    (i₀ : Nat) (hi₀ : 1 ≤ i₀) (hkρ : k ≤ ρ i₀)
    (i j : Nat) (hi : i₀+1 ≤ i) (hj : i₀+1 ≤ j) :
    rcut a d i m k = rcut a d j m k := by
  have hi' : i₀ ≤ i := Nat.le_trans (Nat.le_succ _) hi
  have hj' : i₀ ≤ j := Nat.le_trans (Nat.le_succ _) hj
  rcases Nat.lt_trichotomy (a i₀*k) (d i₀*m) with hlt | heq | hgt
  · exact (rinvS_cut m k i hk (rinvS hd hρ htel m k i₀ hi₀ hkρ hlt i hi')).trans
        (rinvS_cut m k j hk (rinvS hd hρ htel m k i₀ hi₀ hkρ hlt j hj')).symm
  · have hf := eq_false_at m k i₀ hk hmonoS heq
    exact (false_fwd hd hmono m k (i₀+1) hf i hi).trans
        (false_fwd hd hmono m k (i₀+1) hf j hj).symm
  · have hfalse : rcut a d i₀ m k = false := decide_eq_false (Nat.not_le.mpr hgt)
    exact (false_fwd hd hmono m k i₀ hfalse i hi').trans
        (false_fwd hd hmono m k i₀ hfalse j hj').symm

/-- ★★★ **The graded generator, existential form.**  Every cut-sequence carrying
    the scheduled rate certificate has a total ∅-axiom modulus
    `N(m,k) = B k + 1`, where `B` witnesses the schedule's admission depth
    (`k ≤ ρ (B k)`). -/
theorem rateS_total_modulus (hd : ∀ i, 1 ≤ d i) (hρ : ∀ i, 1 ≤ i → 1 ≤ ρ i)
    (htel : HtelS a d ρ)
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (B : Nat → Nat) (hB : ∀ k, 1 ≤ k → 1 ≤ B k ∧ k ≤ ρ (B k))
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k :=
  ⟨B k + 1, fun i j hi hj =>
    rateS_cut_const hd hρ htel hmono hmonoS m k hk (B k)
      (hB k hk).1 (hB k hk).2 i j hi hj⟩

/-! ## The identity schedule — degree 1, `N = k+2` -/

/-- ★★★ **Rate-carrying ⟹ total modulus, identity schedule (constant form).**
    The `ρ = id` instance of `rateS_cut_const` at base layer `i₀ = k+1`: the cut
    is constant past `k+2`. -/
theorem rate_cut_const (hd : ∀ i, 1 ≤ d i) (htel : Htel a d)
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (m k : Nat) (hk : 1 ≤ k) (i j : Nat) (hi : k+2 ≤ i) (hj : k+2 ≤ j) :
    rcut a d i m k = rcut a d j m k :=
  rateS_cut_const hd (fun _ h1 => h1) (htelS_of_htel htel) hmono hmonoS m k hk
    (k+1) (Nat.succ_le_succ (Nat.zero_le k)) (Nat.le_succ k) i j hi hj

/-- ★★★ **The identity-schedule generator, existential form.**  Every
    rate-carrying convergent cut-sequence has a total ∅-axiom modulus
    (`N = k+2`). -/
theorem rate_total_modulus (hd : ∀ i, 1 ≤ d i) (htel : Htel a d)
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k :=
  ⟨k+2, fun i j hi hj => rate_cut_const hd htel hmono hmonoS m k hk i j hi hj⟩

/-! ## The root schedule — degree `s`, `N = k^s + 1` -/

/-- ★★★ **Graded rate-carrying ⟹ degree-`s` total modulus (constant form).**
    Under the degree-`s` root schedule `ρ = rootFloor s`, probe denominator `k`
    is admitted at layer `k^s` (`rootFloor_pow`), so the cut is constant past
    `k^s + 1`.  The certificate `HtelS a d (rootFloor s)` defends only the
    slack `1/(⌊i^{1/s}⌋·d_i)` per layer — an `r^{s-1}` factor of overtake
    forgiven at the admission layer `i = r^s` relative to the identity schedule
    — and the price appears here, as the modulus degree. -/
theorem graded_cut_const (s : Nat) (hs : 1 ≤ s)
    (hd : ∀ i, 1 ≤ d i) (htel : HtelS a d (rootFloor s))
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (m k : Nat) (hk : 1 ≤ k) (i j : Nat) (hi : k^s+1 ≤ i) (hj : k^s+1 ≤ j) :
    rcut a d i m k = rcut a d j m k :=
  rateS_cut_const hd (fun n h1 => rootFloor_pos s n h1) htel hmono hmonoS m k hk
    (k^s) (one_le_pow hk s) (Nat.le_of_eq (rootFloor_pow s hs k).symm) i j hi hj

/-- ★★★ **The graded generator at degree `s`, existential form.**  Every
    cut-sequence carrying the degree-`s` rate certificate has a total ∅-axiom
    modulus `N(m,k) = k^s + 1` — the polynomial-slack refinement the
    modulus-degree ladder asked for: rescue is graded by the schedule the way
    `CompletabilityGrade` grades break. -/
theorem graded_total_modulus (s : Nat) (hs : 1 ≤ s)
    (hd : ∀ i, 1 ≤ d i) (htel : HtelS a d (rootFloor s))
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k :=
  ⟨k^s + 1, fun i j hi hj =>
    graded_cut_const s hs hd htel hmono hmonoS m k hk i j hi hj⟩

/-- Strict single-step growth of the convergents propagates to the full
    monotonicity the generator consumes (`hmono` from `hmonoS` + positive
    denominators) — instances need only supply the one-step strict inequality. -/
theorem hmono_of_hmonoS (hd : ∀ i, 1 ≤ d i)
    (hmonoS : ∀ i, a i * d (i+1) < a (i+1) * d i) :
    ∀ N i, N ≤ i → a N * d i ≤ a i * d N := by
  intro N i hNi
  have aux : ∀ t, a N * d (N+t) ≤ a (N+t) * d N := by
    intro t
    induction t with
    | zero => exact Nat.le_refl _
    | succ t ih =>
      have hstep : a (N+t) * d (N+t+1) ≤ a (N+t+1) * d (N+t) :=
        Nat.le_of_lt (hmonoS (N+t))
      have h1 : (a N * d (N+t+1)) * d (N+t) = (a N * d (N+t)) * d (N+t+1) := by
        rw [mul_assoc, Nat.mul_comm (d (N+t+1)) (d (N+t)), ← mul_assoc]
      have h3 : (a (N+t) * d N) * d (N+t+1) = (a (N+t) * d (N+t+1)) * d N := by
        rw [mul_assoc, Nat.mul_comm (d N) (d (N+t+1)), ← mul_assoc]
      have h5 : (a (N+t+1) * d (N+t)) * d N = (a (N+t+1) * d N) * d (N+t) := by
        rw [mul_assoc, Nat.mul_comm (d (N+t)) (d N), ← mul_assoc]
      have hbig : (a N * d (N+t+1)) * d (N+t) ≤ (a (N+t+1) * d N) * d (N+t) := by
        rw [h1]
        exact Nat.le_trans (Nat.mul_le_mul_right _ ih)
          (Nat.le_trans (Nat.le_of_eq h3)
            (Nat.le_trans (Nat.mul_le_mul_right _ hstep) (Nat.le_of_eq h5)))
      exact le_of_mul_le_mul_right (hd (N+t)) hbig
  rw [← add_sub_of_le hNi]; exact aux (i - N)

/-- ★★★ **The depth-rank ⟶ rate-certificate bridge.**  The rate certificate `Htel`
    is exactly a *smallness* condition on the **cross-determinant** `W_i = a_{i+1}·d_i
    − a_i·d_{i+1}` (the divergence-ladder's central object, here given by `hW`): the
    margin is non-increasing iff `i(i+1)·W_i + i·d_i ≤ (i+1)·d_{i+1}`, i.e. the
    cross-det is small relative to the denominator's discrete growth.  This is where
    the depth arc (cross-determinant `W`) meets the modulus generator (rate `Htel`):
    a real whose cross-determinant is controlled by its denominator growth carries its
    own modulus.  (Scheduled form: `RateStratification.htelS_iff_dominatesS`.) -/
theorem Htel_of_crossdet (W : Nat → Nat)
    (hW : ∀ i, a (i+1) * d i = a i * d (i+1) + W i)
    (hcond : ∀ i, 1 ≤ i → i*(i+1)*W i + i*d i ≤ (i+1)*d (i+1)) : Htel a d := by
  intro i hi
  show (a (i+1)*(i+1)+1)*(i*d i) ≤ (a i*i+1)*((i+1)*d (i+1))
  have hLHS : (a (i+1)*(i+1)+1)*(i*d i) = i*(i+1)*(a (i+1)*d i) + i*d i := by
    rw [add_mul, Nat.one_mul]; congr 1
    rw [mul_mul_mul_comm_213, Nat.mul_comm (a (i+1)) i, ← mul_mul_mul_comm_213]
  have hRHS : (a i*i+1)*((i+1)*d (i+1)) = i*(i+1)*(a i*d (i+1)) + (i+1)*d (i+1) := by
    rw [add_mul, Nat.one_mul]; congr 1
    rw [mul_mul_mul_comm_213, Nat.mul_comm (a i) (i+1), mul_mul_mul_comm_213,
        Nat.mul_comm (i+1) i]
  rw [hLHS, hRHS, hW i, Nat.mul_add, Nat.add_assoc]
  exact Nat.add_le_add_left (hcond i hi) _

end E213.Lib.Math.NumberSystems.Real213.RateModulus
