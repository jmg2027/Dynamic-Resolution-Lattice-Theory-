import E213.Meta.Tactic.NatHelper
import E213.Meta.Int213.Core

/-!
# Zero-run non-holonomicity — a bounded, growth-free non-holonomicity criterion

`NonHolonomicWitness` certifies non-holonomicity by **growth** (Klazar): `(n!)ⁿ` outgrows every
holonomic envelope.  This file gives an **orthogonal** criterion that works on *bounded*
sequences, via the **homogeneity** of a P-recursive recurrence.

A P-recursive (holonomic) integer sequence satisfies a homogeneous recurrence
`lead(n)·a(n+k) = Σᵢ qᵢ(n)·a(n+i)` with `lead` a nonzero polynomial — hence `lead(n) ≠ 0` for
all `n` past its finitely many roots.  Therefore, **once a window of `k` consecutive zeros
occurs past those roots, the recurrence forces every later term to be zero** (a zero window has
zero right-hand side, and `lead(n) ≠ 0` cancels).  So:

> **`zero_run_not_homogRec`** — a sequence with *arbitrarily long zero-runs at arbitrarily large
> positions* **and** *infinitely many nonzero terms* satisfies **no** such homogeneous
> recurrence: it is non-holonomic.

This is captured ∅-axiom for the general homogeneous-recurrence class (`HomogRec`: any
`lead·a(n+k) = R(n, window)` with `R(n, ·)` vanishing on the zero window and `lead` eventually
nonzero — strictly larger than P-recursive, so non-membership is stronger).  No growth
hypothesis, no `funext` (homogeneity is stated pointwise), no analysis.

The companion file `ZeroRunNonHolonomicWitness` exhibits an explicit bounded witness (the
indicator of the powers of two) inhabiting the criterion's hypotheses.
-/

namespace E213.Lib.Math.Cauchy.ZeroRunNonHolonomic

/-- A **homogeneous finite-window recurrence** for `a : Nat → Int` of order `k`:
    `lead n · a(n+k) = R n (window)`, where the right-hand side `R n` **vanishes on the zero
    window** (homogeneity, stated pointwise to avoid `funext`) and the leading coefficient
    `lead` is **eventually nonzero** (`lead n ≠ 0` for `n ≥ R₀`).  Every integer-valued
    P-recursive sequence satisfies one — `lead` the leading polynomial (nonzero past its roots),
    `R n` the integer-linear combination of the lower terms. -/
def HomogRec (a : Nat → Int) : Prop :=
  ∃ (k : Nat) (lead : Nat → Int) (R : Nat → (Nat → Int) → Int) (R₀ : Nat),
    (∀ n, R₀ ≤ n → lead n ≠ 0) ∧
    (∀ n (w : Nat → Int), (∀ i, i < k → w i = 0) → R n w = 0) ∧
    (∀ n, lead n * a (n + k) = R n (fun i => a (n + i)))

/-- A nonzero `lead` times a value is zero ⟹ the value is zero (`Int` has no zero divisors).
    Decidable case split (no `propext` from the `mul_eq_zero` iff). -/
theorem int_eq_zero_of_mul_left {x y : Int} (hx : x ≠ 0) (h : x * y = 0) : y = 0 := by
  rcases E213.Meta.Int213.mul_eq_zero h with hx0 | hy0
  · exact absurd hx0 hx
  · exact hy0

/-- ★★★ **Zero-run non-holonomicity.**  If `a` has arbitrarily long zero-runs at arbitrarily
    large positions and infinitely many nonzero terms, it satisfies **no** homogeneous
    finite-window recurrence with eventually-nonzero leading coefficient — in particular it is
    **not P-recursive (non-holonomic)**.  Bounded or not; no growth needed. -/
theorem zero_run_not_homogRec (a : Nat → Int)
    (hruns : ∀ k R₀, ∃ N, R₀ ≤ N ∧ ∀ i, i < k → a (N + i) = 0)
    (hinf : ∀ M, ∃ m, M ≤ m ∧ a m ≠ 0) :
    ¬ HomogRec a := by
  rintro ⟨k, lead, R, R₀, lead_ne, homog, rec⟩
  obtain ⟨N, hNR₀, hzero⟩ := hruns k R₀
  -- zero propagates forever (manual strong induction via a bound `T`)
  have aux : ∀ T t, t < T → a (N + t) = 0 := by
    intro T
    induction T with
    | zero => intro t ht; exact absurd ht (Nat.not_lt_zero t)
    | succ T ihT =>
      intro t ht
      rcases Nat.lt_or_ge t k with htk | hkt
      · exact hzero t htk
      · have hle : t ≤ T := Nat.le_of_lt_succ ht
        have hwin : ∀ i, i < k → (fun i => a (N + (t - k) + i)) i = 0 := by
          intro i hi
          show a (N + (t - k) + i) = 0
          have h1 : (t - k) + i < (t - k) + k := Nat.add_lt_add_left hi (t - k)
          rw [E213.Tactic.NatHelper.sub_add_cancel hkt] at h1
          have hih := ihT ((t - k) + i) (Nat.lt_of_lt_of_le h1 hle)
          rwa [← Nat.add_assoc] at hih
        have hRzero : R (N + (t - k)) (fun i => a (N + (t - k) + i)) = 0 :=
          homog (N + (t - k)) _ hwin
        have hrecn := rec (N + (t - k))
        rw [hRzero] at hrecn
        have hleadne : lead (N + (t - k)) ≠ 0 :=
          lead_ne (N + (t - k)) (Nat.le_trans hNR₀ (Nat.le_add_right N (t - k)))
        have haz : a (N + (t - k) + k) = 0 := int_eq_zero_of_mul_left hleadne hrecn
        have hidx : N + (t - k) + k = N + t := by
          rw [Nat.add_assoc, E213.Tactic.NatHelper.sub_add_cancel hkt]
        rwa [hidx] at haz
  -- contradiction with infinitely many nonzero terms
  obtain ⟨m, hNm, ham⟩ := hinf N
  have hcontra : a m = 0 := by
    have hh := aux (m - N + 1) (m - N) (Nat.lt_succ_self _)
    rwa [E213.Tactic.NatHelper.add_sub_of_le hNm] at hh
  exact ham hcontra

/-! ## §2 — the autonomous (time-invariant) finite-window machine, and its determinacy bound

A *homogeneous P-recursive* recurrence (`HomogRec`) lets the coefficients vary with `n`.  The
complementary class is the **autonomous** one — a fixed next-state rule `F` of the window,
independent of `n`: this is exactly a deterministic **finite-state machine** (time-invariant
transition) reading a length-`k` window.  `F` depends only on the window's first `k` entries
(stated pointwise, no `funext`). -/

/-- `a` is generated by an **autonomous finite-window recurrence** (a deterministic, time-invariant
    finite-state machine): a fixed `F` of the length-`k` window, `n`-independent. -/
def AutoRec (a : Nat → Int) : Prop :=
  ∃ (k : Nat) (F : (Nat → Int) → Int),
    (∀ w w' : Nat → Int, (∀ i, i < k → w i = w' i) → F w = F w') ∧
    (∀ n, a (n + k) = F (fun i => a (n + i)))

/-- ★★★ **Determinacy obstruction.**  If *some window pattern* occurs followed by **two
    different** next-values (here: a length-`k` all-zero window continued once by `v` and once by
    `v' ≠ v`, for every `k`), then `a` is generated by **no** autonomous finite-window machine.
    A deterministic FSM cannot emit two outputs from one state — the Myhill–Nerode kernel of
    "needs unbounded memory".  No pigeonhole, no encoding, no `funext`. -/
theorem two_continuations_not_autoRec (a : Nat → Int)
    (h : ∀ k, ∃ N N' v v', v ≠ v'
        ∧ (∀ i, i < k → a (N + i) = 0) ∧ a (N + k) = v
        ∧ (∀ i, i < k → a (N' + i) = 0) ∧ a (N' + k) = v') :
    ¬ AutoRec a := by
  rintro ⟨k, F, hdep, hrec⟩
  obtain ⟨N, N', v, v', hvv', hN0, hNv, hN'0, hN'v'⟩ := h k
  have hFN : F (fun i => a (N + i)) = v := (hrec N).symm.trans hNv
  have hFN' : F (fun i => a (N' + i)) = v' := (hrec N').symm.trans hN'v'
  have hwin : F (fun i => a (N + i)) = F (fun i => a (N' + i)) := by
    apply hdep
    intro i hi
    show a (N + i) = a (N' + i)
    rw [hN0 i hi, hN'0 i hi]
  rw [hFN, hFN'] at hwin
  exact hvv' hwin

/-- ★★★ **The general Myhill–Nerode obstruction.**  If, for every window length `k`, two
    positions carry **equal** length-`k` windows but **different** next-values, then `a` is
    generated by **no** autonomous finite-state machine.  (`two_continuations_not_autoRec` is the
    all-zero-window special case.) -/
theorem distinct_next_equal_window_not_autoRec (a : Nat → Int)
    (h : ∀ k, ∃ N N', (∀ i, i < k → a (N + i) = a (N' + i)) ∧ a (N + k) ≠ a (N' + k)) :
    ¬ AutoRec a := by
  rintro ⟨k, F, hdep, hrec⟩
  obtain ⟨N, N', hwin, hne⟩ := h k
  have hwinF : F (fun i => a (N + i)) = F (fun i => a (N' + i)) := hdep _ _ hwin
  rw [(hrec N), (hrec N')] at hne
  exact hne hwinF

/-! ## §3 — the unified finite-state-machine class -/

/-- `a` is generated by **some** finite-state machine: either a time-varying homogeneous
    P-recursive recurrence (`HomogRec`) or a time-invariant autonomous one (`AutoRec`).  A
    sequence is **non-holonomic in the strong, machine-free sense** when it satisfies neither. -/
def FiniteRecurrence (a : Nat → Int) : Prop := HomogRec a ∨ AutoRec a

end E213.Lib.Math.Cauchy.ZeroRunNonHolonomic
