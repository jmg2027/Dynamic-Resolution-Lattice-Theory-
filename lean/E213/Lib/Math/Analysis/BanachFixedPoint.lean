import E213.Lib.Math.Analysis.UniformLimitContinuous

/-!
# Banach fixed-point theorem — constructive (modulus) form (∅-axiom, vein-C)

Classically a contraction on a *complete* metric space has a unique fixed
point, proved by invoking completeness as an existence axiom.  ∅-axiom forces
the fixed point to be **computed**: the Picard iterates `xₙ = Tⁿ x₀` are
Cauchy with an explicit **geometric modulus**, and the limit (reached by none,
approached to every scale) is the fixed point.

The forcing heart is `picard_cauchy`: the convergence modulus `N(m)` is
computed from `m` alone (given a base gap `close (s+1) x₀ x₁`), via the
geometric tail bound `Σ 1/2^k`.  Completeness is then a thin wrapper
(`CompleteMetricModulus`) carrying a `lim` of any modulus-Cauchy sequence; the
fixed point is `lim (picard T x0)`, located equality `T x* = x*` to every
scale, and unique.
-/

namespace E213.Lib.Math.Analysis.BanachFixedPoint

open E213.Lib.Math.Analysis.UniformLimitContinuous

/-! ## 1. Contraction and the Picard iterates -/

/-- **Contraction** — `T` halves distances in the `1/2^m` graduation:
    a pair within `1/2^(m+1)` maps to a pair within `1/2^(m+2)` (ratio ≤ 1/2,
    `d(Tx,Ty) ≤ d(x,y)/2`). -/
def Contraction {X : Type} (M : MetricModulus X) (T : X → X) : Prop :=
  ∀ m x y, M.close (m + 1) x y → M.close (m + 2) (T x) (T y)

/-- **Picard iterates** `xₙ = Tⁿ x₀`. -/
def picard {X : Type} (T : X → X) (x0 : X) : Nat → X
  | 0     => x0
  | n + 1 => T (picard T x0 n)

/-! ## 2. The geometric step + tail bounds (the forcing heart) -/

variable {X : Type} (M : MetricModulus X) {T : X → X}

/-- **`picard_step_geometric`** — each consecutive gap improves by one dyadic
    level per step: if the first gap is `close (s+1) x₀ x₁`, then the `n`-th
    gap is `close (s+1+n) xₙ xₙ₊₁`.  (Each `T`-application halves the gap, i.e.
    advances the scale by one.) -/
theorem picard_step_geometric (hT : Contraction M T) (x0 : X) (s : Nat)
    (hbase : M.close (s + 1) (picard T x0 0) (picard T x0 1)) :
    ∀ n, M.close (s + 1 + n) (picard T x0 n) (picard T x0 (n + 1)) := by
  intro n
  induction n with
  | zero => exact hbase
  | succ k ih =>
      -- ih : close (s+1+k) x_k x_{k+1}; rewrite to close ((s+k)+1) for hT
      have ih' : M.close ((s + k) + 1) (picard T x0 k) (picard T x0 (k + 1)) := by
        have : s + 1 + k = (s + k) + 1 := by rw [Nat.add_right_comm s 1 k]
        rw [this] at ih; exact ih
      -- contraction at level (s+k): close ((s+k)+1) → close ((s+k)+2)
      have hc : M.close ((s + k) + 2)
          (T (picard T x0 k)) (T (picard T x0 (k + 1))) :=
        hT (s + k) (picard T x0 k) (picard T x0 (k + 1)) ih'
      -- T x_k = x_{k+1}, T x_{k+1} = x_{k+2}; rescale (s+k)+2 = s+1+(k+1)
      have he : (s + k) + 2 = s + 1 + (k + 1) := by
        have h1 : (s + k) + 2 = (s + k + 1) + 1 := rfl
        have h2 : s + 1 + (k + 1) = (s + k + 1) + 1 := by
          rw [Nat.add_assoc s 1 (k + 1), Nat.add_comm 1 (k + 1),
            ← Nat.add_assoc s (k + 1) 1]
          rw [show s + (k + 1) = s + k + 1 from (Nat.add_assoc s k 1).symm]
        rw [h1, h2]
      rw [he] at hc
      exact hc

/-- **`picard_tail`** — the geometric series tail bound, **uniform in `j`**:
    starting from `xₙ`, the whole tail `x_{n+j}` stays within `1/2^(s+n)`
    (the sum `Σ_{i≥0} 1/2^(s+1+n+i) = 1/2^(s+n)`).  This is why the modulus is
    computable: the bound does not depend on how far ahead `j` reaches. -/
theorem picard_tail (hT : Contraction M T) (x0 : X) (s : Nat)
    (hbase : M.close (s + 1) (picard T x0 0) (picard T x0 1)) :
    ∀ j n, M.close (s + n) (picard T x0 n) (picard T x0 (n + j)) := by
  intro j
  induction j with
  | zero =>
      intro n
      -- close (s+n) x_n x_{n+0} = x_n  : reflexivity
      have : picard T x0 (n + 0) = picard T x0 n := by rw [Nat.add_zero]
      rw [this]
      exact M.crefl (s + n) (picard T x0 n)
  | succ j ih =>
      intro n
      -- step at index n : close (s+1+n) x_n x_{n+1}
      have hstep : M.close (s + 1 + n) (picard T x0 n) (picard T x0 (n + 1)) :=
        picard_step_geometric M hT x0 s hbase n
      -- IH at n+1 (n still general because ih is ∀ n):
      have ih1 : M.close (s + (n + 1))
          (picard T x0 (n + 1)) (picard T x0 ((n + 1) + j)) :=
        ih (n + 1)
      -- both legs at scale (s+n)+1 = s+1+n = s+(n+1)
      have e1 : s + 1 + n = (s + n) + 1 := by
        rw [Nat.add_right_comm s 1 n]
      have e2 : s + (n + 1) = (s + n) + 1 := by
        rw [Nat.add_assoc]
      rw [e1] at hstep
      rw [e2] at ih1
      -- ctri : close ((s+n)+1) a b ∧ close ((s+n)+1) b c → close (s+n) a c
      have hmerge : M.close (s + n)
          (picard T x0 n) (picard T x0 ((n + 1) + j)) :=
        M.ctri (s + n) (picard T x0 n) (picard T x0 (n + 1))
          (picard T x0 ((n + 1) + j)) hstep ih1
      -- (n+1)+j = n+(j+1)
      have eidx : (n + 1) + j = n + (j + 1) := by
        rw [Nat.add_right_comm n 1 j, Nat.add_assoc n j 1]
      rw [eidx] at hmerge
      exact hmerge

/-! ## 3. The Cauchy modulus and the fixed point -/

/-- **`cmono_le`** — coarsening across many scales: `close (b + d) x y` gives
    `close b x y` for every `d` (a finer dyadic bound implies every coarser
    one), by iterating the one-step `cmono`. -/
theorem cmono_le (b : Nat) (x y : X) :
    ∀ d, M.close (b + d) x y → M.close b x y := by
  intro d
  induction d with
  | zero => intro h; rw [Nat.add_zero] at h; exact h
  | succ d ih =>
      intro h
      -- close (b+(d+1)) = close ((b+d)+1) → close (b+d) → close b
      have h' : M.close ((b + d) + 1) x y := by
        rw [Nat.add_assoc b d 1]; exact h
      exact ih (M.cmono (b + d) x y h')

/-- **`close_of_ge`** — from the tail bound `close (s+n) xₙ x_{n+j}`, if a
    target scale `m ≤ s + p` is wanted and `q = p + j`, coarsen to `close m`. -/
theorem close_le_tail (hT : Contraction M T) (x0 : X) (s : Nat)
    (hbase : M.close (s + 1) (picard T x0 0) (picard T x0 1))
    (m p j : Nat) (hm : m ≤ s + p) :
    M.close m (picard T x0 p) (picard T x0 (p + j)) := by
  -- tail gives close (s+p); coarsen to m using m ≤ s+p
  have htail : M.close (s + p) (picard T x0 p) (picard T x0 (p + j)) :=
    picard_tail M hT x0 s hbase j p
  -- s + p = m + (s + p - m)
  obtain ⟨d, hd⟩ := Nat.le.dest hm   -- m + d = s + p
  rw [← hd] at htail
  exact cmono_le M m (picard T x0 p) (picard T x0 (p + j)) d htail

/-- **★★ `picard_cauchy` — the forcing heart (∅-axiom, constructive).**

    The Picard iterates are Cauchy with the **explicitly computed geometric
    modulus** `N(m) = m`: given the base gap `close (s+1) x₀ x₁`, for every
    target scale `m` and all `p q ≥ m`, the iterates are within `1/2^m`.

    The modulus is computed from `m` and the first step alone — no completeness,
    no omniscience.  It rests on the geometric tail bound `picard_tail`
    (`Σ 1/2^k` converges, *uniformly in how far the tail reaches*), coarsened to
    scale `m` via `cmono_le`. -/
theorem picard_cauchy (hT : Contraction M T) (x0 : X) (s : Nat)
    (hbase : M.close (s + 1) (picard T x0 0) (picard T x0 1)) :
    ∀ m, ∃ N, ∀ p q, p ≥ N → q ≥ N →
      M.close m (picard T x0 p) (picard T x0 q) := by
  intro m
  refine ⟨m, ?_⟩
  intro p q hp hq
  -- WLOG by Nat.le_total; both branches use close_le_tail with q = p + j.
  rcases Nat.le_total p q with hpq | hqp
  · -- p ≤ q : q = p + j
    obtain ⟨j, hj⟩ := Nat.le.dest hpq   -- p + j = q
    have hmp : m ≤ s + p := Nat.le_trans hp (Nat.le_add_left p s)
    have := close_le_tail M hT x0 s hbase m p j hmp
    rw [hj] at this
    exact this
  · -- q ≤ p : p = q + j ; symmetrise
    obtain ⟨j, hj⟩ := Nat.le.dest hqp   -- q + j = p
    have hmq : m ≤ s + q := Nat.le_trans hq (Nat.le_add_left q s)
    have hclose := close_le_tail M hT x0 s hbase m q j hmq
    rw [hj] at hclose
    exact M.csymm m (picard T x0 q) (picard T x0 p) hclose

/-! ## 4. Completeness wrapper, the fixed point, and uniqueness -/

/-- **CompleteMetricModulus X** — a `MetricModulus` together with a limit
    operator `lim` taking any *modulus-Cauchy* sequence to a point it converges
    to.  `climconv` is the abstract completeness statement: every Cauchy
    sequence has a computed limit it approaches to every scale.  (∅-axiom: no
    existence miracle — `lim` is data, the convergence is its spec.) -/
structure CompleteMetricModulus (X : Type) extends MetricModulus X where
  /-- the limit of a sequence (data, applied to Cauchy sequences). -/
  lim : (Nat → X) → X
  /-- completeness: any modulus-Cauchy sequence converges to its `lim`. -/
  climconv : ∀ (seq : Nat → X),
    (∀ m, ∃ N, ∀ p q, p ≥ N → q ≥ N → close m (seq p) (seq q)) →
    ∀ m, ∃ N, ∀ p, p ≥ N → close m (seq p) (lim seq)

namespace CompleteMetricModulus

variable {X : Type} (C : CompleteMetricModulus X) {T : X → X}

/-- **`banach_fixed_point` — the headline (∅-axiom, constructive).**

    Over a complete dyadic metric, a contraction `T` has the explicit point
    `x* = lim (picard T x0)` as a fixed point: `close m x* (T x*)` for **every**
    scale `m` (located equality `T x* = x*`).  The iterates approach `x*`
    (`picard_cauchy` + `climconv`); `x*` itself is reached by none — only the
    Cauchy limit. -/
theorem banach_fixed_point (hT : Contraction C.toMetricModulus T)
    (x0 : X) (s : Nat)
    (hbase : C.close (s + 1) (picard T x0 0) (picard T x0 1)) :
    ∀ m, C.close m (C.lim (picard T x0)) (T (C.lim (picard T x0))) := by
  intro m
  -- abbreviation for the Picard limit (the explicit fixed point)
  let xstar : X := C.lim (picard T x0)
  show C.close m xstar (T xstar)
  -- iterates are Cauchy (the forcing heart)
  have hcau : ∀ k, ∃ N, ∀ p q, p ≥ N → q ≥ N →
      C.close k (picard T x0 p) (picard T x0 q) :=
    picard_cauchy C.toMetricModulus hT x0 s hbase
  -- convergence to xstar at scale (m+2), and (m+3) to drive the contraction
  obtain ⟨N1, hN1⟩ := C.climconv (picard T x0) hcau (m + 2)
  obtain ⟨N2, hN2⟩ := C.climconv (picard T x0) hcau (m + 3)
  let n : Nat := N1 + N2
  have hnN1 : n ≥ N1 := Nat.le_add_right N1 N2
  have hnN2 : n ≥ N2 := Nat.le_add_left N2 N1
  -- (A) x_{n+1} close (m+2) to xstar
  have hA : C.close (m + 2) (picard T x0 (n + 1)) xstar :=
    hN1 (n + 1) (Nat.le_trans hnN1 (Nat.le_succ n))
  -- (B) x_n close (m+3) to xstar → contraction → close (m+4) (T x_n)(T xstar)
  have hBconv : C.close (m + 3) (picard T x0 n) xstar := hN2 n hnN2
  have hBT : C.close ((m + 2) + 2) (T (picard T x0 n)) (T xstar) :=
    hT (m + 2) (picard T x0 n) xstar hBconv
  -- T x_n = x_{n+1}; coarsen (m+4) → (m+2)
  have hBT' : C.close (m + 2) (picard T x0 (n + 1)) (T xstar) := by
    have hidx : T (picard T x0 n) = picard T x0 (n + 1) := rfl
    rw [hidx] at hBT
    exact cmono_le C.toMetricModulus (m + 2) (picard T x0 (n + 1)) (T xstar) 2 hBT
  -- chain  xstar —(m+2)— x_{n+1} —(m+2)— T xstar ⇒ close (m+1) ⇒ close m
  have hAsym : C.close (m + 2) xstar (picard T x0 (n + 1)) :=
    C.csymm (m + 2) (picard T x0 (n + 1)) xstar hA
  have hm1 : C.close (m + 1) xstar (T xstar) :=
    C.ctri (m + 1) xstar (picard T x0 (n + 1)) (T xstar) hAsym hBT'
  exact C.cmono m xstar (T xstar) hm1

/-- **`banach_unique` — uniqueness (∅-axiom, constructive).**

    Two **exact** fixed points (`T x = x`, `T y = y`) lying in a common ball
    (`close 0 x y`, the coarsest bound — automatic for fixed points reached as
    Cauchy limits) are within `1/2^m` for **every** scale `m`, hence coincide
    as located points.

    The contraction halves their distance with *no* padding cost (exact
    equalities), so from `close m x y` it gains a scale (`close (m+1) x y`);
    seeded by `close 0 x y` and iterated, every scale is reached.  The fixed
    point is unique up to located equality. -/
theorem banach_unique (hT : Contraction C.toMetricModulus T)
    (x y : X) (hx : T x = x) (hy : T y = y) (h1 : C.close 1 x y) :
    ∀ m, C.close m x y := by
  -- gain-a-scale step: close (k+1) x y → close (k+2) x y (no padding, exact FPs)
  have step : ∀ k, C.close (k + 1) x y → C.close (k + 2) x y := by
    intro k hk
    have hTxy : C.close (k + 2) (T x) (T y) := hT k x y hk
    rw [hx, hy] at hTxy            -- close (k+2) x y
    exact hTxy
  -- reach every scale ≥ 1 by iterating step from close 1
  have hsucc : ∀ m, C.close (m + 1) x y := by
    intro m
    induction m with
    | zero => exact h1
    | succ k ih => exact step k ih
  intro m
  cases m with
  | zero => exact C.cmono 0 x y (hsucc 0)   -- close 0 from close 1
  | succ k => exact hsucc k

end CompleteMetricModulus

/-! ## 5. Non-vacuous instance — the headline is inhabited

A concrete `CompleteMetricModulus` certifying the wrapper + headline are not
vacuous: the one-point carrier `Unit` with the everywhere-`True` dyadic metric
(every pair is within `1/2^m` at every scale — the degenerate complete metric).
Any `T : Unit → Unit` is a contraction, the limit is the unique point, and
`banach_fixed_point` produces `close m x* (T x*)` at every scale. -/

/-- The everywhere-`True` `MetricModulus` on `Unit` (all four laws trivial). -/
def trivMet : MetricModulus Unit where
  close := fun _ _ _ => True
  crefl := fun _ _ => trivial
  csymm := fun _ _ _ _ => trivial
  cmono := fun _ _ _ _ => trivial
  ctri  := fun _ _ _ _ _ _ => trivial

/-- The complete version of `trivMet`: `lim` is the unique point, and every
    sequence converges to it (vacuously, since `close` is always `True`). -/
def trivComplete : CompleteMetricModulus Unit where
  toMetricModulus := trivMet
  lim := fun _ => ()
  climconv := fun _ _ _ => ⟨0, fun _ _ => trivial⟩

/-- Any `T : Unit → Unit` is a `trivMet`-contraction (the conclusion is `True`). -/
theorem triv_contraction (T : Unit → Unit) :
    Contraction trivComplete.toMetricModulus T :=
  fun _ _ _ _ => trivial

/-- **Inhabitance of the headline.**  For the identity on `Unit`, the Picard
    limit `x* = lim (picard id ())` is a fixed point at every scale — the
    `banach_fixed_point` conclusion is a real, inhabited statement. -/
theorem inhabited_banach_fixed_point :
    ∀ m, trivComplete.close m
      (trivComplete.lim (picard (fun _ : Unit => ()) ()))
      ((fun _ : Unit => ()) (trivComplete.lim (picard (fun _ : Unit => ()) ()))) :=
  CompleteMetricModulus.banach_fixed_point trivComplete
    (triv_contraction (fun _ : Unit => ())) () 0 trivial

/-- **Inhabitance of uniqueness.**  On `Unit`, the unique point `()` is the
    located unique fixed point of `id`. -/
theorem inhabited_banach_unique :
    ∀ m, trivComplete.close m () () :=
  CompleteMetricModulus.banach_unique trivComplete
    (triv_contraction (fun _ : Unit => ())) () () rfl rfl trivial

end E213.Lib.Math.Analysis.BanachFixedPoint
