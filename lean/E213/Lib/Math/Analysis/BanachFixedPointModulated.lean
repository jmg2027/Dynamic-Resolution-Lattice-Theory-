import E213.Lib.Math.Analysis.BanachFixedPoint

/-!
# Banach fixed point through a *modulated* completeness engine (∅-axiom, vein-C)

`BanachFixedPoint.lean` proves the headline `banach_fixed_point` over a
`CompleteMetricModulus`, whose `lim : (Nat → X) → X` is total on **bare**
Cauchy sequences and whose `climconv` claims convergence for *every* such
sequence.  A total, choice-free `lim` correct on all bare Cauchy sequences is
constructively impossible: it would have to recover each sequence's hidden
convergence modulus `N(m)` from the bare `∀m,∃N` data — exactly the smuggled
countable-choice principle `AC₀,₀` that ∅-axiom forbids
(the `wall_constructive` frontier).  So `CompleteMetricModulus`
is hard to *inhabit* non-trivially: the only instance in the tree is the
degenerate everywhere-`True` metric on `Unit`.

This file removes the over-strong interface.  The decisive leverage
(the `wall_synthesis` frontier): **the contraction supplies its
own modulus** — `picard_cauchy` already produces the explicit `N(m)=m`
(`BanachFixedPoint.lean:154`).  A modulated engine therefore needs no generic
bare-sequence `lim`; it carries the modulus that is already in hand.

`CompleteMetricModulusMod` re-signatures completeness so its `limMod` takes the
modulus **as data** (an argument), making it total and choice-free — the
standard Bishop completion shape, and the same one the repo's own real-number
completion uses (`Analysis/CauchyComplete.CauchyCutSeq`, modulus stored as a
field).  `banach_fixed_point_modulated` is then the *same* proof skeleton as
`banach_fixed_point`, with no bare `lim` anywhere; `picard_cauchy_mod`
repackages `picard_cauchy` into the uniform (modulus-as-argument) form it
consumes.

The honest residual is **representation-dependence**: the modulus is part of the
input, so the bare "∀ Cauchy sequence" quantifier does slightly less than it
appears — exactly 213's own presentation-dependence stance
(`Real213/PresentationDependence`).  The fixed point is reached by no bare
sequence, only by a *presented* (modulated) one.

All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.BanachFixedPoint

open E213.Lib.Math.Analysis.UniformLimitContinuous (MetricModulus)

/-! ## 1. The Picard orbit is Cauchy in the *uniform* (modulus-as-data) form -/

variable {X : Type} (M : MetricModulus X) {T : X → X}

/-- **`picard_cauchy_mod` — the modulated forcing heart (∅-axiom).**

    `picard_cauchy` with the existential `∃N` wrapper deleted and the witness
    `N = m` inlined: the iterates are Cauchy with the explicit identity modulus.
    For every scale `m` and all `p, q ≥ m`, the iterates are within `1/2^m`.
    The body is `close_le_tail` + `cmono_le`, exactly as in `picard_cauchy`. -/
theorem picard_cauchy_mod (hT : Contraction M T) (x0 : X) (s : Nat)
    (hbase : M.close (s + 1) (picard T x0 0) (picard T x0 1)) :
    ∀ m p q, p ≥ m → q ≥ m → M.close m (picard T x0 p) (picard T x0 q) := by
  intro m p q hp hq
  rcases Nat.le_total p q with hpq | hqp
  · obtain ⟨j, hj⟩ := Nat.le.dest hpq   -- p + j = q
    have hmp : m ≤ s + p := Nat.le_trans hp (Nat.le_add_left p s)
    have := close_le_tail M hT x0 s hbase m p j hmp
    rw [hj] at this
    exact this
  · obtain ⟨j, hj⟩ := Nat.le.dest hqp   -- q + j = p
    have hmq : m ≤ s + q := Nat.le_trans hq (Nat.le_add_left q s)
    have hclose := close_le_tail M hT x0 s hbase m q j hmq
    rw [hj] at hclose
    exact M.csymm m (picard T x0 q) (picard T x0 p) hclose

/-! ## 2. The modulated completeness engine -/

/-- **CompleteMetricModulusMod X** — a `MetricModulus` together with a limit
    operator `limMod` taking a sequence **together with its convergence modulus**
    `N` (and the modulated-Cauchy proof against that `N`) to a point it converges
    to.  Unlike `CompleteMetricModulus.lim`, `limMod` never has to *recover* the
    modulus from bare data — it is handed over as an argument, so the operator is
    total and choice-free (the Bishop completion shape).  `climconvMod` is the
    completeness law: the supplied modulus drives convergence to `limMod`. -/
structure CompleteMetricModulusMod (X : Type) extends MetricModulus X where
  /-- the limit of a modulated-Cauchy sequence (modulus + proof carried as data). -/
  limMod : (seq : Nat → X) → (N : Nat → Nat) →
    (∀ m p q, p ≥ N m → q ≥ N m → close m (seq p) (seq q)) → X
  /-- completeness: a modulated-Cauchy sequence converges to its `limMod`. -/
  climconvMod : ∀ (seq : Nat → X) (N : Nat → Nat)
    (hcau : ∀ m p q, p ≥ N m → q ≥ N m → close m (seq p) (seq q)),
    ∀ m, ∃ K, ∀ p, p ≥ K → close m (seq p) (limMod seq N hcau)

namespace CompleteMetricModulusMod

variable {X : Type} (C : CompleteMetricModulusMod X) {T : X → X}

/-- The Picard limit through the modulated engine: `limMod` applied to the orbit
    with its closed-form identity modulus `N(m)=m` (from `picard_cauchy_mod`). -/
def picardLim (C : CompleteMetricModulusMod X) {T : X → X}
    (hT : Contraction C.toMetricModulus T) (x0 : X) (s : Nat)
    (hbase : C.close (s + 1) (picard T x0 0) (picard T x0 1)) : X :=
  C.limMod (picard T x0) (fun m => m)
    (picard_cauchy_mod C.toMetricModulus hT x0 s hbase)

/-- **★★ `banach_fixed_point_modulated` — the headline through a modulated
    engine (∅-axiom, no bare `lim`).**

    Over a *modulated*-complete dyadic metric, a contraction `T` has the explicit
    point `x* = picardLim …` (the orbit's `limMod`, fed the closed-form modulus
    `N(m)=m`) as a fixed point: `close m x* (T x*)` for every scale `m` (located
    equality `T x* = x*`).  The proof is the `banach_fixed_point` skeleton with
    `climconv` replaced by `climconvMod` applied to the *one* explicit orbit —
    nothing uses the bare-sequence generality, so the choice-free modulated
    interface suffices. -/
theorem banach_fixed_point_modulated (hT : Contraction C.toMetricModulus T)
    (x0 : X) (s : Nat)
    (hbase : C.close (s + 1) (picard T x0 0) (picard T x0 1)) :
    ∀ m, C.close m (C.picardLim hT x0 s hbase) (T (C.picardLim hT x0 s hbase)) := by
  intro m
  let xstar : X := C.picardLim hT x0 s hbase
  show C.close m xstar (T xstar)
  -- the orbit is modulated-Cauchy with the identity modulus
  have hcau : ∀ k p q, p ≥ k → q ≥ k →
      C.close k (picard T x0 p) (picard T x0 q) :=
    picard_cauchy_mod C.toMetricModulus hT x0 s hbase
  -- convergence to xstar at scales (m+2) and (m+3), via climconvMod on the orbit
  obtain ⟨N1, hN1⟩ :=
    C.climconvMod (picard T x0) (fun k => k) hcau (m + 2)
  obtain ⟨N2, hN2⟩ :=
    C.climconvMod (picard T x0) (fun k => k) hcau (m + 3)
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

end CompleteMetricModulusMod

/-! ## 3. Non-vacuous instance — the modulated headline is inhabited

The same degenerate carrier as `BanachFixedPoint`'s `trivComplete`, now under
the modulated interface: every pair is everywhere-`True` close, `limMod` is the
unique point, and the modulated headline produces `close m x* (T x*)` at every
scale.  The genuinely non-trivial inhabitant is the dyadic completion (built in
`Probability/Limit/DyadicCompletion`). -/

/-- The complete (modulated) version of `trivMet`. -/
def trivCompleteMod : CompleteMetricModulusMod Unit where
  toMetricModulus := trivMet
  limMod := fun _ _ _ => ()
  climconvMod := fun _ _ _ _ => ⟨0, fun _ _ => trivial⟩

/-- **Inhabitance of the modulated headline.**  For the identity on `Unit`, the
    modulated Picard limit is a fixed point at every scale. -/
theorem inhabited_banach_fixed_point_modulated :
    ∀ m, trivCompleteMod.close m
      (trivCompleteMod.picardLim
        (triv_contraction (fun _ : Unit => ())) () 0 trivial)
      ((fun _ : Unit => ())
        (trivCompleteMod.picardLim
          (triv_contraction (fun _ : Unit => ())) () 0 trivial)) :=
  CompleteMetricModulusMod.banach_fixed_point_modulated trivCompleteMod
    (triv_contraction (fun _ : Unit => ())) () 0 trivial

end E213.Lib.Math.Analysis.BanachFixedPoint
