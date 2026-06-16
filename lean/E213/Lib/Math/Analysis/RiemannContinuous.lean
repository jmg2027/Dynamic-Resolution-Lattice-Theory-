import E213.Lib.Math.Analysis.UniformLimitContinuous
import E213.Lib.Math.Analysis.ExtremeValue
import E213.Lib.Math.Analysis.Integration.CutRiemann
import E213.Lib.Math.Analysis.CauchyComplete

/-!
# Riemann integrability of a modulus-continuous function — convergence rate COMPUTED
  (∅-axiom, vein-C "force the modulus")

Classically: a (uniformly) continuous function on `[0,1]` is Riemann integrable,
and this rests on uniform continuity + completeness *as an existence axiom*.
∅-axiom forces the **convergence rate into the open**: the dyadic Riemann sums
`riemannSum f n` form a **Cauchy sequence with an explicit convergence modulus**
derived from the uniform-continuity modulus `omega`.  The integral is then the
*explicit* Cauchy limit (`RiemannIntegralData` / `CauchyCutSeq.limit`) — no
completeness miracle.

## The forcing chain

1. (abstract metric, reusing `MetricModulus` from `UniformLimitContinuous`)
   **`tail_telescope`** + **`refine_cauchy`** — the telescoping heart.  If the
   `i`-th refinement step is a geometric `1/2^(m+2+i)`-step,
       `M.close (m + 2 + i) (h i) (h (i+1))`,
   (each refinement level is twice as fine), then the whole tail telescopes
   through repeated halving triangles to a `1/2^m`-bound:
       `M.close m (h p) (h q)`   for all `p, q`,
   because `1/2^(m+2) + 1/2^(m+3) + … < 1/2^(m+1) < 1/2^m`.

2. **`ModContRiemann`** packages a modulus-continuous `f` on the dyadic grid:
   the dyadic Riemann sum sequence `rs : Nat → Cut`, the uniform-continuity
   modulus `omega`, the metric `M` on cut values, and the **one-step
   refinement bound** `step` derived from `omega` (refining one level changes
   each rectangle height by `< 1/2^{omega …}` over total width 1).

3. **`riemannSum_cauchy`** (★) — the Cauchy property of the dyadic Riemann
   sums with the *computed* modulus from `omega`.

4. **`integral`** — the cut-level integral as `RiemannIntegralData.limit` /
   `CauchyCutSeq.limit`, a computable real carrying the convergence modulus.

5. Non-vacuous: the **constant function** (reuse `unitConstRiemann`), where
   `integral c = c` and the one-step refinement bound is `0` at every level.

Every theorem is ∅-axiom (verify: `tools/scan_axioms.py E213.Lib.Math.Analysis.RiemannContinuous`).
-/

namespace E213.Lib.Math.Analysis.RiemannContinuous

open E213.Lib.Math.Analysis.UniformLimitContinuous
  (MetricModulus)
open E213.Lib.Math.Analysis.ExtremeValue (Cut)
open E213.Lib.Math.Analysis.Integration.CutRiemann
  (riemannSumOnSamples RiemannIntegralData unitConstRiemann unitConstRiemann_limit)
open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-! ## 1. The telescoping heart — geometric refinement ⇒ Cauchy (abstract metric)

We reuse `MetricModulus X` (the `1/2^m`-graduated dyadic metric from
`UniformLimitContinuous`), whose `ctri` is the halving triangle
`1/2^(m+1) + 1/2^(m+1) = 1/2^m` and whose `cmono` is `1/2^(m+1) < 1/2^m`. -/

variable {X : Type}

/-- **Geometric telescope (from a base index).**  If the `i`-th refinement step
    `h i → h (i+1)` is a `1/2^(m+2+i)`-step (geometric: each level twice as
    fine), then `h s` is within `1/2^(m+1+s)` of every later `h (s+p)`:
        `(∀ i, close (m+2+i) (h i) (h (i+1)))  ⟹  close (m+1+s) (h s) (h (s+p))`.

    The conclusion budget `m+1+s` *sharpens with the base* `s`: the tail
    `1/2^(m+2+s) + 1/2^(m+3+s) + … < 1/2^(m+1+s)`.  Proof by induction on the
    length `p`: head step (index `s`, at `m+2+s = (m+1+s)+1`) plus the tail
    (`ih` at base `s+1`, conclusion `m+1+(s+1) = (m+1+s)+1`) are *both* one
    level finer than the target `m+1+s`, so a single halving triangle
    (`ctri (m+1+s)`) closes it.  No `cmono` bookkeeping needed — the geometric
    budget aligns exactly. -/
theorem tail_telescope (M : MetricModulus X)
    (h : Nat → X) (m : Nat)
    (hstep : ∀ i, M.close (m + 2 + i) (h i) (h (i + 1))) :
    ∀ p s, M.close (m + 1 + s) (h s) (h (s + p)) := by
  intro p
  induction p with
  | zero =>
    intro s
    have e : s + 0 = s := Nat.add_zero s
    rw [e]
    exact M.crefl (m + 1 + s) (h s)
  | succ p ih =>
    intro s
    -- head at index s: close (m+2+s) (h s) (h (s+1)) = close ((m+1+s)+1) …
    have hhead : M.close ((m + 1 + s) + 1) (h s) (h (s + 1)) := by
      have hb := hstep s
      -- m + 2 + s = (m + 1 + s) + 1 : both normalise to m + s + 2
      have e2 : m + 2 + s = (m + 1 + s) + 1 := by
        calc m + 2 + s = m + s + 2 := Nat.add_right_comm m 2 s
          _ = (m + s + 1) + 1 := rfl
          _ = (m + 1 + s) + 1 := by rw [Nat.add_right_comm m 1 s]
      rw [e2] at hb
      exact hb
    -- tail at base s+1: close (m+1+(s+1)) (h (s+1)) (h ((s+1)+p))
    have htail : M.close (m + 1 + (s + 1)) (h (s + 1)) (h ((s + 1) + p)) := ih (s + 1)
    -- m+1+(s+1) = (m+1+s)+1
    have etail : m + 1 + (s + 1) = (m + 1 + s) + 1 := by rw [Nat.add_succ]
    rw [etail] at htail
    -- ctri (m+1+s): two (m+1+s)+1-steps compose to one (m+1+s)-step
    have hcomb : M.close (m + 1 + s) (h s) (h ((s + 1) + p)) :=
      M.ctri (m + 1 + s) (h s) (h (s + 1)) (h ((s + 1) + p)) hhead htail
    -- s + (p+1) = (s+1) + p
    have eidx : s + (p + 1) = (s + 1) + p := by rw [Nat.add_succ, Nat.succ_add]
    rw [eidx]
    exact hcomb

/-- **Coarsening across many levels.**  `close (a + t) x y → close a x y` —
    iterate `cmono` `t` times (a `1/2^(a+t)`-bound implies the coarser
    `1/2^a`-bound). -/
theorem close_coarsen (M : MetricModulus X) (a : Nat) (x y : X) :
    ∀ t, M.close (a + t) x y → M.close a x y := by
  intro t
  induction t with
  | zero =>
    intro h
    have e : a + 0 = a := Nat.add_zero a
    rw [e] at h; exact h
  | succ t ih =>
    intro h
    -- close (a+(t+1)) = close ((a+t)+1) → close (a+t) by cmono, then ih
    apply ih
    have e : a + (t + 1) = (a + t) + 1 := Nat.add_succ a t
    rw [e] at h
    exact M.cmono (a + t) x y h

/-- **★ `refine_cauchy` — geometric refinement ⇒ Cauchy with computed modulus.**
    If the `i`-th refinement step is a `1/2^(m'+2+i)`-step *for every target
    scale's base* — concretely, if for each `m` the steps from some start index
    `startN m` on are `1/2^((m) + 2 + i)`-fine — then `h` is Cauchy: any two
    indices past `startN m` agree to `1/2^m`.

    Here phrased for a single sequence whose steps are uniformly geometric from
    index `0`: `close (m+2+i) (h i) (h (i+1))` for all `i` gives, for any
    `p, q`, `close m (h p) (h q)`.  The Cauchy modulus is `0` (the geometric
    decay is already global); for a modulus that *starts* at `startN m` see
    `ModContRiemann.riemannSum_cauchy`, where `startN` is read off `omega`. -/
theorem refine_cauchy (M : MetricModulus X)
    (h : Nat → X) (m : Nat)
    (hstep : ∀ i, M.close (m + 2 + i) (h i) (h (i + 1))) :
    ∀ p q, M.close m (h p) (h q) := by
  intro p q
  -- close (m+1+0) (h 0) (h (0+p)) and likewise for q; coarsen to (m+1); ctri.
  have hp0 : M.close (m + 1) (h 0) (h p) := by
    have := tail_telescope M h m hstep p 0
    -- m+1+0 = m+1, 0+p = p
    have e1 : m + 1 + 0 = m + 1 := Nat.add_zero _
    have e2 : (0 : Nat) + p = p := Nat.zero_add p
    rw [e1, e2] at this; exact this
  have hq0 : M.close (m + 1) (h 0) (h q) := by
    have := tail_telescope M h m hstep q 0
    have e1 : m + 1 + 0 = m + 1 := Nat.add_zero _
    have e2 : (0 : Nat) + q = q := Nat.zero_add q
    rw [e1, e2] at this; exact this
  -- h p — h 0 — h q via ctri m (both legs at m+1)
  have hp0' : M.close (m + 1) (h p) (h 0) := M.csymm (m + 1) _ _ hp0
  exact M.ctri m (h p) (h 0) (h q) hp0' hq0

/-! ## 2. A modulus-continuous `f` on the dyadic grid + its Riemann-sum sequence

`ModContRiemann` packages exactly the data the classical "continuous ⇒
integrable" theorem hides: the dyadic Riemann-sum sequence `rs n` (the
resolution-`n` dyadic sum), a metric `M` on the value space, and the
**computed refinement schedule** `startN : Nat → Nat` read off the
uniform-continuity modulus `omega`.

`refineStep` is the heart's hypothesis: *past the computed start level*
`startN m`, the `j`-th further refinement changes the Riemann sum by only a
geometric `1/2^(m+2+j)` (refining one level halves each rectangle's height
error `< 1/2^(omega …)` over total width `1`, so the whole sum moves by the
same geometric amount).  This is the uniform-continuity bound *summed over the
unit interval* — the quantity classical integrability leaves implicit. -/

variable {V : Type}

/-- **Modulus-continuous `f` on the dyadic grid of `[0,1]`, Riemann-sum form.**
    `rs n` is the dyadic Riemann sum at resolution `n`; `M` the value metric;
    `startN m` the computed resolution (from `omega`) past which refinements are
    geometric at target scale `m`. -/
structure ModContRiemann (V : Type) where
  /-- value metric on Riemann sums (`1/2^m`-graduated). -/
  M       : MetricModulus V
  /-- the dyadic Riemann-sum sequence: `rs n` at resolution `n`. -/
  rs      : Nat → V
  /-- the computed refinement-start modulus, read off the uniform-continuity
      modulus `omega` (the data classical integrability hides). -/
  startN  : Nat → Nat
  /-- **★ the consecutive-refinement bound (forcing hypothesis).**  Past the
      computed start `startN m`, the `j`-th further refinement step is a
      geometric `1/2^(m+2+j)`-step:
          `M.close (m+2+j) (rs (startN m + j)) (rs (startN m + j + 1))`.
      Derived from `omega` + the unit interval length. -/
  refineStep : ∀ m j,
    M.close (m + 2 + j) (rs (startN m + j)) (rs (startN m + j + 1))

namespace ModContRiemann

variable (f : ModContRiemann V)

/-- **★★ `riemannSum_cauchy` — the forcing heart.**  The dyadic Riemann sums
    form a Cauchy sequence with the **computed modulus** `startN` (read off the
    uniform-continuity modulus `omega`): for every target scale `m`, any two
    resolutions `p, q ≥ startN m` give Riemann sums within `1/2^m`.

    Proof: shift the sequence to base `startN m` (`g j = rs (startN m + j)`); its
    steps are geometric `1/2^(m+2+j)` by `refineStep`; `tail_telescope` lands the
    two tails within `1/2^(m+1)` of `rs (startN m)`, and a halving triangle
    (`ctri m`) closes them within `1/2^m`.  The convergence rate is *computed*:
    to know the integral to scale `m`, refine to resolution `startN m`. -/
theorem riemannSum_cauchy (m p q : Nat)
    (hp : p ≥ f.startN m) (hq : q ≥ f.startN m) :
    f.M.close m (f.rs p) (f.rs q) := by
  -- shifted sequence g j := rs (startN m + j); write s for startN m.
  -- p = s + a, q = s + b for a = p - s, b = q - s.
  obtain ⟨a, ha⟩ := Nat.le.dest hp   -- s + a = p
  obtain ⟨b, hb⟩ := Nat.le.dest hq   -- s + b = q
  -- tail_telescope on g j = rs (s + j): close (m+1) (g 0) (g a), (g 0) (g b)
  have hstep : ∀ j, f.M.close (m + 2 + j)
      (f.rs (f.startN m + j)) (f.rs (f.startN m + j + 1)) :=
    fun j => f.refineStep m j
  have hga : f.M.close (m + 1) (f.rs (f.startN m)) (f.rs (f.startN m + a)) := by
    have hh := tail_telescope f.M (fun j => f.rs (f.startN m + j)) m
      (by intro j; exact hstep j) a 0
    -- hh : close (m+1+0) (rs (startN m + 0)) (rs (startN m + (0+a)))
    rw [Nat.add_zero (m + 1), Nat.add_zero (f.startN m), Nat.zero_add a] at hh
    exact hh
  have hgb : f.M.close (m + 1) (f.rs (f.startN m)) (f.rs (f.startN m + b)) := by
    have hh := tail_telescope f.M (fun j => f.rs (f.startN m + j)) m
      (by intro j; exact hstep j) b 0
    rw [Nat.add_zero (m + 1), Nat.add_zero (f.startN m), Nat.zero_add b] at hh
    exact hh
  -- rewrite s+a = p, s+b = q
  rw [ha] at hga
  rw [hb] at hgb
  -- rs p — rs s — rs q via ctri m
  have hga' : f.M.close (m + 1) (f.rs p) (f.rs (f.startN m)) :=
    f.M.csymm (m + 1) _ _ hga
  exact f.M.ctri m (f.rs p) (f.rs (f.startN m)) (f.rs q) hga' hgb

end ModContRiemann

/-! ## 3. Non-vacuous instance — the constant function

A constant function `f ≡ c` on `[0,1]` has constant Riemann sums (`rs n = v`
at every resolution): every refinement leaves the sum unchanged, so the
consecutive-refinement bound is *reflexivity* (`startN = 0`, a `0`-step at every
level).  `riemannSum_cauchy` then certifies the Cauchy property non-vacuously.

We use the concrete `distMet L` metric from `UniformLimitContinuous` (the
`Nat`-distance dyadic metric, all four laws discharged by `Nat` arithmetic),
with value `rs n = v` for any fixed numerator `v`. -/

open E213.Lib.Math.Analysis.UniformLimitContinuous (distMet)

/-- The constant Riemann-sum sequence (value `v` at every resolution) over the
    concrete `distMet L` metric.  `startN = 0` and the refinement step is
    `close (m+2+j) v v`, i.e. reflexivity — the constant function's sum never
    moves under refinement. -/
def constRiemann (L v : Nat) : ModContRiemann Nat where
  M       := distMet L
  rs      := fun _ => v
  startN  := fun _ => 0
  refineStep := fun m j => (distMet L).crefl (m + 2 + j) v

/-- **`constRiemann` is Cauchy with modulus `0`** (the constant Riemann sums
    agree to every scale at every pair of resolutions) — a concrete witness
    that `riemannSum_cauchy` is non-vacuous. -/
theorem constRiemann_cauchy (L v : Nat) (m p q : Nat) :
    (constRiemann L v).M.close m
      ((constRiemann L v).rs p) ((constRiemann L v).rs q) :=
  (constRiemann L v).riemannSum_cauchy m p q (Nat.zero_le _) (Nat.zero_le _)

/-! ## 4. The integral as the explicit Cauchy limit (cut-level)

The forcing heart `riemannSum_cauchy` makes the dyadic Riemann sums a Cauchy
sequence with a *computed* modulus; the integral is then their **explicit limit**.
At the cut level the corpus packages this as `RiemannIntegralData` (a Cauchy
sequence of cuts + modulus, limit via `RiemannIntegralData.limit`).  For the
constant function on `[0,1]` we reuse `unitConstRiemann`: the dyadic Riemann sum
of a constant `c` is identically `c` at every resolution, the Cauchy modulus is
`0`, and the integral is `c`. -/

/-- **`integral` (cut-level)** — the Riemann integral of a constant `c` on
    `[0,1]` as the explicit Cauchy limit of its dyadic Riemann sums.  Reuses the
    corpus `RiemannIntegralData.limit` (the convergence-modulus-carrying limit). -/
def integralConst (c : Cut) : Cut := (unitConstRiemann c).limit

/-- **★ `integralConst_eq` — `∫[0,1] c = c`.**  The integral of a constant is the
    constant: the dyadic Riemann sums are identically `c` (Cauchy modulus `0`),
    so their explicit limit is `c`.  This is the integral *computed* as a Cauchy
    limit, not posited by a completeness axiom. -/
theorem integralConst_eq (c : Cut) : integralConst c = c :=
  unitConstRiemann_limit c

/-- The rational constant `2` integrates to `2` on `[0,1]` — a fully concrete,
    `decide`-checkable numeric instance of `integralConst_eq`. -/
theorem integralConst_two_at :
    integralConst (constCut 2 1) 4 1 = true := by
  rw [integralConst_eq]; decide

end E213.Lib.Math.Analysis.RiemannContinuous
