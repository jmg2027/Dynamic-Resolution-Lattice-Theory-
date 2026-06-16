import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.PureNat

/-!
# Uniform limit of continuous functions is continuous — constructive
  (modulus) form (∅-axiom, vein-C)

The honest 213 version of the "3ε" theorem.  Classically: a uniform limit
of continuous functions is continuous.  ∅-axiom forces the content into the
open: the limit's continuity **modulus is computed** from the convergence
rate `r` and a single `f_n`'s modulus `ω_n` — no compactness, no omniscience.

For a target scale `m` the bookkeeping is

    |f x − f y| ≤ |f x − F n x| + |F n x − F n y| + |F n y − f y|

with `n = r (m+2)`.  Each of the three pieces is `< 1/2^(m+2)`; their sum
is `< 3/2^(m+2) < 1/2^m`.  So inputs within `1/2^(ω_n (m+2))` give outputs
within `1/2^m`.  The computed modulus

    Ω m = ω_{r (m+2)} (m+2)

is the whole content — this file proves it, unconditionally and ∅-axiom.

## Representation: an abstract dyadic metric (companion to `ExtremeValue`)

`MetricModulus X` packages a carrier `X` with a relation
`close : Nat → X → X → Prop` read as "within `1/2^m`", together with the
four laws a `1/2^m`-graduated metric satisfies.  The headline is proved
purely from these laws (the 3ε argument is the *halving triangle* applied
twice).  A concrete `Nat`-distance instance (`distMet`) discharges all four
laws by `Nat` arithmetic, so the package is non-vacuous.
-/

namespace E213.Lib.Math.Analysis.UniformLimitContinuous

open E213.Meta.Nat.NatDiv213 (two_cancel_lt)
open E213.Meta.Nat.PureNat (mul_assoc)

/-! ## 1. The dyadic metric structure (`1/2^m`-graduated) -/

/-- **MetricModulus X** — a metric on `X` graduated by the dyadic scale
    `1/2^m`.  `close m a b` reads "`a` and `b` are within `1/2^m`".

    The four laws are exactly what a real `1/2^m`-metric obeys:
    * `crefl` — a point is within `1/2^m` of itself (distance `0`);
    * `csymm` — symmetry of the distance;
    * `cmono` — a finer bound implies a coarser one (`1/2^(m+1) < 1/2^m`);
    * `ctri` — the **halving triangle**: two `1/2^(m+1)`-steps compose to a
      `1/2^m`-step (the `ε/2 + ε/2 = ε` law, the heart of the 3ε proof). -/
structure MetricModulus (X : Type) where
  /-- `close m a b`: `a` and `b` are within `1/2^m` of each other. -/
  close : Nat → X → X → Prop
  /-- reflexivity: every point is within `1/2^m` of itself. -/
  crefl : ∀ m a, close m a a
  /-- symmetry of the metric. -/
  csymm : ∀ m a b, close m a b → close m b a
  /-- monotonicity in the scale: `1/2^(m+1) < 1/2^m`. -/
  cmono : ∀ m a b, close (m + 1) a b → close m a b
  /-- **halving triangle**: `1/2^(m+1) + 1/2^(m+1) = 1/2^m`. -/
  ctri  : ∀ m a b c, close (m + 1) a b → close (m + 1) b c → close m a c

namespace MetricModulus

variable {X : Type} (M : MetricModulus X)

/-- **Quarter triangle (4-fold)**: three `1/2^(m+2)`-steps compose to a
    `1/2^m`-step — `3/2^(m+2) < 1/2^m`.  This is the precise statement that
    powers the 3ε argument: the two outer convergence gaps plus the inner
    continuity gap, each `< 1/2^(m+2)`, sum to `< 1/2^m`.

    Proof: `close (m+2) a b ∧ close (m+2) b c ⇒ close (m+1) a c` (one halving
    triangle), then together with `close (m+2) c d ⇒ close (m+1) c d` (mono)
    a second halving triangle gives `close m a d`. -/
theorem qtri (m : Nat) (a b c d : X)
    (hab : M.close (m + 2) a b) (hbc : M.close (m + 2) b c)
    (hcd : M.close (m + 2) c d) : M.close m a d := by
  -- a —(m+1)— c  via the halving triangle on the two (m+2)-steps a–b, b–c
  have hac : M.close (m + 1) a c := M.ctri (m + 1) a b c hab hbc
  -- c —(m+1)— d  by monotonicity from the (m+2)-step c–d
  have hcd' : M.close (m + 1) c d := M.cmono (m + 1) c d hcd
  -- a —(m)— d  by a second halving triangle
  exact M.ctri m a c d hac hcd'

end MetricModulus

/-! ## 2. Continuity-with-modulus and uniform convergence-with-rate

We fix a domain carrier `D` with its own dyadic metric `MD`, and a codomain
carrier `V` with metric `MV`.  A function is `D → V`. -/

variable {D V : Type}

/-- **ContinuousWithModulus MD MV f ω** — `f : D → V` is uniformly continuous
    with explicit modulus `ω : Nat → Nat`: inputs within `1/2^(ω m)` map to
    outputs within `1/2^m`.  (Uniform: the same `ω` works at every point —
    the clean form for the unconditional theorem.) -/
def ContinuousWithModulus
    (MD : MetricModulus D) (MV : MetricModulus V)
    (f : D → V) (ω : Nat → Nat) : Prop :=
  ∀ m x y, MD.close (ω m) x y → MV.close m (f x) (f y)

/-- **UnifConv MV F f r** — the sequence `F : Nat → (D → V)` converges to
    `f : D → V` **uniformly** with explicit rate `r : Nat → Nat`: for every
    scale `m` and every index `n ≥ r m`, `F n` is within `1/2^m` of `f` at
    *every* point `x` (uniform = the same `r` for all `x`). -/
def UnifConv
    (MV : MetricModulus V)
    (F : Nat → (D → V)) (f : D → V) (r : Nat → Nat) : Prop :=
  ∀ m, ∀ n, n ≥ r m → ∀ x, MV.close m (F n x) (f x)

/-! ## 3. The headline: the computed modulus `Ω m = ω_{r(m+2)}(m+2)` -/

/-- **★★ `uniform_limit_continuous` — the headline (∅-axiom, constructive).**

    If every `F n` is uniformly continuous with modulus `ω_ : Nat → Nat → Nat`
    (`ω_ n` is the modulus of `F n`), and `F → f` uniformly with rate `r`,
    then the limit `f` is uniformly continuous with the **explicitly computed**
    modulus

        Ω m = ω_ (r (m+2)) (m+2).

    The modulus is *computed* from the convergence rate `r` and a single
    `f_n`'s modulus `ω_ (r (m+2))` — no compactness, no omniscience, no `LPO`.
    Continuity of the limit is not a non-constructive miracle: the data
    determine the new modulus.

    Proof (the 3ε bookkeeping).  Fix `m`, points `x y` with
    `MD.close (Ω m) x y`, i.e. `MD.close (ω_ n (m+2)) x y` for `n = r (m+2)`.
      * continuity of `F n` at scale `m+2`: `MV.close (m+2) (F n x) (F n y)`;
      * convergence at `x`: `MV.close (m+2) (f x) (F n x)`
        (symmetrised from `F n x → f x`);
      * convergence at `y`: `MV.close (m+2) (F n y) (f y)`.
    Chain `f x — F n x — F n y — f y` with the **quarter triangle**
    (`3/2^(m+2) < 1/2^m`) to land `MV.close m (f x) (f y)`. -/
theorem uniform_limit_continuous
    (MD : MetricModulus D) (MV : MetricModulus V)
    (F : Nat → (D → V)) (f : D → V)
    (ω_ : Nat → Nat → Nat) (r : Nat → Nat)
    (hcont : ∀ n, ContinuousWithModulus MD MV (F n) (ω_ n))
    (hconv : UnifConv MV F f r) :
    ContinuousWithModulus MD MV f (fun m => ω_ (r (m + 2)) (m + 2)) := by
  intro m x y hxy
  -- `hxy : MD.close (ω_ (r (m+2)) (m+2)) x y` after beta reduction.
  -- the index whose modulus we borrowed is `n = r (m+2)`.
  -- continuity of F n at scale m+2 (hxy is exactly its modulus hypothesis)
  have hFxy : MV.close (m + 2) (F (r (m + 2)) x) (F (r (m + 2)) y) :=
    hcont (r (m + 2)) (m + 2) x y hxy
  -- convergence at x and y at scale m+2 (n ≥ r (m+2) by reflexivity)
  have hge : r (m + 2) ≥ r (m + 2) := Nat.le_refl _
  have hfx : MV.close (m + 2) (F (r (m + 2)) x) (f x) :=
    hconv (m + 2) (r (m + 2)) hge x
  have hfy : MV.close (m + 2) (F (r (m + 2)) y) (f y) :=
    hconv (m + 2) (r (m + 2)) hge y
  -- symmetrise the x-gap so the chain reads  f x — F n x — F n y — f y
  have hxf : MV.close (m + 2) (f x) (F (r (m + 2)) x) :=
    MV.csymm (m + 2) _ _ hfx
  -- quarter triangle: three (m+2)-steps compose to one m-step
  exact MV.qtri m (f x) (F (r (m + 2)) x) (F (r (m + 2)) y) (f y) hxf hFxy hfy

/-! ## 4. Concrete instance — the `Nat`-distance dyadic metric

To certify the package is non-vacuous we exhibit a concrete `MetricModulus`.

Values are `Nat` numerators over a *fixed* denominator `2^(L+1)` (we take the
denominator `≥ 2` so the metric is non-degenerate).  "`a` within `1/2^m`"
means `2^m · distN a b < 2^(L+1)`, where `distN a b = (a − b) + (b − a)` is
the truncated-subtraction `Nat` distance (`= |a − b|`).  All four metric laws
are pure `Nat` arithmetic. -/

/-- Truncated-subtraction distance on `Nat`:  `distN a b = |a − b|`. -/
def distN (a b : Nat) : Nat := (a - b) + (b - a)

/-- `distN` is symmetric. -/
theorem distN_symm (a b : Nat) : distN a b = distN b a :=
  Nat.add_comm (a - b) (b - a)

/-- `distN a a = 0`. -/
theorem distN_self (a : Nat) : distN a a = 0 := by
  show (a - a) + (a - a) = 0
  rw [Nat.sub_self]

/-- `n ≤ n.pred + 1` — unconditional (succ of pred dominates). -/
theorem le_pred_succ (n : Nat) : n ≤ n.pred + 1 := by
  cases n with
  | zero   => exact Nat.zero_le _
  | succ k => exact Nat.le_refl (k + 1)

/-- `a ≤ (a - b) + b` — unconditional `Nat` truncated subtraction, ∅-axiom
    (Lean-core `Nat.sub_le_iff_le_add` pulls `propext`; proved by induction
    on `b` with `le_pred_succ`). -/
theorem le_sub_add : ∀ (b a : Nat), a ≤ (a - b) + b := by
  intro b
  induction b with
  | zero => intro a; exact Nat.le_refl a
  | succ b ih =>
      intro a
      have hstep : (a - b) + b ≤ ((a - b).pred + 1) + b :=
        Nat.add_le_add_right (le_pred_succ (a - b)) b
      have heq : ((a - b).pred + 1) + b = (a - b).pred + (b + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 b]
      have hsub : a - (b + 1) = (a - b).pred := rfl
      calc a ≤ (a - b) + b := ih a
        _ ≤ ((a - b).pred + 1) + b := hstep
        _ = (a - b).pred + (b + 1) := heq
        _ = (a - (b + 1)) + (b + 1) := by rw [hsub]

/-- `(k + c) - c = k` — ∅-axiom (Lean-core `Nat.add_sub_cancel` pulls
    `propext`; proved by induction on `c` with `Nat.succ_sub_succ`). -/
theorem add_sub_cancel_p (k : Nat) : ∀ c, (k + c) - c = k := by
  intro c
  induction c with
  | zero => rfl
  | succ c ih =>
      show (k + (c + 1)) - (c + 1) = k
      rw [← Nat.add_assoc k c 1, Nat.succ_sub_succ]
      exact ih

/-- `a ≤ k + c → a - c ≤ k` — ∅-axiom twin of `Nat.sub_le_iff_le_add.mpr`. -/
theorem sub_le_of_le_add {a c k : Nat} (h : a ≤ k + c) : a - c ≤ k :=
  calc a - c ≤ (k + c) - c := Nat.sub_le_sub_right h c
    _ = k := add_sub_cancel_p k c

/-- One-sided bound feeding the triangle inequality:
    `a - c ≤ (a - b) + (b - c)`.  Pure `Nat` truncated-subtraction. -/
theorem sub_tri (a b c : Nat) : a - c ≤ (a - b) + (b - c) := by
  -- via sub_le_of_le_add: suffices a ≤ ((a-b)+(b-c)) + c, RHS ≥ (a-b)+b ≥ a.
  apply sub_le_of_le_add
  have hbc : b ≤ (b - c) + c := le_sub_add c b
  have hab : a ≤ (a - b) + b := le_sub_add b a
  have step : (a - b) + b ≤ (a - b) + ((b - c) + c) :=
    Nat.add_le_add_left hbc (a - b)
  have hassoc : (a - b) + ((b - c) + c) = ((a - b) + (b - c)) + c :=
    (Nat.add_assoc (a - b) (b - c) c).symm
  rw [hassoc] at step
  exact Nat.le_trans hab step

/-- **Triangle inequality** for `distN`:  `|a − c| ≤ |a − b| + |b − c|`. -/
theorem distN_tri (a b c : Nat) : distN a c ≤ distN a b + distN b c := by
  -- distN a c = (a - c) + (c - a); bound each leg by sub_tri.
  have hac : a - c ≤ (a - b) + (b - c) := sub_tri a b c
  have hca : c - a ≤ (c - b) + (b - a) := sub_tri c b a
  -- add the two; regroup into (distN a b) + (distN b c).
  have hsum : (a - c) + (c - a)
      ≤ ((a - b) + (b - c)) + ((c - b) + (b - a)) :=
    Nat.add_le_add hac hca
  -- ((a-b)+(b-c)) + ((c-b)+(b-a)) = ((a-b)+(b-a)) + ((b-c)+(c-b))
  --   = distN a b + distN b c   (rearrange the four summands)
  have hrearr : ((a - b) + (b - c)) + ((c - b) + (b - a))
      = ((a - b) + (b - a)) + ((b - c) + (c - b)) := by
    -- pure commutative-monoid rearrangement of four Nat summands
    have e1 : ((a - b) + (b - c)) + ((c - b) + (b - a))
        = (a - b) + ((b - c) + ((c - b) + (b - a))) :=
      Nat.add_assoc (a - b) (b - c) ((c - b) + (b - a))
    rw [e1]
    have e2 : (b - c) + ((c - b) + (b - a))
        = ((b - c) + (c - b)) + (b - a) :=
      (Nat.add_assoc (b - c) (c - b) (b - a)).symm
    rw [e2]
    have e3 : (b - c) + (c - b) = (c - b) + (b - c) := Nat.add_comm _ _
    rw [show (a - b) + (((b - c) + (c - b)) + (b - a))
          = ((a - b) + ((b - c) + (c - b))) + (b - a) from
        (Nat.add_assoc (a - b) ((b - c) + (c - b)) (b - a)).symm]
    -- now both sides are sums of {(a-b),(b-a),(b-c),(c-b)}; finish by assoc/comm
    rw [show (a - b) + ((b - c) + (c - b)) = ((a - b) + (b - c)) + (c - b) from
        (Nat.add_assoc (a - b) (b - c) (c - b)).symm]
    -- LHS now: (((a-b)+(b-c))+(c-b)) + (b-a)
    -- RHS:     ((a-b)+(b-a)) + ((b-c)+(c-b))
    rw [show ((a - b) + (b - a)) + ((b - c) + (c - b))
          = (a - b) + ((b - a) + ((b - c) + (c - b))) from
        Nat.add_assoc (a - b) (b - a) ((b - c) + (c - b))]
    rw [Nat.add_assoc ((a - b) + (b - c)) (c - b) (b - a)]
    rw [Nat.add_assoc (a - b) (b - c) ((c - b) + (b - a))]
    -- LHS: (a-b) + ((b-c) + ((c-b)+(b-a)))   RHS: (a-b) + ((b-a)+((b-c)+(c-b)))
    rw [show (b - c) + ((c - b) + (b - a)) = ((b - c) + (c - b)) + (b - a) from
        (Nat.add_assoc (b - c) (c - b) (b - a)).symm]
    rw [show (b - a) + ((b - c) + (c - b)) = ((b - c) + (c - b)) + (b - a) from
        Nat.add_comm (b - a) ((b - c) + (c - b))]
  show (a - c) + (c - a) ≤ distN a b + distN b c
  have : distN a b + distN b c
      = ((a - b) + (b - a)) + ((b - c) + (c - b)) := rfl
  rw [this, ← hrearr]
  exact hsum

/-- The concrete metric relation: `a` within `1/2^m` of `b` over denominator
    `2^(L+1)`, i.e. `2^m · |a − b| < 2^(L+1)`. -/
def closeN (L : Nat) (m a b : Nat) : Prop := 2 ^ m * distN a b < 2 ^ (L + 1)

/-- Reflexivity of `closeN`: `2^m · 0 = 0 < 2^(L+1)`. -/
theorem closeN_refl (L m a : Nat) : closeN L m a a := by
  show 2 ^ m * distN a a < 2 ^ (L + 1)
  rw [distN_self a, Nat.mul_zero]
  exact Nat.pos_pow_of_pos (L + 1) (by decide)

/-- Symmetry of `closeN` (from `distN` symmetry). -/
theorem closeN_symm (L m a b : Nat) (h : closeN L m a b) : closeN L m b a := by
  show 2 ^ m * distN b a < 2 ^ (L + 1)
  rw [distN_symm b a]; exact h

/-- Monotonicity in the scale:  `closeN L (m+1) a b → closeN L m a b`.
    `2^m · d ≤ 2^(m+1) · d < 2^(L+1)`. -/
theorem closeN_mono (L m a b : Nat) (h : closeN L (m + 1) a b) :
    closeN L m a b := by
  show 2 ^ m * distN a b < 2 ^ (L + 1)
  have hpow : 2 ^ m ≤ 2 ^ (m + 1) := by
    rw [Nat.pow_succ]
    calc 2 ^ m = 2 ^ m * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ m * 2 := Nat.mul_le_mul_left _ (by decide)
  have hle : 2 ^ m * distN a b ≤ 2 ^ (m + 1) * distN a b :=
    Nat.mul_le_mul_right _ hpow
  exact Nat.lt_of_le_of_lt hle h

/-- **Halving triangle** for `closeN`: two `1/2^(m+1)`-steps compose to a
    `1/2^m`-step.  The arithmetic heart: from `2·X < 2^(L+1)` and
    `2·Y < 2^(L+1)` we get `X + Y < 2^(L+1)`, and `2^m·|a−c| ≤ X + Y`. -/
theorem closeN_tri (L m a b c : Nat)
    (hab : closeN L (m + 1) a b) (hbc : closeN L (m + 1) b c) :
    closeN L m a c := by
  show 2 ^ m * distN a c < 2 ^ (L + 1)
  -- abbreviations X = 2^m·d(a,b), Y = 2^m·d(b,c)
  -- hab : 2^(m+1)·d(a,b) < 2^(L+1), i.e. 2·X < 2^(L+1)
  have hX : 2 * (2 ^ m * distN a b) < 2 ^ (L + 1) := by
    have : 2 ^ (m + 1) * distN a b = 2 * (2 ^ m * distN a b) := by
      rw [Nat.pow_succ]
      -- 2^m * 2 * d = 2 * (2^m * d)
      rw [Nat.mul_comm (2 ^ m) 2, mul_assoc]
    rw [← this]; exact hab
  have hY : 2 * (2 ^ m * distN b c) < 2 ^ (L + 1) := by
    have : 2 ^ (m + 1) * distN b c = 2 * (2 ^ m * distN b c) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, mul_assoc]
    rw [← this]; exact hbc
  -- X + Y < 2^(L+1) :  2(X+Y) = 2X + 2Y < 2^(L+1) + 2^(L+1) = 2·2^(L+1)
  have hsum2 : 2 * ((2 ^ m * distN a b) + (2 ^ m * distN b c))
      < 2 * 2 ^ (L + 1) := by
    rw [Nat.mul_add]
    calc 2 * (2 ^ m * distN a b) + 2 * (2 ^ m * distN b c)
        < 2 ^ (L + 1) + 2 * (2 ^ m * distN b c) :=
          Nat.add_lt_add_right hX _
      _ < 2 ^ (L + 1) + 2 ^ (L + 1) :=
          Nat.add_lt_add_left hY _
      _ = 2 * 2 ^ (L + 1) := by rw [Nat.two_mul]
  have hsum : (2 ^ m * distN a b) + (2 ^ m * distN b c) < 2 ^ (L + 1) :=
    two_cancel_lt _ _ hsum2
  -- 2^m·d(a,c) ≤ 2^m·(d(a,b)+d(b,c)) = 2^m·d(a,b) + 2^m·d(b,c) < 2^(L+1)
  have htri : 2 ^ m * distN a c
      ≤ 2 ^ m * (distN a b + distN b c) :=
    Nat.mul_le_mul_left _ (distN_tri a b c)
  have hdistr : 2 ^ m * (distN a b + distN b c)
      = (2 ^ m * distN a b) + (2 ^ m * distN b c) := Nat.mul_add _ _ _
  rw [hdistr] at htri
  exact Nat.lt_of_le_of_lt htri hsum

/-- **distMet L** — the concrete `Nat`-distance dyadic metric over denominator
    `2^(L+1)`.  Discharges all four `MetricModulus` laws by pure `Nat`
    arithmetic, certifying the package is inhabited (the headline is not
    vacuous). -/
def distMet (L : Nat) : MetricModulus Nat where
  close := closeN L
  crefl := fun m a => closeN_refl L m a
  csymm := fun m a b h => closeN_symm L m a b h
  cmono := fun m a b h => closeN_mono L m a b h
  ctri  := fun m a b c hab hbc => closeN_tri L m a b c hab hbc

/-! ## 5. Inhabitance of the hypotheses — a genuinely-varying example

`F n = ` the identity on `Nat` for all `n` is the trivial uniform limit, but
to exhibit a non-degenerate witness we take `F n x = f x` for all `n` (any
`f`).  Then:
* every `F n` shares `f`'s modulus (`hcont`);
* `F → f` uniformly with rate `r = fun _ => 0` (the gap is `0` at every `n`).

`uniform_limit_continuous` then yields the computed modulus for `f` — so the
headline's conclusion is a real, inhabited statement.  (A genuinely varying
`F n ≠ f` would converge with a nontrivial `r`; the same theorem applies, the
modulus `Ω m = ω_{r(m+2)}(m+2)` simply borrows from a deeper index.) -/

/-- The identity function on `Nat` is uniformly continuous in the concrete
    metric `distMet L` with modulus `ω = id`:  inputs within `1/2^m` map to
    outputs within `1/2^m` (identity preserves the distance exactly). -/
theorem id_continuousWithModulus (L : Nat) :
    ContinuousWithModulus (distMet L) (distMet L)
      (fun x : Nat => x) (fun m => m) := by
  intro m x y hxy
  -- close m (id x) (id y) = close m x y = hxy
  exact hxy

/-- **Inhabitance witness.**  For the constant sequence `F n = f` (here
    `f = id` on `Nat` in the metric `distMet L`):  every `F n` is continuous
    with modulus `id`, and `F → f` uniformly with rate `0`.  Hence
    `uniform_limit_continuous` certifies `f` continuous with the computed
    modulus `Ω m = id (m+2) = m+2`.  This instantiates the headline on a
    concrete, non-vacuous metric. -/
theorem inhabited_uniform_limit (L : Nat) :
    ContinuousWithModulus (distMet L) (distMet L)
      (fun x : Nat => x) (fun m : Nat => m + 2) := by
  -- F n = id for all n; ω_ n = id; r = fun _ => 0.
  have hcont : ∀ n : Nat, ContinuousWithModulus (distMet L) (distMet L)
      (fun x : Nat => x) (fun m : Nat => m) := fun _ => id_continuousWithModulus L
  have hconv : UnifConv (distMet L)
      (fun _ : Nat => fun x : Nat => x) (fun x : Nat => x) (fun _ => 0) := by
    intro m n _ x
    -- (F n x) = x = f x, so close m x x by reflexivity
    exact (distMet L).crefl m x
  -- assemble: Ω m = ω_ (r (m+2)) (m+2) = id (m+2) = m+2.
  exact uniform_limit_continuous (distMet L) (distMet L)
    (fun _ : Nat => fun x : Nat => x) (fun x : Nat => x)
    (fun _ : Nat => fun m : Nat => m) (fun _ : Nat => 0) hcont hconv

end E213.Lib.Math.Analysis.UniformLimitContinuous
