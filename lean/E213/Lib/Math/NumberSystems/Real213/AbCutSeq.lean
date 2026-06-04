import E213.Lib.Math.Cauchy.MonotonicBounded
import E213.Lib.Math.NumberSystems.Real213.Core.ValidCut
import E213.Lib.Math.Analysis.CauchyCompleteValid

/-!
# AbCutSeq — every monotone-bounded ab-sequence is a `Real213` cut

`EulerCut` (e) and `PiCut` (π/2, π) each lifted a rational climbing sequence from
the `Cauchy/MonotonicBounded` Raw level to the `Real213` `ValidCut` level, and the
machinery was *identical*: each layer is a `ValidCut`+`RatioCut`, a `false`
reading is nested forward, the sequence is eventually constant at any witnessed
threshold, and it completes (given a modulus) to a `ValidCut` limit.

This file extracts that shared structure once.  An `AbCutSeq` is any sequence of
`Raw`s that is **ab-monotone** (`IsAbMonotonic`, the rationals climb) with
**positive denominators** (`IsAbPositiveB`).  From those two facts alone the whole
cut interface follows — generically, ∅-axiom:

  * `cut n` — the layer-n rational read as a Cut (`decide (aₙ·k ≤ bₙ·m)`,
    definitionally a `constCut`), hence a `ValidCut` and a `RatioCut`;
  * `cut_false_fwd` — **nesting**: a `false` reading persists at every later layer
    (the monotone-chain engine `orderProj_false_propagates`);
  * `cut_eventually_const` — eventual constancy at any `false`-witnessed `(m,k)`;
  * `toCauchy` / `toCauchy_limit_valid` — completion (given a modulus) to a
    `CauchyCutSeq` whose limit is a `ValidCut`, via `CauchyCutSeq.limit_valid`.

`EulerCut` and `PiCut` are now thin instances: they supply the `AbCutSeq` (from
`euler_isAbMonotonic`/`wallis_isAbMonotonic`) and add only their concrete
*localization* (which rational bracket pins the constant), which is genuinely
per-constant.

The completion's modulus is, for a transcendental, a **hypothesis** — a total
`N(m,k)` would be the global order-Cauchy closure that `Cauchy/MonotonicBounded`
(§180–194) refuses as smuggled LEM.  Algebraic constants (φ) supply a closed-form
modulus and complete unconditionally; the structure here is the common spine.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213

open E213.Theory (Raw)
open E213.Lib.Math.Cauchy.MonotonicBounded
open E213.Lib.Math.Cauchy.Archimedean (orderProj)
open E213.Lens.Instances.AB (abLens)
open E213.Lib.Math.NumberSystems.Real213.Core.ValidCut
open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)

/-- A monotone, positive-denominator ab-sequence — the structural carrier shared
    by Euler (e), Wallis (π/2), and any constructive real built as a climbing
    sequence of rationals.  (Algebraic φ also fits, though it additionally has a
    closed-form cut.) -/
structure AbCutSeq where
  xs : Nat → Raw
  mono : IsAbMonotonic xs
  pos : IsAbPositiveB xs

namespace AbCutSeq

/-- **Layer-n cut**: `decide (aₙ·k ≤ bₙ·m)`, the layer-n rational read as a Cut.
    Definitionally a `constCut (aₙ) (bₙ)`. -/
def cut (S : AbCutSeq) (n : Nat) : Nat → Nat → Bool :=
  fun m k => orderProj m k (abLens.view (S.xs n))

/-- ★ Each layer cut is a `ValidCut` (monotone in `m`, antitone in `k`). -/
theorem cut_valid (S : AbCutSeq) (n : Nat) : ValidCut (S.cut n) := constCut_valid _ _

/-- ★ Each layer cut is a `RatioCut` (respects rational ordering). -/
theorem cut_ratio (S : AbCutSeq) (n : Nat) : RatioCut (S.cut n) := constCut_ratio _ _

/-- ★★ **Nesting**: a `false` reading at layer `N` persists at every later layer.
    The rationals climb toward the limit, so once they exceed `m/k` they stay
    above it.  This is the monotone-chain engine `orderProj_false_propagates`. -/
theorem cut_false_fwd (S : AbCutSeq) (m k N : Nat) (hN : S.cut N m k = false)
    (i : Nat) (hi : i ≥ N) : S.cut i m k = false :=
  orderProj_false_propagates S.xs S.mono S.pos m k N hN i hi

/-- ★★ **Eventual constancy** at a `false`-witnessed threshold — the per-`(m,k)`
    order-Cauchy property, exactly the field a `CauchyCutSeq` needs. -/
theorem cut_eventually_const (S : AbCutSeq) (m k N₀ : Nat)
    (hN₀ : S.cut N₀ m k = false) :
    ∀ i j, i ≥ N₀ → j ≥ N₀ → S.cut i m k = S.cut j m k := by
  intro i j hi hj
  rw [S.cut_false_fwd m k N₀ hN₀ i hi, S.cut_false_fwd m k N₀ hN₀ j hj]

/-- **Completion to a `CauchyCutSeq`**, given a supplied modulus witnessing the
    order-Cauchy property.  For a transcendental the modulus is a hypothesis (no
    LEM-free total cut); the moment it is given, completion proceeds. -/
def toCauchy (S : AbCutSeq) (N : Nat → Nat → Nat)
    (hc : ∀ m k i j, i ≥ N m k → j ≥ N m k → S.cut i m k = S.cut j m k) :
    CauchyCutSeq where
  cs := S.cut
  N := N
  cauchy := hc

/-- ★★★ **The completed limit is a real (`ValidCut`).**  Directly from the general
    completeness `CauchyCutSeq.limit_valid`, since every layer cut is valid.  Any
    monotone-bounded ab-sequence is a bona fide `Real213` cut wherever completed. -/
theorem toCauchy_limit_valid (S : AbCutSeq) (N : Nat → Nat → Nat)
    (hc : ∀ m k i j, i ≥ N m k → j ≥ N m k → S.cut i m k = S.cut j m k) :
    ValidCut (S.toCauchy N hc).limit :=
  (S.toCauchy N hc).limit_valid (fun i => S.cut_valid i)

/-- ★★★ **The completed limit inherits any localization bracket.**  If the layer
    cuts read `false` at the lower rational `lm/lk` from layer `nl` on, and `true`
    at the upper rational `um/uk` at every layer, then the limit reads `false` at
    `lm/lk` and `true` at `um/uk` — provided the supplied modulus reached `nl`
    there (`N lm lk ≥ nl`).  The limit is pinned strictly inside the bracket as a
    real cut, not merely the approximants.

    This is the generic localization-transport: each constant (e in (8/3,3), π in
    (14/5,4), …) instantiates it with its own bracket and `decide`-checked
    witnesses, instead of re-deriving the inheritance by hand. -/
theorem limit_brackets (S : AbCutSeq) (N : Nat → Nat → Nat)
    (hc : ∀ m k i j, i ≥ N m k → j ≥ N m k → S.cut i m k = S.cut j m k)
    (lm lk um uk nl : Nat)
    (hlow : ∀ n, n ≥ nl → S.cut n lm lk = false)
    (hup : ∀ n, S.cut n um uk = true)
    (hreach : N lm lk ≥ nl) :
    (S.toCauchy N hc).limit lm lk = false
    ∧ (S.toCauchy N hc).limit um uk = true := by
  refine ⟨?_, ?_⟩
  · show S.cut (N lm lk) lm lk = false
    exact hlow (N lm lk) hreach
  · show S.cut (N um uk) um uk = true
    exact hup (N um uk)

end AbCutSeq

end E213.Lib.Math.NumberSystems.Real213
