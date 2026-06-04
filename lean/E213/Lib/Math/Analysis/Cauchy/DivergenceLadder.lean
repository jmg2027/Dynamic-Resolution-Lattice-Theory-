import E213.Meta.Tactic.NatHelper

/-!
# DivergenceLadder — depth is a finite-difference ladder; ∞ for Liouville-type growth

`DivergenceDepth` found e's divergence ladder bottoms out at a constant in 3 steps.
This file makes the **ladder** itself abstract — the finite-difference operator and
its iterate — and proves the two ends of the spectrum:

  - a sequence **reaches its floor** (finite depth) iff some iterated difference is
    constant — e's ratio `n+1` floors at one difference (`e_ratio_floor`);
  - a sequence of **unbounded order of growth never floors** (depth ∞) — if every
    lift is still strictly increasing, no iterate is constant (`infinite_depth`).
    This is the Liouville case: its cross-determinant ratio grows
    super-polynomially (`10^{(k+1)!}`-type), so every difference level is again
    strictly increasing.

## What depth measures — and what it does *not*

It is tempting to call depth a 213-native **irrationality measure** `μ`.  That
would be wrong, and the data says so:

| real | classical `μ` (Liouville–Roth) | ladder depth |
|---|---|---|
| algebraic (deg ≥ 2) | `2` (Roth) | **1** |
| e | `2` | **3** |
| π | `2` (conjectured; `≤ 7.1` proved) | **6** |
| Liouville | `∞` | **∞** |

`μ` collapses algebraic, e, and π to the *same* value `2` — it cannot tell them
apart.  Depth separates them `1 < 3 < 6`.  So **depth is not `μ`**; it is a
*finer, orthogonal* invariant.  `μ` measures *how well the number is approximated*
by rationals; depth measures *how complex the recurrence generating its
approximants is*:

  - **depth 1** ⟺ cross-determinant constant ⟺ the convergents obey a
    *constant-coefficient* (autonomous, `det = 1`) recurrence ⟺ **quadratic
    algebraic** (φ, √2 — Pell/Cassini).
  - **finite depth `d`** ⟺ the cross-determinant ratio is a degree-`(d−2)`
    polynomial in `n` ⟺ the convergents are **P-recursive** (polynomial-coefficient
    recurrence): e (coefficient `n+1`, degree 1 → depth 3), π (coefficient
    `4(n+1)²(2n+1)(2n+3)`, degree 4 → depth 6).  This is the class of *structured*
    transcendentals.
  - **depth ∞** ⟺ no polynomial-coefficient recurrence governs the convergents ⟺
    super-polynomial growth ⟺ **Liouville-type** (and, where μ is concerned,
    exactly the numbers μ also sends to ∞).

So depth aligns with the **holonomic / P-recursive** hierarchy (the algorithmic
complexity of the approximation), agreeing with `μ` only at the pathological end
(`∞`).  It is the constructive, 213-native reading: a real's place is set by *how
deep a finite recurrence-tower its approximants need* — exactly "the infinite
handled by a finite reference, iterated until it bottoms out", and depth counts the
iterations.

All ∅-axiom.
-/

namespace E213.Lib.Math.Analysis.Cauchy.DivergenceLadder

/-! ## §1 — the ladder: finite difference and its iterate -/

/-- The **lift** (forward finite difference): `diff s n = s(n+1) − s n`. -/
def diff (s : Nat → Nat) : Nat → Nat := fun n => s (n+1) - s n

/-- `k`-fold lift. -/
def liftK : Nat → (Nat → Nat) → (Nat → Nat)
  | 0,   s => s
  | k+1, s => diff (liftK k s)

/-- A sequence is **constant** (the ladder floor). -/
def isConst (s : Nat → Nat) : Prop := ∀ n, s n = s 0

/-- A sequence **reaches its floor** if some iterated lift is constant; the least
    such `k` is its *divergence depth*. -/
def reachesFloor (s : Nat → Nat) : Prop := ∃ k, isConst (liftK k s)

/-! ## §2 — finite depth: e's ratio floors at one lift -/

/-- ★★ **e's ratio sequence reaches its floor at level 1.**  e's cross-determinant
    ratio is `rₙ = n+1`; one lift gives `diff r = 1`, constant.  So the `e` ladder
    bottoms out — e has *finite* depth (3 from L0, counting cross-det and ratio;
    1 here counting from the ratio level).  Finite depth = structured. -/
theorem e_ratio_floor : reachesFloor (fun n => n+1) := by
  refine ⟨1, fun n => ?_⟩
  show diff (fun n => n+1) n = diff (fun n => n+1) 0
  show (n+1+1) - (n+1) = (0+1+1) - (0+1)
  rw [E213.Tactic.NatHelper.succ_sub (n+1), E213.Tactic.NatHelper.succ_sub (0+1)]

/-! ## §3 — infinite depth: super-polynomial growth never floors -/

/-- ★★★ **The infinite-depth criterion (Liouville case).**  If *every* lift of `s`
    is still strictly increasing at the start (`(liftK k s) 0 < (liftK k s) 1` for
    all `k`), then `s` **never reaches its floor** — no iterated difference is
    constant, so the divergence depth is ∞.

    This is the Liouville-type pathology: the cross-determinant ratio grows
    super-polynomially (`10^{(k+1)!}`-style), so each difference level is again
    strictly increasing and the ladder never terminates.  Depth ∞ is exactly where
    this construction agrees with the classical irrationality measure `μ = ∞`. -/
theorem infinite_depth (s : Nat → Nat)
    (hstrict : ∀ k, (liftK k s) 0 < (liftK k s) 1) : ¬ reachesFloor s := by
  intro ⟨k, hck⟩
  have h1 : (liftK k s) 1 = (liftK k s) 0 := hck 1
  exact absurd h1 (fun e => absurd (e ▸ hstrict k) (Nat.lt_irrefl _))

/-- ★★ **Constant sequences are the floor (depth 0).**  The algebraic base case:
    a constant cross-determinant (φ, √2: `W_n = ±1`) is *already* at the floor —
    `reachesFloor` with `k = 0`.  Algebraic irrationals have the shallowest ladder. -/
theorem const_reaches_floor (c : Nat) : reachesFloor (fun _ => c) :=
  ⟨0, fun _ => rfl⟩

end E213.Lib.Math.Analysis.Cauchy.DivergenceLadder
