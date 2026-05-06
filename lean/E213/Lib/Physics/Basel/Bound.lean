import E213.Lib.Physics.Simplex.Counts

/-!
# Basel partial sum S(N) — rational approximation to ζ(2)

In standard formulation, ζ(2) = π²/6 enters DRLT via
    1/α_GUT = d² · ζ(2)
But ζ(2) is the *infinite* limit of finite rational sums.

On the finite discrete lattice, we replace ζ(2) by `S N` at
sufficient resolution N, with explicit *rational* error bounds:

  Loose (telescoping from `1/n² < 1/(n(n-1))`):
      S(N) ≤ ζ(2) ≤ upper(N) := S(N) + 1/N

  Tight two-sided (telescoping from `1/n² > 1/(n(n+1))` on the lower):
      lower_tight(N) := S(N) + 1/(N+1)  ≤  ζ(2)  ≤  upper(N)
      width = 1/N − 1/(N+1) = 1/(N(N+1))   (quadratic improvement)

Both endpoints are rational.  ζ(2) itself is never needed as a
Lean term — only its rational interval bracket.

This file defines S, upper, lower_tight, and proves concrete
bracket facts at N = 2, 3, 10, 20, 30, 50, all 0-axiom decide-checked.

Convention: rationals as unreduced `(Nat × Nat)` = `(num, den)`,
matching `ABLens.view`.  Comparison via cross-multiplication.

Consolidation note (2026-05-05): formerly split into `Bound.lean`
(loose endpoints + concrete N=2,3) and `BoundTight.lean` (tight
two-sided + N=10,20,30,50).  Merged here per
`research-notes/CONSOLIDATION_PROTOCOL.md`.
-/

namespace E213.Lib.Physics.Basel.Bound

/-- Partial Basel sum S(N) = Σ_{n=1}^N 1/n² as `(num, den)`.
    Recursion: S(n+1) = S(n) + 1/(n+1)². -/
def S : Nat → (Nat × Nat)
  | 0     => (0, 1)
  | n + 1 =>
    let p := S n
    let k := (n + 1) * (n + 1)
    (p.1 * k + p.2, p.2 * k)

theorem S_0 : S 0 = (0, 1) := rfl
theorem S_1 : S 1 = (1, 1) := by decide
theorem S_2 : S 2 = (5, 4) := by decide
theorem S_3 : S 3 = (49, 36) := by decide

/-- Upper bracket: upper(N) = S(N) + 1/N (telescoping bound).
    Proof of ζ(2) ≤ upper(N) uses 1/n² < 1/(n(n-1)) for n ≥ 2 and
    telescoping; not needed as a Lean theorem because we only use
    upper(N) as a *rational* interval endpoint. -/
def upper : Nat → (Nat × Nat)
  | 0     => (2, 1)  -- crude placeholder
  | N + 1 =>
    let p := S (N + 1)
    (p.1 * (N + 1) + p.2, p.2 * (N + 1))

theorem upper_2 : upper 2 = (14, 8) := by decide   -- = 7/4
theorem upper_3 : upper 3 = (183, 108) := by decide -- = 61/36

/-- Cross-multiplication comparison on `(Nat × Nat)` as rationals. -/
def lt (p q : Nat × Nat) : Bool := p.1 * q.2 < q.1 * p.2

/-- S is strictly increasing (verified at small N). -/
theorem mono_1_2 : lt (S 1) (S 2) = true := by decide
theorem mono_2_3 : lt (S 2) (S 3) = true := by decide

/-- upper is strictly *decreasing* (better bracket as N grows). -/
theorem upper_mono_2_3 : lt (upper 3) (upper 2) = true := by decide

/-- Bracket: S(N) < upper(N) at concrete N. -/
theorem bracket_2 : lt (S 2) (upper 2) = true := by decide
theorem bracket_3 : lt (S 3) (upper 3) = true := by decide

/-- Bracket width at N=3 is exactly 1/3 (telescoping):
      upper(3) - S(3) = 61/36 - 49/36 = 12/36 = 1/3.
    In cross-mult form: (u.1·s.2 - s.1·u.2) · 3 = s.2 · u.2. -/
theorem bracket_width_3 :
    let s := S 3; let u := upper 3
    (u.1 * s.2 - s.1 * u.2) * 3 = s.2 * u.2 := by decide

/-- Concrete endpoints: S(3) = 49/36 ≤ ζ(2) ≤ 183/108 = upper(3).
    All rational, all `decide`-checked. ζ(2) never appears as a Lean
    term — only the rational bracket endpoints. -/
theorem bracket_endpoints_3 :
    S 3 = (49, 36) ∧ upper 3 = (183, 108) := by decide

-- ═══ Tight two-sided bracket (formerly BoundTight.lean) ═══

/-- Tight lower bound: S(N) + 1/(N+1) as `(num, den)`. -/
def lower_tight (N : Nat) : (Nat × Nat) :=
  let s := S N
  (s.1 * (N + 1) + s.2, s.2 * (N + 1))

theorem lower_tight_2 : lower_tight 2 = (5 * 3 + 4, 4 * 3) := by decide
theorem lower_tight_3 : lower_tight 3 = (49 * 4 + 36, 36 * 4) := by decide

/-- lower_tight < upper at concrete N (sanity). -/
theorem bracket_tight_2 : lt (lower_tight 2) (upper 2) = true := by decide
theorem bracket_tight_3 : lt (lower_tight 3) (upper 3) = true := by decide

/-- Width identity at N=3:
      upper(3) − lower_tight(3)
        = 61/36 − 220/144 = (61·4 − 220)/144 = 24/144 = 1/(3·4).
    Cross-mult form. -/
theorem width_3 :
    let l := lower_tight 3; let u := upper 3
    (u.1 * l.2 - l.1 * u.2) * (3 * 4) = l.2 * u.2 := by decide

/-- Tight lower is strictly above plain lower (S N) at N=3:
    S(3) = 49/36 < lower_tight(3) = 220/144. -/
theorem tight_above_plain_3 :
    lt (S 3) (lower_tight 3) = true := by decide

/-- Concrete bracket endpoints at N=10 (large but `decide`-able). -/
theorem bracket_10_endpoints :
    let l := lower_tight 10; let u := upper 10
    lt l u = true := by decide

/-- N=20 bracket — width 1/(20·21) = 1/420 on ζ(2). -/
theorem bracket_20 :
    let l := lower_tight 20; let u := upper 20
    lt l u = true := by decide

/-- N=30 bracket — width 1/(30·31) = 1/930 ≈ 1.075×10⁻³ on ζ(2).
    On 1/α_em (×60): width ≈ 0.0645. -/
theorem bracket_30 :
    let l := lower_tight 30; let u := upper 30
    lt l u = true := by decide

/-- N=50 bracket — width 1/(50·51) = 1/2550 ≈ 3.92×10⁻⁴ on ζ(2).
    On 1/α_em (×60): width ≈ 0.0235. -/
theorem bracket_50 :
    let l := lower_tight 50; let u := upper 50
    lt l u = true := by decide

-- Note on N > 50: `S 100` exceeds Lean's default `maxRecDepth = 512`.
-- Higher N is decidable in principle but blocked by recursive
-- unfolding cost.  The asymptotic-limit analysis in
-- `AlphaEM/StructuralGap.lean` does not depend on N → ∞: the
-- candidate formula has an intrinsic 5.4×10⁻⁴ gap to the observed
-- 1/α_em that no amount of bracket tightening can close.

end E213.Lib.Physics.Basel.Bound
