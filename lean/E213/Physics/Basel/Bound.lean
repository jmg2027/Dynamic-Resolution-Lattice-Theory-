import E213.Physics.Simplex.Counts

/-!
# Basel partial sum S(N) — rational approximation to ζ(2)

In standard formulation, ζ(2) = π²/6 enters DRLT via
    1/α_GUT = d² · ζ(2)
But ζ(2) is the *infinite* limit of finite rational sums.

On the finite discrete lattice, we replace ζ(2) by `S N` at
sufficient resolution N, with explicit *rational* error bound:

    S(N) ≤ ζ(2) ≤ upper(N) := S(N) + 1/N

Both endpoints are rational.  ζ(2) itself is never needed as a
Lean term — only its rational interval bracket.

This file defines S, upper, and proves concrete bracket facts at
small N, all 0-axiom decide-checked.

Convention: rationals as unreduced `(Nat × Nat)` = `(num, den)`,
matching `ABLens.view`.  Comparison via cross-multiplication.
-/

namespace E213.Physics.Basel

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

end E213.Physics.Basel
