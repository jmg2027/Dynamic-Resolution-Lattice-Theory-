import E213.Meta.Tactic.NatHelper

/-!
# CrossDetDiscriminant — the cross-determinant's two reference forms, by sign of discriminant

The completability classification lives in the `(W, d)` plane of the cross-determinant
`W_i = a_{i+1}d_i − a_i d_{i+1}`.  Two quadratic reference forms sit behind it, and they
differ by the **sign of their discriminant** — which is exactly the difference between an
unbounded *line* of convergents and a bounded *curve* (torus / elliptic-curve lattice):

  - **golden** `Q(m,k) = m² − mk − k²`, discriminant `+5 = NS + NT` — the det-one floor's
    conserved invariant (`ProbeTwistConic.Q_preserved`, the `W ≡ 1` locus of
    `DepthFloorDetOne`, the `P = [[2,1],[1,1]]` orbit).  It is **indefinite**: it takes
    both signs (`m=1,k=0` gives `+1`; `m=1,k=1` gives `−1`).  Indefinite ⟹ unbounded
    (hyperbolic) level sets ⟹ an infinite convergent line — the real-quadratic ring
    `ℤ[φ]` with its infinite unit group `φⁿ`.  This is the **trivially-free bottom** of
    the rate-carrying stratification: the floor completes via its convergent line.
  - **Eisenstein** `N(a,b) = a² − ab + b²`, discriminant `−3` — the `ℤ[ω]` norm
    (`ω² + ω + 1 = 0`).  It is **positive-definite**: `a·b ≤ a² + b²` for *all* `a, b`, so
    the form is never negative.  Definite ⟹ bounded (elliptic) level sets ⟹ no convergent
    direction; the natural object is the lattice `ℤ[ω]` and its torus — the imaginary-
    quadratic side.

This file proves the dichotomy's ∅-axiom heart **over `ℕ`** — definite-vs-indefinite as a
sign comparison `a·b ⋚ a² + b²` — without the signed-`ℤ`/`ℤ[ω]` machinery: the boundedness
that forces "line vs curve" is already visible in `ℕ`.

  * `eisenstein_definite` — `a·b ≤ a² + b²` for all `a, b` (the Eisenstein form never goes
    negative): bounded level sets.
  * `golden_indefinite` — the golden form takes both signs (`mk+k² < m²` at `(1,0)`,
    `m² < mk+k²` at `(1,1)`): unbounded level sets.
  * `discriminant_dichotomy` bundles them: the det-one floor's reference is indefinite
    (line, completes), the Eisenstein reference is definite (curve).

All zero-axiom.
-/

namespace E213.Lib.Math.Real213.CrossDetDiscriminant

/-! ## §1 — the Eisenstein form is positive-definite (bounded level sets) -/

/-- ★★ **The Eisenstein form `a² − ab + b²` is positive-definite over `ℕ`.**  Stated
    sign-free: `a·b ≤ a² + b²` for all `a, b`, so the form `a² − ab + b²` is never
    negative.  Whichever of `a, b` is larger absorbs the cross term `a·b` into its square,
    and the other square only adds.  Definite ⟹ the level sets are bounded (ellipses) ⟹
    no convergent line; the `ℤ[ω]` lattice is the reference, the imaginary-quadratic /
    elliptic-curve side. -/
theorem eisenstein_definite (a b : Nat) : a * b ≤ a * a + b * b := by
  rcases Nat.lt_or_ge a b with h | h
  · exact Nat.le_trans (Nat.mul_le_mul_right b (Nat.le_of_lt h))
      (Nat.le_add_left (b * b) (a * a))
  · exact Nat.le_trans (Nat.mul_le_mul_left a h) (Nat.le_add_right (a * a) (b * b))

/-! ## §2 — the golden form is indefinite (unbounded level sets) -/

/-- ★★ **The golden form `m² − mk − k²` is indefinite over `ℕ`.**  It takes both signs:
    `mk + k² < m²` at `(m,k) = (1,0)` (value `+1`) and `m² < mk + k²` at `(1,1)`
    (value `−1`).  Indefinite ⟹ the level sets are unbounded (hyperbolae, discriminant
    `+5`) ⟹ an infinite convergent line — the det-one floor's `P`-orbit, the real-
    quadratic `ℤ[φ]` with its infinite unit group.  This is the trivially-free bottom of
    the completability stratification: the floor completes along its convergent line. -/
theorem golden_indefinite :
    (∃ m k : Nat, m * k + k * k < m * m) ∧ (∃ m k : Nat, m * m < m * k + k * k) :=
  ⟨⟨1, 0, by decide⟩, ⟨1, 1, by decide⟩⟩

/-! ## §3 — the dichotomy -/

/-- ★★★ **The sign-of-discriminant dichotomy.**  The two cross-determinant reference
    forms split by the sign of their discriminant, visible already over `ℕ`:

    1. the **Eisenstein** form (disc `−3`) is positive-**definite** — `a·b ≤ a² + b²`
       always — so its level sets are bounded (a torus / `j=0` elliptic-curve lattice);
    2. the **golden** form (disc `+5`, the det-one floor) is **indefinite** — it takes
       both signs — so its level sets are unbounded (a convergent line, `ℤ[φ]`'s infinite
       units).

    Definite ⟹ curve, indefinite ⟹ line: the sign of the discriminant *is* the
    line-vs-curve shape of the reference, and the det-one floor (golden, indefinite) is
    the completing bottom of the rate-carrying stratification.  (The full signed-`ℤ[ω]`
    cross-determinant theory — `eisenstein_norm_posdef` over `ℤ`, the `j=0` period
    lattice — is a separate edifice; this is the `ℕ`-visible heart.) -/
theorem discriminant_dichotomy :
    (∀ a b : Nat, a * b ≤ a * a + b * b)
    ∧ ((∃ m k : Nat, m * k + k * k < m * m) ∧ (∃ m k : Nat, m * m < m * k + k * k)) :=
  ⟨eisenstein_definite, golden_indefinite⟩

end E213.Lib.Math.Real213.CrossDetDiscriminant
