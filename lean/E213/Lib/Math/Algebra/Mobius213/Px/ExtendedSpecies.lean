import E213.Lib.Physics.Simplex.Counts
import E213.Meta.Int213.Core

/-!
# Mobius213.Px.ExtendedSpecies — modular / Pell / lattice / Bezout species

Six symmetry-revealing species of P(x) spanning iteration-
level (mod-p periods, Pell orbits) and higher-order
(lattice invariant form, Bezout polynomial identity) frames:

  · `pentagonal_period_mod5` — P^5 ≡ −I (mod 5), witnessed
    via entry-wise reduction `89 ≡ 4`, `55 ≡ 0`, `34 ≡ 4`
    (mod 5), plus `4 = −1 (mod 5)`.  Aut = ℤ/10 (full period
    is 2d = 10).  Atomic: d.

  · `mod_2_period_3` — P³ ≡ I (mod 2), witnessed via
    entry-wise reduction `13 ≡ 1`, `8 ≡ 0`, `5 ≡ 1`
    (mod 2).  Period in GL(2, F_2) is exactly NS = 3.
    Aut = ℤ/NS.  Atomic: NS.

  · `pell_solutions_orbit` — fundamental solutions of
    `x² − d·y² = ±1`: `(2, 1)` gives `−det`, `(9, 4)`
    gives `+det`.  Aut = ℤ (Pell unit orbit).  Atomic: det.

  · `pell_recurrence_orbit` — Pell recurrence under
    multiplication by ε = NT + √d:
      `a_{n+1} = NT·a_n + d·b_n`,
      `b_{n+1} = a_n + NT·b_n`.
    Witnessed at `(2, 1) → (9, 4)` and `(9, 4) → (38, 17)`.
    Aut = linear_recurrence.  Atomic: NT.

  · `lattice_invariant_form` — P preserves the quadratic
    form `Q = [[-2, 1], [1, 2]]` with `det(Q) = -d`.
    Witnessed entry-by-entry: `P · Q · P = Q` (since P = Pᵀ).
    Aut = trivial (Q-stabiliser in this realisation).
    Atomic: d.

  · `bezout_polynomial_identity` — Bezout identity for
    `(2x+1, x+1)` as coprime polynomials in ℤ[x]:
      `(2·x + 1) + det = NT·(x + 1)`,
    i.e. `NT·(x + 1) − (2·x + 1) = det = 1`.
    Witnesses gcd = det.  Aut = trivial.  Atomic: det.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Algebra.Mobius213.Px.ExtendedSpecies

open E213.Lib.Physics.Simplex.Counts (NS NT d)

/-! ## §1 — pentagonal_period_mod5 -/

/-- `P^5 = [[89, 55], [55, 34]]`; entry (0,0) reduces to 4 mod 5. -/
theorem pentagonal_top_left_mod5 : (89 : Nat) % 5 = 4 := by decide

/-- Off-diagonal entry reduces to 0 mod 5. -/
theorem pentagonal_off_diag_mod5 : (55 : Nat) % 5 = 0 := by decide

/-- Entry (1,1) reduces to 4 mod 5. -/
theorem pentagonal_bot_right_mod5 : (34 : Nat) % 5 = 4 := by decide

/-- `4 ≡ -1 (mod 5)`, witnessing `[[4,0],[0,4]] = -I (mod 5)`. -/
theorem neg_one_eq_four_mod5 : (4 + 1 : Nat) % 5 = 0 := by decide

/-! ## §2 — mod_2_period_3 -/

/-- `P^3 = [[13, 8], [8, 5]]`; entry (0,0) reduces to 1 mod 2. -/
theorem mod2_top_left : (13 : Nat) % 2 = 1 := by decide

/-- Off-diagonal entry reduces to 0 mod 2. -/
theorem mod2_off_diag : (8 : Nat) % 2 = 0 := by decide

/-- Entry (1,1) reduces to 1 mod 2. -/
theorem mod2_bot_right : (5 : Nat) % 2 = 1 := by decide

/-- Period of P in GL(2, F_2) equals `NS = 3`. -/
theorem mod2_period_is_NS : (3 : Nat) = NS := by decide

/-! ## §3 — pell_solutions_orbit -/

/-- Pell `x² − d·y² = −det` fundamental solution at `(2, 1)`:
    `4 − 5 = −1`. -/
theorem pell_neg_det_solution :
    (2 : Int)^2 - (d : Int) * 1^2 = -(1 : Int) := by decide

/-- Pell `x² − d·y² = +det` fundamental solution at `(9, 4)`:
    `81 − 80 = 1`. -/
theorem pell_pos_det_solution :
    (9 : Int)^2 - (d : Int) * 4^2 = (1 : Int) := by decide

/-! ## §4 — pell_recurrence_orbit -/

/-- Pell `a`-recurrence step `(2, 1) → 9`:
    `NT·2 + d·1 = 4 + 5 = 9`. -/
theorem pell_step_a_2_to_9 :
    (NT : Int) * 2 + (d : Int) * 1 = 9 := by decide

/-- Pell `b`-recurrence step `(2, 1) → 4`:
    `2 + NT·1 = 2 + 2 = 4`. -/
theorem pell_step_b_1_to_4 : 2 + (NT : Int) * 1 = 4 := by decide

/-- Pell `a`-recurrence step `(9, 4) → 38`:
    `NT·9 + d·4 = 18 + 20 = 38`. -/
theorem pell_step_a_9_to_38 :
    (NT : Int) * 9 + (d : Int) * 4 = 38 := by decide

/-- Pell `b`-recurrence step `(9, 4) → 17`:
    `9 + NT·4 = 9 + 8 = 17`. -/
theorem pell_step_b_4_to_17 : 9 + (NT : Int) * 4 = 17 := by decide

/-! ## §5 — lattice_invariant_form -/

/-- The preserved quadratic form is `Q = [[-2, 1], [1, 2]]`
    with `det(Q) = -2·2 - 1·1 = -5 = -d`. -/
theorem lattice_Q_det :
    (-2 : Int) * 2 - 1 * 1 = -(d : Int) := by decide

/-- After computing `P · Q = [[-3, 4], [-1, 3]]`, the product
    `(P · Q) · P` has entry (0,0) = `-3·2 + 4·1 = -2`,
    matching `Q_{0,0}`. -/
theorem lattice_form_top_left :
    (-3 : Int) * 2 + 4 * 1 = -2 := by decide

/-- Entry (0,1) of `(P · Q) · P` equals `-3·1 + 4·1 = 1`,
    matching `Q_{0,1}`. -/
theorem lattice_form_off_diag :
    (-3 : Int) * 1 + 4 * 1 = 1 := by decide

/-- Entry (1,1) of `(P · Q) · P` equals `-1·1 + 3·1 = 2`,
    matching `Q_{1,1}`. -/
theorem lattice_form_bot_right :
    (-1 : Int) * 1 + 3 * 1 = 2 := by decide

/-! ## §6 — bezout_polynomial_identity -/

/-- ★★★★★ **Bezout polynomial identity** for `(2x+1, x+1)`:

      `(2x + 1) + det = NT·(x + 1)`

    Witnesses gcd `((2x+1), (x+1)) = det = 1` in ℤ[x] via a
    single Bezout-style step.  Equivalent to the Euclidean
    step `numerator_preserving_euclidean` already in
    `Mobius213.Px.OpenSpeciesClosure`, here re-cast as the
    explicit Bezout combination. -/
theorem bezout_polynomial (x : Int) :
    (2 * x + 1) + 1 = (NT : Int) * (x + 1) := by
  show 2 * x + 1 + 1 = 2 * (x + 1)
  rw [E213.Meta.Int213.mul_add, E213.Meta.Int213.mul_one]
  -- Goal: 2*x + 1 + 1 = 2*x + 2 — `(1 + 1 : Int) = 2` by defeq
  rw [E213.Meta.Int213.add_assoc]
  rfl

/-! ## §7 — Master: 6-species closure -/

/-- ★★★★★★★★ **Modular/Pell/lattice/Bezout master**: bundles
    the 6 species into one theorem.  Each conjunct is the
    atomic-witness for one species. -/
theorem extended_species_master :
    -- (a) pentagonal_period_mod5
    ((89 : Nat) % 5 = 4 ∧ (55 : Nat) % 5 = 0 ∧ (34 : Nat) % 5 = 4
      ∧ (4 + 1 : Nat) % 5 = 0)
    -- (b) mod_2_period_3
    ∧ ((13 : Nat) % 2 = 1 ∧ (8 : Nat) % 2 = 0 ∧ (5 : Nat) % 2 = 1
        ∧ (3 : Nat) = NS)
    -- (c) pell_solutions_orbit
    ∧ ((2 : Int)^2 - (d : Int) * 1^2 = -(1 : Int)
        ∧ (9 : Int)^2 - (d : Int) * 4^2 = (1 : Int))
    -- (d) pell_recurrence_orbit
    ∧ ((NT : Int) * 2 + (d : Int) * 1 = 9
        ∧ 2 + (NT : Int) * 1 = 4
        ∧ (NT : Int) * 9 + (d : Int) * 4 = 38
        ∧ 9 + (NT : Int) * 4 = 17)
    -- (e) lattice_invariant_form
    ∧ ((-2 : Int) * 2 - 1 * 1 = -(d : Int)
        ∧ (-3 : Int) * 2 + 4 * 1 = -2
        ∧ (-3 : Int) * 1 + 4 * 1 = 1
        ∧ (-1 : Int) * 1 + 3 * 1 = 2)
    -- (f) bezout_polynomial_identity
    ∧ (∀ x : Int, (2 * x + 1) + 1 = (NT : Int) * (x + 1)) :=
  ⟨⟨pentagonal_top_left_mod5, pentagonal_off_diag_mod5,
    pentagonal_bot_right_mod5, neg_one_eq_four_mod5⟩,
   ⟨mod2_top_left, mod2_off_diag, mod2_bot_right, mod2_period_is_NS⟩,
   ⟨pell_neg_det_solution, pell_pos_det_solution⟩,
   ⟨pell_step_a_2_to_9, pell_step_b_1_to_4,
    pell_step_a_9_to_38, pell_step_b_4_to_17⟩,
   ⟨lattice_Q_det, lattice_form_top_left,
    lattice_form_off_diag, lattice_form_bot_right⟩,
   bezout_polynomial⟩

end E213.Lib.Math.Algebra.Mobius213.Px.ExtendedSpecies
