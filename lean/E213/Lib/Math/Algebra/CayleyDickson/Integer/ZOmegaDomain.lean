import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaAlgebra213
import E213.Meta.Nat.IntHelpers
import E213.Meta.Tactic.QuadNorm

open E213.Meta.Nat
open E213.Meta.Nat.IntHelpers
open E213.Tactic

/-!
# `ℤ[ω]` integral domain (Eisenstein)

`quad_norm` macro for `normSq_mul`.  `normSq_nonneg` uses
`2·(a² - ab + b²) = a² + b² + (a + -b)²`.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega

open E213.Meta.Int213

/-! ### Int finishing helpers (Lean-kernel reduction over `Int`)

These helpers work by Lean kernel reduction + the PURE `Int213`
ring/order lemmas (constructive `Int.NonNeg` case analysis), avoiding
`omega` / `simp`-driven Int arithmetic that leaks
`[propext, Quot.sound]`.  The `0 ≤ N + N → 0 ≤ N` halving step lives
in `Meta/Int213/Core.nonneg_of_add_self`. -/

/-- Eisenstein doubling identity:
    `(a²-ab+b²) + (a²-ab+b²) = (a-b)² + (a²+b²)`.  Both squares are
    `Int213`-nonneg, so the LHS is nonneg; halving (via
    `Int213.nonneg_of_add_self`) gives `normSq ≥ 0`.  Closed by the
    `Int213` AC-rewrite `simp only` set. -/
private theorem eisenstein_double (a b : Int) :
    (a*a - a*b + b*b) + (a*a - a*b + b*b)
      = (a - b)*(a - b) + (a*a + b*b) := by
  simp only [Int.sub_eq_add_neg, neg_mul, mul_neg, Int.neg_neg, neg_add,
             add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm,
             add_assoc, add_comm, add_left_comm, Int.add_zero, zero_add]
  rw [E213.Meta.Int213.mul_comm b a]


/-- `|uv|² = |u|²·|v|²` for the Eisenstein norm.  Typeclass projection
    through `IntegerNormed213.normSq_mul` — `[propext]`-only purity. -/
theorem normSq_mul (u v : ZOmega) :
    (u * v).normSq = u.normSq * v.normSq :=
  E213.Meta.Algebra213.IntegerNormed213.normSq_mul u v

/-- ∅-axiom finisher for the real-part `conj_mul` residue.  After
    `simp only` reduces both sides to associativity-only normal form
    (without AC-closing — which would pull `propext`), both equal
    `p + (-q + -r)` where `p = ac, q = ad, r = bc, s = bd`; closed by
    pure `Int213` `rw`-chains. -/
private theorem conj_fc1 (p q r s : Int) :
    p + -s + (-q + -r + s) = p + -r + (-q + s) + -s := by
  have L : p + -s + (-q + -r + s) = p + (-q + -r) := by
    rw [add_assoc p (-s) (-q + -r + s),
        show (-s) + (-q + -r + s) = (-q + -r) from by
          rw [add_comm (-q + -r) s, ← add_assoc (-s) s (-q+-r),
              add_left_neg s, zero_add]]
  have R : p + -r + (-q + s) + -s = p + (-q + -r) := by
    rw [add_assoc (p + -r) (-q + s) (-s),
        show (-q + s) + -s = -q from by
          rw [add_assoc (-q) s (-s), add_neg_cancel s, Int.add_zero],
        add_assoc p (-r) (-q), add_comm (-r) (-q)]
  rw [L, R]

/-- ∅-axiom finisher for the imag-part `conj_mul` residue.  Both sides
    equal `-q + -r + s` (`q = ad, r = bc, s = bd`); pure `Int213` rw. -/
private theorem conj_fc2 (q r s : Int) :
    -q + -r + s = -q + s + (-r + s) + -s := by
  have R : -q + s + (-r + s) + -s = -q + -r + s := by
    rw [add_assoc (-q + s) (-r + s) (-s),
        show (-r + s) + -s = -r from by
          rw [add_assoc (-r) s (-s), add_neg_cancel s, Int.add_zero],
        add_assoc (-q) s (-r), add_comm s (-r), ← add_assoc (-q) (-r) s]
  rw [R]

/-- `conj` distributes over multiplication.  Both component goals are
    pure `Int` ring identities.  Each is reduced by the PURE `Int213`
    distribute+associate `simp only` set (NO AC-closing lemmas — those
    let `simp` close the `Eq` and so pull `propext`); the residue is
    then closed by the pure `rw`-chain finishers `conj_fc1`/`conj_fc2`.
    No `omega`. -/
theorem conj_mul (u v : ZOmega) :
    conj (u * v) = conj u * conj v := by
  apply ext
  · show (u.re*v.re - u.im*v.im)
        - (u.re*v.im + u.im*v.re - u.im*v.im)
       = (u.re - u.im)*(v.re - v.im) - (-u.im)*(-v.im)
    simp only [Int.sub_eq_add_neg, neg_mul, mul_neg, Int.neg_neg, neg_add,
               add_mul, mul_add, mul_assoc]
    exact conj_fc1 (u.re*v.re) (u.re*v.im) (u.im*v.re) (u.im*v.im)
  · show -(u.re*v.im + u.im*v.re - u.im*v.im)
       = (u.re - u.im)*(-v.im) + (-u.im)*(v.re - v.im)
         - (-u.im)*(-v.im)
    simp only [Int.sub_eq_add_neg, neg_mul, mul_neg, Int.neg_neg, neg_add,
               add_mul, mul_add, mul_assoc]
    exact conj_fc2 (u.re*v.im) (u.im*v.re) (u.im*v.im)

/-- `0 ≤ a² - ab + b²`.  No sign case-split: the Eisenstein doubling
    identity `normSq + normSq = (a-b)² + (a²+b²)` exhibits `2·normSq`
    as a sum of three `Int213`-nonneg squares; `nonneg_of_add_self`
    halves.  Replaces the `omega`-based sign analysis. -/
theorem normSq_nonneg (u : ZOmega) : 0 ≤ u.normSq := by
  show 0 ≤ u.re * u.re - u.re * u.im + u.im * u.im
  apply nonneg_of_add_self
  rw [eisenstein_double u.re u.im]
  exact E213.Meta.Int213.add_nonneg
    (IntHelpers.mul_self_nonneg (u.re - u.im))
    (E213.Meta.Int213.add_nonneg
      (IntHelpers.mul_self_nonneg u.re)
      (IntHelpers.mul_self_nonneg u.im))

theorem normSq_eq_zero_iff (u : ZOmega) : u.normSq = 0 ↔ u = 0 := by
  refine ⟨?_, ?_⟩
  · intro h
    have h_eq : u.re * u.re - u.re * u.im + u.im * u.im = 0 := h
    -- normSq + normSq = (a-b)² + (a²+b²) = 0; all squares Int213-nonneg.
    have h_dbl : (u.re - u.im)*(u.re - u.im) + (u.re*u.re + u.im*u.im) = 0 := by
      rw [← eisenstein_double u.re u.im, h_eq, Int.add_zero]
    obtain ⟨_, h_ab⟩ := E213.Meta.Int213.add_eq_zero_of_nonneg
      (IntHelpers.mul_self_nonneg (u.re - u.im))
      (E213.Meta.Int213.add_nonneg
        (IntHelpers.mul_self_nonneg u.re) (IntHelpers.mul_self_nonneg u.im))
      h_dbl
    -- h_ab : a*a + b*b = 0  ⇒  a*a = 0 ∧ b*b = 0.
    obtain ⟨h_a2_eq, h_b2_eq⟩ := E213.Meta.Int213.add_eq_zero_of_nonneg
      (IntHelpers.mul_self_nonneg u.re) (IntHelpers.mul_self_nonneg u.im) h_ab
    have h_re : u.re = 0 := IntHelpers.mul_self_eq_zero.mp h_a2_eq
    have h_im : u.im = 0 := IntHelpers.mul_self_eq_zero.mp h_b2_eq
    exact ext h_re h_im
  · rintro rfl
    show (0 : Int) * 0 - 0 * 0 + 0 * 0 = 0
    decide

theorem no_zero_div (u v : ZOmega) : u * v = 0 → u = 0 ∨ v = 0 := by
  intro huv
  have hn : (u * v).normSq = 0 := by
    rw [huv]; show (0 : Int) * 0 - 0 * 0 + 0 * 0 = 0
    decide
  rw [normSq_mul] at hn
  rcases E213.Meta.Int213.mul_eq_zero hn with h | h
  · exact Or.inl ((normSq_eq_zero_iff u).mp h)
  · exact Or.inr ((normSq_eq_zero_iff v).mp h)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
