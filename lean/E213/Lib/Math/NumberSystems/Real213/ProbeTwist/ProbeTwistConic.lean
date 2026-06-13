import E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213Equiv
import E213.Meta.Nat.PureNat

/-!
# ProbeTwistConic — the wobble lives on a conic `Q = m² − mk − k²`

`ProbeTwistDynamics` showed the probe-twist runs the Pell recurrence backwards on a
cut's value (`f⁻¹`).  This file gives the **shape that motion traces**: a conic.

The Möbius matrix `P = [[2,1],[1,1]]` is `det = 1`, so it preserves the quadratic
form it acts by — and that form is the φ-norm

    Q(m, k) := m² − mk − k².

`Pstep (m,k) = (2m+k, m+k)` leaves `Q` **exactly invariant** (`Q_preserved`,
PURE, stated sign-free over `ℕ`).  So every twist step keeps `(m,k)` on its own
level set `Q = N`:

  - the φ-convergents `(3,2),(8,5),(21,13),…` all sit on `Q = −1`
    (`PhiNormInvariant.phi_norm_eq_neg_one` is the `Q=−1` case, per-sequence);
  - the `(2,1),(5,3),(13,8),…` orbit sits on `Q = +1`;
  - `(7,4)` and its orbit on `Q = 5`; `e`'s approximant `(65,24)` on `Q = 2089`.

These level sets `Q = N` are **hyperbolae** (the form `m²−mk−k²` is indefinite,
discriminant `1 + 4 = 5 > 0` — the same `5 = NS + NT` that makes φ irrational).
The twist slides each point along its hyperbola; the invariant `N = Q(m,k)` is the
**conserved label of the orbit** — the wobble's shape.  φ is the asymptotic
direction of *every* such hyperbola (slope → φ), which is why all orbits are drawn
φ-ward under the forward map and φ-outward under the twist, while never leaving
their own `Q = N` curve.

So "what shape does the wobble trace?" — **the hyperbola `Q(m,k) = N`, with the
value's φ-norm `N` the conserved quantity, and φ the common asymptote.**

The identity is stated without `ℕ`-subtraction (Q can be negative): moving every
negative term to the other side,

    Q(2m+k, m+k) = Q(m, k)   ⟺   (2m+k)² + mk + k² = (2m+k)(m+k) + (m+k)² + m².

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ProbeTwist.ProbeTwistConic

open E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213Equiv (Pstep)
open E213.Meta.Nat.PureNat (add_mul mul_assoc)

/-! ## §1 — square / product expansions (PURE) -/

private theorem sqmk (m k : Nat) : (m+k)*(m+k) = m*m + 2*(m*k) + k*k := by
  rw [add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm k m, ← Nat.add_assoc,
      Nat.add_assoc (m*m) (m*k) (m*k), show m*k+m*k=2*(m*k) from by rw [← Nat.two_mul]]

private theorem sq2mk (m k : Nat) : (2*m+k)*(2*m+k) = 4*(m*m) + 4*(m*k) + k*k := by
  rw [add_mul, Nat.mul_add, Nat.mul_add,
      show (2*m)*(2*m) = 4*(m*m) from by
        rw [mul_assoc 2 m (2*m), Nat.mul_comm m (2*m), mul_assoc 2 m m, ← mul_assoc 2 2 (m*m)],
      show (2*m)*k = 2*(m*k) from mul_assoc 2 m k,
      show k*(2*m) = 2*(m*k) from by rw [Nat.mul_comm k (2*m), mul_assoc 2 m k],
      ← Nat.add_assoc, Nat.add_assoc (4*(m*m)) (2*(m*k)) (2*(m*k)),
      show 2*(m*k)+2*(m*k) = 4*(m*k) from by rw [← add_mul]]

private theorem prod (m k : Nat) : (2*m+k)*(m+k) = 2*(m*m) + 3*(m*k) + k*k := by
  rw [add_mul, Nat.mul_add, Nat.mul_add,
      show (2*m)*m = 2*(m*m) from mul_assoc 2 m m,
      show (2*m)*k = 2*(m*k) from mul_assoc 2 m k, Nat.mul_comm k m,
      ← Nat.add_assoc, Nat.add_assoc (2*(m*m)) (2*(m*k)) (m*k),
      show 2*(m*k)+m*k = 3*(m*k) from by rw [show (3:Nat)=2+1 from rfl, add_mul, Nat.one_mul]]

/-! ## §2 — both sides reduce to the canonical `4A + 5B + 2C` -/

private theorem Lc (A B C : Nat) : 4*A+4*B+C + B + C = 4*A + 5*B + 2*C := by
  rw [Nat.add_assoc (4*A+4*B) C B, Nat.add_comm C B, ← Nat.add_assoc (4*A+4*B) B C,
      Nat.add_assoc (4*A) (4*B) B,
      show 4*B+B = 5*B from by rw [show (5:Nat)=4+1 from rfl, add_mul, Nat.one_mul],
      Nat.add_assoc (4*A+5*B) C C, show C+C = 2*C from by rw [← Nat.two_mul]]

private theorem inner (A B C : Nat) : (A+2*B+C)+A = 2*A+2*B+C := by
  rw [Nat.add_right_comm (A+2*B) C A, Nat.add_right_comm A (2*B) A,
      show A+A = 2*A from (Nat.two_mul A).symm]

private theorem mc (A B C : Nat) : 2*A+3*B+C+2*A+2*B+C = 2*A+2*A+3*B+2*B+C+C := by
  rw [Nat.add_right_comm (2*A+3*B) C (2*A), Nat.add_right_comm (2*A) (3*B) (2*A),
      Nat.add_right_comm (2*A+2*A+3*B) C (2*B)]

private theorem Rc (A B C : Nat) : 2*A+3*B+C + (A+2*B+C) + A = 4*A + 5*B + 2*C := by
  rw [Nat.add_assoc (2*A+3*B+C) (A+2*B+C) A, inner A B C,
      ← Nat.add_assoc (2*A+3*B+C) (2*A+2*B) C, ← Nat.add_assoc (2*A+3*B+C) (2*A) (2*B), mc,
      show 2*A+2*A = 4*A from by rw [show (4:Nat)=2+2 from rfl, add_mul],
      show (2:Nat)*C = C+C from by rw [Nat.two_mul],
      Nat.add_assoc (4*A) (3*B) (2*B),
      show 3*B+2*B = 5*B from by rw [show (5:Nat)=3+2 from rfl, add_mul],
      Nat.add_assoc (4*A+5*B) C C]

/-! ## §3 — `Pstep` preserves the φ-norm conic `Q = m² − mk − k²` -/

/-- ★★★ **The probe-twist preserves the φ-norm `Q = m² − mk − k²`.**  Stated
    sign-free (Q can be negative over `ℕ`): every negative term moved across,

        (2m+k)² + mk + k²  =  (2m+k)(m+k) + (m+k)² + m²,

    which is `Q(2m+k, m+k) = Q(m, k)` — `Q(Pstep(m,k)) = Q(m,k)`.  So each twist
    step keeps `(m,k)` on its level curve `Q = N`; `N` is the conserved orbit
    label.  These level sets are hyperbolae (discriminant `5 = NS+NT`), and the
    wobble slides each point along its own hyperbola toward/away from the common
    asymptotic slope φ. -/
theorem Q_preserved (m k : Nat) :
    (2*m+k)*(2*m+k) + m*k + k*k = (2*m+k)*(m+k) + (m+k)*(m+k) + m*m := by
  rw [sq2mk, prod, sqmk, Lc (m*m) (m*k) (k*k)]
  -- goal: 4A+5B+2C = (2A+3B+C) + (A+2B+C) + A   (A=m², B=mk, C=k²)
  exact (Rc (m*m) (m*k) (k*k)).symm

/-- ★★ **`Pstep` form**: restated directly as `Q ∘ Pstep = Q` on the pair.  The
    twist `(m,k) ↦ (2m+k, m+k)` conserves the φ-norm; the orbit's `Q`-value is its
    invariant shape-label. -/
theorem Pstep_conserves_Q (m k : Nat) :
    (Pstep (m,k)).1 * (Pstep (m,k)).1 + m*k + k*k
    = (Pstep (m,k)).1 * (Pstep (m,k)).2 + (Pstep (m,k)).2 * (Pstep (m,k)).2 + m*m := by
  show (2*m+k)*(2*m+k) + m*k + k*k = (2*m+k)*(m+k) + (m+k)*(m+k) + m*m
  exact Q_preserved m k

end E213.Lib.Math.NumberSystems.Real213.ProbeTwist.ProbeTwistConic
