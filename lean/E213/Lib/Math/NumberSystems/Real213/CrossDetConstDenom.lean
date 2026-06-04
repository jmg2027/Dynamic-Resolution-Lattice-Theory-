import E213.Lib.Math.NumberSystems.Real213.CrossDetOvertake
import E213.Lib.Math.NumberSystems.Real213.FibCassiniNat
import E213.Meta.Tactic.NatHelper

/-!
# CrossDetConstDenom — constant cross-determinant (`W = w₀`) ⟹ free modulus; φ instance

The third rung of the cross-determinant classification.  Where e and the Liouville
constant have `W = d` (`CrossDetEqDenom`), the **algebraic** reals have a *constant*
cross-determinant — the det-one floor of `DepthFloorDetOne` (φ, √2: `W = ±1`, the
Cassini/Pell unit).  This file extracts the `W = w₀` rung and gives φ as its concrete
named inhabitant, through the *same* `CrossDetSmall` bridge as e and Liouville.

  * ★★★ `crossdet_const_total_modulus` — a convergent num/den whose cross-determinant
    is the constant `w₀`, with `CrossDetSmall (fun _ => w₀) d`, carries a free total
    ∅-axiom modulus.  A one-line specialization of
    `CrossDetOvertake.crossdet_small_total_modulus` at `W := fun _ => w₀`.
  * ★★★ `phi_total_modulus_via_const` — φ, presented by its even-indexed Fibonacci
    convergents `aPhi i = fib(2i+2)`, `dPhi i = fib(2i+1)`, completes through this
    bridge.  The linear num/den cross-determinant is the constant `1`
    (`FibCassiniNat.convergent_cross`, the Cassini unit — distinct from the squared
    Cassini norm), and the even-Fibonacci denominator's step-ratio `fib(2i+3)/fib(2i+1)
    → φ² ≈ 2.618` dominates the polynomial factor `i(i+1)` for **all** `i ≥ 1`
    (`phi_hgrow`, via `fib(2i+3) ≥ 2·fib(2i+1)` and `i ≤ fib(2i+1)`).

So the det-one floor — which completes elsewhere by a closed-form route — is unified
into the same cross-determinant bridge as the structured transcendentals.  The three
rungs `{W const (φ), W = d (e, Liouville)} ⊆ CrossDetSmall` are all free; the overtake
(`CrossDetOvertake`) is the first rung outside.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.CrossDetConstDenom

open E213.Lib.Math.NumberSystems.Real213.CrossDetOvertake (CrossDetSmall crossdet_small_total_modulus)
open E213.Lib.Math.NumberSystems.Real213.RateModulus (rcut)
open E213.Lib.Math.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Lib.Math.NumberSystems.Real213.FibCassiniNat (fib_odd_pos fib_lb conv_mono convergent_cross)
open E213.Tactic.NatHelper (mul_assoc le_of_mul_le_mul_right mul_mul_mul_comm_213)

/-! ## §1 — the `W = const` rung -/

/-- ★★★ **Constant cross-determinant ⟹ free modulus.**  A convergent num/den `a/d`
    whose cross-determinant is the constant `w₀` (`hWconst`), with positive denominators
    and `CrossDetSmall (fun _ => w₀) d`, carries a free total ∅-axiom modulus
    `N(m,k) = k+2`.  Specialization of `crossdet_small_total_modulus` at the constant
    cross-determinant — the algebraic (det-one floor) rung. -/
theorem crossdet_const_total_modulus {a d : Nat → Nat} (w₀ : Nat)
    (hd : ∀ i, 1 ≤ d i)
    (hWconst : ∀ i, a (i + 1) * d i = a i * d (i + 1) + w₀)
    (hgrow : CrossDetSmall (fun _ => w₀) d)
    (hmono : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoS : ∀ i, a i * d (i + 1) < a (i + 1) * d i)
    (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut a d i m k = rcut a d j m k :=
  crossdet_small_total_modulus (fun _ => w₀) hd hWconst hgrow hmono hmonoS m k hk

/-! ## §2 — φ's even-indexed Fibonacci convergents -/

/-- φ's numerator convergent `aPhi i = fib(2i+2)`. -/
def aPhi (i : Nat) : Nat := fib (2 * i + 2)

/-- φ's denominator convergent `dPhi i = fib(2i+1)`. -/
def dPhi (i : Nat) : Nat := fib (2 * i + 1)

theorem aPhi_pos (i : Nat) : 0 < aPhi i :=
  Nat.lt_of_lt_of_le (by decide) (Nat.le_trans (fib_odd_pos i) (Nat.le_add_right _ _))

theorem phi_hd : ∀ i, 1 ≤ dPhi i := fun i => fib_odd_pos i

/-- φ's linear num/den cross-determinant is the constant `1` (the Cassini unit). -/
theorem phi_hWconst : ∀ i, aPhi (i+1) * dPhi i = aPhi i * dPhi (i+1) + 1 := by
  intro i
  show fib (2*(i+1)+2) * fib (2*i+1) = fib (2*i+2) * fib (2*(i+1)+1) + 1
  rw [show 2*(i+1)+2 = 2*i+4 from by rw [Nat.mul_succ],
      show 2*(i+1)+1 = 2*i+3 from by rw [Nat.mul_succ]]
  exact convergent_cross i

theorem phi_hmonoS : ∀ i, aPhi i * dPhi (i+1) < aPhi (i+1) * dPhi i := by
  intro i
  show fib (2*i+2) * fib (2*(i+1)+1) < fib (2*(i+1)+2) * fib (2*i+1)
  rw [show 2*(i+1)+2 = 2*i+4 from by rw [Nat.mul_succ],
      show 2*(i+1)+1 = 2*i+3 from by rw [Nat.mul_succ]]
  exact conv_mono i

/-- The even-Fibonacci denominator at least doubles every step:
    `2·fib(2i+1) ≤ fib(2i+3)` (one φ²-step). -/
theorem fib_odd_double (i : Nat) : 2 * fib (2*i+1) ≤ fib (2*i+3) := by
  have e : fib (2*i+3) = fib (2*i+2) + fib (2*i+1) := rfl
  have e2 : fib (2*i+2) = fib (2*i+1) + fib (2*i) := rfl
  rw [e, e2, Nat.two_mul, Nat.add_assoc, Nat.add_comm (fib (2*i)) (fib (2*i+1)), ← Nat.add_assoc]
  exact Nat.le_add_right _ _

/-- The smallness condition holds for φ's denominator at **every** `i`: the φ²-step
    ratio (`fib_odd_double`) dominates the polynomial factor `i(i+1)` (using
    `i ≤ fib(2i+1)`). -/
theorem phi_hgrow : CrossDetSmall (fun _ => 1) dPhi := by
  intro i _
  show i * (i + 1) * 1 + i * fib (2*i+1) ≤ (i + 1) * fib (2*i+1+2)
  rw [Nat.mul_one, show 2*i+1+2 = 2*i+3 from rfl]
  have hrhs : (i + 1) * (2 * fib (2*i+1)) ≤ (i + 1) * fib (2*i+3) :=
    Nat.mul_le_mul_left (i+1) (fib_odd_double i)
  refine Nat.le_trans ?_ hrhs
  rw [show (i+1) * (2 * fib (2*i+1)) = (i+1)*fib (2*i+1) + (i+1)*fib (2*i+1) from by
        rw [← Nat.mul_add, ← Nat.two_mul]]
  apply Nat.add_le_add
  · rw [Nat.mul_comm i (i+1)]
    exact Nat.mul_le_mul_left (i+1) (Nat.le_trans (Nat.le_succ i) (fib_lb i))
  · exact Nat.mul_le_mul_right (fib (2*i+1)) (Nat.le_succ i)

/-! ## §3 — across-layer monotonicity, then the φ instance -/

theorem step_le (n : Nat) : aPhi n * dPhi (n+1) ≤ aPhi (n+1) * dPhi n :=
  Nat.le_of_lt (phi_hmonoS n)

private theorem rearr (w x y z : Nat) : (w*x)*(y*z) = (w*z)*(y*x) := by
  rw [mul_mul_mul_comm_213 w x y z, mul_mul_mul_comm_213 w z y x, Nat.mul_comm x z]

/-- One-step ratio monotonicity composes across a middle index `M` (positive-denominator
    cross-multiplication cancellation). -/
theorem ratio_trans (N M i : Nat)
    (h1 : aPhi N * dPhi M ≤ aPhi M * dPhi N)
    (h2 : aPhi M * dPhi i ≤ aPhi i * dPhi M) :
    aPhi N * dPhi i ≤ aPhi i * dPhi N := by
  have hposM : 0 < aPhi M * dPhi M := Nat.mul_pos (aPhi_pos M) (fib_odd_pos M)
  have key : (aPhi N * dPhi i) * (aPhi M * dPhi M) ≤ (aPhi i * dPhi N) * (aPhi M * dPhi M) := by
    calc (aPhi N * dPhi i) * (aPhi M * dPhi M)
        = (aPhi N * dPhi M) * (aPhi M * dPhi i) := rearr (aPhi N) (dPhi i) (aPhi M) (dPhi M)
      _ ≤ (aPhi M * dPhi N) * (aPhi i * dPhi M) := Nat.mul_le_mul h1 h2
      _ = (aPhi i * dPhi N) * (aPhi M * dPhi M) := by
          rw [mul_mul_mul_comm_213 (aPhi M) (dPhi N) (aPhi i) (dPhi M),
              Nat.mul_comm (aPhi M) (aPhi i),
              mul_mul_mul_comm_213 (aPhi i) (aPhi M) (dPhi N) (dPhi M),
              rearr (aPhi i) (dPhi N) (aPhi M) (dPhi M)]
  exact le_of_mul_le_mul_right hposM key

theorem phi_hmono : ∀ N i, N ≤ i → aPhi N * dPhi i ≤ aPhi i * dPhi N := by
  intro N i hNi
  obtain ⟨t, rfl⟩ := Nat.le.dest hNi
  induction t with
  | zero => exact Nat.le_of_eq (by rw [Nat.add_zero])
  | succ s ih =>
    rw [show N+(s+1) = (N+s)+1 from rfl]
    exact ratio_trans N (N+s) ((N+s)+1) (ih (Nat.le_add_right N s)) (step_le (N+s))

/-- ★★★ **φ completes through the constant-cross-determinant bridge.**  φ's even-indexed
    Fibonacci convergents `fib(2i+2)/fib(2i+1)` have constant cross-determinant `1` and a
    denominator outgrowing the polynomial factor, so `crossdet_const_total_modulus` gives
    a free total ∅-axiom modulus `N(m,k) = k+2` — the algebraic floor unified into the
    same bridge as e and the Liouville constant. -/
theorem phi_total_modulus_via_const (m k : Nat) (hk : 1 ≤ k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut aPhi dPhi i m k = rcut aPhi dPhi j m k :=
  crossdet_const_total_modulus 1 phi_hd phi_hWconst phi_hgrow phi_hmono phi_hmonoS m k hk

end E213.Lib.Math.NumberSystems.Real213.CrossDetConstDenom
