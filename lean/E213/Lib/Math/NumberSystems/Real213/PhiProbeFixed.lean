import E213.Lib.Math.NumberSystems.Real213.PhiAsCut
import E213.Lib.Math.NumberSystems.Real213.MobiusProbeTwist
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper

/-!
# PhiProbeFixed — φ is the fixed cut of the P-twist on the probe lattice

`MobiusProbeTwist` showed the Möbius `P = [[2,1],[1,1]]` twists the cut-probe
coordinates `(m,k) ↦ (2m+k, m+k)` and that the twist sends cuts to cuts.  φ is the
*eigenratio* of `P`, so it should sit still under the twist — and it does:

    cutThroughP phiCut = phiCut    (pointwise, ∀ m k).

φ is the **fixed cut** of the probe-twist — the cut-level shadow of "φ is the
eigenvector of `P`": viewing φ's comparison behaviour through one `P`-step on the
probe lattice returns it unchanged.

Both `phiCut m k` and `cutThroughP phiCut m k = phiCut (2m+k) (m+k)` are routed
through one **subtraction-free master invariant**

    masterCut m k := decide (k ≤ 2m ∧ m·k + k·k ≤ m·m)

(the φ-norm condition `m² ≥ mk + k²`); each equals it (`phiCut_eq_master`,
`ctp_eq_master`), so they are equal (`phi_is_probe_twist_fixed`).  The bridge from
`phiCut`'s native `(2m−k)²` form is `(2m−k)² + 4mk = 4m² + k²` (`bridge`, regime
`k ≤ 2m`); the twisted side is subtraction-free (`cond1` always holds, `2(2m+k) −
(m+k) = 3m+k` never truncates).  Both `cond2`s coincide via the linear equivalence
`5A + 10B + 5C ≤ 9A + 6B + C ⟺ B + C ≤ A`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.PhiProbeFixed

open E213.Lib.Math.NumberSystems.Real213.PhiAsCut (phiCut)
open E213.Lib.Math.NumberSystems.Real213.MobiusProbeTwist (cutThroughP)
open E213.Meta.Nat.PureNat (add_mul mul_assoc)

/-! ## §1 — square expansions (PURE 2-variable algebra) -/

private theorem sqmk (m k : Nat) : (m+k)*(m+k) = m*m + 2*(m*k) + k*k := by
  rw [add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm k m, ← Nat.add_assoc,
      Nat.add_assoc (m*m) (m*k) (m*k), show m*k+m*k=2*(m*k) from by rw [← Nat.two_mul]]

private theorem sq5mk (m k : Nat) : 5*((m+k)*(m+k)) = 5*(m*m) + 10*(m*k) + 5*(k*k) := by
  rw [sqmk, Nat.mul_add, Nat.mul_add, show 5*(2*(m*k)) = 10*(m*k) from by rw [← mul_assoc]]

private theorem sq3mk (m k : Nat) : (3*m+k)*(3*m+k) = 9*(m*m) + 6*(m*k) + k*k := by
  rw [add_mul, Nat.mul_add, Nat.mul_add,
      show (3*m)*(3*m) = 9*(m*m) from by
        rw [mul_assoc 3 m (3*m), Nat.mul_comm m (3*m), mul_assoc 3 m m, ← mul_assoc 3 3 (m*m)],
      show (3*m)*k = 3*(m*k) from mul_assoc 3 m k,
      show k*(3*m) = 3*(m*k) from by rw [Nat.mul_comm k (3*m), mul_assoc 3 m k],
      ← Nat.add_assoc, Nat.add_assoc (9*(m*m)) (3*(m*k)) (3*(m*k)),
      show 3*(m*k) + 3*(m*k) = 6*(m*k) from by rw [← add_mul]]

/-! ## §2 — the linear master equivalence `5A+10B+5C ≤ 9A+6B+C ⟺ B+C ≤ A` -/

private theorem lhs_canon (A B C : Nat) : 9*A+6*B+C + (4*B+4*C) = 9*A + 10*B + 5*C := by
  rw [Nat.add_assoc (9*A+6*B) C (4*B+4*C), ← Nat.add_assoc C (4*B) (4*C),
      Nat.add_comm C (4*B), Nat.add_assoc (4*B) C (4*C),
      ← Nat.add_assoc (9*A+6*B) (4*B) (C+4*C), Nat.add_assoc (9*A) (6*B) (4*B),
      show 6*B+4*B = 10*B from by rw [← add_mul],
      show C+4*C = 5*C from by rw [show (5:Nat)=1+4 from rfl, add_mul, Nat.one_mul]]

private theorem rhs_canon (A B C : Nat) : 5*A+10*B+5*C + 4*A = 9*A + 10*B + 5*C := by
  rw [Nat.add_assoc (5*A+10*B) (5*C) (4*A), Nat.add_comm (5*C) (4*A),
      ← Nat.add_assoc (5*A+10*B) (4*A) (5*C), Nat.add_assoc (5*A) (10*B) (4*A),
      Nat.add_comm (10*B) (4*A), ← Nat.add_assoc (5*A) (4*A) (10*B),
      show 5*A+4*A = 9*A from by rw [← add_mul]]

private theorem ident (A B C : Nat) : 9*A+6*B+C + (4*B+4*C) = 5*A+10*B+5*C + 4*A := by
  rw [lhs_canon, rhs_canon]

private theorem arith_fwd (A B C : Nat) (h : 5*A+10*B+5*C ≤ 9*A+6*B+C) : B+C ≤ A := by
  have h2 : 5*A+10*B+5*C + (4*B+4*C) ≤ 5*A+10*B+5*C + 4*A := by
    rw [← ident]; exact Nat.add_le_add_right h (4*B+4*C)
  have h3 : 4*B+4*C ≤ 4*A := E213.Tactic.NatHelper.le_of_add_le_add_left h2
  have h4 : 4*(B+C) ≤ 4*A := by rw [Nat.mul_add]; exact h3
  exact Nat.le_of_mul_le_mul_left h4 (by decide)

private theorem arith_bwd (A B C : Nat) (h : B+C ≤ A) : 5*A+10*B+5*C ≤ 9*A+6*B+C := by
  have h3 : 4*B+4*C ≤ 4*A := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left 4 h
  have h2 : 5*A+10*B+5*C + (4*B+4*C) ≤ 9*A+6*B+C + (4*B+4*C) := by
    rw [ident]; exact Nat.add_le_add_left h3 (5*A+10*B+5*C)
  exact E213.Tactic.NatHelper.le_of_add_le_add_left
    (by rw [Nat.add_comm (5*A+10*B+5*C), Nat.add_comm (9*A+6*B+C)] at h2; exact h2)

/-! ## §3 — auxiliary: the φ-norm forces `k ≤ 2m` -/

private theorem sq_le_imp (x y : Nat) (h : x*x ≤ y*y) : x ≤ y := by
  cases Nat.lt_or_ge y x with
  | inr hle => exact hle
  | inl hgt =>
    have h3 : (y+1)*(y+1) ≤ x*x := Nat.mul_le_mul hgt hgt
    have h4 : (y+1)*(y+1) = y*y + (2*y+1) := by
      rw [add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one, Nat.one_mul,
          Nat.add_assoc, ← Nat.add_assoc y y 1, ← Nat.two_mul]
    rw [h4] at h3
    have h6 : y*y + (2*y+1) ≤ y*y + 0 := by rw [Nat.add_zero]; exact Nat.le_trans h3 h
    exact absurd (E213.Tactic.NatHelper.le_of_add_le_add_left h6)
      (Nat.not_le_of_lt (Nat.zero_lt_succ _))

private theorem k_le_2m_of_norm (m k : Nat) (h : m*k + k*k ≤ m*m) : k ≤ 2*m := by
  have hkk : k*k ≤ m*m := Nat.le_trans (Nat.le_add_left (k*k) (m*k)) h
  have hkm : k ≤ m := sq_le_imp k m hkk
  exact Nat.le_trans hkm (by
    calc m = 1*m := (Nat.one_mul m).symm
      _ ≤ 2*m := Nat.mul_le_mul_right m (by decide))

/-! ## §4 — the two cut forms both reduce to the master invariant -/

/-- The subtraction-free **master cut**: `m/k ≥ φ` iff `k ≤ 2m` and `mk + k² ≤
    m²` (the φ-norm condition `m² ≥ mk + k²`, no `(2m−k)`). -/
def masterCut (m k : Nat) : Bool := decide (k ≤ 2*m ∧ m*k + k*k ≤ m*m)

/-- Bridge identity (regime `k ≤ 2m`): `(2m−k)² + 4mk = 4m² + k²`. -/
private theorem bridge (m k : Nat) (h : k ≤ 2*m) :
    (2*m-k)*(2*m-k) + 4*(m*k) = 4*(m*m) + k*k := by
  have hp : (2*m - k) + k = 2*m := E213.Tactic.NatHelper.sub_add_cancel h
  have key : (2*m)*(2*m) = (2*m-k)*(2*m-k) + 2*((2*m-k)*k) + k*k := by
    calc (2*m)*(2*m) = ((2*m-k)+k)*((2*m-k)+k) := by rw [hp]
      _ = (2*m-k)*(2*m-k) + 2*((2*m-k)*k) + k*k := by
            rw [add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm k (2*m-k), ← Nat.add_assoc,
                Nat.add_assoc ((2*m-k)*(2*m-k)) ((2*m-k)*k) ((2*m-k)*k),
                show (2*m-k)*k + (2*m-k)*k = 2*((2*m-k)*k) from by rw [← Nat.two_mul]]
  have h4mm : 4*(m*m) = (2*m)*(2*m) := by
    rw [mul_assoc 2 m (2*m), Nat.mul_comm m (2*m), mul_assoc 2 m m, ← mul_assoc 2 2 (m*m)]
  have h4mk : 4*(m*k) = 2*((2*m-k)*k) + 2*(k*k) := by
    have e2mk : (2*m)*k = (2*m-k)*k + k*k := by
      calc (2*m)*k = ((2*m-k)+k)*k := by rw [hp]
        _ = (2*m-k)*k + k*k := add_mul _ _ _
    have e4 : 4*(m*k) = 2*((2*m)*k) := by
      rw [show (4:Nat) = 2*2 from rfl, mul_assoc 2 2 (m*k), mul_assoc 2 m k]
    rw [e4, e2mk, Nat.mul_add]
  rw [h4mk, ← Nat.add_assoc, show (2:Nat)*(k*k) = k*k + k*k from by rw [Nat.two_mul],
      ← Nat.add_assoc, ← key, h4mm]

private theorem k_sq_split (k : Nat) : 5*k*k = k*k + 4*(k*k) := by
  have e5k : 5*k = k + 4*k := by rw [show (5:Nat) = 1+4 from rfl, add_mul, Nat.one_mul]
  calc 5*k*k = (k + 4*k)*k := by rw [e5k]
    _ = k*k + 4*k*k := by rw [add_mul]
    _ = k*k + 4*(k*k) := by rw [mul_assoc 4 k k]

/-- ★★★ **`phiCut = masterCut`** (∀): φ's native cut equals the subtraction-free
    master form.  Regime `k ≤ 2m`: `5k² ≤ (2m−k)² ⟺ mk+k² ≤ m²` via `bridge`;
    else both `cond1` fail. -/
theorem phiCut_eq_master (m k : Nat) : phiCut m k = masterCut m k := by
  show decide (k ≤ 2*m ∧ 5*k*k ≤ (2*m-k)*(2*m-k)) = decide (k ≤ 2*m ∧ m*k+k*k ≤ m*m)
  by_cases hk : k ≤ 2*m
  · have cond2_iff : (5*k*k ≤ (2*m-k)*(2*m-k)) ↔ (m*k+k*k ≤ m*m) := by
      have hb := bridge m k hk
      constructor
      · intro h5
        have h6 : 5*k*k + 4*(m*k) ≤ 4*(m*m) + k*k := by
          rw [← hb]; exact Nat.add_le_add_right h5 (4*(m*k))
        have h7 : k*k + (4*(k*k) + 4*(m*k)) ≤ k*k + 4*(m*m) := by
          rw [Nat.add_comm (k*k) (4*(m*m)), ← Nat.add_assoc]
          calc k*k + 4*(k*k) + 4*(m*k) = 5*k*k + 4*(m*k) := by rw [← k_sq_split]
            _ ≤ 4*(m*m) + k*k := h6
        have h8 : 4*(k*k) + 4*(m*k) ≤ 4*(m*m) := E213.Tactic.NatHelper.le_of_add_le_add_left h7
        have h9 : 4*(k*k + m*k) ≤ 4*(m*m) := by rw [Nat.mul_add]; exact h8
        have h10 : k*k + m*k ≤ m*m := Nat.le_of_mul_le_mul_left h9 (by decide)
        rw [Nat.add_comm (m*k) (k*k)]; exact h10
      · intro hm
        have h9 : 4*(k*k + m*k) ≤ 4*(m*m) := Nat.mul_le_mul_left 4 (by rw [Nat.add_comm]; exact hm)
        have h8 : 4*(k*k) + 4*(m*k) ≤ 4*(m*m) := by rw [← Nat.mul_add]; exact h9
        have h7 : 5*k*k + 4*(m*k) ≤ k*k + 4*(m*m) := by
          rw [k_sq_split, Nat.add_assoc]; exact Nat.add_le_add_left h8 (k*k)
        have h6 : 5*k*k + 4*(m*k) ≤ (2*m-k)*(2*m-k) + 4*(m*k) := by
          rw [hb, Nat.add_comm (4*(m*m)) (k*k)]; exact h7
        exact E213.Tactic.NatHelper.le_of_add_le_add_left
          (by rw [Nat.add_comm (5*k*k), Nat.add_comm ((2*m-k)*(2*m-k))] at h6; exact h6)
    by_cases h2 : m*k+k*k ≤ m*m
    · rw [decide_eq_true (⟨hk, cond2_iff.mpr h2⟩ : k ≤ 2*m ∧ 5*k*k ≤ (2*m-k)*(2*m-k)),
          decide_eq_true (⟨hk, h2⟩ : k ≤ 2*m ∧ m*k+k*k ≤ m*m)]
    · rw [decide_eq_false (fun hp => h2 (cond2_iff.mp hp.2)),
          decide_eq_false (fun hp => h2 hp.2)]
  · rw [decide_eq_false (fun hp => hk hp.1), decide_eq_false (fun hp => hk hp.1)]

/-- 2(2m+k) − (m+k) = 3m+k (no truncation). -/
private theorem sub_simp (m k : Nat) : 2*(2*m+k) - (m+k) = 3*m+k := by
  have e : 2*(2*m+k) = (3*m+k) + (m+k) := by
    rw [Nat.mul_add, show 2*(2*m) = 4*m from by rw [← mul_assoc],
        show (4:Nat)*m = 3*m + m from by rw [show (4:Nat)=3+1 from rfl, add_mul, Nat.one_mul],
        Nat.two_mul, Nat.add_assoc, ← Nat.add_assoc m k k, Nat.add_comm m k,
        Nat.add_assoc k m k, ← Nat.add_assoc (3*m) k (m+k), Nat.add_comm m k]
  rw [e, E213.Tactic.NatHelper.add_sub_cancel_right]

private theorem hcond1 (m k : Nat) : (m+k) ≤ 2*(2*m+k) := by
  rw [Nat.mul_add, show 2*(2*m)=4*m from by rw [← mul_assoc]]
  exact Nat.add_le_add (by calc m = 1*m := (Nat.one_mul m).symm
                              _ ≤ 4*m := Nat.mul_le_mul_right m (by decide))
                       (by calc k = 1*k := (Nat.one_mul k).symm
                              _ ≤ 2*k := Nat.mul_le_mul_right k (by decide))

/-- ★★★ **`cutThroughP phiCut = masterCut`** (∀): the twisted side reduces to the
    master form — subtraction-free, via `5(m+k)² ≤ (3m+k)² ⟺ mk+k² ≤ m²`. -/
theorem ctp_eq_master (m k : Nat) : cutThroughP phiCut m k = masterCut m k := by
  show decide ((m+k) ≤ 2*(2*m+k)
        ∧ 5*(m+k)*(m+k) ≤ (2*(2*m+k)-(m+k))*(2*(2*m+k)-(m+k)))
     = decide (k ≤ 2*m ∧ m*k+k*k ≤ m*m)
  have cond2_iff : (5*(m+k)*(m+k) ≤ (2*(2*m+k)-(m+k))*(2*(2*m+k)-(m+k)))
                   ↔ (m*k + k*k ≤ m*m) := by
    rw [sub_simp, show 5*(m+k)*(m+k) = 5*((m+k)*(m+k)) from mul_assoc 5 (m+k) (m+k),
        sq5mk, sq3mk]
    constructor
    · intro h; exact arith_fwd (m*m) (m*k) (k*k) h
    · intro h; exact arith_bwd (m*m) (m*k) (k*k) h
  by_cases h2 : m*k+k*k ≤ m*m
  · rw [decide_eq_true (⟨hcond1 m k, cond2_iff.mpr h2⟩
          : (m+k) ≤ 2*(2*m+k) ∧ 5*(m+k)*(m+k) ≤ (2*(2*m+k)-(m+k))*(2*(2*m+k)-(m+k))),
        decide_eq_true (⟨k_le_2m_of_norm m k h2, h2⟩ : k ≤ 2*m ∧ m*k+k*k ≤ m*m)]
  · rw [decide_eq_false (fun hp => h2 (cond2_iff.mp hp.2)), decide_eq_false (fun hp => h2 hp.2)]

/-- ★★★★ **φ is the fixed cut of the probe-twist**: `cutThroughP phiCut = phiCut`
    pointwise.  φ — the eigenratio of `P = [[2,1],[1,1]]` — is fixed by one `P`-step
    on the probe lattice.  The cut-level shadow of "φ is `P`'s eigenvector". -/
theorem phi_is_probe_twist_fixed (m k : Nat) :
    cutThroughP phiCut m k = phiCut m k := by
  rw [ctp_eq_master, phiCut_eq_master]

end E213.Lib.Math.NumberSystems.Real213.PhiProbeFixed
