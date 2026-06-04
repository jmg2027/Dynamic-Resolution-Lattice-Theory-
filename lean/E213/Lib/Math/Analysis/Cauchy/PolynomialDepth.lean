import E213.Lib.Math.Analysis.Cauchy.FiniteDepthAlgebra

/-!
# PolynomialDepth — every degree-`d` polynomial sequence has divergence-depth `d` (general)

`DepthQuadraticGeneric`/`DepthCubicGeneric` proved depth 2 / depth 3 for *fixed* small
degrees over `ℕ`, each needing the monomial→Newton (Stirling) conversion by hand.  Over `ℤ`,
where the finite-difference operator `Δ` closes under iteration, the finite-depth sequences
form a **ring** (`FiniteDepthAlgebra.polyDepthZ_{add,smul,mul}`), and the general statement
falls out with no Stirling and no per-degree reordering:

  * `idZ` (the sequence `n ↦ n`) has depth 1 (`Δ idZ ≡ 1`);
  * `powSeq i` (the sequence `n ↦ nⁱ`) has depth `i` — `i` factors of `idZ`, depth-additive
    under `polyDepthZ_mul`;
  * `polySeq a d` (`n ↦ Σ_{i≤d} aᵢ·nⁱ`, any `ℤ`-coefficients) has depth `d` — a `polyDepthZ_add`
    of `polyDepthZ_smul`-scaled `powSeq`s, lifted to a common depth by `polyDepthZ_mono`.

> ★★★ `polyDepthZ_polySeq` : `∀ a d, polyDepthZ d (polySeq a d)` — the complete
> "degree = divergence depth" theorem, subsuming the quadratic/cubic/… rungs in one, via the
> ring structure rather than the Newton basis.

All zero-axiom.
-/

namespace E213.Lib.Math.Analysis.Cauchy.PolynomialDepth

open E213.Lib.Math.Analysis.Cauchy.NewtonGregory (diffZ liftKZ isConstZ polyDepthZ)
open E213.Lib.Math.Analysis.Cauchy.FiniteDepthAlgebra
  (polyDepthZ_add polyDepthZ_smul polyDepthZ_mul polyDepthZ_iff_vanish vanishZ vanishZ_succ)
open E213.Meta.Int213 (add_comm add_assoc add_neg_cancel)

/-! ## §1 — base cases: constants (depth 0), the identity (depth 1) -/

/-- Constants have divergence-depth 0. -/
theorem polyDepthZ_const (c : Int) : polyDepthZ 0 (fun _ => c) := fun _ => rfl

/-- The identity `ℤ`-sequence `n ↦ n`. -/
def idZ : Nat → Int := fun n => Int.ofNat n

/-- `Δ idZ ≡ 1`: the identity's forward difference is the constant `1`.  (`x - a ≡ x + (-a)`
    definitionally; close with `add_assoc` + `add_neg_cancel`, all PURE Int213.) -/
theorem diffZ_id (n : Nat) : diffZ idZ n = 1 := by
  show Int.ofNat n + 1 - Int.ofNat n = 1
  rw [add_comm (Int.ofNat n) 1]
  show (1 + Int.ofNat n) + (-(Int.ofNat n)) = 1
  rw [add_assoc 1 (Int.ofNat n) (-(Int.ofNat n)), add_neg_cancel (Int.ofNat n)]
  rfl

/-- The identity sequence has divergence-depth 1. -/
theorem polyDepthZ_id : polyDepthZ 1 idZ := by
  intro n
  show diffZ idZ n = diffZ idZ 0
  rw [diffZ_id n, diffZ_id 0]

/-! ## §2 — monomial powers: `nⁱ` has depth `i` (ring, no Stirling) -/

/-- The power sequence `n ↦ nⁱ`, built as `i` factors of `idZ`. -/
def powSeq : Nat → (Nat → Int)
  | 0     => fun _ => 1
  | i + 1 => fun n => powSeq i n * idZ n

/-- ★★ `nⁱ` has divergence-depth `i` — depth-additivity (`polyDepthZ_mul`) applied `i`
    times to the depth-1 `idZ`. -/
theorem polyDepthZ_powSeq : ∀ i, polyDepthZ i (powSeq i)
  | 0     => polyDepthZ_const 1
  | i + 1 => polyDepthZ_mul (polyDepthZ_powSeq i) polyDepthZ_id

/-! ## §3 — depth monotonicity (a degree-`d` sequence is also "depth ≤ e") -/

theorem vanishZ_add_right {k : Nat} {s : Nat → Int} (h : vanishZ k s) :
    ∀ m, vanishZ (k + m) s
  | 0     => h
  | m + 1 => vanishZ_succ (vanishZ_add_right h m)

/-- `polyDepthZ` is monotone in the depth: degree `d` ⟹ depth `e` for any `d ≤ e`. -/
theorem polyDepthZ_mono {d e : Nat} (hde : d ≤ e) {s : Nat → Int}
    (h : polyDepthZ d s) : polyDepthZ e s := by
  obtain ⟨m, rfl⟩ := Nat.le.dest hde
  refine polyDepthZ_iff_vanish.mpr ?_
  have hv : vanishZ (d + 1 + m) s := vanishZ_add_right (polyDepthZ_iff_vanish.mp h) m
  rwa [Nat.add_right_comm d 1 m] at hv

/-! ## §4 — the general theorem: every degree-`d` polynomial has depth `d` -/

/-- The monomial-basis polynomial `n ↦ Σ_{i≤d} aᵢ·nⁱ` (Horner-free, degree `d`). -/
def polySeq (a : Nat → Int) : Nat → (Nat → Int)
  | 0     => fun _ => a 0
  | d + 1 => fun n => polySeq a d n + a (d + 1) * powSeq (d + 1) n

/-- ★★★ **Every degree-`d` polynomial sequence has divergence-depth `d`.**  For any
    `ℤ`-coefficients `a` and degree `d`, `polyDepthZ d (polySeq a d)` — the complete
    "degree = depth" theorem.  Proof: the top term `a_{d+1}·n^{d+1}` has depth `d+1`
    (`polyDepthZ_smul` of `polyDepthZ_powSeq`), the lower part has depth `d` lifted to `d+1`
    (`polyDepthZ_mono`), and they sum (`polyDepthZ_add`).  No Stirling conversion, no
    per-degree reorder — the finite-depth ring does the bookkeeping. -/
theorem polyDepthZ_polySeq (a : Nat → Int) : ∀ d, polyDepthZ d (polySeq a d)
  | 0     => polyDepthZ_const (a 0)
  | d + 1 =>
      polyDepthZ_add
        (polyDepthZ_mono (Nat.le_succ d) (polyDepthZ_polySeq a d))
        (polyDepthZ_smul (a (d + 1)) (polyDepthZ_powSeq (d + 1)))

/-! ## §5 — the ζ(3) Apéry leading coefficient: negative coefficients, **no reindex**

The `ℕ` version (`DepthAperyCubic.aperyLead`) had to reindex `n = m+2` to dodge the negative
`−5`, `−51` in `34n³ − 51n² + 27n − 5`.  Over `ℤ` the general theorem applies *directly*. -/

/-- The coefficients of the ζ(3) Apéry leading-quotient `34n³ − 51n² + 27n − 5`. -/
def aperyCoeff : Nat → Int
  | 0 => -5
  | 1 => 27
  | 2 => -51
  | _ => 34

/-- ★★★ **The ζ(3) Apéry leading coefficient has divergence-depth 3, over ℤ, with no
    reindex.**  `polySeq aperyCoeff 3 = 34n³ − 51n² + 27n − 5` (negative coefficients and
    all), depth 3 as a one-line instance of the general `polyDepthZ_polySeq` — the `ℤ` ring
    handles directly what the `ℕ` version needed the `n = m+2` shift to avoid. -/
theorem aperyLeadZ_depth : polyDepthZ 3 (polySeq aperyCoeff 3) :=
  polyDepthZ_polySeq aperyCoeff 3

/-- `polySeq aperyCoeff 3` is the genuine Apéry coefficient: its value at `n = 2` is
    `34·8 − 51·4 + 27·2 − 5 = 117` (matching `DepthAperyCubic.aperyLead 0`). -/
theorem aperyLeadZ_value : polySeq aperyCoeff 3 2 = 117 := by decide

end E213.Lib.Math.Analysis.Cauchy.PolynomialDepth
