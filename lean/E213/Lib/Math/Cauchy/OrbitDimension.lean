import E213.Lib.Math.Cauchy.FiniteDepthAlgebra
import E213.Meta.Int213.PolyIntM
import E213.Meta.Int213.PolyIntMTactic

/-!
# OrbitDimension — above the polynomials: the C-finite rung

`DepthCharacterization.finite_depthZ_iff` pins the **bottom** of the divergence
ladder exactly: a `ℤ`-sequence has finite faithful divergence depth `d` iff it is a
degree-`d` polynomial (`Δ`-nilpotency).  But the depth axis is **coarse above the
polynomials** — it throws `2ⁿ`, `e`'s value sequence, Fibonacci, and the Liouville
numbers all into one bin (`∞`).  It sees only *polynomial / not*.

The finer invariant is the **dimension of the `Δ`-orbit** `⟨s, Δs, Δ²s, …⟩`.  A
**C-finite** sequence is one whose top difference is a `ℤ`-linear combination of the
lower ones — `Δᵏ s = Σ_{i<k} cᵢ Δⁱ s`, a *monic* constant-coefficient annihilator
`p(Δ) s ≡ 0`.  Equivalently: the orbit is finite-dimensional, of dimension ≤ `k`.

This file builds the first rung above `finite_depthZ_iff`:

  - ★ `twoPow_is_diffZ_fixed` : `Δ(2ⁿ) = 2ⁿ` — the geometric **eigen-identity**
    (`2^(n+1) − 2^n = 2·2^n − 2^n = 2^n`).  Hence `2ⁿ` is a **fixed point of `Δ`**.
  - `liftKZ_twoPow_fixed` : every iterate `Δᵏ(2ⁿ) = 2ⁿ` — the orbit never dies.
  - `CFiniteZ` — the C-finite predicate (monic `Δ`-orbit recurrence).
  - ★ `polyDepthZ_cfiniteZ` : **polynomial ⟹ C-finite** (annihilator `Δ^{d+1}`).
  - ★ `cfiniteZ_twoPow` : **`2ⁿ` is C-finite** (annihilator `Δ − 1`, orbit dim 1).
  - ★★★ `twoPow_not_polyDepthZ` : **`2ⁿ` is not polynomial** (∞ divergence depth)
    — the **strict inclusion** `polynomial ⊊ C-finite`, the rung above the
    characterization.  (`Δᵏ(2ⁿ) = 2ⁿ`, never `≡ 0` since `2⁰ = 1 ≠ 0`.)
  - `cfiniteZ_smul`, `cfiniteZ_shift` : C-finite is a module, shift-stable.

213-native: divergence depth measured distance to the **constant floor** (a
polynomial returns to it in finitely many self-pointings, `DepthResidueFloor`).
`2ⁿ` never returns — but it is a *fixed point of the pointing itself* (`Δ(2ⁿ)=2ⁿ`):
pointing at how it changes gives it back unchanged.  The orbit dimension counts how
many independent such self-relations the rule carries — `1` for the pure eigen-
sequence.

All ∅-axiom (over `Int213`; `powInt` is the core-free `Int` power).
-/

namespace E213.Lib.Math.Cauchy.OrbitDimension

open E213.Lib.Math.Cauchy.NewtonGregory
  (diffZ liftKZ isConstZ polyDepthZ mul_zero')
open E213.Lib.Math.Cauchy.FiniteDepthAlgebra
  (vanishZ polyDepthZ_iff_vanish liftKZ_smul liftKZ_shift)
open E213.Meta.Int213.PolyIntM (powInt)
open E213.Meta.Int213
  (zero_mul mul_add add_comm mul_comm zero_add)

/-! ## §1 — the geometric eigen-sequence `2ⁿ` over `ℤ` -/

/-- The geometric sequence `n ↦ 2ⁿ` over `ℤ`, via the core-free power `powInt`. -/
def twoPowZ : Nat → Int := fun n => powInt 2 n

/-- ★ **The geometric eigen-identity.**  `Δ(2ⁿ) = 2ⁿ`: the forward difference fixes
    the geometric sequence — `2^(n+1) − 2^n = 2·2^n − 2^n = 2^n`.  So `2ⁿ` is a
    **fixed point of the difference operator**, the cleanest witness of a sequence
    that never floors yet is as tame as a length-1 recurrence. -/
theorem twoPow_is_diffZ_fixed (n : Nat) : diffZ twoPowZ n = twoPowZ n := by
  show powInt 2 n * 2 - powInt 2 n = powInt 2 n
  ring_intZ

/-- **Every iterate of `Δ` fixes `2ⁿ`**: `Δᵏ(2ⁿ) = 2ⁿ` for all `k`.  The orbit
    `⟨2ⁿ, Δ2ⁿ, Δ²2ⁿ, …⟩` is the single line `⟨2ⁿ⟩` — it never collapses to `0`. -/
theorem liftKZ_twoPow_fixed : ∀ k n, liftKZ k twoPowZ n = twoPowZ n
  | 0,   _ => rfl
  | k+1, n => by
    show liftKZ k twoPowZ (n+1) - liftKZ k twoPowZ n = twoPowZ n
    rw [liftKZ_twoPow_fixed k (n+1), liftKZ_twoPow_fixed k n]
    exact twoPow_is_diffZ_fixed n

/-! ## §2 — the C-finite predicate: a monic `Δ`-orbit recurrence -/

/-- The `ℤ`-linear combination `Σ_{i<k} cᵢ · (Δⁱ s) n` of the first `k` iterated
    differences of `s` (the "lower part" of a `Δ`-orbit recurrence). -/
def linComb (c : Nat → Int) (s : Nat → Int) : Nat → Nat → Int
  | 0,   _ => 0
  | k+1, n => linComb c s k n + c k * liftKZ k s n

/-- ★ **C-finite.**  `s` is C-finite iff some iterated difference `Δᵏ s` is a fixed
    `ℤ`-linear combination of the lower ones — a *monic constant-coefficient*
    annihilator `Δᵏ s − Σ_{i<k} cᵢ Δⁱ s ≡ 0`.  Equivalently the `Δ`-orbit
    `⟨s, Δs, …⟩` is finite-dimensional (dimension ≤ `k`).  This is the rung of the
    ladder strictly above the polynomials. -/
def CFiniteZ (s : Nat → Int) : Prop :=
  ∃ (k : Nat) (c : Nat → Int), ∀ n, liftKZ k s n = linComb c s k n

/-! ### linComb structural laws -/

/-- `linComb` of the zero coefficient sequence is `0`. -/
theorem linComb_zero (c : Nat → Int) (hc : ∀ i, c i = 0) (s : Nat → Int) :
    ∀ k n, linComb c s k n = 0
  | 0,   _ => rfl
  | k+1, n => by
    show linComb c s k n + c k * liftKZ k s n = 0
    rw [linComb_zero c hc s k n, hc k, zero_mul, Int.add_zero]

/-- `linComb` pulls out a scalar in the sequence argument. -/
theorem linComb_smul (c : Nat → Int) (a : Int) (s : Nat → Int) :
    ∀ k n, linComb c (fun m => a * s m) k n = a * linComb c s k n
  | 0,   _ => by show (0 : Int) = a * 0; rw [mul_zero']
  | k+1, n => by
    show linComb c (fun m => a * s m) k n + c k * liftKZ k (fun m => a * s m) n
       = a * (linComb c s k n + c k * liftKZ k s n)
    rw [linComb_smul c a s k n, liftKZ_smul a s k n, mul_add]
    show a * linComb c s k n + c k * (a * liftKZ k s n)
       = a * linComb c s k n + a * (c k * liftKZ k s n)
    rw [show c k * (a * liftKZ k s n) = a * (c k * liftKZ k s n) from by ring_intZ]

/-- `linComb` commutes with the shift in its sequence argument. -/
theorem linComb_shift (c : Nat → Int) (s : Nat → Int) :
    ∀ k n, linComb c (fun m => s (m + 1)) k n = linComb c s k (n + 1)
  | 0,   _ => rfl
  | k+1, n => by
    show linComb c (fun m => s (m + 1)) k n + c k * liftKZ k (fun m => s (m + 1)) n
       = linComb c s k (n + 1) + c k * liftKZ k s (n + 1)
    rw [linComb_shift c s k n, liftKZ_shift s k n]

/-! ## §3 — the inclusions: polynomial ⟹ C-finite ⟹ (not back) -/

/-- ★ **Polynomial ⟹ C-finite.**  A degree-`d` polynomial has `Δ^{d+1} s ≡ 0`
    (`polyDepthZ_iff_vanish`), so it is C-finite with the *zero* lower part — its
    annihilator is the pure monomial `Δ^{d+1}`.  Polynomials sit inside C-finite. -/
theorem polyDepthZ_cfiniteZ {d : Nat} {s : Nat → Int} (h : polyDepthZ d s) :
    CFiniteZ s := by
  refine ⟨d + 1, (fun _ => 0), fun n => ?_⟩
  rw [linComb_zero (fun _ => 0) (fun _ => rfl) s (d + 1) n]
  exact (polyDepthZ_iff_vanish.mp h) n

/-- ★ **`2ⁿ` is C-finite.**  Its annihilator is `Δ − 1` (orbit dimension `1`):
    `Δ¹(2ⁿ) = 2ⁿ = 1·Δ⁰(2ⁿ)`.  The minimal nontrivial rung above the polynomials. -/
theorem cfiniteZ_twoPow : CFiniteZ twoPowZ := by
  refine ⟨1, (fun _ => 1), fun n => ?_⟩
  -- liftKZ 1 twoPowZ n = linComb (fun _ => 1) twoPowZ 1 n = 0 + 1 * (twoPowZ n)
  show liftKZ 1 twoPowZ n = (0 : Int) + 1 * liftKZ 0 twoPowZ n
  rw [liftKZ_twoPow_fixed 1 n, Int.one_mul, zero_add]
  show twoPowZ n = liftKZ 0 twoPowZ n
  rfl

/-- ★★★ **`2ⁿ` is not a polynomial — the strict inclusion `polynomial ⊊ C-finite`.**
    Every iterate `Δᵏ(2ⁿ) = 2ⁿ` (`liftKZ_twoPow_fixed`), so no iterate is `≡ 0`
    (`2⁰ = 1 ≠ 0`).  Hence `2ⁿ` has **no finite divergence depth**, while being
    C-finite (`cfiniteZ_twoPow`).  The orbit-dimension axis (`= 1`) separates `2ⁿ`
    from the polynomials where the divergence-depth axis (`= ∞`) cannot. -/
theorem twoPow_not_polyDepthZ (d : Nat) : ¬ polyDepthZ d twoPowZ := by
  intro h
  have hv : liftKZ (d + 1) twoPowZ 0 = 0 := (polyDepthZ_iff_vanish.mp h) 0
  rw [liftKZ_twoPow_fixed (d + 1) 0] at hv
  -- hv : twoPowZ 0 = 0; but twoPowZ 0 = powInt 2 0 = 1, so (1 : Int) = 0
  have hv2 : (1 : Int) = 0 := hv
  exact Nat.noConfusion (Int.ofNat.inj hv2)

/-! ## §4 — C-finite is a module + shift-stable -/

/-- **C-finite is closed under scalar multiplication** (same annihilator). -/
theorem cfiniteZ_smul (a : Int) {s : Nat → Int} (h : CFiniteZ s) :
    CFiniteZ (fun m => a * s m) := by
  obtain ⟨k, c, hrec⟩ := h
  refine ⟨k, c, fun n => ?_⟩
  rw [liftKZ_smul a s k n, hrec n, linComb_smul c a s k n]

/-- **C-finite is shift-stable** (same annihilator). -/
theorem cfiniteZ_shift {s : Nat → Int} (h : CFiniteZ s) :
    CFiniteZ (fun m => s (m + 1)) := by
  obtain ⟨k, c, hrec⟩ := h
  refine ⟨k, c, fun n => ?_⟩
  rw [liftKZ_shift s k n, hrec (n + 1), linComb_shift c s k n]

end E213.Lib.Math.Cauchy.OrbitDimension
