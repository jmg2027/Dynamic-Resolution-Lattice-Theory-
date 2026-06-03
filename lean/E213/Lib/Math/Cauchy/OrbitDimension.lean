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
  (vanishZ polyDepthZ_iff_vanish liftKZ_smul liftKZ_shift liftKZ_add liftKZ_congrZ)
open E213.Meta.Int213.PolyIntM (powInt)
open E213.Meta.Int213
  (zero_mul mul_add add_comm mul_comm zero_add mul_one mul_eq_zero sub_add_cancel_int neg_mul)

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

/-- `linComb` is additive in its sequence argument (fixed coefficients). -/
theorem linComb_add (c : Nat → Int) (u v : Nat → Int) :
    ∀ k n, linComb c (fun m => u m + v m) k n = linComb c u k n + linComb c v k n
  | 0,   _ => by show (0 : Int) = 0 + 0; rw [zero_add]
  | k+1, n => by
    show linComb c (fun m => u m + v m) k n + c k * liftKZ k (fun m => u m + v m) n
       = (linComb c u k n + c k * liftKZ k u n) + (linComb c v k n + c k * liftKZ k v n)
    rw [linComb_add c u v k n, liftKZ_add u v k n]
    ring_intZ

/-- `linComb` commutes with the shift in its sequence argument. -/
theorem linComb_shift (c : Nat → Int) (s : Nat → Int) :
    ∀ k n, linComb c (fun m => s (m + 1)) k n = linComb c s k (n + 1)
  | 0,   _ => rfl
  | k+1, n => by
    show linComb c (fun m => s (m + 1)) k n + c k * liftKZ k (fun m => s (m + 1)) n
       = linComb c s k (n + 1) + c k * liftKZ k s (n + 1)
    rw [linComb_shift c s k n, liftKZ_shift s k n]

/-- `linComb` respects pointwise equality of the sequence argument. -/
theorem linComb_congr {s t : Nat → Int} (c : Nat → Int) (h : ∀ m, s m = t m) :
    ∀ k n, linComb c s k n = linComb c t k n
  | 0,   _ => rfl
  | k+1, n => by
    show linComb c s k n + c k * liftKZ k s n = linComb c t k n + c k * liftKZ k t n
    rw [linComb_congr c h k n, liftKZ_congrZ h k n]

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

/-- **C-finite is closed under addition of two sequences sharing one annihilator.**
    The solution set of a fixed constant-coefficient `Δ`-orbit recurrence is a
    module (linearity of `linComb`).  The *general* sum (distinct annihilators
    `p`, `q`) closes under the product operator `p·q` — the `ℤ[Δ]`-module / ring
    structure one rung up, whose proof needs the operator-product (convolution)
    machinery; this is the linear half. -/
theorem cfiniteZ_add_sameRec {s t : Nat → Int} {k : Nat} {c : Nat → Int}
    (hs : ∀ n, liftKZ k s n = linComb c s k n)
    (ht : ∀ n, liftKZ k t n = linComb c t k n) :
    CFiniteZ (fun m => s m + t m) := by
  refine ⟨k, c, fun n => ?_⟩
  rw [liftKZ_add s t k n, hs n, ht n, linComb_add c s t k n]

/-- **C-finite respects pointwise equality.** -/
theorem cfiniteZ_congr {s t : Nat → Int} (h : ∀ n, s n = t n) (hs : CFiniteZ s) :
    CFiniteZ t := by
  obtain ⟨k, c, hrec⟩ := hs
  refine ⟨k, c, fun n => ?_⟩
  rw [← liftKZ_congrZ h k n, hrec n, linComb_congr c h k n]

/-! ## §5 — the general geometric family `cⁿ` (orbit dimension 1) -/

/-- The geometric sequence `n ↦ cⁿ` over `ℤ`, via the core-free power `powInt`.
    (`twoPowZ = geomZ 2`.) -/
def geomZ (c : Int) : Nat → Int := fun n => powInt c n

/-- ★ **The geometric eigen-identity, general base.**  `Δ(cⁿ) = (c−1)·cⁿ`
    (`cⁿ⁺¹ − cⁿ = c·cⁿ − cⁿ = (c−1)·cⁿ`).  Base `c = 2` recovers `Δ(2ⁿ) = 2ⁿ`. -/
theorem geom_diffZ (c : Int) (n : Nat) : diffZ (geomZ c) n = (c - 1) * geomZ c n := by
  show powInt c n * c - powInt c n = (c - 1) * powInt c n
  ring_intZ

/-- Every iterate: `Δᵏ(cⁿ) = (c−1)ᵏ·cⁿ`.  The `Δ`-orbit is the single line `⟨cⁿ⟩`. -/
theorem liftKZ_geomZ (c : Int) : ∀ k n,
    liftKZ k (geomZ c) n = powInt (c - 1) k * geomZ c n
  | 0,   n => by show geomZ c n = 1 * geomZ c n; rw [Int.one_mul]
  | k+1, n => by
    show liftKZ k (geomZ c) (n+1) - liftKZ k (geomZ c) n
       = powInt (c - 1) k * (c - 1) * geomZ c n
    rw [liftKZ_geomZ c k (n+1), liftKZ_geomZ c k n]
    show powInt (c - 1) k * (geomZ c n * c) - powInt (c - 1) k * geomZ c n
       = powInt (c - 1) k * (c - 1) * geomZ c n
    ring_intZ

/-- ★ **Every geometric sequence is C-finite** (orbit dimension 1, annihilator
    `Δ − (c−1)`).  The whole geometric family sits on the first rung above the
    polynomials. -/
theorem cfiniteZ_geom (c : Int) : CFiniteZ (geomZ c) := by
  refine ⟨1, (fun _ => c - 1), fun n => ?_⟩
  show liftKZ 1 (geomZ c) n = (0 : Int) + (c - 1) * liftKZ 0 (geomZ c) n
  rw [liftKZ_geomZ c 1 n, zero_add]
  show 1 * (c - 1) * geomZ c n = (c - 1) * geomZ c n
  ring_intZ

/-- `xᵏ⁺¹ = 0 ⟹ x = 0` over `ℤ` (no zero divisors). -/
theorem powInt_eq_zero : ∀ (x : Int) (k : Nat), powInt x (k+1) = 0 → x = 0
  | x, 0,   h => by
    have h' : (1 : Int) * x = 0 := h
    rwa [Int.one_mul] at h'
  | x, k+1, h => by
    have h' : powInt x (k+1) * x = 0 := h
    rcases mul_eq_zero h' with h1 | h2
    · exact powInt_eq_zero x k h1
    · exact h2

/-- ★ **A geometric sequence `cⁿ` with `c ≠ 1` is not a polynomial.**  Its iterated
    differences `Δᵏ(cⁿ) = (c−1)ᵏ·cⁿ` never vanish (`(c−1)ᵏ⁺¹ = 0` would force
    `c = 1`), so it has no finite divergence depth — the geometric family `c ≠ 1`
    lies strictly above the polynomials, orbit dimension exactly 1. -/
theorem geom_not_polyDepthZ {c : Int} (hc : c ≠ 1) (d : Nat) :
    ¬ polyDepthZ d (geomZ c) := by
  intro h
  have hv : liftKZ (d+1) (geomZ c) 0 = 0 := (polyDepthZ_iff_vanish.mp h) 0
  rw [liftKZ_geomZ c (d+1) 0] at hv
  have hv2 : powInt (c - 1) (d+1) = 0 := by
    have hh : powInt (c - 1) (d+1) * geomZ c 0 = 0 := hv
    rwa [show geomZ c 0 = 1 from rfl, mul_one] at hh
  have hc1 : c - 1 = 0 := powInt_eq_zero (c - 1) d hv2
  apply hc
  have hcc : c - 1 + 1 = 0 + 1 := congrArg (· + 1) hc1
  rwa [sub_add_cancel_int, zero_add] at hcc

/-- `cⁿ·dⁿ = (cd)ⁿ` — the geometric bases multiply. -/
theorem powInt_mul_base (c d : Int) : ∀ n, powInt c n * powInt d n = powInt (c * d) n
  | 0   => Int.one_mul 1
  | n+1 => by
    show powInt c n * c * (powInt d n * d) = powInt (c * d) n * (c * d)
    rw [← powInt_mul_base c d n]
    ring_intZ

/-- ★ **Hadamard product, geometric case:** `cⁿ · dⁿ` is C-finite (it *is* `(cd)ⁿ`,
    orbit dimension 1).  A concrete instance of the C-finite ring's *product*
    closure — the orbit dimensions multiply `1·1 = 1` (the general Hadamard closure
    is the open frontier; here the geometric tensor is explicit). -/
theorem cfiniteZ_geom_mul (c d : Int) :
    CFiniteZ (fun n => geomZ c n * geomZ d n) :=
  cfiniteZ_congr (fun n => (powInt_mul_base c d n).symm) (cfiniteZ_geom (c * d))

/-! ## §6 — a non-geometric witness: Fibonacci (orbit dimension 2) -/

/-- Fibonacci over `ℤ`, `fibZ(n+2) = fibZ(n+1) + fibZ n`. -/
def fibZ : Nat → Int
  | 0     => 0
  | 1     => 1
  | n + 2 => fibZ (n + 1) + fibZ n

/-- The orbit recurrence coefficients for Fibonacci: `Δ²f = f − Δf`
    (`fibCoeff 0 = 1`, `fibCoeff (i+1) = −1`). -/
def fibCoeff : Nat → Int
  | 0     => 1
  | _ + 1 => -1

/-- ★ **Fibonacci is C-finite with orbit dimension 2** — the cleanest
    *non-geometric*, *non-polynomial* witness above the polynomials.  The shift
    recurrence `f(n+2) = f(n+1) + f n` becomes the `Δ`-orbit recurrence
    `Δ²f = f − Δf` (`E² = I + 2Δ + Δ²`, so `E²−E−I = Δ²+Δ−I`).  Two independent
    self-relations (`f` and `Δf`) generate the orbit — dimension exactly 2, one
    above the geometric family. -/
theorem cfiniteZ_fib : CFiniteZ fibZ := by
  refine ⟨2, fibCoeff, fun n => ?_⟩
  show fibZ (n+1+1) - fibZ (n+1) - (fibZ (n+1) - fibZ n)
     = (0 + 1 * fibZ n) + (-1) * (fibZ (n+1) - fibZ n)
  rw [show fibZ (n+1+1) = fibZ (n+1) + fibZ n from rfl, neg_mul, zero_add,
      Int.one_mul, Int.one_mul]
  ring_intZ

end E213.Lib.Math.Cauchy.OrbitDimension
