import E213.Math.Real213.DyadicBracket
import E213.Math.Real213.CutSumOne
import E213.Math.Real213.CutSumPointwise
import E213.Math.Real213.CutContinuity
import E213.Math.Real213.ConstCutScale
import E213.Kernel.Tactic.Nat213

/-!
# Research.Real213DyadicRiemann: dyadic Riemann sample-sum trajectory

## 213-native philosophy (Phase J Sec 3)

User insight: "Riemann integration is simply the act of dyadically
accumulating deterministic bracket cuts.  Since we have already
mastered dyadic branching in bisectN, implementing the integral
trajectory generator — which multiplies bracket widths as weights
and sums them — is the path of least resistance from the framework."

This is the integral as a **dyadic accumulator**, not as a real-valued
limit.  At depth n, we subdivide the bracket into 2^n sub-brackets
and accumulate sample values via cutSum.

## Significance

- bisectN: dyadic binary tree DESCENT (one path).
- riemann: dyadic binary tree FULL ACCUMULATION (all leaves summed).

The two operations are complementary uses of the same dyadic
structure — IVT picks ONE leaf, integral sums ALL leaves.

## Definition

`riemannSampleSum f db depth` accumulates f(midpoint) over the 2^depth
sub-brackets of db, via tree-recursive cutSum.

Note: this gives Σ f(samples) without multiplying by sample width.
True integral = sample_sum * (width) = sample_sum * lenNum / 2^(E+depth+1).
The pure sample sum is the natural primitive.
-/

namespace E213.Math.Real213.DyadicRiemann

open E213.Math.Real213.CutSum (cutSum)
open E213.Firmware E213.Hypervisor
open E213.Math.Real213.CutPoset (cutEq)
open E213.Math.Real213.CutSumOne (cutSum_self cutSum_half_general
  cutSum_int_int cutSum_self_at)
open E213.Math.Real213.CutSumPointwise (cutSum_pointwise_eq)
open E213.Math.Real213.ConstCutScale (constCut_scale)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Real213.DyadicBracket
open E213.Math.Real213.CutContinuity (constCutFn)

/-- **Dyadic Riemann sample sum** at depth `n`: accumulates f(midCut)
    over the 2^n sub-brackets via tree recursion.

    Base (depth 0): just f(db.midCut).
    Step (depth+1): cutSum of left-half and right-half sample sums. -/
def riemannSampleSum (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) : Nat → (Nat → Nat → Bool)
  | 0 => f db.midCut
  | n+1 =>
    cutSum (riemannSampleSum f db.leftHalf n)
           (riemannSampleSum f db.rightHalf n)

/-- Unfold at depth 0 (rfl). -/
theorem riemannSampleSum_zero
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) (db : DyadicBracket) :
    riemannSampleSum f db 0 = f db.midCut := rfl

/-- Unfold at depth n+1 (rfl). -/
theorem riemannSampleSum_succ
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) (n : Nat) :
    riemannSampleSum f db (n+1)
    = cutSum (riemannSampleSum f db.leftHalf n)
             (riemannSampleSum f db.rightHalf n) := rfl

/-- **Pointwise** version: ∀ m k, riemannSampleSum (...) db n m k
    = constCut (2^n * a) b m k.  ∅-axiom — uses `cutSum_pointwise_eq`
    + `cutSum_self_at` chain (no funext). -/
theorem riemannSampleSum_constCut_at (a b : Nat) (db : DyadicBracket) :
    ∀ n m k, riemannSampleSum (constCutFn (constCut a b)) db n m k
           = constCut (2^n * a) b m k
  | 0, m, k => by
    show constCut a b m k = constCut (2^0 * a) b m k
    have h : (2 : Nat)^0 * a = a := show 1 * a = a from Nat.one_mul a
    rw [h]
  | n+1, m, k => by
    show cutSum (riemannSampleSum (constCutFn (constCut a b))
                  db.leftHalf n)
                (riemannSampleSum (constCutFn (constCut a b))
                  db.rightHalf n) m k
       = constCut (2^(n+1) * a) b m k
    let ih_l : ∀ m' k',
        riemannSampleSum (constCutFn (constCut a b)) db.leftHalf n m' k'
        = constCut (2^n * a) b m' k' :=
      riemannSampleSum_constCut_at a b db.leftHalf n
    let ih_r : ∀ m' k',
        riemannSampleSum (constCutFn (constCut a b)) db.rightHalf n m' k'
        = constCut (2^n * a) b m' k' :=
      riemannSampleSum_constCut_at a b db.rightHalf n
    have step1 :
        cutSum (riemannSampleSum (constCutFn (constCut a b)) db.leftHalf n)
               (riemannSampleSum (constCutFn (constCut a b)) db.rightHalf n)
               m k
        = cutSum (constCut (2^n * a) b) (constCut (2^n * a) b) m k :=
      cutSum_pointwise_eq _ _ _ _ ih_l ih_r m k
    have step2 :
        cutSum (constCut (2^n * a) b) (constCut (2^n * a) b) m k
        = constCut (2 * (2^n * a)) b m k :=
      cutSum_self_at (2^n * a) b m k
    have h : 2 * (2^n * a) = 2^(n+1) * a := by
      rw [Nat.pow_succ, Nat.mul_comm (2^n) 2, E213.Tactic.Nat213.mul_assoc]
    rw [step1, step2, h]

/-- **Riemann sum of constant cut**: at depth n, sum = 2^n copies
    of the constant.  Function-equality version (uses `funext` —
    DIRTY); prefer `riemannSampleSum_constCut_at` (pointwise, ∅-axiom)
    for new code. -/
theorem riemannSampleSum_constCut (a b : Nat) (db : DyadicBracket)
    (n : Nat) :
    riemannSampleSum (constCutFn (constCut a b)) db n
    = constCut (2^n * a) b :=
  funext fun m => funext fun k =>
    riemannSampleSum_constCut_at a b db n m k

/-- **Riemann sum of zero function** = 0 at every depth. -/
theorem riemannSampleSum_zero_fn (db : DyadicBracket) (n : Nat) :
    riemannSampleSum (constCutFn (constCut 0 1)) db n = constCut 0 1 := by
  rw [riemannSampleSum_constCut 0 1 db n]
  rw [Nat.mul_zero]

/-- **Riemann sum of constant 1** at depth n = (2^n)/1.
    Sum of 2^n copies of 1 is 2^n. -/
theorem riemannSampleSum_one_fn (db : DyadicBracket) (n : Nat) :
    riemannSampleSum (constCutFn (constCut 1 1)) db n = constCut (2^n) 1 := by
  rw [riemannSampleSum_constCut 1 1 db n]
  rw [Nat.mul_one]

/-- **Riemann sum congruence**: pointwise-equal functions give
    pointwise-equal Riemann sums at every depth and bracket. -/
theorem riemannSampleSum_congr
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) (n : Nat)
    (h : ∀ x, f x = g x) :
    riemannSampleSum f db n = riemannSampleSum g db n := by
  induction n generalizing db with
  | zero =>
    show f db.midCut = g db.midCut
    exact h db.midCut
  | succ k ih =>
    show cutSum (riemannSampleSum f db.leftHalf k)
                (riemannSampleSum f db.rightHalf k)
       = cutSum (riemannSampleSum g db.leftHalf k)
                (riemannSampleSum g db.rightHalf k)
    rw [ih db.leftHalf, ih db.rightHalf]

/-- **Riemann sum at depth 1**: explicit two-sample form. -/
theorem riemannSampleSum_one_depth
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) (db : DyadicBracket) :
    riemannSampleSum f db 1
    = cutSum (f db.leftHalf.midCut) (f db.rightHalf.midCut) := rfl

/-- **Riemann linearity on integer constants**: ∫(a + c) = ∫a + ∫c
    for constant integer integrands. -/
theorem riemannSampleSum_int_linear
    (a c : Nat) (db : DyadicBracket) (n : Nat) :
    cutSum (riemannSampleSum (constCutFn (constCut a 1)) db n)
           (riemannSampleSum (constCutFn (constCut c 1)) db n)
    = constCut (2^n * (a + c)) 1 := by
  rw [riemannSampleSum_constCut a 1 db n,
      riemannSampleSum_constCut c 1 db n]
  rw [cutSum_int_int]
  show constCut (2^n * a + 2^n * c) 1 = constCut (2^n * (a + c)) 1
  rw [show 2^n * a + 2^n * c = 2^n * (a + c) from (Nat.mul_add (2^n) a c).symm]

/-- **Riemann linearity on half constants**: ∫((a + c)/2) = ∫(a/2) + ∫(c/2). -/
theorem riemannSampleSum_half_linear
    (a c : Nat) (db : DyadicBracket) (n : Nat) :
    cutSum (riemannSampleSum (constCutFn (constCut a 2)) db n)
           (riemannSampleSum (constCutFn (constCut c 2)) db n)
    = constCut (2^n * (a + c)) 2 := by
  rw [riemannSampleSum_constCut a 2 db n,
      riemannSampleSum_constCut c 2 db n]
  rw [cutSum_half_general]
  show constCut (2^n * a + 2^n * c) 2 = constCut (2^n * (a + c)) 2
  rw [show 2^n * a + 2^n * c = 2^n * (a + c) from (Nat.mul_add (2^n) a c).symm]

/-- **Riemann sum normalized by sample count gives back the integrand**:
    Σ_{depth n} (a/b) at sample count 2^n, viewed at denominator
    scaled by 2^n, equals a/b cut-equivalently.

    Real meaning: average sample value = constant integrand.
    Proof: pure constCut_scale rescaling. -/
theorem riemannSampleSum_const_normalized (a b : Nat) (n : Nat) :
    constCut (2^n * a) (b * 2^n) = constCut a b := by
  rw [Nat.mul_comm (2^n) a]
  exact (constCut_scale a b (2^n)
    (Nat.pos_pow_of_pos n (Nat.zero_lt_succ 1))).symm

/-- **Pointwise** version of `riemannSampleSum_const_normalized`:
    ∀ m k, constCut (2^n * a) (b * 2^n) m k = constCut a b m k.
    ∅-axiom — uses `constCut_scale_at` (pointwise, no funext). -/
theorem riemannSampleSum_const_normalized_at
    (a b : Nat) (n : Nat) (m k : Nat) :
    constCut (2^n * a) (b * 2^n) m k = constCut a b m k := by
  rw [Nat.mul_comm (2^n) a]
  exact (E213.Math.Real213.ConstCutScale.constCut_scale_at a b (2^n)
    (Nat.pos_pow_of_pos n (Nat.zero_lt_succ 1)) m k).symm

/-- **Riemann sum on identity at depth 0**: the trivial single-sample
    case.  Just f(midpoint) = midpoint. -/
theorem riemannSampleSum_id_depth_zero (db : DyadicBracket) :
    riemannSampleSum id db 0 = db.midCut := rfl

/-! ### M2: Riemann finite-N marker (no π / ∞ in dyadic accumulation)

Sister-branch `Physics/FiniteUniverse.no_pi_in_finite_alpha_em` style:
explicitly mark that at every finite depth, the Riemann sum is a
concrete (Nat, Nat) rational — no transcendence creeps in. -/

/-- **Concrete Riemann sum at depth 3 on a generic bracket**:
    constant 1/1 integrand gives sum = 8/1 (= 2³ samples). -/
theorem riemann_depth_3_concrete (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 1 1)) db 3 = constCut 8 1 :=
  riemannSampleSum_constCut 1 1 db 3

/-- **Concrete Riemann sum at depth 5**: sum = 32/1 = 2⁵. -/
theorem riemann_depth_5_concrete (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 1 1)) db 5 = constCut 32 1 :=
  riemannSampleSum_constCut 1 1 db 5

/-- **No-π marker for Riemann**: every concrete Riemann sum on a
    constant integrand is an explicit (Nat, Nat) rational, with NO
    transcendence (π, e, etc.) anywhere in the structure.

    Direct analog of physics-track `no_pi_in_finite_alpha_em`. -/
theorem no_pi_in_finite_riemann (a b : Nat) (db : DyadicBracket) (n : Nat) :
    ∃ M : Nat, riemannSampleSum (constCutFn (constCut a b)) db n
             = constCut M b :=
  ⟨2^n * a, riemannSampleSum_constCut a b db n⟩

/-! ### O4: Riemann concrete sums for various constant integrands -/

/-- Σ_{depth 2} (1/2) at any bracket = 4/2.  4 samples × 1/2 = 2. -/
theorem riemann_half_depth_2 (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 1 2)) db 2 = constCut 4 2 :=
  riemannSampleSum_constCut 1 2 db 2

/-- Σ_{depth 3} (1/2) = 8/2.  8 samples × 1/2 = 4. -/
theorem riemann_half_depth_3 (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 1 2)) db 3 = constCut 8 2 :=
  riemannSampleSum_constCut 1 2 db 3

/-- Σ_{depth 4} (3/4) = 48/4.  16 samples × 3/4 = 12. -/
theorem riemann_threequarter_depth_4 (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 3 4)) db 4 = constCut 48 4 :=
  riemannSampleSum_constCut 3 4 db 4

/-- Σ_{depth 6} (1/3) = 64/3.  64 samples × 1/3. -/
theorem riemann_third_depth_6 (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 1 3)) db 6 = constCut 64 3 :=
  riemannSampleSum_constCut 1 3 db 6

/-- **Riemann constant doubling recurrence**: at depth n+1, the sum
    of constant a/b is the cutSum of the depth n sum with itself.

    This expresses that doubling the sample count = doubling the sum
    (constant integrand). -/
theorem riemann_const_doubling (a b : Nat) (db : DyadicBracket) (n : Nat) :
    riemannSampleSum (constCutFn (constCut a b)) db (n+1)
    = cutSum (riemannSampleSum (constCutFn (constCut a b)) db n)
             (riemannSampleSum (constCutFn (constCut a b)) db n) := by
  rw [riemannSampleSum_constCut a b db (n+1)]
  rw [riemannSampleSum_constCut a b db n]
  rw [cutSum_self]
  show constCut (2^(n+1) * a) b = constCut (2 * (2^n * a)) b
  congr 1
  rw [Nat.pow_succ, E213.Tactic.Nat213.mul_assoc,
      E213.Tactic.Nat213.mul_left_comm]

/-! ### R2: Riemann sums at higher depths (8, 10) -/

/-- Σ_{depth 8} (1/3) = 256/3.  256 samples × 1/3. -/
theorem riemann_third_depth_8 (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 1 3)) db 8 = constCut 256 3 :=
  riemannSampleSum_constCut 1 3 db 8

/-- Σ_{depth 10} (1/2) = 1024/2.  1024 samples × 1/2 = 512. -/
theorem riemann_half_depth_10 (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 1 2)) db 10 = constCut 1024 2 :=
  riemannSampleSum_constCut 1 2 db 10

/-- Σ_{depth 8} (5/7) = 1280/7.  256 samples × 5/7. -/
theorem riemann_fiveSeventh_depth_8 (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 5 7)) db 8 = constCut 1280 7 :=
  riemannSampleSum_constCut 5 7 db 8

/-- Σ_{depth 12} (1/100) = 4096/100. -/
theorem riemann_hundredth_depth_12 (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 1 100)) db 12
    = constCut 4096 100 :=
  riemannSampleSum_constCut 1 100 db 12

/-! ### U2: Riemann sums at very deep depths (14, 16, 20) -/

/-- Σ_{depth 14} (1/2) = 16384/2 = 8192. -/
theorem riemann_half_depth_14 (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 1 2)) db 14
    = constCut 16384 2 :=
  riemannSampleSum_constCut 1 2 db 14

/-- Σ_{depth 16} (1/3) = 65536/3. -/
theorem riemann_third_depth_16 (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 1 3)) db 16
    = constCut 65536 3 :=
  riemannSampleSum_constCut 1 3 db 16

/-- Σ_{depth 20} (7/13) = (1048576 × 7)/13 = 7340032/13. -/
theorem riemann_sevenThirteenth_depth_20 (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 7 13)) db 20
    = constCut 7340032 13 :=
  riemannSampleSum_constCut 7 13 db 20

/-- Σ_{depth 25} (1/2) closed form: 2^25 / 2 = 33554432 / 2. -/
theorem riemann_half_depth_25 (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 1 2)) db 25
    = constCut (2^25 * 1) 2 :=
  riemannSampleSum_constCut 1 2 db 25

/-- Σ_{depth 30} (1/2) closed form: 2^30 / 2 = 1073741824 / 2. -/
theorem riemann_half_depth_30 (db : DyadicBracket) :
    riemannSampleSum (constCutFn (constCut 1 2)) db 30
    = constCut (2^30 * 1) 2 :=
  riemannSampleSum_constCut 1 2 db 30

/-- **Riemann universal facts bundle (W2)**: closed form +
    doubling recurrence + normalized average for constant integrand. -/
theorem riemann_universal_facts (a b : Nat) (db : DyadicBracket) (n : Nat) :
    -- (1) Closed form: Σ_{depth n} (a/b) = (2^n * a) / b.
    riemannSampleSum (constCutFn (constCut a b)) db n = constCut (2^n * a) b
    -- (2) Doubling recurrence: depth (n+1) = double depth n.
    ∧ riemannSampleSum (constCutFn (constCut a b)) db (n+1)
      = cutSum (riemannSampleSum (constCutFn (constCut a b)) db n)
               (riemannSampleSum (constCutFn (constCut a b)) db n)
    -- (3) Normalized average: scaled denom recovers original constant.
    ∧ constCut (2^n * a) (b * 2^n) = constCut a b :=
  ⟨riemannSampleSum_constCut a b db n,
   riemann_const_doubling a b db n,
   riemannSampleSum_const_normalized a b n⟩

/-! ### Z1: Fundamental Dyadic Calculus Theorem (constant integrand) -/

/-- **Fundamental theorem of dyadic calculus (constant case)**:
    The sample sum at depth n, when interpreted at scaled denominator
    b*2^n, equals the constant integrand a/b cut-EQ-uivalent.

    Real meaning: ∫_a^b (constant c) dx = c × (b-a)
    expressed via cut-equivalence.  Sister-branch FiniteUniverse
    pattern at the calculus level. -/
theorem fundamental_dyadic_calculus_const (a b : Nat) (n : Nat) :
    cutEq (constCut (2^n * a) (b * 2^n)) (constCut a b) :=
  fun m k => by rw [riemannSampleSum_const_normalized]

/-! ### AA1: Riemann sum at depth 0 explicit -/

/-- Riemann at depth 0 = single sample at midpoint.  For const f
    = constCutFn c, this gives c. -/
theorem riemann_const_depth_zero (c : Nat → Nat → Bool) (db : DyadicBracket) :
    riemannSampleSum (constCutFn c) db 0 = c := rfl

/-- Riemann at depth 0 with id integrand gives midpoint. -/
theorem riemann_id_depth_zero (db : DyadicBracket) :
    riemannSampleSum id db 0 = db.midCut := rfl

/-! ### Pointwise PURE wrappers for the depth-N concrete theorems

Each function-eq depth-N theorem (Σ_{depth n} c = constCut N b) has
a pointwise variant via `riemannSampleSum_constCut_at` (PURE).
These let downstream code reason at the cut-function level without
inheriting Quot.sound from the funext bridge. -/

/-- (1/2) at depth 2, pointwise (PURE). -/
theorem riemann_half_depth_2_at (db : DyadicBracket) (m k : Nat) :
    riemannSampleSum (constCutFn (constCut 1 2)) db 2 m k = constCut 4 2 m k :=
  riemannSampleSum_constCut_at 1 2 db 2 m k

/-- (1/2) at depth 3, pointwise (PURE). -/
theorem riemann_half_depth_3_at (db : DyadicBracket) (m k : Nat) :
    riemannSampleSum (constCutFn (constCut 1 2)) db 3 m k = constCut 8 2 m k :=
  riemannSampleSum_constCut_at 1 2 db 3 m k

/-- (3/4) at depth 4, pointwise (PURE). -/
theorem riemann_threequarter_depth_4_at (db : DyadicBracket) (m k : Nat) :
    riemannSampleSum (constCutFn (constCut 3 4)) db 4 m k = constCut 48 4 m k :=
  riemannSampleSum_constCut_at 3 4 db 4 m k

/-- (1/3) at depth 6, pointwise (PURE). -/
theorem riemann_third_depth_6_at (db : DyadicBracket) (m k : Nat) :
    riemannSampleSum (constCutFn (constCut 1 3)) db 6 m k = constCut 64 3 m k :=
  riemannSampleSum_constCut_at 1 3 db 6 m k

/-- (1/3) at depth 8, pointwise (PURE). -/
theorem riemann_third_depth_8_at (db : DyadicBracket) (m k : Nat) :
    riemannSampleSum (constCutFn (constCut 1 3)) db 8 m k = constCut 256 3 m k :=
  riemannSampleSum_constCut_at 1 3 db 8 m k

/-- (1/2) at depth 10, pointwise (PURE). -/
theorem riemann_half_depth_10_at (db : DyadicBracket) (m k : Nat) :
    riemannSampleSum (constCutFn (constCut 1 2)) db 10 m k
    = constCut 1024 2 m k :=
  riemannSampleSum_constCut_at 1 2 db 10 m k

/-- (5/7) at depth 8, pointwise (PURE). -/
theorem riemann_fiveSeventh_depth_8_at (db : DyadicBracket) (m k : Nat) :
    riemannSampleSum (constCutFn (constCut 5 7)) db 8 m k
    = constCut 1280 7 m k :=
  riemannSampleSum_constCut_at 5 7 db 8 m k

/-- (1/100) at depth 12, pointwise (PURE). -/
theorem riemann_hundredth_depth_12_at (db : DyadicBracket) (m k : Nat) :
    riemannSampleSum (constCutFn (constCut 1 100)) db 12 m k
    = constCut 4096 100 m k :=
  riemannSampleSum_constCut_at 1 100 db 12 m k

/-- (1/2) at depth 14, pointwise (PURE). -/
theorem riemann_half_depth_14_at (db : DyadicBracket) (m k : Nat) :
    riemannSampleSum (constCutFn (constCut 1 2)) db 14 m k
    = constCut 16384 2 m k :=
  riemannSampleSum_constCut_at 1 2 db 14 m k

/-- (1/3) at depth 16, pointwise (PURE). -/
theorem riemann_third_depth_16_at (db : DyadicBracket) (m k : Nat) :
    riemannSampleSum (constCutFn (constCut 1 3)) db 16 m k
    = constCut 65536 3 m k :=
  riemannSampleSum_constCut_at 1 3 db 16 m k

end E213.Math.Real213.DyadicRiemann
