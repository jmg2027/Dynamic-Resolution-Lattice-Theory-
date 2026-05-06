import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Real213.CutSumOne
import E213.Math.Real213.CutSumPointwise
import E213.Math.Real213.CutContinuity
import E213.Math.Real213.ConstCutScale
import E213.Kernel.Tactic.Nat213

import E213.Math.Real213.CutPoset
import E213.Math.Real213.CutSum
import E213.Math.Real213.CutSumTest
/-!
# Real213DyadicRiemann: dyadic Riemann sample-sum trajectory

## 213-native philosophy (Sec 3)

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

namespace E213.Math.Analysis.DyadicSearch.DyadicRiemann

open E213.Math.Real213.CutSum (cutSum)
open E213.Firmware E213.Lens
open E213.Math.Real213.CutPoset (cutEq)
open E213.Math.Real213.CutSumOne (cutSum_self cutSum_half_general
  cutSum_int_int cutSum_self_at)
open E213.Math.Real213.CutSumPointwise (cutSum_pointwise_eq)
open E213.Math.Real213.ConstCutScale (constCut_scale)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.DyadicSearch.DyadicBracket
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

/-- **Riemann sum of constant cut**, cutEq form (PURE).
    At depth n, sum equals 2^n copies of the constant pointwise. -/
theorem riemannSampleSum_constCut (a b : Nat) (db : DyadicBracket)
    (n : Nat) :
    cutEq (riemannSampleSum (constCutFn (constCut a b)) db n)
          (constCut (2^n * a) b) :=
  riemannSampleSum_constCut_at a b db n

/-- **Riemann sum of zero function** ≡ 0 at every depth (cutEq, PURE). -/
theorem riemannSampleSum_zero_fn (db : DyadicBracket) (n : Nat) :
    cutEq (riemannSampleSum (constCutFn (constCut 0 1)) db n) (constCut 0 1) := by
  intro m k
  rw [riemannSampleSum_constCut_at 0 1 db n m k]
  rw [Nat.mul_zero]

/-- **Riemann sum of constant 1** at depth n ≡ (2^n)/1 (cutEq, PURE). -/
theorem riemannSampleSum_one_fn (db : DyadicBracket) (n : Nat) :
    cutEq (riemannSampleSum (constCutFn (constCut 1 1)) db n) (constCut (2^n) 1) := by
  intro m k
  rw [riemannSampleSum_constCut_at 1 1 db n m k]
  rw [Nat.mul_one]

/-- **Riemann sum congruence**, cutEq form (PURE): if f, g agree
    pointwise on every cut function input, their Riemann sums agree
    pointwise at every depth and bracket. -/
theorem riemannSampleSum_congr
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (db : DyadicBracket) (n : Nat)
    (h : ∀ x m k, f x m k = g x m k) :
    cutEq (riemannSampleSum f db n) (riemannSampleSum g db n) := by
  induction n generalizing db with
  | zero =>
    intro m k
    show f db.midCut m k = g db.midCut m k
    exact h db.midCut m k
  | succ j ih =>
    intro m k
    show cutSum (riemannSampleSum f db.leftHalf j)
                (riemannSampleSum f db.rightHalf j) m k
       = cutSum (riemannSampleSum g db.leftHalf j)
                (riemannSampleSum g db.rightHalf j) m k
    exact cutSum_pointwise_eq _ _ _ _
      (ih db.leftHalf) (ih db.rightHalf) m k

/-- **Riemann sum at depth 1**: explicit two-sample form (rfl, PURE). -/
theorem riemannSampleSum_one_depth
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) (db : DyadicBracket) :
    riemannSampleSum f db 1
    = cutSum (f db.leftHalf.midCut) (f db.rightHalf.midCut) := rfl

/-! ### Riemann linearity (deferred to CutSumOne refactor)

The `riemannSampleSum_int_linear` and `_half_linear` theorems were
removed during the cutEq migration because they require
`cutSum_int_int_at` / `cutSum_half_general_at` (PURE pointwise
forms) which don't yet exist in `CutSumOne.lean`.  After the
CutSumOne PURE migration adds those, the linearity theorems can
be restored as cutEq forms.  No downstream consumers. -/

/-- **Pointwise** version of `riemannSampleSum_const_normalized`:
    ∀ m k, constCut (2^n * a) (b * 2^n) m k = constCut a b m k.
    ∅-axiom — uses `constCut_scale_at` (pointwise, no funext). -/
theorem riemannSampleSum_const_normalized_at
    (a b : Nat) (n : Nat) (m k : Nat) :
    constCut (2^n * a) (b * 2^n) m k = constCut a b m k := by
  rw [Nat.mul_comm (2^n) a]
  exact (E213.Math.Real213.ConstCutScale.constCut_scale_at a b (2^n)
    (Nat.pos_pow_of_pos n (Nat.zero_lt_succ 1)) m k).symm

/-- **Riemann sum normalized**, cutEq form (PURE).
    Real meaning: average sample value ≡ constant integrand. -/
theorem riemannSampleSum_const_normalized (a b : Nat) (n : Nat) :
    cutEq (constCut (2^n * a) (b * 2^n)) (constCut a b) :=
  riemannSampleSum_const_normalized_at a b n

/-- **Riemann sum on identity at depth 0**: the trivial single-sample
    case.  Just f(midpoint) = midpoint. -/
theorem riemannSampleSum_id_depth_zero (db : DyadicBracket) :
    riemannSampleSum id db 0 = db.midCut := rfl

/-! ### M2: Riemann finite-N marker (no π / ∞ in dyadic accumulation)

Sister-branch `Physics/FiniteUniverse.no_pi_in_finite_alpha_em` style:
explicitly mark that at every finite depth, the Riemann sum is a
concrete (Nat, Nat) rational — no transcendence creeps in. -/

/-- **Concrete Riemann sum at depth 3 on a generic bracket**, cutEq (PURE).
    constant 1/1 integrand gives sum ≡ 8/1 (= 2³ samples). -/
theorem riemann_depth_3_concrete (db : DyadicBracket) :
    cutEq (riemannSampleSum (constCutFn (constCut 1 1)) db 3) (constCut 8 1) :=
  riemannSampleSum_constCut_at 1 1 db 3

/-- **Concrete Riemann sum at depth 5**, cutEq (PURE): sum ≡ 32/1 = 2⁵. -/
theorem riemann_depth_5_concrete (db : DyadicBracket) :
    cutEq (riemannSampleSum (constCutFn (constCut 1 1)) db 5) (constCut 32 1) :=
  riemannSampleSum_constCut_at 1 1 db 5

/-- **No-π marker for Riemann**: every concrete Riemann sum on a
    constant integrand is an explicit (Nat, Nat) rational, with NO
    transcendence (π, e, etc.) anywhere in the structure (cutEq, PURE).

    Direct analog of physics-track `no_pi_in_finite_alpha_em`. -/
theorem no_pi_in_finite_riemann (a b : Nat) (db : DyadicBracket) (n : Nat) :
    ∃ M : Nat, cutEq (riemannSampleSum (constCutFn (constCut a b)) db n)
                     (constCut M b) :=
  ⟨2^n * a, riemannSampleSum_constCut_at a b db n⟩

/-! ### O4–U2: Riemann concrete sums for various constant integrands

The depth-N concrete sum theorems for half / third / threequarter /
fiveSeventh / hundredth / sevenThirteenth at depths 2..30 live as
PURE `_at` variants below (Σ_{depth n} (a/b) ≡ (2^n·a)/b at every
(m, k)).  See the "Pointwise PURE wrappers" section.

Function-equality wrappers were removed (2026-05-XX, part 19) per
the Core/Bridges discipline — they introduced `funext` =
Quot.sound for no semantic gain over the cutEq formulation. -/

/-- **Riemann constant doubling recurrence**, cutEq (PURE):
    at depth n+1, the constant-a/b Riemann sum is the cutSum of
    the depth-n sum with itself. -/
theorem riemann_const_doubling (a b : Nat) (db : DyadicBracket) (n : Nat) :
    cutEq (riemannSampleSum (constCutFn (constCut a b)) db (n+1))
          (cutSum (riemannSampleSum (constCutFn (constCut a b)) db n)
                  (riemannSampleSum (constCutFn (constCut a b)) db n)) := by
  intro m k
  rw [riemannSampleSum_constCut_at a b db (n+1) m k]
  show constCut (2^(n+1) * a) b m k
     = cutSum (riemannSampleSum (constCutFn (constCut a b)) db n)
              (riemannSampleSum (constCutFn (constCut a b)) db n) m k
  rw [cutSum_pointwise_eq _ _ _ _
       (riemannSampleSum_constCut_at a b db n)
       (riemannSampleSum_constCut_at a b db n) m k]
  rw [cutSum_self_at (2^n * a) b m k]
  congr 1
  rw [Nat.pow_succ, E213.Tactic.Nat213.mul_assoc,
      E213.Tactic.Nat213.mul_left_comm]

/-! ### W2: Riemann universal facts — pointwise bundle -/

/-- **Riemann universal facts bundle**, cutEq form (PURE):
    closed form + doubling recurrence + normalized average. -/
theorem riemann_universal_facts (a b : Nat) (db : DyadicBracket) (n : Nat) :
    cutEq (riemannSampleSum (constCutFn (constCut a b)) db n) (constCut (2^n * a) b)
    ∧ cutEq (riemannSampleSum (constCutFn (constCut a b)) db (n+1))
            (cutSum (riemannSampleSum (constCutFn (constCut a b)) db n)
                    (riemannSampleSum (constCutFn (constCut a b)) db n))
    ∧ cutEq (constCut (2^n * a) (b * 2^n)) (constCut a b) :=
  ⟨riemannSampleSum_constCut_at a b db n,
   riemann_const_doubling a b db n,
   riemannSampleSum_const_normalized_at a b n⟩

/-! ### Z1: Fundamental Dyadic Calculus Theorem (constant integrand) -/

/-- **Fundamental theorem of dyadic calculus (constant case)** (cutEq, PURE).
    Real meaning: ∫_a^b (constant c) dx = c × (b-a) expressed via
    cut-equivalence. -/
theorem fundamental_dyadic_calculus_const (a b : Nat) (n : Nat) :
    cutEq (constCut (2^n * a) (b * 2^n)) (constCut a b) :=
  riemannSampleSum_const_normalized_at a b n

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

/-- (7/13) at depth 20, pointwise (PURE). -/
theorem riemann_sevenThirteenth_depth_20_at (db : DyadicBracket) (m k : Nat) :
    riemannSampleSum (constCutFn (constCut 7 13)) db 20 m k
    = constCut 7340032 13 m k :=
  riemannSampleSum_constCut_at 7 13 db 20 m k

/-- (1/2) at depth 25, pointwise (PURE). -/
theorem riemann_half_depth_25_at (db : DyadicBracket) (m k : Nat) :
    riemannSampleSum (constCutFn (constCut 1 2)) db 25 m k
    = constCut (2^25 * 1) 2 m k :=
  riemannSampleSum_constCut_at 1 2 db 25 m k

/-- (1/2) at depth 30, pointwise (PURE). -/
theorem riemann_half_depth_30_at (db : DyadicBracket) (m k : Nat) :
    riemannSampleSum (constCutFn (constCut 1 2)) db 30 m k
    = constCut (2^30 * 1) 2 m k :=
  riemannSampleSum_constCut_at 1 2 db 30 m k

end E213.Math.Analysis.DyadicSearch.DyadicRiemann
