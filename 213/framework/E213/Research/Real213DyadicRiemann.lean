import E213.Research.Real213DyadicBracket
import E213.Research.Real213CutSumOne
import E213.Research.Real213CutContinuity
import E213.Research.Real213ConstCutScale

/-!
# Research.Real213DyadicRiemann: dyadic Riemann sample-sum trajectory

## 213-native philosophy (Phase J Sec 3)

User insight: "리만 적분은 단순히 결정론적인 브라켓 컷들을
다이애딕하게 누적하는(Accumulate) 행위입니다.  bisectN에서 이미
다이애딕 분기를 마스터했으니, 브라켓의 길이를 가중치로 곱해서
더하는 적분 궤적 생성기를 먼저 구현하시는 것이 프레임워크의
저항을 덜 받는 길입니다."

This is the integral as a **dyadic accumulator**, not as a real-valued
limit.  At depth n, we subdivide the bracket into 2^n sub-brackets
and accumulate sample values via cutSum.

## 의의

- bisectN: dyadic binary tree DESCENT (one path).
- riemann: dyadic binary tree FULL ACCUMULATION (all leaves summed).

The two operations are complementary uses of the same dyadic
structure — IVT picks ONE leaf, integral sums ALL leaves.

## 정의

`riemannSampleSum f db depth` accumulates f(midpoint) over the 2^depth
sub-brackets of db, via tree-recursive cutSum.

Note: this gives Σ f(samples) without multiplying by sample width.
True integral = sample_sum * (width) = sample_sum * lenNum / 2^(E+depth+1).
The pure sample sum is the natural primitive.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

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

/-- **Riemann sum of constant cut**: at depth n, sum = 2^n copies
    of the constant.  By cutSum_self: constCut (2^n * a) b. -/
theorem riemannSampleSum_constCut (a b : Nat) (db : DyadicBracket) :
    ∀ n, riemannSampleSum (constCutFn (constCut a b)) db n
       = constCut (2^n * a) b
  | 0 => by
    show constCut a b = constCut (2^0 * a) b
    have h : (2 : Nat)^0 * a = a := by
      show 1 * a = a
      exact Nat.one_mul a
    rw [h]
  | n+1 => by
    show cutSum (riemannSampleSum (constCutFn (constCut a b))
                  db.leftHalf n)
                (riemannSampleSum (constCutFn (constCut a b))
                  db.rightHalf n)
       = constCut (2^(n+1) * a) b
    rw [riemannSampleSum_constCut a b db.leftHalf n,
        riemannSampleSum_constCut a b db.rightHalf n]
    rw [cutSum_self]
    show constCut (2 * (2^n * a)) b = constCut (2^(n+1) * a) b
    have h : 2 * (2^n * a) = 2^(n+1) * a := by
      rw [Nat.pow_succ, Nat.mul_comm (2^n) 2, Nat.mul_assoc]
    rw [h]

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
    (Nat.pos_pow_of_pos n (by decide : 0 < 2))).symm

end E213.Research.Real213CutSum
