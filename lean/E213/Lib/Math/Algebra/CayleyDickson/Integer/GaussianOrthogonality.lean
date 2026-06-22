import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIArith
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIDomain
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZIAlgebra213
import E213.Meta.Algebra213.Core
import E213.Meta.Int213.Core

/-!
# GaussianOrthogonality — order-4 character orthogonality `Σ iᵏ = 0` (∅-axiom)

The **order-4 leg** of the character-orthogonality target in
`research-notes/decomposition/practice/fourier.md`.  The order-2 (Legendre)
case is `ModArith/CharacterOrthogonality.quadratic_orthogonality`; orders 3 and
6 are `RootOfUnityOrthogonality.{omega,zeta6}_orthogonality` in `ℤ[ω]`.  Order 4
needs neither `Real213` nor a transcendental cut: the primitive 4th root of
unity is the imaginary unit `i`, which **already lives in the Gaussian integers
`ℤ[i]`** (`ZI`, `i² = −1`, `i⁴ = 1`) — a concrete, decidable, ∅-axiom
`CommRing213` (`ZIAlgebra213`).

## The technique — the geometric telescope, abstracted

The single algebraic engine (`geomSum_telescope`) is stated here **generically
over any `CommRing213`** with a left-unit element `one`:

> `(ζ − 1) · Σ_{k=0}^{n−1} ζᵏ = ζⁿ − 1`.

When `ζⁿ = 1` the right side is `0`, so `(ζ − 1) · Σ = 0`.  In an integral
domain a *primitive* root (`ζ ≠ 1`) forces `Σ = 0`.  Orders 2, 3, 4, 6 are
instances of this one mechanism; here order 4 is realised in `ℤ[i]`.

  * ★★★★ `geomSum_telescope`   — `(ζ−1)·Σ_{k<n} ζᵏ = ζⁿ−1` (generic CommRing213).
  * ★★★★ `orthogonality_of_pow_one` — generic conditional: `ζⁿ = 1` ⟹
    `(ζ−1)·Σ = 0` (defect carried entirely by `ζ−1`).
  * ★★★  `i_orthogonality`     — `1 + i + i² + i³ = 0` (order-4 character sum).
  * ★★★  `i_pow_four` / `i_sq_eq_neg_one` / `i_pow_ne_one_lt_four` — `i` is a
    primitive 4th root (`i⁴=1`, `i²=−1≠1`, order exactly 4).

All ∅-axiom (`#print axioms` clean).

## What this closes / the residual

Closes the concrete cyclotomic orders **2, 3, 4, 6** — exactly the roots of
unity realised by `{±1}` (order 1,2), `ℤ[ω]` (3, 6), `ℤ[i]` (4).  The *generic
conditional* (`orthogonality_of_pow_one`) is order-agnostic.  The residual open
part is **arbitrary `n`**: a primitive `n`-th root for `n ∉ {1,2,3,4,6}` is not a
Gaussian/Eisenstein integer, so exhibiting one needs a general cyclotomic ring
`ℤ[ζ_n]` the repo does not yet build (those `ζ` remain `Real213` cuts).  The
conditional is closed; only the witness for general `n` is open.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianOrthogonality

open E213.Meta.Algebra213 (Ring213 CommRing213)

/-! ## §1 — the generic geometric telescope over any `CommRing213`

`Ring213` deliberately omits `1` (see `Meta/Algebra213/Core.lean`), so we carry
the unit `one : α` and its left-unit law `hone` as section hypotheses.  Powers
and partial sums are defined relative to `one`; the telescope and the conditional
orthogonality are then pure `Ring213`/`CommRing213` algebra. -/

/-- Bare power `ζ^n` (left fold), `ζ^0 = one`. -/
def gpow {α : Type} [CommRing213 α] (one : α) (z : α) : Nat → α
  | 0     => one
  | n + 1 => gpow one z n * z

@[simp] theorem gpow_zero {α : Type} [CommRing213 α] (one z : α) :
    gpow one z 0 = one := rfl
theorem gpow_succ {α : Type} [CommRing213 α] (one z : α) (n : Nat) :
    gpow one z (n + 1) = gpow one z n * z := rfl

/-- The partial sum `Σ_{k=0}^{n-1} ζᵏ`. -/
def gsum {α : Type} [CommRing213 α] (one : α) (z : α) : Nat → α
  | 0     => 0
  | n + 1 => gsum one z n + gpow one z n

@[simp] theorem gsum_zero {α : Type} [CommRing213 α] (one z : α) :
    gsum one z 0 = 0 := rfl
theorem gsum_succ {α : Type} [CommRing213 α] (one z : α) (n : Nat) :
    gsum one z (n + 1) = gsum one z n + gpow one z n := rfl

/-- `a − a = 0` in any `Ring213` (`a + -a = 0`). -/
private theorem sub_self_ring {α : Type} [CommRing213 α] (a : α) :
    a + (-a) = 0 := by
  rw [Ring213.add_comm]; exact Ring213.add_left_neg a

/-- `(u − v)·w = u·w − v·w`, written additively `(u + -v)·w = u·w + -(v·w)`. -/
private theorem sub_mul_ring {α : Type} [CommRing213 α] (u v w : α) :
    (u + (-v)) * w = u * w + (-(v * w)) := by
  rw [Ring213.add_mul, Ring213.neg_mul]

/-- The single induction-step ring identity (writing `p = zⁿ`):
    `(p + -one) + (z + -one)·p = p·z + -one`.  Mirrors
    `RootOfUnityOrthogonality.telescope_step`, generic over `CommRing213`. -/
private theorem telescope_step {α : Type} [CommRing213 α]
    (one : α) (hone : ∀ a : α, one * a = a) (p z : α) :
    (p + (-one)) + (z + (-one)) * p = p * z + (-one) := by
  rw [sub_mul_ring z one p, hone p, CommRing213.mul_comm z p]
  -- goal: (p + -one) + (p·z + -p) = p·z + -one
  rw [Ring213.add_assoc p (-one) (p * z + (-p))]
  rw [← Ring213.add_assoc (-one) (p * z) (-p)]
  rw [Ring213.add_comm (-one) (p * z)]
  rw [Ring213.add_assoc (p * z) (-one) (-p)]
  rw [Ring213.add_comm (-one) (-p)]
  rw [← Ring213.add_assoc (p * z) (-p) (-one)]
  rw [← Ring213.add_assoc p (p * z + -p) (-one)]
  rw [← Ring213.add_assoc p (p * z) (-p)]
  rw [Ring213.add_comm p (p * z)]
  rw [Ring213.add_assoc (p * z) p (-p)]
  rw [sub_self_ring p, Ring213.add_zero (p * z)]

/-- ★★★★ **The geometric telescope** — generic over `CommRing213`.

    `(ζ − 1) · Σ_{k=0}^{n−1} ζᵏ = ζⁿ − 1` (written `(z + -one)·gsum = gpow + -one`).

    By induction on `n`: the `n+1` step adds `(ζ−1)·ζⁿ = ζⁿ⁺¹ − ζⁿ` to the
    inductive `ζⁿ − 1`; the `−ζⁿ`/`+ζⁿ` cancel, leaving `ζⁿ⁺¹ − 1`.  This is the
    single engine behind every order's orthogonality — the order-`d`
    generalisation of the order-2 `+1,−1` pair telescope. -/
theorem geomSum_telescope {α : Type} [CommRing213 α]
    (one : α) (hone : ∀ a : α, one * a = a) (z : α) :
    ∀ n, (z + (-one)) * gsum one z n = gpow one z n + (-one)
  | 0     => by
    show (z + (-one)) * 0 = one + (-one)
    rw [Ring213.mul_zero (z + (-one))]
    exact (sub_self_ring one).symm
  | n + 1 => by
    rw [gsum_succ, Ring213.mul_add, geomSum_telescope one hone z n, gpow_succ]
    exact telescope_step one hone (gpow one z n) z

/-- ★★★★ **Generic conditional orthogonality.**  For *any* `ζ : α` in a
    `CommRing213` that is an `n`-th root of unity (`ζⁿ = one`), the geometric sum
    is annihilated by `ζ − 1`:

      `(ζ − 1) · Σ_{k=0}^{n−1} ζᵏ = 0`.

    Immediate from `geomSum_telescope` once `gpow z n = one`.  In an integral
    domain a *primitive* root (`ζ ≠ 1`, with `ζ − 1` not a zero divisor) then
    forces `Σ = 0` — the whole orthogonality defect carried by the factor
    `ζ − 1`.  This is the order-agnostic statement; orders 2, 3, 4, 6 are
    instances. -/
theorem orthogonality_of_pow_one {α : Type} [CommRing213 α]
    (one : α) (hone : ∀ a : α, one * a = a) (z : α) (n : Nat)
    (hz : gpow one z n = one) :
    (z + (-one)) * gsum one z n = 0 := by
  rw [geomSum_telescope one hone z n, hz]
  exact sub_self_ring one

/-! ## §2 — order-4 instance in the Gaussian integers `ℤ[i]`

`ZI` is a `CommRing213` (`ZIAlgebra213`), with `1 = ZI.ofInt 1 = ⟨1,0⟩`.  The
imaginary unit `i = ⟨0,1⟩` is the primitive 4th root of unity.  All concrete
facts are decidable (`ZI` has `DecidableEq` and componentwise-`Int` arithmetic),
so the order-4 leg closes by `decide`. -/

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI.ZI

/-- The ring unit `1 = ⟨1,0⟩ = ZI.ofInt 1`. -/
def one : ZI := ZI.ofInt 1

/-- `one` is a left unit for `ZI` (the `CommRing213` `ofInt 1`). -/
theorem one_mul_zi (u : ZI) : one * u = u := by
  apply ext
  · show (1 : Int) * u.re - 0 * u.im = u.re
    rw [E213.Meta.Int213.zero_mul, Int.one_mul,
        Int.sub_eq_add_neg, Int.neg_zero, Int.add_zero]
  · show (1 : Int) * u.im + 0 * u.re = u.im
    rw [E213.Meta.Int213.zero_mul, Int.one_mul, Int.add_zero]

/-! ### ZI-native power / partial sum

`decide` cannot reduce the generic `gpow`/`gsum` (the `*` goes through the
`CommRing213 ZI` instance projection chain, which `whnf` does not unfold).  We
mirror the `RootOfUnityOrthogonality` pattern with `ZI`-concrete `ipow`/`isum`
built on `ZI.mul` directly, prove the order-4 numerics by `decide`, and bridge
to the generic statements by `rfl` (the two definitions are definitionally the
same fold once the instance `*` is unfolded to `ZI.mul`). -/

/-- ZI-native power `z^n` on `ZI.mul`, `z^0 = ⟨1,0⟩`. -/
def ipow (z : ZI) : Nat → ZI
  | 0     => ⟨1, 0⟩
  | n + 1 => ZI.mul (ipow z n) z

/-- ZI-native partial sum `Σ_{k<n} z^k` on `ZI` add. -/
def isum (z : ZI) : Nat → ZI
  | 0     => 0
  | n + 1 => ⟨(isum z n).re + (ipow z n).re, (isum z n).im + (ipow z n).im⟩

/-- `gpow one z` and `ipow z` agree (both fold `ZI.mul` from `⟨1,0⟩`). -/
theorem gpow_eq_ipow (z : ZI) : ∀ n, gpow one z n = ipow z n
  | 0     => rfl
  | n + 1 => by
    rw [gpow_succ, gpow_eq_ipow z n]; rfl

/-- `gsum one z` and `isum z` agree. -/
theorem gsum_eq_isum (z : ZI) : ∀ n, gsum one z n = isum z n
  | 0     => rfl
  | n + 1 => by
    rw [gsum_succ, gsum_eq_isum z n, gpow_eq_ipow z n]; rfl

/-- ★★★ `i² = −1` in `ℤ[i]` — `i` is a square root of `−1`. -/
theorem i_sq_eq_neg_one : gpow one I 2 = -one := by
  rw [gpow_eq_ipow]; decide

/-- ★★★ `i⁴ = 1` in `ℤ[i]` — `i` is a 4th root of unity. -/
theorem i_pow_four : gpow one I 4 = one := by
  rw [gpow_eq_ipow]; decide

/-- ★★★ `i` is a *primitive* 4th root: no smaller positive power is `1`.
    `i¹ = i ≠ 1`, `i² = −1 ≠ 1`, `i³ = −i ≠ 1`. -/
theorem i_pow_ne_one_lt_four :
    gpow one I 1 ≠ one ∧ gpow one I 2 ≠ one ∧ gpow one I 3 ≠ one := by
  rw [gpow_eq_ipow, gpow_eq_ipow, gpow_eq_ipow]; decide

/-- ★★★ **Order-4 orthogonality.**  `Σ_{k=0}^{3} iᵏ = 1 + i + i² + i³ = 0` — the
    sum of all four 4th roots of unity vanishes.  The order-4 analogue of the
    Legendre `1 + (−1) = 0`, realised in `ℤ[i]` with no transcendental cut. -/
theorem i_orthogonality : gsum one I 4 = 0 := by
  rw [gsum_eq_isum]; decide

/-- ★★★★ The order-4 instance of the generic conditional: `(i − 1)·Σ = 0`,
    directly from `orthogonality_of_pow_one` with `gpow one I 4 = one`. -/
theorem i_root_orthogonality : (I + (-one)) * gsum one I 4 = 0 :=
  orthogonality_of_pow_one one one_mul_zi I 4 i_pow_four

/-- ★★★★★ **Capstone — additive character orthogonality at order 4 in `ℤ[i]`.**

    The imaginary unit `i` is a primitive 4th root of unity (`i⁴ = 1`,
    `i² = −1 ≠ 1`, order exactly 4) and `Σ_{k<4} iᵏ = 0`, with the generic
    telescope `(i−1)·Σ = i⁴−1 = 0` as the mechanism.  This is the order-4
    sibling of `RootOfUnityOrthogonality.cyclotomic_orthogonality` (orders 3, 6)
    and `quadratic_orthogonality` (order 2) — together the concrete cyclotomic
    orders `{2,3,4,6}`, all ∅-axiom and transcendental-cut-free. -/
theorem gaussian_orthogonality :
    (gpow one I 4 = one ∧ gpow one I 2 = -one ∧ gsum one I 4 = 0) ∧
    (∀ {β : Type} [_inst : CommRing213 β] (o : β) (_ : ∀ a : β, o * a = a)
        (z : β) (m : Nat), gpow o z m = o → (z + (-o)) * gsum o z m = 0) :=
  ⟨⟨i_pow_four, i_sq_eq_neg_one, i_orthogonality⟩,
   fun {_β} {_inst} o ho z m hz => orthogonality_of_pow_one o ho z m hz⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianOrthogonality
