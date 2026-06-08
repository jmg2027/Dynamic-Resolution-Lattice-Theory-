import E213.Lib.Math.Algebra.Linalg213.DetMul
import E213.Lib.Math.Algebra.Linalg213.CayleyHamilton
import E213.Meta.Int213.PolyIntMTactic

/-!
# Cauchy.CasoratianDeterminant — the order-`k` Casoratian multiplier law, all orders at once

The determinantal depth ladder, closed structurally at **every** order in one theorem.

A direct `ring_intZ` expansion of the explicit determinant proves one rung at a time
(`CassiniUnimodular.det_step` order 2, multiplier `q`; `SecondCasoratian.second_casoratian` order 3,
multiplier `c`) but does not scale: the order-4 normal form exceeds the kernel's reach.  The
structural statement holds at all orders and needs no expansion:

> For a constant-coefficient order-`k` recurrence `s(m+k) = Σ_{l<k} a l · s(m+l)`, the `k×k`
> **Hankel (Casoratian) determinant** `Hₖ(n) = det[s(n+i+j)]_{i,j<k}` multiplies by the
> **companion determinant** at every step:
>
> `Hₖ(n+1) = altSign(k−1) · a 0 · Hₖ(n)`   (`casoratian_det_step`).

The proof is the one structural fact behind every rung: the shifted Hankel matrix is the
companion matrix times the original, `H(n+1) = C · H(n)` (the recurrence read as a single linear
map), so `det H(n+1) = det C · det H(n)` (`DetMul.det_matMul`), and the companion determinant is
`det C = (−1)^{k−1}·a 0` (`det_companion`, cofactor expansion along the single-entry first row).
No genus climbs; the conserved object is the companion-matrix determinant, the same toric /
genus-0 invariant at every order (cf. `SecondCasoratian` §1).

The sign matches the existing rungs: order 2 (`altSign 1 = −1`, recurrence `s(m+2)=p·s(m+1)−q·s(m)`
has `a 0 = −q`, multiplier `(−1)·(−q) = q` = `det_step`); order 3 (`altSign 2 = +1`, `a 0 = c`,
multiplier `c` = `second_casoratian`); order 4 (`altSign 3 = −1`, multiplier `−a 0`).

All ∅-axiom (over `DetN`/`DetMul`, themselves `Int213`-pure).
-/

namespace E213.Lib.Math.Analysis.Cauchy.CasoratianDeterminant

open E213.Lib.Math.Algebra.Linalg213.DetN
  (det minor colShift altSign cofSum det_congr_lt det_one)
open E213.Lib.Math.Algebra.Linalg213.Laplace (matMul)
open E213.Lib.Math.Algebra.Linalg213.DetMul (det_matMul)
open E213.Lib.Math.Algebra.Linalg213.CayleyHamilton (sumZ_iota_delta_lt mul_zero' add_zero' one_mul')
open E213.Lib.Math.Algebra.Linalg213.Permutation (iota sumZ)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (map_eq_of_mem lt_of_mem_iota)
open E213.Meta.Int213 (zero_mul zero_add mul_assoc mul_one neg_mul)

/-! ## §1 — cofactor sum with a single non-zero first-row entry -/

/-- The cofactor sum over the first `c` columns vanishes when row `0` is zero on all of them. -/
theorem cofSum_eq_zero (detN : (Nat → Nat → Int) → Int) (M : Nat → Nat → Int) :
    ∀ c, (∀ l, l < c → M 0 l = 0) → cofSum detN M c = 0
  | 0,   _ => rfl
  | c+1, h => by
    show cofSum detN M c + altSign c * M 0 c * detN (minor M c) = 0
    rw [cofSum_eq_zero detN M c (fun l hl => h l (Nat.lt_succ_of_lt hl)),
        h c (Nat.lt_succ_self c), mul_zero', zero_mul, add_zero']

/-- ★ **Single-entry first row collapses the cofactor expansion.**  If row `0` of `M` vanishes
    everywhere except column `j` (`j < c`), the cofactor sum is the lone `j`-th term. -/
theorem cofSum_single (detN : (Nat → Nat → Int) → Int) (M : Nat → Nat → Int) (j : Nat) :
    ∀ c, j < c → (∀ l, l < c → l ≠ j → M 0 l = 0) →
      cofSum detN M c = altSign j * M 0 j * detN (minor M j)
  | c+1, hj, h => by
    show cofSum detN M c + altSign c * M 0 c * detN (minor M c)
       = altSign j * M 0 j * detN (minor M j)
    by_cases hjc : j = c
    · subst hjc
      rw [cofSum_eq_zero detN M j (fun l hl => h l (Nat.lt_succ_of_lt hl) (Nat.ne_of_lt hl)),
          zero_add]
    · have hc : M 0 c = 0 := h c (Nat.lt_succ_self c) (fun e => hjc e.symm)
      have hjc' : j < c := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hjc
      rw [cofSum_single detN M j c hjc' (fun l hl hlj => h l (Nat.lt_succ_of_lt hl) hlj), hc,
          mul_zero', zero_mul, add_zero']

/-- `l < 1 → l = 0`, hand-rolled `∅`-axiom (core `Nat.lt_one_iff` leaks `propext`). -/
private theorem lt_one_eq_zero : ∀ {l : Nat}, l < 1 → l = 0
  | 0,     _ => rfl
  | _ + 1, h => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero _)

/-! ## §2 — the companion matrix and its determinant -/

/-- The `k×k` **companion matrix** of the recurrence with coefficient row `a` (the constant-
    coefficient shift): rows `0…k−2` are the shift `eᵢ ↦ eᵢ₊₁`, and the last row (`i+1 = k`) is
    the coefficient vector `a`. -/
def companion (a : Nat → Int) (k : Nat) : Nat → Nat → Int :=
  fun i l => if i + 1 = k then a l else (if l = i + 1 then 1 else 0)

/-- The minor `(0,1)` of the size-`(m+2)` companion is the size-`(m+1)` companion of the
    reindexed coefficient row `a ∘ colShift 1` — proved pointwise on the rows the determinant
    sees (`i < m+1`).  This is the recursion behind `det_companion`. -/
theorem minor_companion_eq (a : Nat → Int) (m : Nat) :
    ∀ i, i < m + 1 → ∀ l,
      minor (companion a (m + 2)) 1 i l = companion (fun l => a (colShift 1 l)) (m + 1) i l := by
  intro i _ l
  show (companion a (m + 2)) (i + 1) (colShift 1 l)
     = (if i + 1 = m + 1 then a (colShift 1 l) else (if l = i + 1 then 1 else 0))
  show (if (i + 1) + 1 = m + 2 then a (colShift 1 l) else (if colShift 1 l = (i + 1) + 1 then 1 else 0))
     = (if i + 1 = m + 1 then a (colShift 1 l) else (if l = i + 1 then 1 else 0))
  by_cases hlast : i + 1 = m + 1
  · rw [if_pos hlast, if_pos (by rw [hlast])]
  · rw [if_neg hlast, if_neg (fun e => hlast (Nat.succ.inj e))]
    -- shift row: show `(if colShift 1 l = i+2 then 1 else 0) = (if l = i+1 then 1 else 0)`
    show (if colShift 1 l = (i + 1) + 1 then (1 : Int) else 0) = (if l = i + 1 then 1 else 0)
    by_cases hl0 : l = 0
    · subst hl0
      show (if colShift 1 0 = (i + 1) + 1 then (1 : Int) else 0) = (if 0 = i + 1 then 1 else 0)
      rw [show colShift 1 0 = 0 from rfl, if_neg (fun e => Nat.noConfusion e),
          if_neg (fun e => Nat.noConfusion e.symm)]
    · -- l ≥ 1: colShift 1 l = l + 1
      rw [show colShift 1 l = l + 1 from if_neg (fun hlt => hl0 (lt_one_eq_zero hlt))]
      by_cases hli : l = i + 1
      · rw [if_pos (by rw [hli]), if_pos hli]
      · rw [if_neg (fun e => hli (Nat.succ.inj e)), if_neg hli]

/-- ★★★ **The companion determinant.**  `det (k) (companion a k) = altSign (k−1) · a 0` — the
    constant term of the characteristic polynomial, up to the alternating sign.  (Cofactor
    expansion along the single-entry first row, recursing on the `(0,1)`-minor, which is the
    smaller companion with `a 0` preserved.) -/
theorem det_companion (a : Nat → Int) :
    ∀ m, det (m + 1) (companion a (m + 1)) = altSign m * a 0
  | 0 => by
      rw [det_one]
      show (if 0 + 1 = 1 then a 0 else (if (0 : Nat) = 0 + 1 then 1 else 0)) = altSign 0 * a 0
      rw [if_pos rfl]
      show a 0 = 1 * a 0
      rw [Int.one_mul]
  | m + 1 => by
      show cofSum (det (m + 1)) (companion a (m + 2)) (m + 2) = altSign (m + 1) * a 0
      rw [cofSum_single (det (m + 1)) (companion a (m + 2)) 1 (m + 2)
            (Nat.succ_lt_succ (Nat.succ_pos m))
            (fun l _ hl1 => by
              show (if 0 + 1 = m + 2 then a l else (if l = 0 + 1 then 1 else 0)) = 0
              rw [if_neg (fun e => Nat.noConfusion (Nat.succ.inj e)), if_neg hl1])]
      -- the lone term: altSign 1 * (companion a (m+2)) 0 1 * det (m+1) (minor (companion a (m+2)) 1)
      rw [show (companion a (m + 2)) 0 1 = 1 from by
            show (if 0 + 1 = m + 2 then a 1 else (if (1 : Nat) = 0 + 1 then 1 else 0)) = 1
            rw [if_neg (fun e => Nat.noConfusion (Nat.succ.inj e)), if_pos rfl]]
      rw [det_congr_lt (m + 1) (minor_companion_eq a m),
          det_companion (fun l => a (colShift 1 l)) m]
      show altSign 1 * 1 * (altSign m * a (colShift 1 0)) = altSign (m + 1) * a 0
      rw [show colShift 1 0 = 0 from rfl]
      show -(1 : Int) * 1 * (altSign m * a 0) = -(altSign m) * a 0
      rw [mul_one, neg_mul, Int.one_mul, neg_mul]

/-! ## §3 — the Hankel/Casoratian determinant and the multiplier law -/

/-- The (extended) **Hankel matrix** of a sequence at offset `n`: `M i j = s (n + i + j)`. -/
def hankelMat (s : Nat → Int) (n : Nat) : Nat → Nat → Int := fun i j => s (n + i + j)

/-- The order-`k` **Casoratian** (Hankel) determinant of `s` at offset `n`. -/
def casoratian (s : Nat → Int) (k n : Nat) : Int := det k (hankelMat s n)

/-- Shifting the offset by one shifts the Hankel rows up by one: `H(n+1) i j = H(n) (i+1) j`. -/
theorem hankelMat_shift (s : Nat → Int) (n i j : Nat) :
    hankelMat s (n + 1) i j = hankelMat s n (i + 1) j := by
  show s (n + 1 + i + j) = s (n + (i + 1) + j)
  rw [Nat.add_right_comm n 1 i, Nat.add_assoc n i 1]

/-- ★★ **The shifted Hankel matrix is the companion times the original.**  Read off the
    recurrence: row `i < k` of `H(n+1)` is row `i` of `C · H(n)` — a shift for `i+1 < k`, the
    coefficient combination for `i+1 = k`. -/
theorem hankel_shift_eq_matMul (s : Nat → Int) (a : Nat → Int) (k n : Nat)
    (hrec : ∀ m, s (m + k) = sumZ ((iota k).map (fun l => a l * s (m + l)))) :
    ∀ i, i < k → ∀ j,
      hankelMat s (n + 1) i j = matMul k (companion a k) (hankelMat s n) i j := by
  intro i hi j
  show hankelMat s (n + 1) i j = sumZ ((iota k).map (fun l => companion a k i l * hankelMat s n l j))
  by_cases hlast : i + 1 = k
  · -- last row: coefficient combination = the recurrence
    have hterm : ∀ l, companion a k i l * hankelMat s n l j = a l * s (n + l + j) := fun l => by
      show (if i + 1 = k then a l else (if l = i + 1 then 1 else 0)) * s (n + l + j) = a l * s (n + l + j)
      rw [if_pos hlast]
    rw [map_eq_of_mem _ (fun l => a l * s (n + l + j)) (fun l _ => hterm l)]
    -- recurrence at m = n + j, reindexed (n+j+l = n+l+j, n+j+k = n+k+j)
    rw [map_eq_of_mem (fun l => a l * s (n + l + j)) (fun l => a l * s (n + j + l))
          (fun l _ => by show a l * s (n + l + j) = a l * s (n + j + l); rw [Nat.add_right_comm n l j]),
        ← hrec (n + j)]
    show hankelMat s (n + 1) i j = s (n + j + k)
    rw [hankelMat_shift, show hankelMat s n (i + 1) j = s (n + (i + 1) + j) from rfl, hlast,
        Nat.add_right_comm n k j]
  · -- shift row (i+1 < k): the companion picks out row i+1
    have hi1 : i + 1 < k := Nat.lt_of_le_of_ne hi (fun e => hlast e)
    have hterm : ∀ l, companion a k i l * hankelMat s n l j
        = (if i + 1 = l then hankelMat s n l j else 0) := fun l => by
      show (if i + 1 = k then a l else (if l = i + 1 then 1 else 0)) * hankelMat s n l j
         = (if i + 1 = l then hankelMat s n l j else 0)
      rw [if_neg hlast]
      by_cases hli : l = i + 1
      · rw [if_pos hli, if_pos hli.symm, Int.one_mul]
      · rw [if_neg hli, if_neg (fun e => hli e.symm), zero_mul]
    rw [map_eq_of_mem _ (fun l => if i + 1 = l then hankelMat s n l j else 0) (fun l _ => hterm l),
        sumZ_iota_delta_lt (fun l => hankelMat s n l j) (i + 1) k hi1, hankelMat_shift]

/-- ★★★★ **The order-`k` Casoratian multiplier law (all orders).**  For a constant-coefficient
    order-`(K+1)` recurrence `s(m+K+1) = Σ_{l≤K} a l · s(m+l)`, the `(K+1)×(K+1)` Hankel
    (Casoratian) determinant multiplies by the companion determinant `altSign K · a 0` at every
    step:

    `casoratian s (K+1) (n+1) = altSign K · a 0 · casoratian s (K+1) n`.

    The structural closure of the determinantal depth ladder — `det_step` (order 2) and
    `second_casoratian` (order 3) are the `K = 1, 2` cases, no expansion needed. -/
theorem casoratian_det_step (s : Nat → Int) (a : Nat → Int) (K n : Nat)
    (hrec : ∀ m, s (m + (K + 1)) = sumZ ((iota (K + 1)).map (fun l => a l * s (m + l)))) :
    casoratian s (K + 1) (n + 1) = altSign K * a 0 * casoratian s (K + 1) n := by
  show det (K + 1) (hankelMat s (n + 1)) = altSign K * a 0 * det (K + 1) (hankelMat s n)
  rw [det_congr_lt (K + 1) (hankel_shift_eq_matMul s a (K + 1) n hrec),
      det_matMul (companion a (K + 1)) (hankelMat s n) (K + 1),
      det_companion a K]

/-- The closed form: iterating the multiplier law, `casoratian s (K+1) n = (altSign K · a 0)ⁿ ·
    casoratian s (K+1) 0`. -/
def qpow (q : Int) : Nat → Int
  | 0     => 1
  | n + 1 => q * qpow q n

/-- ★★★ **Closed form of the Casoratian along the offset.** -/
theorem casoratian_det_closed (s : Nat → Int) (a : Nat → Int) (K : Nat)
    (hrec : ∀ m, s (m + (K + 1)) = sumZ ((iota (K + 1)).map (fun l => a l * s (m + l)))) :
    ∀ n, casoratian s (K + 1) n = qpow (altSign K * a 0) n * casoratian s (K + 1) 0
  | 0     => by show casoratian s (K + 1) 0 = 1 * casoratian s (K + 1) 0; rw [Int.one_mul]
  | n + 1 => by
      rw [casoratian_det_step s a K n hrec, casoratian_det_closed s a K hrec n]
      exact (mul_assoc (altSign K * a 0) (qpow (altSign K * a 0) n)
              (casoratian s (K + 1) 0)).symm

/-! ## §4 — the ladder rungs as instances (orders 2, 3, 4)

The general law specialises to each rung by reading off `altSign K`.  `casoratian s 2` is the
`2×2` Hankel determinant `s n·s(n+2) − s(n+1)²` (the object of `CassiniUnimodular.det_step`) and
`casoratian s 3` the `3×3` one (the object of `SecondCasoratian.second_casoratian`); the order-4
rung below lies beyond a direct `ring_intZ` expansion (its `4×4` Hankel normal form exceeds the
kernel) — here a one-line instance. -/

/-- **Order 2** (`K = 1`): multiplier `altSign 1 · a 0 = −a 0`.  With the `det_step` convention
    `s(m+2) = p·s(m+1) − q·s(m)` (`a 0 = −q`) this is `q` — `CassiniUnimodular.det_step`. -/
theorem second_order_multiplier (s a : Nat → Int) (n : Nat)
    (hrec : ∀ m, s (m + 2) = sumZ ((iota 2).map (fun l => a l * s (m + l)))) :
    casoratian s 2 (n + 1) = -(a 0) * casoratian s 2 n := by
  rw [casoratian_det_step s a 1 n hrec]
  show -(1 : Int) * a 0 * casoratian s 2 n = -(a 0) * casoratian s 2 n
  rw [neg_mul, Int.one_mul]

/-- **Order 3** (`K = 2`): multiplier `altSign 2 · a 0 = a 0` — `SecondCasoratian.second_casoratian`. -/
theorem third_order_multiplier (s a : Nat → Int) (n : Nat)
    (hrec : ∀ m, s (m + 3) = sumZ ((iota 3).map (fun l => a l * s (m + l)))) :
    casoratian s 3 (n + 1) = a 0 * casoratian s 3 n := by
  rw [casoratian_det_step s a 2 n hrec]
  show -(-(1 : Int)) * a 0 * casoratian s 3 n = a 0 * casoratian s 3 n
  rw [Int.neg_neg, Int.one_mul]

/-- ★★★ **Order 4** (`K = 3`): multiplier `altSign 3 · a 0 = −a 0` — the rung `ring_intZ` could not
    reach by direct expansion (the `4×4` Hankel normal form exceeds the kernel), here a one-line
    instance of the structural law. -/
theorem fourth_order_multiplier (s a : Nat → Int) (n : Nat)
    (hrec : ∀ m, s (m + 4) = sumZ ((iota 4).map (fun l => a l * s (m + l)))) :
    casoratian s 4 (n + 1) = -(a 0) * casoratian s 4 n := by
  rw [casoratian_det_step s a 3 n hrec]
  show -(-(-(1 : Int))) * a 0 * casoratian s 4 n = -(a 0) * casoratian s 4 n
  rw [Int.neg_neg, neg_mul, Int.one_mul]

end E213.Lib.Math.Analysis.Cauchy.CasoratianDeterminant
