import E213.Lib.Math.NumberTheory.AperyRecurrence

/-!
# AperyCollapsing — the algebraic core of the c-increment collapsing laws

The ζ(3) numerator coefficient `c(n,k) = H₃(n) + κ(n,k)` (harmonic + kernel,
`research-notes/frontiers/zeta3_wz/numerator_plan.md`) has **both increments
collapsing** to rational multiples of the half-weight carrier
`√b = C(n,k)·C(n+k,k)` (verified exact: `zeta3_wz/verify_c_increments.py`):

    (1)  c(n,k) − c(n−1,k) = (−1)^k     · w(n,k) / (n²(n−k))     (cross-`n`)
    (2)  c(n,k) − c(n,k−1) = (−1)^{k−1} · w(n,k) / (2k³)         (cross-`k`)

with `w = 1/√b`.  This re-reads the plan's "no clean WZ certificate" as a **cap
for the `b`-only certificate language** — the extension language over `(b, √b)`
is where the numerator recurrence's Δ-calculus is fully rational
(`frontiers/exterior_as_extension.md` §6 V1).

This file deposits the **all-ℕ algebraic core** of the collapsing laws — the
three identities the ℚ-proof of (1) reduces to, in the `AperyRecurrence`
brick style (`colrec`/`lowrec`/`choose_succ_mul` + `ring_nat`):

  * `sqw_shift_n` — the half-weight's cross-`n` contiguity
    `(n+1−m)·√b(n+1,m) = (n+1+m)·√b(n,m)`; equivalently
    `t(n,m)/t(n+1,m) = (n+1−m)/(n+1+m)`, the step that collapses each kernel
    summand's cross-`n` difference to a single term.
  * `sqw_shift_k` — the half-weight's cross-`k` contiguity
    `(k+1)²·√b(n,k+1) = (n−k)(n+k+1)·√b(n,k)`; the induction step's engine
    (in ℚ: `t(n,k)·(k+1)² = t(n,k+1)·(n+k+1)(n−k)`).
  * `square_split` — the cancellation `k² + (n+k)(n−k) = n²` (`k ≤ n`); the
    "miracle" that recombines the two partial fractions of the induction step
    (`1/(k+1)² − 1/n²` producing exactly the `(n+k+1)(n−k−1)` factor).

With these three, the ℚ-level induction on `k` proving (1) is two lines per
step; the remaining Lean work is the **cleared signed-sum assembly** (the
`HL`-style clearing of `c` by a factor `ℓ` with `cube_dvd_lcm_cube`/`heart_lcm`
discharging the divisibilities, and a pos/neg split for `(−1)^k`) — recorded in
`numerator_plan.md` §"RE-READ" as the next step, not claimed here.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.AperyCollapsing

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose choose_succ_mul
  choose_zero_right choose_self choose_one_right choose_symm_sum)
open E213.Lib.Math.NumberTheory.AperyRecurrence (colrec lowrec colA colB colC colC1
  G1a G1b aperyLead aperyLead_prod)
open E213.Tactic.NatHelper (add_sub_of_le add_sub_cancel_right)

/-- **The half-weight carrier** `√b(n,k) = C(n,k)·C(n+k,k)` — the integer whose
    square is the Apéry summand `b(n,k)` and whose reciprocal `w = 1/√b` carries
    both increments of the numerator coefficient `c`.  The reified operand of the
    extension move. -/
def sqw (n k : Nat) : Nat := choose n k * choose (n + k) k

/-- `√b(n,0) = 1` — the carrier is normalised at the boundary. -/
theorem sqw_zero (n : Nat) : sqw n 0 = 1 := by
  show choose n 0 * choose (n + 0) 0 = 1
  rw [choose_zero_right, choose_zero_right]

/-- ★★★ **Cross-`n` contiguity of the half-weight.**
    `(n+1−m)·√b(n+1,m) = (n+1+m)·√b(n,m)`.

    In ℚ this is `t(n,m)/t(n+1,m) = (n+1−m)/(n+1+m)` for the reciprocal
    `t = 1/√b` — the ratio that collapses the cross-`n` difference of each
    kernel summand of `c` to the single closed term
    `t(n+1,m)·(−2m)/(n+1−m)`.  Two `colrec` applications. -/
theorem sqw_shift_n (n m : Nat) :
    (n + 1 - m) * sqw (n + 1) m = (n + 1 + m) * sqw n m := by
  have h1 : (n + 1 - m) * choose (n + 1) m = (n + 1) * choose n m := colrec n m
  have h2 : (n + m + 1 - m) * choose (n + m + 1) m = (n + m + 1) * choose (n + m) m :=
    colrec (n + m) m
  have hidx : n + 1 + m = n + m + 1 := by ring_nat
  have hsub : n + m + 1 - m = n + 1 := by
    rw [← hidx]
    exact add_sub_cancel_right (n + 1) m
  have h2' : (n + 1) * choose (n + 1 + m) m = (n + 1 + m) * choose (n + m) m := by
    rw [hidx, ← hsub]
    exact h2
  calc (n + 1 - m) * sqw (n + 1) m
      = ((n + 1 - m) * choose (n + 1) m) * choose (n + 1 + m) m := by
        show (n + 1 - m) * (choose (n + 1) m * choose (n + 1 + m) m) = _
        ring_nat
    _ = ((n + 1) * choose n m) * choose (n + 1 + m) m := by rw [h1]
    _ = choose n m * ((n + 1) * choose (n + 1 + m) m) := by ring_nat
    _ = choose n m * ((n + 1 + m) * choose (n + m) m) := by rw [h2']
    _ = (n + 1 + m) * sqw n m := by
        show _ = (n + 1 + m) * (choose n m * choose (n + m) m)
        ring_nat

/-- ★★★ **Cross-`k` contiguity of the half-weight.**
    `(k+1)²·√b(n,k+1) = (n−k)·(n+k+1)·√b(n,k)`.

    In ℚ this is `t(n,k)·(k+1)² = t(n,k+1)·(n+k+1)(n−k)` — the engine of the
    collapsing induction's step (with `square_split` recombining the partial
    fractions).  `lowrec` on the first factor, the absorption `choose_succ_mul`
    on the second.  Holds for all `k` (both sides vanish for `k ≥ n`). -/
theorem sqw_shift_k (n k : Nat) :
    ((k + 1) * (k + 1)) * sqw n (k + 1) = ((n - k) * (n + k + 1)) * sqw n k := by
  have h1 : (k + 1) * choose n (k + 1) = (n - k) * choose n k := lowrec n k
  have h2 : (k + 1) * choose (n + (k + 1)) (k + 1) = (n + k + 1) * choose (n + k) k :=
    choose_succ_mul (n + k) k
  show ((k + 1) * (k + 1)) * (choose n (k + 1) * choose (n + (k + 1)) (k + 1))
      = ((n - k) * (n + k + 1)) * (choose n k * choose (n + k) k)
  calc ((k + 1) * (k + 1)) * (choose n (k + 1) * choose (n + (k + 1)) (k + 1))
      = ((k + 1) * choose n (k + 1)) * ((k + 1) * choose (n + (k + 1)) (k + 1)) := by
        ring_nat
    _ = ((n - k) * choose n k) * ((n + k + 1) * choose (n + k) k) := by rw [h1, h2]
    _ = ((n - k) * (n + k + 1)) * (choose n k * choose (n + k) k) := by ring_nat

/-- ★★ **The recombination square-split.**  `k² + (n+k)·(n−k) = n²` for `k ≤ n` —
    the cancellation that makes the collapsing induction's two partial fractions
    (`1/k² − 1/n²` over the common denominator) recombine into exactly the
    shifted half-weight factor.  Substituting `n = k + d` reduces it to the
    binomial square. -/
theorem square_split {n k : Nat} (h : k ≤ n) :
    k * k + (n + k) * (n - k) = n * n := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, (add_sub_of_le h).symm⟩
  have hd : k + d - k = d := by
    rw [Nat.add_comm k d]
    exact add_sub_cancel_right d k
  rw [hd]
  ring_nat

/-- ★★★ **The collapsing core, bundled.**  The three all-ℕ identities that the
    ℚ-proof of the cross-`n` collapsing law
    `c(n,k) − c(n−1,k) = (−1)^k·w(n,k)/(n²(n−k))` reduces to: the two
    half-weight contiguities and the square-split.  The remaining distance to
    the law itself is the cleared signed-sum assembly (ℚ-glue), not algebra. -/
theorem collapsing_core (n k m : Nat) (h : k ≤ n) :
    ((n + 1 - m) * sqw (n + 1) m = (n + 1 + m) * sqw n m)
    ∧ (((k + 1) * (k + 1)) * sqw n (k + 1) = ((n - k) * (n + k + 1)) * sqw n k)
    ∧ (k * k + (n + k) * (n - k) = n * n) :=
  ⟨sqw_shift_n n m, sqw_shift_k n k, square_split h⟩

/-! ## §2 — the `b`-welds (clearing the numerator-residual's pieces)

The ζ(3) numerator residual `U = (−1)^k√b·u` has four pieces
(`derive_numerator_certificate.py` step (3)); pieces 1–3 are `b(n',m)·w(n'',m)`
products whose cleared ℕ-forms are one-step corollaries of `sqw_shift_n`:
with `b = √b²`, the identity `b(j,m)·w(j+1,m) = √b(j,m)·(j+1−m)/(j+1+m)` clears
to `(j+1+m)·b(j,m) = (j+1−m)·√b(j,m)·√b(j+1,m)`, and likewise for the double
shift.  These welds are what step (b) of the round-4 plan
(`numerator_plan.md` §"THE NUMERATOR CERTIFICATE") ties `rnum_reduced` to the
actual binomial sums with. -/

/-- ★★ **Double cross-`n` contiguity.**
    `(n+1−m)(n+2−m)·√b(n+2,m) = (n+1+m)(n+2+m)·√b(n,m)` — two `sqw_shift_n`
    steps composed; the clearing ratio of `w(j+2,k)` against `√b(j,k)`. -/
theorem sqw_shift_n2 (n m : Nat) :
    ((n + 1 - m) * (n + 2 - m)) * sqw (n + 2) m = ((n + 1 + m) * (n + 2 + m)) * sqw n m := by
  have h1 : (n + 1 - m) * sqw (n + 1) m = (n + 1 + m) * sqw n m := sqw_shift_n n m
  have h2 : (n + 1 + 1 - m) * sqw (n + 1 + 1) m = (n + 1 + 1 + m) * sqw (n + 1) m :=
    sqw_shift_n (n + 1) m
  calc ((n + 1 - m) * (n + 2 - m)) * sqw (n + 2) m
      = (n + 1 - m) * ((n + 2 - m) * sqw (n + 2) m) := by ring_nat
    _ = (n + 1 - m) * ((n + 2 + m) * sqw (n + 1) m) := by rw [show (n + 2 - m) * sqw (n + 2) m
          = (n + 2 + m) * sqw (n + 1) m from h2]
    _ = (n + 2 + m) * ((n + 1 - m) * sqw (n + 1) m) := by ring_nat
    _ = (n + 2 + m) * ((n + 1 + m) * sqw n m) := by rw [h1]
    _ = ((n + 1 + m) * (n + 2 + m)) * sqw n m := by ring_nat

/-- ★★ **Weld for `u`-piece 1** (`b(n,m)·w(n+1,m)`):
    `(n+1+m)·b(n,m) = (n+1−m)·√b(n,m)·√b(n+1,m)`. -/
theorem b_weld_n1 (n m : Nat) :
    (n + 1 + m) * (sqw n m * sqw n m) = (n + 1 - m) * (sqw n m * sqw (n + 1) m) := by
  calc (n + 1 + m) * (sqw n m * sqw n m)
      = ((n + 1 + m) * sqw n m) * sqw n m := by ring_nat
    _ = ((n + 1 - m) * sqw (n + 1) m) * sqw n m := by rw [← sqw_shift_n]
    _ = (n + 1 - m) * (sqw n m * sqw (n + 1) m) := by ring_nat

/-- ★★ **Weld for `u`-piece 2** (`b(n,m)·w(n+2,m)`):
    `(n+1+m)(n+2+m)·b(n,m) = (n+1−m)(n+2−m)·√b(n,m)·√b(n+2,m)`. -/
theorem b_weld_n2 (n m : Nat) :
    ((n + 1 + m) * (n + 2 + m)) * (sqw n m * sqw n m)
      = ((n + 1 - m) * (n + 2 - m)) * (sqw n m * sqw (n + 2) m) := by
  calc ((n + 1 + m) * (n + 2 + m)) * (sqw n m * sqw n m)
      = (((n + 1 + m) * (n + 2 + m)) * sqw n m) * sqw n m := by ring_nat
    _ = (((n + 1 - m) * (n + 2 - m)) * sqw (n + 2) m) * sqw n m := by rw [← sqw_shift_n2]
    _ = ((n + 1 - m) * (n + 2 - m)) * (sqw n m * sqw (n + 2) m) := by ring_nat

/-- ★★ **Weld for `u`-piece 3** (`b(n+1,m)·w(n+2,m)`):
    `(n+2+m)·b(n+1,m) = (n+2−m)·√b(n+1,m)·√b(n+2,m)`. -/
theorem b_weld_mid (n m : Nat) :
    (n + 2 + m) * (sqw (n + 1) m * sqw (n + 1) m)
      = (n + 2 - m) * (sqw (n + 1) m * sqw (n + 2) m) := by
  have h2 : (n + 1 + 1 - m) * sqw (n + 1 + 1) m = (n + 1 + 1 + m) * sqw (n + 1) m :=
    sqw_shift_n (n + 1) m
  calc (n + 2 + m) * (sqw (n + 1) m * sqw (n + 1) m)
      = ((n + 2 + m) * sqw (n + 1) m) * sqw (n + 1) m := by ring_nat
    _ = ((n + 2 - m) * sqw (n + 2) m) * sqw (n + 1) m := by
        rw [show (n + 2 + m) * sqw (n + 1) m = (n + 2 - m) * sqw (n + 2) m from h2.symm]
    _ = (n + 2 - m) * (sqw (n + 1) m * sqw (n + 2) m) := by ring_nat

/-- ★★★ **The `b`-welds, bundled** — the cleared ℕ-forms of the numerator
    residual's pieces 1–3, each a `sqw_shift_n` corollary.  Together with
    `gb_weld` (piece 4) and `AperyNumeratorWZ.rnum_reduced` these are the
    step-(b) inputs of the round-4 assembly. -/
theorem b_welds (n m : Nat) :
    ((n + 1 + m) * (sqw n m * sqw n m) = (n + 1 - m) * (sqw n m * sqw (n + 1) m))
    ∧ (((n + 1 + m) * (n + 2 + m)) * (sqw n m * sqw n m)
        = ((n + 1 - m) * (n + 2 - m)) * (sqw n m * sqw (n + 2) m))
    ∧ ((n + 2 + m) * (sqw (n + 1) m * sqw (n + 1) m)
        = (n + 2 - m) * (sqw (n + 1) m * sqw (n + 2) m)) :=
  ⟨b_weld_n1 n m, b_weld_n2 n m, b_weld_mid n m⟩

/-- ★★★ **Weld for `u`-piece 4** (the `Ĝ`-piece's crossed reduction).  The
    Abel term `−Ĝ(j,k+1)·Δₖc(j+2,k+1)` carries the three crossed binomials
    `C(j+2,k+1)`, `C(j+k+1,k+1)²`, `C(j+k+3,k+1)`; they reduce against the
    row-`j` carrier `√b(j,k)`:

        (k+1)²(j+1−k)(j+k+2)(j+k+3) · C(j+2,k+1)·C(j+k+1,k+1)²
          = (j+1)²(j+2)² (j+k+1) · √b(j,k)·C(j+k+3,k+1).

    `G1a`+`G1b` clear the two `(k+1)`s, `colA` folds the row pair down to
    `C(j,k)`, `colC` (at `k+1`) folds the upper pair down to `C(j+k+1,k+1)`. -/
theorem gb_weld (j k : Nat) :
    ((k + 1) * (k + 1)) * ((j + 1 - k) * ((j + k + 2) * (j + k + 3)))
        * (choose (j + 2) (k + 1) * (choose (j + k + 1) (k + 1) * choose (j + k + 1) (k + 1)))
    = ((j + 1) * (j + 1)) * (((j + 2) * (j + 2))
        * ((j + k + 1) * (sqw j k * choose (j + k + 3) (k + 1)))) := by
  have hG1a : (k + 1) * choose (j + 2) (k + 1) = (j + 2 - k) * choose (j + 2) k := G1a j k
  have hG1b : (k + 1) * choose (j + k + 1) (k + 1) = (j + k + 1) * choose (j + k) k :=
    G1b j k
  have hcolC : (j + 1) * (j + 2) * choose (j + k + 3) (k + 1)
      = (j + k + 2) * (j + k + 3) * choose (j + k + 1) (k + 1) := colC j (k + 1)
  show _ = ((j + 1) * (j + 1)) * (((j + 2) * (j + 2))
      * ((j + k + 1) * ((choose j k * choose (j + k) k) * choose (j + k + 3) (k + 1))))
  calc ((k + 1) * (k + 1)) * ((j + 1 - k) * ((j + k + 2) * (j + k + 3)))
          * (choose (j + 2) (k + 1) * (choose (j + k + 1) (k + 1) * choose (j + k + 1) (k + 1)))
      = ((j + 1 - k) * ((j + k + 2) * (j + k + 3)))
          * (((k + 1) * choose (j + 2) (k + 1))
              * (((k + 1) * choose (j + k + 1) (k + 1)) * choose (j + k + 1) (k + 1))) := by
        ring_nat
    _ = ((j + 1 - k) * ((j + k + 2) * (j + k + 3)))
          * (((j + 2 - k) * choose (j + 2) k)
              * (((j + k + 1) * choose (j + k) k) * choose (j + k + 1) (k + 1))) := by
        rw [hG1a, hG1b]
    _ = ((j + k + 1) * choose (j + k) k)
          * (((j + 1 - k) * (j + 2 - k) * choose (j + 2) k)
              * ((j + k + 2) * (j + k + 3) * choose (j + k + 1) (k + 1))) := by
        ring_nat
    _ = ((j + k + 1) * choose (j + k) k)
          * (((j + 1) * (j + 2) * choose j k)
              * ((j + 1) * (j + 2) * choose (j + k + 3) (k + 1))) := by
        rw [← colA, ← hcolC]
    _ = ((j + 1) * (j + 1)) * (((j + 2) * (j + 2))
          * ((j + k + 1) * ((choose j k * choose (j + k) k) * choose (j + k + 3) (k + 1)))) := by
        ring_nat

/-! ## §3 — the `k = j+1` boundary welds (`T1`'s two pieces)

At the boundary column `k = j+1` the residual `U(j,j+1)` has exactly two
surviving terms (`b(j,j+1) = 0`), and `T1 = U(j,j+1)·(−1)^{j+1}/√b(j,j)`
splits as the aperyLead-piece plus the `Ĝ`-piece
(`derive_numerator_certificate.py` R-BND block).  Each piece's evaluation is a
cleared diagonal-binomial weld; the aperyLead-piece rides on the factorization
`aperyLead j = (2j+3)·(17j²+51j+39)`.  Diagonal indices are written `j+j+…`
(additive normal form). -/

/-- `C(j+2,j+1) = j+2` — the near-diagonal column (symmetry + `C(n,1) = n`). -/
theorem choose_succ_self_right (j : Nat) : choose (j + 2) (j + 1) = j + 2 := by
  rw [choose_symm_sum (j + 2) (j + 1) 1 (by ring_nat), choose_one_right]

/-- ★★ **Boundary weld, aperyLead-piece** (`aL(j)·b(j+1,j+1)·Δₙc(j+2,j+1)`):

        (j+1) · aL(j) · √b(j+1,j+1)²
          = 2(2j+1)(17j²+51j+39) · √b(j,j)·√b(j+2,j+1),

    the cleared form of the piece's value `2(2j+1)(17j²+51j+39)/((j+1)(j+2)²)`
    (·`(−1)^{j+1}√b(j,j)`).  Rides on `aperyLead j = (2j+3)(17j²+51j+39)` and
    the diagonal steps `G1b`/`colB`/`colC1`. -/
theorem t1_aL_weld (j : Nat) :
    (j + 1) * (aperyLead j * (sqw (j + 1) (j + 1) * sqw (j + 1) (j + 1)))
    = 2 * ((2 * j + 1)
        * ((17 * (j * j) + 51 * j + 39) * (sqw j j * sqw (j + 2) (j + 1)))) := by
  have hs1 : sqw (j + 1) (j + 1) = choose (j + j + 2) (j + 1) := by
    show choose (j + 1) (j + 1) * choose (j + 1 + (j + 1)) (j + 1) = _
    rw [choose_self, show j + 1 + (j + 1) = j + j + 2 from by ring_nat]
    ring_nat
  have hsjj : sqw j j = choose (j + j) j := by
    show choose j j * choose (j + j) j = _
    rw [choose_self]
    ring_nat
  have hs2 : sqw (j + 2) (j + 1) = (j + 2) * choose (j + j + 3) (j + 1) := by
    show choose (j + 2) (j + 1) * choose (j + 2 + (j + 1)) (j + 1) = _
    rw [choose_succ_self_right, show j + 2 + (j + 1) = j + j + 3 from by ring_nat]
  have hA : (j + 1) * choose (j + 1 + j + 1) (j + 1)
      = (j + 1 + j + 1) * choose (j + 1 + j) j := G1b (j + 1) j
  rw [show j + 1 + j + 1 = j + j + 2 from by ring_nat,
      show j + 1 + j = j + j + 1 from by ring_nat] at hA
  -- hA : (j+1) · C(2j+2,j+1) = (2j+2) · C(2j+1,j)
  have hB : (j + 1) * choose (j + j + 1) j = (j + j + 1) * choose (j + j) j := colB j j
  have hD : (j + 2) * choose (j + j + 3) (j + 1)
      = (j + j + 3) * choose (j + j + 2) (j + 1) := colC1 j (j + 1)
  rw [hs1, hsjj, hs2, aperyLead_prod, hD]
  calc (j + 1) * ((34 * (j * j * j) + 153 * (j * j) + 231 * j + 117)
          * (choose (j + j + 2) (j + 1) * choose (j + j + 2) (j + 1)))
      = (34 * (j * j * j) + 153 * (j * j) + 231 * j + 117)
          * (choose (j + j + 2) (j + 1) * ((j + 1) * choose (j + j + 2) (j + 1))) := by
        ring_nat
    _ = (34 * (j * j * j) + 153 * (j * j) + 231 * j + 117)
          * (choose (j + j + 2) (j + 1) * ((j + j + 2) * choose (j + j + 1) j)) := by
        rw [hA]
    _ = 2 * ((34 * (j * j * j) + 153 * (j * j) + 231 * j + 117)
          * (choose (j + j + 2) (j + 1) * ((j + 1) * choose (j + j + 1) j))) := by
        ring_nat
    _ = 2 * ((34 * (j * j * j) + 153 * (j * j) + 231 * j + 117)
          * (choose (j + j + 2) (j + 1) * ((j + j + 1) * choose (j + j) j))) := by
        rw [hB]
    _ = 2 * ((2 * j + 1) * ((17 * (j * j) + 51 * j + 39)
          * (choose (j + j) j * ((j + j + 3) * choose (j + j + 2) (j + 1))))) := by
        ring_nat

/-- ★★ **Boundary weld, `Ĝ`-piece** (`−Ĝ(j,j+2)·Δₖc(j+2,j+2)`, where
    `W(j,j+2) = C(2j+2,j+2)²` and `Q(j,j+2) = (j+2)(2j+3)`):

        (j+2)²(2j+3) · C(2j+2,j+2)²
          = (j+1)(j+2)(2j+1) · C(2j,j)·C(2j+4,j+2),

    the cleared form of the piece's value `2(2j+1)(2j+3)/((j+1)(j+2))`
    (·`(−1)^{j+1}√b(j,j)`).  Both sides reduce, by the diagonal `G1b` steps
    (left) and the `colB` steps (right), to the common normal form
    `2(j+2)(2j+3)(2j+1)·C(2j+2,j+2)·C(2j,j)`. -/
theorem t1_ghat_weld (j : Nat) :
    ((j + 2) * (j + 2)) * ((2 * j + 3)
        * (choose (j + j + 2) (j + 2) * choose (j + j + 2) (j + 2)))
    = (j + 1) * ((j + 2) * ((2 * j + 1)
        * (choose (j + j) j * choose (j + j + 4) (j + 2)))) := by
  have hE : (j + 2) * choose (j + j + 2) (j + 2)
      = (j + j + 2) * choose (j + j + 1) (j + 1) := G1b j (j + 1)
  have hF : (j + 1) * choose (j + j + 1) (j + 1) = (j + j + 1) * choose (j + j) j :=
    G1b j j
  have hG : (j + 2) * choose (j + 1 + (j + 2) + 1) (j + 2)
      = (j + 1 + (j + 2) + 1) * choose (j + 1 + (j + 2)) (j + 2) := colB (j + 1) (j + 2)
  rw [show j + 1 + (j + 2) + 1 = j + j + 4 from by ring_nat,
      show j + 1 + (j + 2) = j + j + 3 from by ring_nat] at hG
  -- hG : (j+2) · C(2j+4,j+2) = (2j+4) · C(2j+3,j+2)
  have hH : (j + 1) * choose (j + j + 3) (j + 2)
      = (j + j + 3) * choose (j + j + 2) (j + 2) := colB j (j + 2)
  have hL : ((j + 2) * (j + 2)) * ((2 * j + 3)
          * (choose (j + j + 2) (j + 2) * choose (j + j + 2) (j + 2)))
      = 2 * ((j + 2) * ((2 * j + 3) * ((2 * j + 1)
          * (choose (j + j + 2) (j + 2) * choose (j + j) j)))) := by
    calc ((j + 2) * (j + 2)) * ((2 * j + 3)
            * (choose (j + j + 2) (j + 2) * choose (j + j + 2) (j + 2)))
        = (2 * j + 3) * (choose (j + j + 2) (j + 2)
            * ((j + 2) * ((j + 2) * choose (j + j + 2) (j + 2)))) := by ring_nat
      _ = (2 * j + 3) * (choose (j + j + 2) (j + 2)
            * ((j + 2) * ((j + j + 2) * choose (j + j + 1) (j + 1)))) := by rw [hE]
      _ = (2 * j + 3) * (choose (j + j + 2) (j + 2)
            * ((j + 2) * (2 * ((j + 1) * choose (j + j + 1) (j + 1))))) := by ring_nat
      _ = (2 * j + 3) * (choose (j + j + 2) (j + 2)
            * ((j + 2) * (2 * ((j + j + 1) * choose (j + j) j)))) := by rw [hF]
      _ = 2 * ((j + 2) * ((2 * j + 3) * ((2 * j + 1)
            * (choose (j + j + 2) (j + 2) * choose (j + j) j)))) := by ring_nat
  have hR : (j + 1) * ((j + 2) * ((2 * j + 1)
          * (choose (j + j) j * choose (j + j + 4) (j + 2))))
      = 2 * ((j + 2) * ((2 * j + 3) * ((2 * j + 1)
          * (choose (j + j + 2) (j + 2) * choose (j + j) j)))) := by
    calc (j + 1) * ((j + 2) * ((2 * j + 1)
            * (choose (j + j) j * choose (j + j + 4) (j + 2))))
        = (j + 1) * ((2 * j + 1) * (choose (j + j) j
            * ((j + 2) * choose (j + j + 4) (j + 2)))) := by ring_nat
      _ = (j + 1) * ((2 * j + 1) * (choose (j + j) j
            * ((j + j + 4) * choose (j + j + 3) (j + 2)))) := by rw [hG]
      _ = (j + j + 4) * ((2 * j + 1) * (choose (j + j) j
            * ((j + 1) * choose (j + j + 3) (j + 2)))) := by ring_nat
      _ = (j + j + 4) * ((2 * j + 1) * (choose (j + j) j
            * ((j + j + 3) * choose (j + j + 2) (j + 2)))) := by rw [hH]
      _ = 2 * ((j + 2) * ((2 * j + 3) * ((2 * j + 1)
            * (choose (j + j + 2) (j + 2) * choose (j + j) j)))) := by ring_nat
  exact hL.trans hR.symm

end E213.Lib.Math.NumberTheory.AperyCollapsing
