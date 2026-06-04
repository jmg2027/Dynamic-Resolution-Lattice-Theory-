import E213.Lib.Math.Analysis.Cauchy.NewtonGregory
import E213.Lib.Math.Analysis.Cauchy.HurwitzianCF
import E213.Meta.Nat.AddMod213

/-!
# QuasiPolyBound — quasi-polynomial continued fractions are polynomially bounded

The Hurwitzian ⟹ μ=2 spine, ∅-axiom.  `NewtonGregory.poly_bound` bounds a single
faithfully-depth-`d` `ℤ`-sequence; this file lifts it to the whole partial-quotient
sequence of a **quasi-polynomial** continued fraction (the `ℤ`-faithful analogue of
`HurwitzianCF.QuasiPolyCF`):

> ★★★ `quasiPolyCFZ_poly_bounded` : if every residue section `k ↦ a(p·k+r)` is a
> genuinely depth-`dᵣ` `ℤ`-sequence (`QuasiPolyCFZ p a`), then the whole sequence is
> polynomially bounded — `∃ C D, ∀ n, a n ≤ C·(n+1)^D`.

This closes the general bridge `HANDOFF` flagged Newton–Gregory-blocked over `ℕ`
(the per-residue bounds are reassembled with a finite max and the `n = p·⌊n/p⌋ +
n%p` decomposition).  By the classical `μ = 2 + limsupₙ (ln a_{n+1} / ln qₙ)`
(cited), polynomially-bounded partial quotients ⟹ `μ = 2`.

Two witnesses: **periodic** continued fractions (quadratic irrationals, Lagrange)
land at degree 0 — *bounded* partial quotients; **e** = [2;1,2k,1,…] lands with a
linear residue section — the general machinery subsuming `ePQ_linear_bound`.

All ∅-axiom (`poly_bound` + pure finite-max + the pure `div_add_mod`).
-/

namespace E213.Lib.Math.Analysis.Cauchy.QuasiPolyBound

open E213.Lib.Math.Analysis.Cauchy.NewtonGregory (liftKZ diffZ polyDepthZ poly_bound)
open E213.Lib.Math.Analysis.Cauchy.DepthPRecursive (polyDepth)
open E213.Lib.Math.Analysis.Cauchy.HurwitzianCF
  (QuasiPolyCF Periodic periodic_const_subseq ePQ res3_div resP_mod)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Meta.Nat.NatDiv213 (div_le_self_pos)
open E213.Tactic.NatHelper (add_sub_of_le)
open E213.Meta.Int213 (add_comm add_assoc add_neg_cancel)

/-! ## §1 — a pure finite maximum (core `Nat.max`/`le_max_*` pull `propext`) -/

/-- Pure binary max: `nmax a b = a + (b − a) = max a b`. -/
def nmax (a b : Nat) : Nat := a + (b - a)

theorem le_nmax_left (a b : Nat) : a ≤ nmax a b := Nat.le_add_right a (b - a)

theorem le_nmax_right (a b : Nat) : b ≤ nmax a b := by
  unfold nmax
  rcases Nat.le_total a b with h | h
  · exact Nat.le_of_eq (add_sub_of_le h).symm
  · exact Nat.le_trans h (Nat.le_add_right a (b - a))

/-- Max of `f r` over `r < q`. -/
def maxOver : Nat → (Nat → Nat) → Nat
  | 0,   _ => 0
  | q+1, f => nmax (f q) (maxOver q f)

theorem maxOver_ge (f : Nat → Nat) : ∀ q r, r < q → f r ≤ maxOver q f
  | 0,   r, h => absurd h (Nat.not_lt_zero r)
  | q+1, r, h => by
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with heq | hlt
    · rw [heq]; exact le_nmax_left (f q) (maxOver q f)
    · exact Nat.le_trans (maxOver_ge f q r hlt) (le_nmax_right (f q) (maxOver q f))

/-! ## §2 — ℤ-faithful quasi-polynomial continued fractions -/

/-- `a` is **quasi-polynomial over `ℤ`** with period `p`: every residue section
    `k ↦ a(p·k+r)`, lifted to `ℤ`, is genuinely depth-`dᵣ` (faithful `polyDepthZ`,
    unlike the ℕ-truncated `QuasiPolyCF`).  The formal handle on "Hurwitzian
    partial quotients" that survives the difference operator. -/
def QuasiPolyCFZ (p : Nat) (a : Nat → Nat) : Prop :=
  ∀ r, r < p → ∃ d, polyDepthZ d (fun k => (a (p * k + r) : Int))

/-- Each residue section is polynomially bounded (`poly_bound` + `|↑m| = m`). -/
theorem section_bound {p : Nat} {a : Nat → Nat} {r : Nat}
    (h : ∃ d, polyDepthZ d (fun k => (a (p * k + r) : Int))) :
    ∃ C d, ∀ k, a (p * k + r) ≤ C * (k + 1) ^ d := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨C, hC⟩ := poly_bound hd
  exact ⟨C, d, fun k => hC k⟩

/-! ## §3 — reassembly: per-residue bounds ⟹ a uniform bound over `r < q` -/

/-- Induct on the residue count `q`: a single `(C, D)` bounding every section
    `r < q` (finite max of the per-residue `(Cᵣ, dᵣ)`). -/
theorem partial_bound (p : Nat) (a : Nat → Nat) :
    ∀ q, (∀ r, r < q → ∃ d, polyDepthZ d (fun k => (a (p * k + r) : Int)))
      → ∃ C D, ∀ r, r < q → ∀ k, a (p * k + r) ≤ C * (k + 1) ^ D
  | 0,   _ => ⟨0, 0, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  | q+1, h => by
    obtain ⟨C', D', hCD'⟩ := partial_bound p a q (fun r hr => h r (Nat.lt_succ_of_lt hr))
    obtain ⟨Cq, dq, hq⟩ := section_bound (h q (Nat.lt_succ_self q))
    refine ⟨nmax C' Cq, nmax D' dq, fun r hr k => ?_⟩
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hr) with heq | hlt
    · rw [heq]
      exact Nat.le_trans (hq k)
        (Nat.mul_le_mul (le_nmax_right C' Cq)
          (Nat.pow_le_pow_right (Nat.le_add_left 1 k) (le_nmax_right D' dq)))
    · exact Nat.le_trans (hCD' r hlt k)
        (Nat.mul_le_mul (le_nmax_left C' Cq)
          (Nat.pow_le_pow_right (Nat.le_add_left 1 k) (le_nmax_left D' dq)))

/-! ## §4 — the headline: quasi-polynomial CF ⟹ polynomially-bounded p.q. -/

/-- ★★★ **Quasi-polynomial continued fractions are polynomially bounded.**
    `QuasiPolyCFZ p a ⟹ ∃ C D, ∀ n, a n ≤ C·(n+1)^D`.  Reassemble the per-residue
    `poly_bound`s (uniform `(C, D)` via `partial_bound`), then for arbitrary `n`
    decompose `n = p·⌊n/p⌋ + n%p` and bound `⌊n/p⌋ + 1 ≤ n + 1`.  By the classical
    `μ` formula (cited), this gives `μ = 2` — the ∅-axiom half of "Hurwitzian ⟹
    μ = 2".  Closes `HANDOFF` Open Problem #4's downstream T4. -/
theorem quasiPolyCFZ_poly_bounded {p : Nat} {a : Nat → Nat} (hp : 0 < p)
    (h : QuasiPolyCFZ p a) : ∃ C D, ∀ n, a n ≤ C * (n + 1) ^ D := by
  obtain ⟨C, D, hCD⟩ := partial_bound p a p (fun r hr => h r hr)
  refine ⟨C, D, fun n => ?_⟩
  have hb : a (p * (n / p) + n % p) ≤ C * (n / p + 1) ^ D := hCD (n % p) (Nat.mod_lt n hp) (n / p)
  rw [div_add_mod n p] at hb
  exact Nat.le_trans hb
    (Nat.mul_le_mul (Nat.le_refl C)
      (Nat.pow_le_pow_left (Nat.succ_le_succ (div_le_self_pos n p hp)) D))

/-! ## §5 — witnesses -/

/-- A periodic continued fraction is `QuasiPolyCFZ` (every section is constant,
    depth 0). -/
theorem periodic_quasiPolyCFZ (p : Nat) (a : Nat → Nat) (hper : Periodic p a) :
    QuasiPolyCFZ p a := by
  intro r _hr
  refine ⟨0, fun n => ?_⟩
  show ((a (p * n + r) : Int)) = ((a (p * 0 + r) : Int))
  rw [periodic_const_subseq p a hper r n, periodic_const_subseq p a hper r 0]

/-- ★★ **Quadratic irrationals have bounded partial quotients** (Lagrange, the
    degree-0 case): a periodic CF is polynomially bounded — in fact `a n ≤ C`
    (`D = 0`, `(n+1)^0 = 1`). -/
theorem periodic_partial_bounded {p : Nat} {a : Nat → Nat} (hp : 0 < p)
    (hper : Periodic p a) : ∃ C D, ∀ n, a n ≤ C * (n + 1) ^ D :=
  quasiPolyCFZ_poly_bounded hp (periodic_quasiPolyCFZ p a hper)

/-- `(x + c) − x = c` (pure). -/
theorem add_sub_self_left (x c : Int) : (x + c) - x = c := by
  rw [Int.sub_eq_add_neg, add_comm x c, add_assoc, add_neg_cancel, Int.add_zero]

/-- ★★★ **e's continued fraction is `QuasiPolyCFZ 3`** (the transcendental
    Hurwitzian witness).  Residues `0, 2 (mod 3)` are constant `1` (`polyDepthZ 0`);
    residue `1 (mod 3)` is the linear `2k+2`, whose faithful first difference is the
    constant `2` (`polyDepthZ 1`).  The ℤ-faithful counterpart of `e_cf_quasipoly`. -/
theorem e_cf_quasiPolyCFZ : QuasiPolyCFZ 3 ePQ := by
  intro r hr
  rcases r with _ | _ | _ | r
  · -- r = 0: constant 1
    refine ⟨0, fun n => ?_⟩
    show ((ePQ (3 * n + 0) : Int)) = ((ePQ (3 * 0 + 0) : Int))
    rw [show ePQ (3 * n + 0) = 1 from by unfold ePQ; rw [if_neg (by rw [resP_mod]; decide)],
        show ePQ (3 * 0 + 0) = 1 from by unfold ePQ; rw [if_neg (by rw [resP_mod]; decide)]]
  · -- r = 1: linear 2k+2, faithful first difference constant 2
    have hval : ∀ k, ePQ (3 * k + 1) = 2 * k + 2 := fun k => by
      unfold ePQ; rw [if_pos (by rw [resP_mod]; decide), res3_div]
    have key : ∀ m : Nat, ((2 * (m + 1) + 2 : Nat) : Int) - ((2 * m + 2 : Nat) : Int) = 2 := by
      intro m
      rw [show (2 * (m + 1) + 2 : Nat) = (2 * m + 2) + 2 from by rw [Nat.mul_succ]]
      exact add_sub_self_left ((2 * m + 2 : Nat) : Int) 2
    refine ⟨1, fun n => ?_⟩
    show diffZ (fun k => ((ePQ (3 * k + 1) : Nat) : Int)) n
       = diffZ (fun k => ((ePQ (3 * k + 1) : Nat) : Int)) 0
    show ((ePQ (3 * (n + 1) + 1) : Int)) - ((ePQ (3 * n + 1) : Int))
       = ((ePQ (3 * (0 + 1) + 1) : Int)) - ((ePQ (3 * 0 + 1) : Int))
    rw [hval (n + 1), hval n, hval (0 + 1), hval 0, key n, key 0]
  · -- r = 2: constant 1
    refine ⟨0, fun n => ?_⟩
    show ((ePQ (3 * n + 2) : Int)) = ((ePQ (3 * 0 + 2) : Int))
    rw [show ePQ (3 * n + 2) = 1 from by unfold ePQ; rw [if_neg (by rw [resP_mod]; decide)],
        show ePQ (3 * 0 + 2) = 1 from by unfold ePQ; rw [if_neg (by rw [resP_mod]; decide)]]
  · exact absurd (Nat.lt_of_le_of_lt (Nat.le_add_left 3 r) hr) (Nat.lt_irrefl 3)

/-- ★★ **e's partial quotients are polynomially bounded** — the general spine
    (`quasiPolyCFZ_poly_bounded`) reaching the canonical Hurwitzian transcendental,
    subsuming the hand-built `HurwitzianCF.ePQ_linear_bound`.  Hence (cited) the
    irrationality measure `μ(e) = 2`. -/
theorem e_partial_quotients_poly_bounded : ∃ C D, ∀ n, ePQ n ≤ C * (n + 1) ^ D :=
  quasiPolyCFZ_poly_bounded (by decide) e_cf_quasiPolyCFZ

end E213.Lib.Math.Analysis.Cauchy.QuasiPolyBound
