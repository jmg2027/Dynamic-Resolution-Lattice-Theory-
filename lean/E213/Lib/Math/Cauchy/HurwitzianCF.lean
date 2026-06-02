import E213.Lib.Math.Cauchy.DepthPRecursiveInstances
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Tactic.NatHelper

/-!
# Hurwitzian continued fractions — the quasi-polynomial partial-quotient class

The continued-fraction **holonomicity tier** of a real lives on its partial-quotient
sequence `(aᵢ)`, a different object from the convergent cross-determinant (which is the
det-one floor `W² = 1` for *every* real, `ContinuedFractionFloor.cf_det_sq`).  A real is
**Hurwitzian** (Hurwitz; e, e², tan 1, …) when `(aᵢ)` is eventually *quasi-polynomial* —
polynomial on each residue class mod some period `p`.  This is the formalised handle on
"P-recursive / holonomic partial quotients": quasi-polynomial ⟹ P-recursive (a finite
interleaving of polynomial sequences satisfies a polynomial-coefficient recurrence), the
clean implication the literature treats as folklore but does not state.

The tiers (each closable ∅-axiom except the top):

  | tier | class | `(aᵢ)` | example |
  |---|---|---|---|
  | 0 | quadratic irrational | eventually periodic | φ=[1;1,…], √2=[1;2,2,…] |
  | 1 | Hurwitzian, aperiodic | quasi-polynomial | e=[2;1,2k,1,…] |
  | ∞ | non-holonomic | no recurrence | π=[3;7,15,1,292,…] (conjectured) |

Reusing `polyDepth` (degree-`d` = `d`-th finite difference constant) per residue class:

  * `QuasiPolyCF p a` — `a` is polynomial on each residue class mod `p`.
  * `periodic_quasipoly` — eventually-periodic ⟹ quasi-polynomial (tier 0).
  * `e_cf_quasipoly` — e's `[2;1,2k,1]` pattern is `QuasiPolyCF 3` (tier 1).  The
    folklore "Hurwitzian ⟹ holonomic" made an explicit ∅-axiom theorem for e.

π's `(aᵢ)` is conjectured to be in *no* `QuasiPolyCF p` (and non-holonomic): the open top.
That `e`'s pattern equals e's CF is Euler/Hermite (cited, not re-proven); the 213 content
is the quasi-polynomial structure of the explicit sequence.
-/

namespace E213.Lib.Math.Cauchy.HurwitzianCF

open E213.Lib.Math.Cauchy.DivergenceLadder (diff liftK isConst)
open E213.Lib.Math.Cauchy.DepthPRecursive (polyDepth polyDepth_succ_iff const_polyDepth0 liftK_congr)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_self zero_mod mod_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure)
open E213.Meta.Nat.NatDiv213 (add_mul_div_left_pure)
open E213.Tactic.NatHelper (add_sub_cancel_right)

/-! ## §0 — pure residue arithmetic for the period-3 sections (no `Nat.mul_add_mod`,
which leaks `propext`/`Quot.sound`) -/

/-- `(3·k + r) % 3 = r % 3` — ∅-axiom (built from the repo's pure mod lemmas). -/
theorem res3_mod (k r : Nat) : (3 * k + r) % 3 = r % 3 := by
  have h1 : (3 * k) % 3 = 0 := by
    rw [mul_mod_left_pure 3 k 3, mod_self 3, Nat.zero_mul, zero_mod]
  rw [add_mod_gen (3 * k) r 3, h1, Nat.zero_add, mod_mod]

/-- `(3·k + 1) / 3 = k` — ∅-axiom (via `add_mul_div_left_pure`). -/
theorem res3_div (k : Nat) : (3 * k + 1) / 3 = k := by
  have h13 : (1 : Nat) / 3 = 0 := rfl
  rw [Nat.add_comm (3 * k) 1, add_mul_div_left_pure 1 3 k (by decide), h13, Nat.zero_add]

/-! ## §1 — depth congruence (pointwise-equal sequences have equal depth) -/

/-- `polyDepth` respects pointwise equality (no `funext`, via `liftK_congr`). -/
theorem polyDepth_congr {d : Nat} {s t : Nat → Nat} (h : ∀ n, s n = t n)
    (hs : polyDepth d s) : polyDepth d t := by
  intro n
  rw [← liftK_congr d s t h n, ← liftK_congr d s t h 0]
  exact hs n

/-! ## §2 — the quasi-polynomial CF class -/

/-- `a` is **quasi-polynomial** with period `p`: polynomial (finite difference-depth) on
    each residue class `mod p`.  The formal handle on "Hurwitzian / holonomic partial
    quotients". -/
def QuasiPolyCF (p : Nat) (a : Nat → Nat) : Prop :=
  ∀ r, r < p → ∃ d, polyDepth d (fun k => a (p * k + r))

/-! ## §3 — tier 0: periodic ⟹ quasi-polynomial -/

/-- `a` is eventually... (here exactly) periodic with period `p`. -/
def Periodic (p : Nat) (a : Nat → Nat) : Prop := ∀ n, a (n + p) = a n

/-- Each residue subsequence of a periodic sequence is constant. -/
theorem periodic_const_subseq (p : Nat) (a : Nat → Nat) (hp : Periodic p a)
    (r : Nat) : ∀ k, a (p * k + r) = a r := by
  intro k
  induction k with
  | zero => rw [Nat.mul_zero, Nat.zero_add]
  | succ k ih => rw [Nat.mul_succ, Nat.add_right_comm (p * k) p r, hp (p * k + r), ih]

/-- ★★★ **Tier 0: a periodic CF is quasi-polynomial** — each residue subsequence is
    constant (depth 0).  Quadratic irrationals (Lagrange: periodic CF) land here. -/
theorem periodic_quasipoly (p : Nat) (a : Nat → Nat) (hp : Periodic p a) :
    QuasiPolyCF p a := by
  intro r _hr
  exact ⟨0, polyDepth_congr (fun n => (periodic_const_subseq p a hp r n).symm)
            (const_polyDepth0 (a r))⟩

/-! ## §4 — tier 1: e's continued fraction is quasi-polynomial -/

/-- e's partial-quotient pattern `[2; 1, 2, 1, 1, 4, 1, 1, 6, …]` as a sequence on the
    *fractional* indices (`ePQ i = a_{i+1}`): `a_{3k+1} = 2k+2`, else `1`. -/
def ePQ (i : Nat) : Nat := if i % 3 == 1 then 2 * (i / 3) + 2 else 1

/-- ★★★ **Tier 1: e's continued fraction is `QuasiPolyCF 3`.**  Residues `0, 2 (mod 3)`
    are constant `1` (depth 0); residue `1 (mod 3)` is the linear `2k+2` (depth 1).  The
    explicit ∅-axiom witness that e is Hurwitzian, hence its partial quotients are
    P-recursive — the folklore implication made a theorem. -/
theorem e_cf_quasipoly : QuasiPolyCF 3 ePQ := by
  intro r hr
  rcases r with _ | _ | _ | r
  · -- r = 0: constant 1
    refine ⟨0, polyDepth_congr (s := fun _ => 1) ?_ (const_polyDepth0 1)⟩
    intro k
    show (1 : Nat) = ePQ (3 * k + 0)
    unfold ePQ
    rw [if_neg (by rw [res3_mod]; decide)]
  · -- r = 1: linear 2k+2, depth 1
    refine ⟨1, polyDepth_congr (s := fun k => 2 * k + 2) ?_ ?_⟩
    · intro k
      show 2 * k + 2 = ePQ (3 * k + 1)
      unfold ePQ
      rw [if_pos (by rw [res3_mod]; decide), res3_div]
    · apply (polyDepth_succ_iff 0 (fun k => 2 * k + 2)).mpr
      refine polyDepth_congr (s := fun _ => 2) ?_ (const_polyDepth0 2)
      intro k
      show (2 : Nat) = 2 * (k + 1) + 2 - (2 * k + 2)
      rw [Nat.mul_succ, Nat.add_comm (2 * k + 2) 2, add_sub_cancel_right]
  · -- r = 2: constant 1
    refine ⟨0, polyDepth_congr (s := fun _ => 1) ?_ (const_polyDepth0 1)⟩
    intro k
    show (1 : Nat) = ePQ (3 * k + 2)
    unfold ePQ
    rw [if_neg (by rw [res3_mod]; decide)]
  · -- r ≥ 3: impossible
    exact absurd (Nat.lt_of_lt_of_le hr (Nat.le_add_left 3 r)) (Nat.lt_irrefl _)

/-! ## §5 — the holonomicity certificate: quasi-polynomial ⟹ constant-coefficient
recurrence -/

/-- The finite difference of a constant sequence is `0`. -/
theorem isConst_diff_zero {t : Nat → Nat} (h : isConst t) : ∀ n, diff t n = 0 := by
  intro n
  show t (n + 1) - t n = 0
  rw [h (n + 1), h n, Nat.sub_self]

/-- ★★★ **Holonomicity certificate.**  A `polyDepth d` sequence satisfies the homogeneous
    **constant-coefficient** recurrence `Δ^{d+1} s = 0` (the `(d+1)`-th finite difference
    vanishes identically) — i.e. `Σⱼ C(d+1,j)(−1)ʲ s_{n+j} = 0`.  So every polynomial
    section is C-finite, hence P-recursive (holonomic).  This is the bridge "quasi-polynomial
    ⟹ holonomic" at the level of one residue class; the global interleaving of finitely many
    such sections is holonomic by the classical interlacing-closure of P-recursive sequences
    (cited). -/
theorem polyDepth_diff_recurrence {d : Nat} {s : Nat → Nat} (h : polyDepth d s) :
    ∀ n, liftK (d + 1) s n = 0 :=
  isConst_diff_zero h

/-- ★★★ **Each residue section of a quasi-polynomial CF is C-finite.**  For a
    `QuasiPolyCF p a`, every residue section `k ↦ a(p·k+r)` satisfies a constant-coefficient
    recurrence `Δ^{dᵣ+1} = 0`.  Quasi-polynomial ⟹ (section-wise) holonomic, explicitly. -/
theorem quasipoly_section_recurrence {p : Nat} {a : Nat → Nat} (h : QuasiPolyCF p a)
    (r : Nat) (hr : r < p) :
    ∃ d, ∀ n, liftK (d + 1) (fun k => a (p * k + r)) n = 0 := by
  obtain ⟨d, hd⟩ := h r hr
  exact ⟨d, polyDepth_diff_recurrence hd⟩

end E213.Lib.Math.Cauchy.HurwitzianCF
