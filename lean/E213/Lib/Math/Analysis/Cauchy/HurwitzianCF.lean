import E213.Lib.Math.Analysis.Cauchy.DepthPRecursiveInstances
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.PureNat
import E213.Meta.Tactic.NatHelper

/-!
# Hurwitzian continued fractions — the quasi-polynomial partial-quotient class

The continued-fraction **holonomicity tier** of a real lives on its partial-quotient
sequence `(aᵢ)`, a different object from the convergent cross-determinant (which is the
det-one floor `W² = 1` for *every* real, `ContinuedFractionFloor.cf_det_sq`).  A real is
**Hurwitzian** (Hurwitz; e, e², tan 1, …) when `(aᵢ)` is eventually *quasi-polynomial* —
polynomial on each residue class mod some period `p`.  `QuasiPolyCF p a` formalises this
(rational-coefficient, **integer-valued** polynomials — `polyDepth` is the integer-valued,
not integer-coefficient, class — one fixed polynomial per residue class).  It is a clean
*sufficient* condition for P-recursive: `QuasiPolyCF ⟹` each section is C-finite
(`polyDepth_diff_recurrence`, `Δ^{d+1} = 0`), and a finite interleaving of C-finite
sections is P-recursive (classical interlacing closure, cited) — the folklore "Hurwitzian ⟹
holonomic" the literature does not state.

  | tier | class | `(aᵢ)` | example |
  |---|---|---|---|
  | 0 | quadratic irrational | eventually periodic | φ=[1;1,…], √2=[1;2,2,…] |
  | 1 | Hurwitzian, aperiodic | quasi-polynomial | e=[2;1,2k,1,…], tan 1=[1;1,1,3,1,5,…] |
  | top | non-Hurwitzian | not `QuasiPolyCF` any `p` | `2ⁿ` (still C-finite!); π (conj.) |

**Scope honesty.**  `QuasiPolyCF ⊊ C-finite ⊊ holonomic/P-recursive` — strictly.  So the
top tier here is "**non-Hurwitzian**", which is *weaker* than "non-holonomic": `2ⁿ` is not
`QuasiPolyCF` (`geometric_not_quasipoly`) yet is C-finite (`2ⁿ⁺¹ = 2·2ⁿ`), hence holonomic.
"π is non-holonomic" is therefore a **strictly harder** open conjecture than "π is
non-Hurwitzian"; this file proves neither for π — it pins the provable tiers below it.

Reusing `polyDepth` (degree-`d` = `d`-th finite difference constant) per residue class:

  * `periodic_quasipoly` — eventually-periodic ⟹ quasi-polynomial (tier 0).
  * `e_cf_quasipoly`, `tan_cf_quasipoly` — tier-1 witnesses (e, tan 1).
  * `geometric_not_quasipoly` — the non-Hurwitzian tier is non-empty (`2ⁿ`), and
    `QuasiPolyCF ⊊ holonomic` is concrete.

That `e`'s/`tan 1`'s pattern equals the actual CF is Euler/Hermite (cited, not re-proven);
the 213 content is the quasi-polynomial structure of the explicit sequence.  Indexing:
`ePQ i = a_{i+1}` (the fractional partial quotients, `a₀` held outside); the `2k` terms of e
sit on residue `1 (mod 3)` in this 0-based index.
-/

namespace E213.Lib.Math.Analysis.Cauchy.HurwitzianCF

open E213.Lib.Math.Analysis.Cauchy.DivergenceLadder (diff liftK isConst)
open E213.Lib.Math.Analysis.Cauchy.DepthPRecursive (polyDepth polyDepth_succ_iff const_polyDepth0 liftK_congr)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_self zero_mod mod_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure)
open E213.Meta.Nat.NatDiv213 (add_mul_div_left_pure)
open E213.Tactic.NatHelper (add_sub_cancel_right)

/-! ## §0 — pure residue arithmetic for the period-3 sections (no `Nat.mul_add_mod`,
which leaks `propext`/`Quot.sound`) -/

/-- `(p·k + r) % p = r % p` — ∅-axiom (built from the repo's pure mod lemmas). -/
theorem resP_mod (p k r : Nat) : (p * k + r) % p = r % p := by
  have h1 : (p * k) % p = 0 := by
    rw [mul_mod_left_pure p k p, mod_self p, Nat.zero_mul, zero_mod]
  rw [add_mod_gen (p * k) r p, h1, Nat.zero_add, mod_mod]

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
    rw [if_neg (by rw [resP_mod]; decide)]
  · -- r = 1: linear 2k+2, depth 1
    refine ⟨1, polyDepth_congr (s := fun k => 2 * k + 2) ?_ ?_⟩
    · intro k
      show 2 * k + 2 = ePQ (3 * k + 1)
      unfold ePQ
      rw [if_pos (by rw [resP_mod]; decide), res3_div]
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
    rw [if_neg (by rw [resP_mod]; decide)]
  · -- r ≥ 3: impossible
    exact absurd (Nat.lt_of_lt_of_le hr (Nat.le_add_left 3 r)) (Nat.lt_irrefl _)

/-! ## §4b — tier 1, second witness: tan 1 = [1; 1, 1, 3, 1, 5, 1, 7, …] -/

/-- tan 1's partial-quotient pattern (`tanPQ i = a_{i+1}`): `a` is `i` on odd indices
    (`1, 3, 5, …`) and `1` on even indices.  `[1; 1, 1, 3, 1, 5, 1, 7, …]`. -/
def tanPQ (i : Nat) : Nat := if i % 2 == 0 then 1 else i

/-- ★★★ **Tier 1: tan 1's continued fraction is `QuasiPolyCF 2`.**  Residue `0 (mod 2)` is
    constant `1` (depth 0); residue `1 (mod 2)` is the linear `2k+1` (depth 1).  A second
    Hurwitzian witness (modulus 2, cheaper than e) — the tier is not an e-only artifact. -/
theorem tan_cf_quasipoly : QuasiPolyCF 2 tanPQ := by
  intro r hr
  rcases r with _ | _ | r
  · -- r = 0: constant 1
    refine ⟨0, polyDepth_congr (s := fun _ => 1) ?_ (const_polyDepth0 1)⟩
    intro k
    show (1 : Nat) = tanPQ (2 * k + 0)
    unfold tanPQ
    rw [if_pos (by rw [resP_mod]; decide)]
  · -- r = 1: linear 2k+1, depth 1
    refine ⟨1, polyDepth_congr (s := fun k => 2 * k + 1) ?_ ?_⟩
    · intro k
      show 2 * k + 1 = tanPQ (2 * k + 1)
      unfold tanPQ
      rw [if_neg (by rw [resP_mod]; decide)]
    · apply (polyDepth_succ_iff 0 (fun k => 2 * k + 1)).mpr
      refine polyDepth_congr (s := fun _ => 2) ?_ (const_polyDepth0 2)
      intro k
      show (2 : Nat) = 2 * (k + 1) + 1 - (2 * k + 1)
      rw [Nat.mul_succ, Nat.add_comm (2 * k + 1) 2, add_sub_cancel_right]
  · exact absurd (Nat.lt_of_lt_of_le hr (Nat.le_add_left 2 r)) (Nat.lt_irrefl _)

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

/-! ## §6 — the non-Hurwitzian tier is non-empty: `2ⁿ ∉ QuasiPolyCF` (yet C-finite) -/

open E213.Lib.Math.Analysis.Cauchy.DivergenceLadder (reachesFloor infinite_depth)
open E213.Lib.Math.Analysis.Cauchy.DepthPRecursive (polyDepth_reachesFloor)

/-- Pure `a^(m·n) = (a^m)^n` (Lean-core `Nat.pow_mul` pulls `propext`). -/
theorem pow_mul_pure (a m : Nat) : ∀ n, a ^ (m * n) = (a ^ m) ^ n := by
  intro n
  induction n with
  | zero => rw [Nat.mul_zero, Nat.pow_zero, Nat.pow_zero]
  | succ n ih => rw [Nat.mul_succ, E213.Meta.Nat.PureNat.pow_add, ih, Nat.pow_succ]

/-- Pure left-distributivity of truncated subtraction when `n ≤ m`. -/
theorem mul_sub_pure_le (k m n : Nat) (h : n ≤ m) : k * (m - n) = k * m - k * n := by
  have key : k * (m - n) + k * n = k * m := by
    rw [← Nat.mul_add, E213.Tactic.NatHelper.sub_add_cancel h]
  rw [← key, E213.Tactic.NatHelper.add_sub_cancel_right]

/-- The divergence ladder keeps a geometric sequence geometric: `Δʲ (c·bᵏ) = Aⱼ·bⁿ` for a
    coefficient `Aⱼ ≥ 1`.  (Existential form — the exact `Aⱼ = c·(b−1)ʲ` is absorbed, which
    is all `geom_infinite_depth` needs.) -/
theorem liftK_geo (c b : Nat) (hb : 2 ≤ b) (hc : 1 ≤ c) :
    ∀ j, ∃ A, 1 ≤ A ∧ ∀ n, liftK j (fun k => c * b ^ k) n = A * b ^ n := by
  intro j
  induction j with
  | zero => exact ⟨c, hc, fun _ => rfl⟩
  | succ j ih =>
    obtain ⟨A, hA, hform⟩ := ih
    have hb1 : 1 ≤ b - 1 := Nat.le_sub_one_of_lt hb
    refine ⟨A * (b - 1), Nat.mul_le_mul hA hb1, ?_⟩
    intro n
    show liftK j (fun k => c * b ^ k) (n + 1) - liftK j (fun k => c * b ^ k) n
        = A * (b - 1) * b ^ n
    rw [hform (n + 1), hform n,
        ← mul_sub_pure_le A (b ^ (n + 1)) (b ^ n)
          (Nat.pow_le_pow_right (Nat.le_trans (by decide) hb) (Nat.le_succ n)),
        Nat.pow_succ b n]
    have hbn : b ^ n * b - b ^ n = b ^ n * (b - 1) := by
      have h := mul_sub_pure_le (b ^ n) b 1 (Nat.le_trans (by decide) hb)
      rw [Nat.mul_one] at h; exact h.symm
    rw [hbn, Nat.mul_comm (b ^ n) (b - 1), ← E213.Tactic.NatHelper.mul_assoc]

/-- A geometric sequence `c·bᵏ` (`c ≥ 1`, `b ≥ 2`) has **no** finite divergence depth: at
    every lift level the value at `0` is strictly below the value at `1`. -/
theorem geom_infinite_depth (c b : Nat) (hc : 1 ≤ c) (hb : 2 ≤ b) :
    ¬ reachesFloor (fun k => c * b ^ k) := by
  apply infinite_depth
  intro j
  obtain ⟨A, hA, hform⟩ := liftK_geo c b hb hc j
  rw [hform 0, hform 1, Nat.pow_zero, Nat.mul_one, Nat.pow_one]
  -- A < A * b, since A ≥ 1 and b ≥ 2
  have hAb : A * 2 ≤ A * b := Nat.mul_le_mul_left A hb
  have hlt : A < A * 2 := by
    rw [Nat.mul_two]; exact Nat.lt_add_of_pos_left (Nat.lt_of_lt_of_le (by decide) hA)
  exact Nat.lt_of_lt_of_le hlt hAb

/-- ★★★ **The non-Hurwitzian tier is inhabited, strictly inside holonomic.**  `2ⁿ` is not
    `QuasiPolyCF` for any period `p` (the residue-`0` section `2^{p·k}` is geometric, no
    finite difference-depth), yet `2ⁿ` is C-finite (`2ⁿ⁺¹ = 2·2ⁿ`), hence holonomic.  So
    `QuasiPolyCF ⊊ holonomic` concretely, and "non-Hurwitzian" is strictly weaker than
    "non-holonomic" — the honest gap above which π's open conjecture sits. -/
theorem geometric_not_quasipoly : ∀ p, 1 ≤ p → ¬ QuasiPolyCF p (fun n => 2 ^ n) := by
  intro p hp hquasi
  obtain ⟨d, hd⟩ := hquasi 0 hp
  have hsec : ∀ k, (fun k => 2 ^ (p * k + 0)) k = (fun k => 1 * (2 ^ p) ^ k) k := by
    intro k
    show 2 ^ (p * k + 0) = 1 * (2 ^ p) ^ k
    rw [Nat.add_zero, pow_mul_pure, Nat.one_mul]
  have hd' : polyDepth d (fun k => 1 * (2 ^ p) ^ k) := polyDepth_congr hsec hd
  have h2p : 2 ≤ 2 ^ p := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hp
    rwa [Nat.pow_one] at h
  exact geom_infinite_depth 1 (2 ^ p) (Nat.le_refl 1) h2p
    (polyDepth_reachesFloor d _ hd')

/-! ## §7 — the bridge to the irrationality measure: Hurwitzian ⟹ polynomially-bounded
partial quotients

The irrationality measure satisfies `μ(x) = 2 + limsupₙ (ln a_{n+1} / ln qₙ)`; if the
partial quotients are bounded by a polynomial in `n` then `μ(x) = 2` (classical, cited).
So an *explicit polynomial bound* on the partial quotients is the ∅-axiom half of
"Hurwitzian ⟹ μ = 2".  Here the tier-1 witnesses get **linear** bounds — e and tan 1 are
badly-approximable-adjacent (`μ = 2`), read straight off the quasi-polynomial structure.
(The general `QuasiPolyCF ⟹ polynomially-bounded` needs the discrete Newton–Gregory bound,
which is delicate over `ℕ` truncated subtraction; the explicit witnesses sidestep it.) -/

/-- e's partial quotients grow at most linearly: `ePQ i ≤ 2·i + 2`.  Hence (cited) `μ(e)=2`. -/
theorem ePQ_linear_bound (i : Nat) : ePQ i ≤ 2 * i + 2 := by
  unfold ePQ
  split
  · exact Nat.add_le_add_right
      (Nat.mul_le_mul_left 2 (E213.Meta.Nat.NatDiv213.div_le_self_pos i 3 (by decide))) 2
  · exact Nat.le_trans (by decide) (Nat.le_add_left 2 (2 * i))

/-- tan 1's partial quotients grow at most linearly: `tanPQ i ≤ i + 1`.  Hence (cited)
    `μ(tan 1) = 2`. -/
theorem tanPQ_linear_bound (i : Nat) : tanPQ i ≤ i + 1 := by
  unfold tanPQ
  split
  · exact Nat.le_add_left 1 i
  · exact Nat.le_succ i

end E213.Lib.Math.Analysis.Cauchy.HurwitzianCF
