import E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus

/-!
# RateComparison — the two-real joint cut has a constructed separation modulus

The single-real generator (`RateModulus`) decides a cut `a_i/d_i ⋚ m/k` against a
**rational** probe `m/k` with a total modulus.  This file takes the open
"two-real separation modulus" frontier: deciding `a_i/d_i ⋚ b_j/e_j` between
**two** rate-carrying reals.

The bilinear object is the **two-convergent cross-determinant**
`a_i·e_j − b_j·d_i` (the Farey/SL₂ `det = ±1` of the single-probe case, with the
rational `m/k` promoted to a second convergent).  The result:

  * ★★ `two_cut_decided` — the arithmetic core: a separating rational `m/k`
    (`a_i/d_i ≤ m/k` and `m/k < b_j/e_j`) forces the joint comparison
    `a_i·e_j < b_j·d_i`.  Pure ℕ cross-multiplication, no schedule.
  * ★★★ `two_real_separation_modulus` — given two monotone rate-carrying
    presentations and an **apartness witness** (a rational `m/k` that the first
    cut sits below and the second sits above, read at the modulus layer `k+2`),
    the joint comparison `a_i·e_j < b_j·d_i` holds for *all* `i, j ≥ k+2`: a
    constructed total ∅-axiom modulus `N = k+2` for the two-real comparison.
    The two single-real moduli compose by `max` (here both `k+2`, so `k+2`).
  * `rcut2_const_true` — the same, as the decided Bool `rcut2` constantly `true`.

The apartness witness is the constructive content of `x ≠ y` for reals presented
as increasing cuts: a rational strictly between them, which exists exactly when
the reals are apart.

Narrative: `theory/math/analysis/holonomic_modulus.md` (the comparison generator).

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Modulus.RateComparison

open E213.Lib.Math.NumberSystems.Real213.Modulus.RateModulus (Htel rcut rate_cut_const)
open E213.Tactic.NatHelper (mul_assoc)

/-- The two-convergent joint cut: `a_i/d_i ≤ b_j/e_j`, cross-multiplied to ℕ. -/
abbrev rcut2 (a d b e : Nat → Nat) (i j : Nat) : Bool :=
  decide (a i * e j ≤ b j * d i)

/-! ## §1 — the arithmetic core -/

/-- ★★ **A separating rational decides the joint cut.**  If `a_i/d_i ≤ m/k`
    (`A·k ≤ D·m`) and `m/k < b_j/e_j` (`E·m < B·k`), with the first denominator
    `D ≥ 1`, then `a_i·e_j < b_j·d_i`.  The bilinear cross-determinant is forced
    positive by sandwiching it across the probe.  (`E·m < B·k` already forces
    `k ≥ 1`, so no separate positivity hypothesis on `k` is needed.) -/
theorem two_cut_decided {A D B E k m : Nat} (hD : 1 ≤ D)
    (h1 : A * k ≤ D * m) (h2 : E * m < B * k) : A * E < B * D := by
  -- (A*E)*k ≤ D*(E*m)
  have s1 : (A * k) * E ≤ (D * m) * E := Nat.mul_le_mul_right E h1
  have eAE : (A * k) * E = (A * E) * k := by
    rw [mul_assoc, Nat.mul_comm k E, ← mul_assoc]
  have eDm : (D * m) * E = D * (E * m) := by rw [mul_assoc, Nat.mul_comm m E]
  rw [eAE, eDm] at s1
  -- D*(E*m) + D ≤ (B*D)*k
  have h2' : E * m + 1 ≤ B * k := h2
  have s2 : D * (E * m + 1) ≤ D * (B * k) := Nat.mul_le_mul_left D h2'
  have eD1 : D * (E * m + 1) = D * (E * m) + D := by rw [Nat.mul_add, Nat.mul_one]
  have eBk : D * (B * k) = (B * D) * k := by rw [← mul_assoc, Nat.mul_comm D B]
  rw [eD1, eBk] at s2
  -- strict: D*(E*m) < D*(E*m)+D ≤ (B*D)*k, so (A*E)*k < (B*D)*k
  have s3 : D * (E * m) < (B * D) * k :=
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right hD) s2
  have hfin : (A * E) * k < (B * D) * k := Nat.lt_of_le_of_lt s1 s3
  -- cancel the common factor `k`
  rcases Nat.lt_or_ge (A * E) (B * D) with h | h
  · exact h
  · exact absurd (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right k h) hfin) (Nat.lt_irrefl _)

/-! ## §2 — the constructed two-real separation modulus -/

variable {a d b e : Nat → Nat}

/-- ★★★ **Two-real separation modulus.**  Two monotone rate-carrying
    presentations `a/d` and `b/e`, together with an apartness witness `m/k` — the
    first cut sits at-or-below it (`hsa`) and the second strictly above it
    (`hsb`), both read at the modulus layer `k+2` — have their joint comparison
    `a_i·e_j < b_j·d_i` settled for every `i, j ≥ k+2`.  The two single-real
    moduli (`rate_cut_const`, layer `k+2` each) compose to the joint modulus. -/
theorem two_real_separation_modulus
    (hda : ∀ i, 1 ≤ d i) (htela : Htel a d)
    (hmonoa : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoSa : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (hdb : ∀ i, 1 ≤ e i) (htelb : Htel b e)
    (hmonob : ∀ N i, N ≤ i → b N * e i ≤ b i * e N)
    (hmonoSb : ∀ i, b i * e (i+1) < b (i+1) * e i)
    (m k : Nat) (hk : 1 ≤ k)
    (hsa : a (k+2) * k ≤ d (k+2) * m)
    (hsb : e (k+2) * m < b (k+2) * k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → a i * e j < b j * d i := by
  refine ⟨k+2, fun i j hi hj => ?_⟩
  -- the first cut is stably `≤ m/k` past `k+2`
  have ca : rcut a d i m k = rcut a d (k+2) m k :=
    rate_cut_const hda htela hmonoa hmonoSa m k hk i (k+2) hi (Nat.le_refl _)
  have hai : a i * k ≤ d i * m := by
    have hka : rcut a d (k+2) m k = true := decide_eq_true hsa
    exact of_decide_eq_true (ca.trans hka)
  -- the second cut is stably `> m/k` past `k+2`
  have cb : rcut b e j m k = rcut b e (k+2) m k :=
    rate_cut_const hdb htelb hmonob hmonoSb m k hk j (k+2) hj (Nat.le_refl _)
  have hbj : e j * m < b j * k := by
    have hkb : rcut b e (k+2) m k = false := decide_eq_false (Nat.not_le.mpr hsb)
    exact Nat.not_le.mp (of_decide_eq_false (cb.trans hkb))
  exact two_cut_decided (hda i) hai hbj

/-- The two-real separation modulus, as the decided Bool `rcut2` constantly
    `true` past `k+2`. -/
theorem rcut2_const_true
    (hda : ∀ i, 1 ≤ d i) (htela : Htel a d)
    (hmonoa : ∀ N i, N ≤ i → a N * d i ≤ a i * d N)
    (hmonoSa : ∀ i, a i * d (i+1) < a (i+1) * d i)
    (hdb : ∀ i, 1 ≤ e i) (htelb : Htel b e)
    (hmonob : ∀ N i, N ≤ i → b N * e i ≤ b i * e N)
    (hmonoSb : ∀ i, b i * e (i+1) < b (i+1) * e i)
    (m k : Nat) (hk : 1 ≤ k)
    (hsa : a (k+2) * k ≤ d (k+2) * m)
    (hsb : e (k+2) * m < b (k+2) * k) :
    ∃ N, ∀ i j, i ≥ N → j ≥ N → rcut2 a d b e i j = true := by
  obtain ⟨N, hN⟩ := two_real_separation_modulus hda htela hmonoa hmonoSa
    hdb htelb hmonob hmonoSb m k hk hsa hsb
  exact ⟨N, fun i j hi hj => decide_eq_true (Nat.le_of_lt (hN i j hi hj))⟩

end E213.Lib.Math.NumberSystems.Real213.Modulus.RateComparison
