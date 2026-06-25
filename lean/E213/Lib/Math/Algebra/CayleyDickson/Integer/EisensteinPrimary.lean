import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaUnits
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConverse
import E213.Meta.Int213.PolyIntMTactic

/-!
# Primary Eisenstein primes — the unique associate `≡ 2 (mod 3)` (rung 4, ∅-axiom)

★★★★★ `exists_unique_primary` : for any `π ∈ ℤ[ω]` coprime to `3` (`3 ∤ ‖π‖²`), exactly **one** of the
six associates `u·π` (`u ∈ units6 = {±1, ±ω, ±ω²}`) is **primary** — congruent to `2` mod `3`:

  `∃! u ∈ units6,  u·π ≡ 2  (mod 3)`.

This is the canonical normalisation that makes cubic reciprocity `(π/π')₃ = (π'/π)₃` hold without a
unit ambiguity (rung 5): one picks the primary representative of each prime.

## The mechanism — reduce mod 3, then `decide`

Everything depends only on `(π.re mod 3, π.im mod 3)`.  `centered_div_int` pushes `π` to a balanced
residue `ρ = ⟨ra, rb⟩` with `ra, rb ∈ {-1,0,1}` (`int_small`), and `CongMod3 π ρ` (componentwise
`3 ∣ ·`) is preserved by multiplication (`cong_mul_left`).  The cubic character's value group `μ₃`
embeds as the six units mod `3`; for `ρ` a **unit** class (6 of the 9), the orbit `{u·ρ}` is the whole
unit group of `ℤ[ω]/3`, hitting the primary class `2 = −1` exactly once — a **finite `decide`** for each
concrete `ρ`.  The three **non-unit** classes (`3 ∣ ‖ρ‖²`) are excluded by `3 ∤ ‖π‖²` via `norm_cong`
(`CongMod3 ⟹ 3 ∣ ‖·‖²` difference).  No excluded middle, no Mathlib.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrimary

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega units6)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConverse (int_small)
open E213.Lib.Math.NumberTheory.ModArith.CenteredDivision (centered_div_int)

/-! ## §1 — componentwise congruence mod 3 (reducible, so `decide` sees through) -/

/-- `p ≡ q (mod 3)` componentwise: `3 ∣ (p.re − q.re)` and `3 ∣ (p.im − q.im)`. -/
abbrev CongMod3 (p q : ZOmega) : Prop := (3 : Int) ∣ (p.re - q.re) ∧ (3 : Int) ∣ (p.im - q.im)

/-- `q` is **primary**: `q ≡ 2 (mod 3)`. -/
abbrev IsPrimary (q : ZOmega) : Prop := CongMod3 q (ofInt 2)

/-- `CongMod3` is symmetric. -/
theorem cong_symm {p q : ZOmega} (h : CongMod3 p q) : CongMod3 q p := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  refine ⟨⟨-a, ?_⟩, ⟨-b, ?_⟩⟩
  · have e : p.re = q.re + 3 * a := by rw [← ha]; ring_intZ
    rw [e]; ring_intZ
  · have e : p.im = q.im + 3 * b := by rw [← hb]; ring_intZ
    rw [e]; ring_intZ

/-- `CongMod3` is transitive. -/
theorem cong_trans {p q r : ZOmega} (h1 : CongMod3 p q) (h2 : CongMod3 q r) : CongMod3 p r := by
  obtain ⟨⟨a1, ha1⟩, ⟨b1, hb1⟩⟩ := h1
  obtain ⟨⟨a2, ha2⟩, ⟨b2, hb2⟩⟩ := h2
  refine ⟨⟨a1 + a2, ?_⟩, ⟨b1 + b2, ?_⟩⟩
  · have e1 : p.re = q.re + 3 * a1 := by rw [← ha1]; ring_intZ
    have e2 : q.re = r.re + 3 * a2 := by rw [← ha2]; ring_intZ
    rw [e1, e2]; ring_intZ
  · have e1 : p.im = q.im + 3 * b1 := by rw [← hb1]; ring_intZ
    have e2 : q.im = r.im + 3 * b2 := by rw [← hb2]; ring_intZ
    rw [e1, e2]; ring_intZ

/-- **Multiplication preserves `CongMod3`** — `p ≡ q (mod 3) ⟹ u·p ≡ u·q (mod 3)`.  The components of
    `u·p − u·q` are integer-linear in `p − q` (Eisenstein product), so divisibility transfers. -/
theorem cong_mul_left (u : ZOmega) {p q : ZOmega} (h : CongMod3 p q) : CongMod3 (u * p) (u * q) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  have e1 : p.re = q.re + 3 * a := by rw [← ha]; ring_intZ
  have e2 : p.im = q.im + 3 * b := by rw [← hb]; ring_intZ
  refine ⟨⟨u.re * a - u.im * b, ?_⟩, ⟨u.re * b + u.im * a - u.im * b, ?_⟩⟩
  · show (u.re * p.re - u.im * p.im) - (u.re * q.re - u.im * q.im) = 3 * (u.re * a - u.im * b)
    rw [e1, e2]; ring_intZ
  · show (u.re * p.im + u.im * p.re - u.im * p.im) - (u.re * q.im + u.im * q.re - u.im * q.im)
       = 3 * (u.re * b + u.im * a - u.im * b)
    rw [e1, e2]; ring_intZ

/-- **`CongMod3` descends to the norm** — `p ≡ q (mod 3) ⟹ 3 ∣ (‖p‖² − ‖q‖²)`.  Used to exclude the
    non-unit residue classes (where `3 ∣ ‖ρ‖²`) from a `π` coprime to `3`. -/
theorem norm_cong {p q : ZOmega} (h : CongMod3 p q) : (3 : Int) ∣ (p.normSq - q.normSq) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  refine ⟨a * (p.re + q.re - p.im) + b * (p.im + q.im - q.re), ?_⟩
  have e1 : p.re = q.re + 3 * a := by rw [← ha]; ring_intZ
  have e2 : p.im = q.im + 3 * b := by rw [← hb]; ring_intZ
  show (p.re * p.re - p.re * p.im + p.im * p.im) - (q.re * q.re - q.re * q.im + q.im * q.im)
     = 3 * (a * (p.re + q.re - p.im) + b * (p.im + q.im - q.re))
  rw [e1, e2]; ring_intZ

/-- `CongMod3 p q ⟹ (IsPrimary p ↔ IsPrimary q)`. -/
theorem primary_iff_of_cong {p q : ZOmega} (h : CongMod3 p q) : IsPrimary p ↔ IsPrimary q :=
  ⟨fun hp => cong_trans (cong_symm h) hp, fun hq => cong_trans h hq⟩

/-! ## §2 — pure membership extraction + the norm exclusion

`u ∈ units6` (`List.Mem`, `Prop`) is `propext`-tainted via core's decidability.  We work with the
**Bool** predicate `units6.contains u = true` instead, extracting the six-way disjunction purely
(`orB_elim` + `of_decide_eq_true`, the `CubeRootsOfUnity` pattern). -/

/-- `(a || b) = true → a = true ∨ b = true` (∅-axiom; inlined). -/
private theorem orB_elim {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false => exact Or.inr h

/-- **`units6` membership is a six-way disjunction** — `units6.contains u = true` exhibits `u` as one
    of the six units explicitly, with no `propext` (Bool `||`-chain via `orB_elim`/`of_decide_eq_true`,
    not `List.Mem`). -/
theorem units6_or {u : ZOmega} (h : units6.contains u = true) :
    u = ⟨1, 0⟩ ∨ u = ⟨-1, 0⟩ ∨ u = ⟨0, 1⟩ ∨ u = ⟨0, -1⟩ ∨ u = ⟨1, 1⟩ ∨ u = ⟨-1, -1⟩ := by
  rcases orB_elim h with h1 | hc
  · exact Or.inl (of_decide_eq_true h1)
  · rcases orB_elim hc with h2 | hc
    · exact Or.inr (Or.inl (of_decide_eq_true h2))
    · rcases orB_elim hc with h3 | hc
      · exact Or.inr (Or.inr (Or.inl (of_decide_eq_true h3)))
      · rcases orB_elim hc with h4 | hc
        · exact Or.inr (Or.inr (Or.inr (Or.inl (of_decide_eq_true h4))))
        · rcases orB_elim hc with h5 | hc
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (of_decide_eq_true h5)))))
          · rcases orB_elim hc with h6 | hf
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (of_decide_eq_true h6)))))
            · exact Bool.noConfusion hf

/-- From `3 ∣ ‖ρ‖²` (a non-unit residue) and `π ≡ ρ`, conclude `3 ∣ ‖π‖²`. -/
theorem norm_dvd_of_residue (π : ZOmega) (ra rb : Int) (hcong : CongMod3 π ⟨ra, rb⟩)
    (hr : (3 : Int) ∣ (⟨ra, rb⟩ : ZOmega).normSq) : (3 : Int) ∣ π.normSq := by
  obtain ⟨c1, hc1⟩ := norm_cong hcong
  obtain ⟨c2, hc2⟩ := hr
  refine ⟨c1 + c2, ?_⟩
  have hsplit : π.normSq = (π.normSq - (⟨ra, rb⟩ : ZOmega).normSq) + (⟨ra, rb⟩ : ZOmega).normSq := by
    ring_intZ
  rw [hsplit, hc1, hc2]; ring_intZ

/-! ## §3 — existence, uniqueness, and the canonical primary associate -/

/-- The shared mod-3 reduction: `π ≡ ⟨ra,rb⟩` with balanced `ra, rb ∈ {-1,0,1}`. -/
private theorem residue_data (π : ZOmega) :
    ∃ ra rb : Int, CongMod3 π ⟨ra, rb⟩ ∧ (ra = -1 ∨ ra = 0 ∨ ra = 1) ∧ (rb = -1 ∨ rb = 0 ∨ rb = 1) := by
  obtain ⟨qa, ra, hae, hab⟩ := centered_div_int π.re 3 (by decide)
  obtain ⟨qb, rb, hbe, hbb⟩ := centered_div_int π.im 3 (by decide)
  rw [show (3 : Int).natAbs = 3 from rfl] at hab hbb
  refine ⟨ra, rb, ⟨⟨qa, ?_⟩, ⟨qb, ?_⟩⟩, int_small ra hab, int_small rb hbb⟩
  · show π.re - ra = 3 * qa; rw [hae]; ring_intZ
  · show π.im - rb = 3 * qb; rw [hbe]; ring_intZ

/-- ★★★★★ **The unique primary associate.**  For `π` coprime to `3` (`3 ∤ ‖π‖²`), exactly one of the
    six unit multiples `u·π` (`units6.contains u`) is primary (`≡ 2 mod 3`):

      `∃! u ∈ units6,  u·π ≡ 2 (mod 3)`.

    Reduce `π` to a balanced residue `ρ = ⟨ra,rb⟩` (`residue_data`).  For each of the six **unit**
    residue classes one explicit unit witnesses primality (`decide` lifts via `cong_mul_left`); the
    three **non-unit** classes (`3 ∣ ‖ρ‖²`) are excluded by `3 ∤ ‖π‖²` (`norm_dvd_of_residue`).
    Uniqueness: any primary multiple, reduced mod `3` and split by `units6_or`, is forced to the
    witness (the other five units fail `decide`).  No excluded middle.  (Carries `propext` solely from
    the Lean-core divisibility-`decide` instance — "always allowed but not target" per
    `STRICT_ZERO_AXIOM.md`; the seven supporting lemmas are all PURE.) -/
theorem exists_unique_primary (π : ZOmega) (hcop : ¬ ((3 : Int) ∣ π.normSq)) :
    ∃ u, units6.contains u = true ∧ IsPrimary (u * π) ∧
      (∀ u', units6.contains u' = true → IsPrimary (u' * π) → u' = u) := by
  obtain ⟨ra, rb, hcong, hra, hrb⟩ := residue_data π
  rcases hra with h | h | h <;> rcases hrb with h' | h' | h' <;> subst h <;> subst h' <;>
    (first
      | refine ⟨⟨1, 0⟩, by decide, (primary_iff_of_cong (cong_mul_left _ hcong)).mpr (by decide), ?_⟩
      | refine ⟨⟨-1, 0⟩, by decide, (primary_iff_of_cong (cong_mul_left _ hcong)).mpr (by decide), ?_⟩
      | refine ⟨⟨0, 1⟩, by decide, (primary_iff_of_cong (cong_mul_left _ hcong)).mpr (by decide), ?_⟩
      | refine ⟨⟨0, -1⟩, by decide, (primary_iff_of_cong (cong_mul_left _ hcong)).mpr (by decide), ?_⟩
      | refine ⟨⟨1, 1⟩, by decide, (primary_iff_of_cong (cong_mul_left _ hcong)).mpr (by decide), ?_⟩
      | refine ⟨⟨-1, -1⟩, by decide, (primary_iff_of_cong (cong_mul_left _ hcong)).mpr (by decide), ?_⟩
      | exact absurd (norm_dvd_of_residue π _ _ hcong (by decide)) hcop) <;>
    (intro w' hcw hpw
     have hl := (primary_iff_of_cong (cong_mul_left w' hcong)).mp hpw
     rcases units6_or hcw with rfl | rfl | rfl | rfl | rfl | rfl <;>
       first | rfl | exact absurd hl (by decide))

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrimary
