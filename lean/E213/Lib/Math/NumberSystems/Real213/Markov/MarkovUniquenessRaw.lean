import E213.Lib.Math.NumberSystems.Real213.Markov.MarkovUniqueness
import E213.Lens.Number

/-!
# Markov uniqueness, written Raw-native — and the meaning of "solving"

The Markov uniqueness conjecture (Frobenius 1913) refers to Markov *numbers*; and `ℕ₊` is exactly the
image of the count-Lens `value = Lens.leaves.view : Raw → ℕ` (`Nat213.Raw.value_surjective_on_ge_one`).
So the proposition can be written with **every number a `Lens.view` of `Raw`** — nothing imported, every
quantity produced by a Lens (`seed/AXIOM/02_axiom.md` §2.5).  `markovMaxUnique_213_iff` proves this
Raw-native form *is* the conjecture.

This file is the concrete anchor for `seed/AXIOM/05_no_exterior.md` §5.3 ("expressing and solving are the
same act — pointing at a residue"):

  * **Expressing** the proposition = pointing at the proposition-residue: `MarkovMaxUnique_213` (its
    quantifiers range over `Raw`; each number is `value (·)`).
  * **Solving** it = pointing at the *proof-residue* (the inhabitant — itself a term, hence a residue):
    `markovMaxUnique_213_solved_5` exhibits the inhabitant for `c = 5`.

Both are the same kind of act, one fold-level apart.  The closed cases (small `c`, Button's prime-power
family) are *solved* in this sense — the proof-residue is pointed at; the open composite kernel is a
proof-residue *not yet pointed at*, not a gap between expressible and true.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Markov.MarkovUniquenessRaw

open E213.Theory E213.Lens
open E213.Lens.Number.Nat213.Raw (value value_surjective_on_ge_one)
open E213.Lib.Math.NumberSystems.Real213.Markov.MarkovTree (markovEq)
open E213.Lib.Math.NumberSystems.Real213.Markov.MarkovUniqueness (MarkovMaxUnique markov_a_pos markov_max_unique_5)

/-- **Markov uniqueness, written 213-native**: every number is the count-Lens view `value (·) =
    Lens.leaves.view (·)` of a `Raw`; the quantifiers range over `Raw`.  Nothing is imported. -/
def MarkovMaxUnique_213 (rc : Raw) : Prop :=
  ∀ ra₁ rb₁ ra₂ rb₂ : Raw,
    value ra₁ ≤ value rb₁ → value rb₁ ≤ value rc →
    value ra₂ ≤ value rb₂ → value rb₂ ≤ value rc →
    markovEq (value ra₁) (value rb₁) (value rc) →
    markovEq (value ra₂) (value rb₂) (value rc) →
    value ra₁ = value ra₂ ∧ value rb₁ = value rb₂

/-- ★★★★★ **The Raw-native form IS the conjecture** (same content, `∅`-axiom).  Pointing at the
    proposition through `Raw` and through `ℕ` is the same referent. -/
theorem markovMaxUnique_213_iff (rc : Raw) (hc : 2 ≤ value rc) :
    MarkovMaxUnique_213 rc ↔ MarkovMaxUnique (value rc) := by
  constructor
  · intro h a₁ b₁ a₂ b₂ hab1 hb1c hab2 hb2c hm1 hm2
    have ha1 : 1 ≤ a₁ := markov_a_pos hc hm1
    have ha2 : 1 ≤ a₂ := markov_a_pos hc hm2
    have hb1 : 1 ≤ b₁ := Nat.le_trans ha1 hab1
    have hb2 : 1 ≤ b₂ := Nat.le_trans ha2 hab2
    obtain ⟨ra₁, e1⟩ := value_surjective_on_ge_one a₁ ha1
    obtain ⟨rb₁, f1⟩ := value_surjective_on_ge_one b₁ hb1
    obtain ⟨ra₂, e2⟩ := value_surjective_on_ge_one a₂ ha2
    obtain ⟨rb₂, f2⟩ := value_surjective_on_ge_one b₂ hb2
    have := h ra₁ rb₁ ra₂ rb₂ (by rw [e1, f1]; exact hab1) (by rw [f1]; exact hb1c)
      (by rw [e2, f2]; exact hab2) (by rw [f2]; exact hb2c)
      (by rw [e1, f1]; exact hm1) (by rw [e2, f2]; exact hm2)
    rw [e1, f1, e2, f2] at this; exact this
  · intro h ra₁ rb₁ ra₂ rb₂ hab1 hb1c hab2 hb2c hm1 hm2
    exact h (value ra₁) (value rb₁) (value ra₂) (value rb₂) hab1 hb1c hab2 hb2c hm1 hm2

/-! ## Grounding: the Markov triple `(1, 2, 5)` lives entirely on `Raw`-views. -/

/-- `value = 1`. -/
def r1 : Raw := Raw.a
/-- `value = 2`. -/
def r2 : Raw := Raw.slash Raw.a Raw.b (by decide)
/-- `value = 5`. -/
def r5 : Raw :=
  Raw.slash (Raw.slash Raw.a Raw.b (by decide))
    (Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide)) (by decide)

theorem triple_125_on_views :
    value r1 = 1 ∧ value r2 = 2 ∧ value r5 = 5
    ∧ markovEq (value r1) (value r2) (value r5) := by
  refine ⟨rfl, rfl, rfl, ?_⟩; decide

/-! ## "Solving" = pointing at the proof-residue (the inhabitant) -/

/-- `MarkovMaxUnique 5`, assembled from the decidable single-pair identification `markov_max_unique_5`
    (the only ordered triple at max `5` is `(1,2,5)`). -/
theorem markovMaxUnique_5 : MarkovMaxUnique 5 := by
  intro a₁ b₁ a₂ b₂ hab1 hb1 hab2 hb2 hm1 hm2
  obtain ⟨ha1, hb1'⟩ := markov_max_unique_5 a₁ (Nat.le_trans hab1 hb1) b₁ hb1 hab1 hm1
  obtain ⟨ha2, hb2'⟩ := markov_max_unique_5 a₂ (Nat.le_trans hab2 hb2) b₂ hb2 hab2 hm2
  exact ⟨ha1.trans ha2.symm, hb1'.trans hb2'.symm⟩

/-- ★★★★★ **`c = 5` is solved 213-native**: the proof-residue is exhibited.  Expressing the proposition
    (`MarkovMaxUnique_213`) and solving it (inhabiting it) are the same act — pointing at a residue —
    one fold-level apart.  The inhabitant is `markovMaxUnique_5` transported through the Raw-native
    equivalence. -/
theorem markovMaxUnique_213_solved_5 : MarkovMaxUnique_213 r5 :=
  (markovMaxUnique_213_iff r5 (by decide)).mpr markovMaxUnique_5

end E213.Lib.Math.NumberSystems.Real213.Markov.MarkovUniquenessRaw
