import E213.Lib.Math.NumberSystems.Real213.Markov.MarkovUniqueness
import E213.Lib.Math.Foundations.MonovariantFlow

/-!
# Markov descent as a universal-descent-schema instance (∅-axiom)

Markov's descent theorem — every ordered Markov triple reaches the root
`(1,1,1)` — is an **instance of the universal descent schema** `descent_reaches`
(`Lib/Math/Foundations/MonovariantFlow`), the first genuinely *relational*
(non-self-map) one.  The step is a **nondeterministic relation** `Down`
= Vieta-jump the max `c ↦ 3ab − c`, then re-sort the triple; the sort has two
branches (where the jumped value lands), so `Down` is a relation, not a
function.  The monovariant `μ = c` (the max) is **invariant under the re-sort**
(a permutation of the triple) and the jump strictly drops it, so `μ` descends
across the *bundled* `Down` step — the schema absorbs the permutation with no
quotient-by-symmetry (`research-notes/frontiers/descent_schema_universal.md`,
the 5-way fold verdict).

Every piece is reused from `MarkovUniqueness`; this file only re-packages the
step into the schema's `∀ x, NF x ∨ ∃ y, R x y ∧ μ y < μ x` shape.  ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Markov.MarkovDescentSchema

open E213.Lib.Math.NumberSystems.Real213.Markov.MarkovTree (markovEq markov_symm)
open E213.Lib.Math.NumberSystems.Real213.Markov.MarkovUniqueness
  (markov_le_3mul markov_partner_is_triple markov_vieta_partner_le markov_mid_lt_max
   markov_neighbor_eq markovEq_perm_cab)
open E213.Lib.Math.Foundations.MonovariantFlow (Reaches descent_reaches)

/-- An ordered Markov triple `(a,b,c)` with `1 ≤ a ≤ b ≤ c`. -/
structure OMarkov where
  a : Nat
  b : Nat
  c : Nat
  eq  : markovEq a b c
  ha  : 1 ≤ a
  hab : a ≤ b
  hbc : b ≤ c

/-- The Markov **down-step relation**: Vieta-jump the max (`c ↦ 3ab − c`), then
    re-sort.  Nondeterministic — the jumped value `w = 3ab − c` lands either above
    or below `a`, giving the two sort branches `(a, w, b)` / `(w, a, b)`. -/
def Down (s t : OMarkov) : Prop :=
  2 ≤ s.c ∧
  ( (s.a < 3 * s.a * s.b - s.c ∧ t.a = s.a ∧ t.b = 3 * s.a * s.b - s.c ∧ t.c = s.b)
  ∨ (3 * s.a * s.b - s.c ≤ s.a ∧ t.a = 3 * s.a * s.b - s.c ∧ t.b = s.a ∧ t.c = s.b) )

/-- **The schema's descent obligation**: every ordered Markov triple is either the
    root (`c < 2`) or has a `Down`-successor with strictly smaller max `c`.  This is
    `reachable_of_fuel`'s body with the fuel-recursion removed (the schema supplies
    it).  The strict descent `t.c = b < c` reuses `markov_mid_lt_max`. -/
theorem down_step (s : OMarkov) :
    s.c < 2 ∨ ∃ t, Down s t ∧ t.c < s.c := by
  rcases Nat.lt_or_ge s.c 2 with hclt | hcge
  · exact Or.inl hclt
  · have hcpos : 0 < s.c := Nat.lt_of_lt_of_le (by decide) hcge
    have hbc_strict : s.b < s.c :=
      markov_mid_lt_max s.a s.b s.c s.eq s.ha s.hab s.hbc hcge
    have hw_triple : markovEq s.a s.b (3 * s.a * s.b - s.c) :=
      markov_partner_is_triple s.a s.b s.c (markov_le_3mul s.a s.b s.c hcpos s.eq) s.eq
    have hwb : 3 * s.a * s.b - s.c ≤ s.b :=
      markov_vieta_partner_le s.a s.b s.c s.eq s.ha s.hab hbc_strict
    have hwpos : 1 ≤ 3 * s.a * s.b - s.c := by
      rcases Nat.eq_zero_or_pos (3 * s.a * s.b - s.c) with h0 | hp
      · exfalso
        have hprod := markov_neighbor_eq s.a s.b s.c hcpos s.eq
        rw [h0, Nat.mul_zero] at hprod
        have h1 : 1 ≤ s.a * s.a + s.b * s.b :=
          Nat.le_trans (Nat.mul_pos s.ha s.ha) (Nat.le_add_right _ _)
        rw [hprod] at h1
        exact absurd h1 (Nat.not_succ_le_zero 0)
      · exact hp
    rcases Nat.lt_or_ge s.a (3 * s.a * s.b - s.c) with hlt | hge
    · exact Or.inr
        ⟨⟨s.a, 3 * s.a * s.b - s.c, s.b,
            markov_symm s.a s.b (3 * s.a * s.b - s.c) hw_triple, s.ha,
            Nat.le_of_lt hlt, hwb⟩,
         ⟨hcge, Or.inl ⟨hlt, rfl, rfl, rfl⟩⟩, hbc_strict⟩
    · exact Or.inr
        ⟨⟨3 * s.a * s.b - s.c, s.a, s.b, markovEq_perm_cab hw_triple, hwpos, hge, s.hab⟩,
         ⟨hcge, Or.inr ⟨hge, rfl, rfl, rfl⟩⟩, hbc_strict⟩

/-- ★★★★★ **Markov descent IS a `descent_reaches` instance.**  Every ordered Markov
    triple descends, by the nondeterministic Vieta-jump-and-resort relation `Down`,
    to a normal form `c < 2` — i.e. the root.  The schema (`descent_reaches`)
    supplies the well-founded recursion; `down_step` supplies the per-step descent.
    The first genuinely relational (non-self-map) instance of the universal descent
    lift. -/
theorem markov_descends_to_root (s : OMarkov) :
    ∃ t, t.c < 2 ∧ Reaches Down s t :=
  descent_reaches Down (fun s => s.c) (fun s => s.c < 2) down_step s

/-- The reached normal form is the root `(1,1,1)`: `c < 2` with `1 ≤ a ≤ b ≤ c`
    forces all three to `1`. -/
theorem markov_descends_to_one (s : OMarkov) :
    ∃ t, t.a = 1 ∧ t.b = 1 ∧ t.c = 1 ∧ Reaches Down s t := by
  obtain ⟨t, hlt, hr⟩ := markov_descends_to_root s
  have h1c : 1 ≤ t.c := Nat.le_trans t.ha (Nat.le_trans t.hab t.hbc)
  have hc1 : t.c = 1 := Nat.le_antisymm (Nat.le_of_lt_succ hlt) h1c
  have h1b : 1 ≤ t.b := Nat.le_trans t.ha t.hab
  have hb1 : t.b = 1 := Nat.le_antisymm (hc1 ▸ t.hbc) h1b
  have ha1 : t.a = 1 := Nat.le_antisymm (hb1 ▸ t.hab) t.ha
  exact ⟨t, ha1, hb1, hc1, hr⟩

end E213.Lib.Math.NumberSystems.Real213.Markov.MarkovDescentSchema
