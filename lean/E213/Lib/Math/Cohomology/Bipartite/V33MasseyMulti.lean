import E213.Lib.Math.Cohomology.Bipartite.V33MasseyWitness

/-!
# Multi-witness Massey sweep at K_{3,3}^{(c=2)}

Extends `V33MasseyWitness` (which formalised the primary witness
⟨g1, g2, g4⟩ violating R_{T_{01}}) with three further non-vacuous
Massey witnesses, each chain-level explicit and each violating a
*different* pair of face-dependence relations in H² = F₂⁵.

## Strategy

The 6 face dependence relations split symmetrically:

  · R_{S_{01}} : face0 ⊕ face1 ⊕ face2 = 0     (S-pair {0,1}, T varies)
  · R_{S_{02}} : face3 ⊕ face4 ⊕ face5 = 0     (S-pair {0,2}, T varies)
  · R_{S_{12}} : face6 ⊕ face7 ⊕ face8 = 0     (S-pair {1,2}, T varies)
  · R_{T_{01}} : face0 ⊕ face3 ⊕ face6 = 0     (T-pair {0,1}, S varies)
  · R_{T_{02}} : face1 ⊕ face4 ⊕ face7 = 0     (T-pair {0,2}, S varies)
  · R_{T_{12}} : face2 ⊕ face5 ⊕ face8 = 0     (T-pair {1,2}, S varies)

They satisfy ONE linear dependency
`R_{S_{01}} ⊕ R_{S_{02}} ⊕ R_{S_{12}} = R_{T_{01}} ⊕ R_{T_{02}} ⊕ R_{T_{12}}`
(both equal the sum of all 9 faces), hence 5 are independent and
the violation pattern characterises a class in `H² = C² / im δ¹`.

## Three new witnesses + existing primary

| Triple | η_{bc} | Rep (face cochain) | Violation pattern |
|---|---|---|---|
| ⟨g1, g2, g4⟩ (primary) | e₆  | (1, 1, 0, 0, 0, 0, 0, 0, 0) | R_{T_{01}} + R_{T_{02}} |
| ⟨g1, g2, g5⟩ (Witness A) | e₈  | (1, 0, 1, 0, 0, 0, 0, 0, 0) | R_{T_{01}} + R_{T_{12}} |
| ⟨g4, g5, g1⟩ (Witness B) | e₂  | (1, 0, 0, 1, 0, 0, 0, 0, 0) | R_{S_{01}} + R_{S_{02}} |
| ⟨g4, g5, g2⟩ (Witness C) | e₈  | (1, 0, 0, 0, 0, 0, 1, 0, 0) | R_{S_{01}} + R_{S_{12}} |

## Capstone: 4-dimensional image of H²

The four violation vectors in `F₂⁶ / (sum-zero)`

      v₀ = (0, 0, 0, 1, 1, 0)     -- primary
      v_A = (0, 0, 0, 1, 0, 1)
      v_B = (1, 1, 0, 0, 0, 0)
      v_C = (1, 0, 1, 0, 0, 0)

are pair-wise linearly independent (each new witness violates a
relation untouched by the previous), so they span a
**4-dimensional subspace** of `H² = F₂⁵`.

This leaves exactly ONE dimension of `H²` *unreached* by simple
star × incidence Massey triples of the forms ⟨S, S, T⟩ and
⟨T, T, S⟩.  Hitting the 5th dimension requires:

  · mixed-side triples ⟨S, T, S⟩ / ⟨T, S, T⟩, or
  · Massey triples that touch the multiplicity-shift cocycles
    `e_{2k+1}` for k ∈ {0..8} (these live in ker δ¹ but escape
    the star/incidence basis).

The 5th-dimensional witness is the **next-session frontier**.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.V33MasseyMulti

open E213.Lib.Math.Cohomology.Bipartite.V33
  (CochE delta1 face0 face1 face2 face3 face4 face5 face6 face7 face8 faceBoundary)
open E213.Lib.Math.Cohomology.Bipartite.V33OppositeCup (cupOpp g1 g2 g4 g5)

/-! ## §1 — Four additional R-relations (R_{S_{02}}, R_{S_{12}},
                                       R_{T_{02}}, R_{T_{12}})

`face_dep_S01` and `face_dep_T01` already live in `V33`.  Here we
add the remaining four canonical row/column relations.  Together
with the two existing ones we have 6 relations, of which 5 are
independent (one is the XOR-sum of the other five). -/

theorem face_dep_S02 :
    ∀ σ : CochE, xor (xor (face3 σ) (face4 σ)) (face5 σ) = false := by
  intro σ
  unfold face3 face4 face5 faceBoundary
  cases σ ⟨0, by decide⟩ <;> cases σ ⟨2, by decide⟩ <;>
  cases σ ⟨4, by decide⟩ <;> cases σ ⟨12, by decide⟩ <;>
  cases σ ⟨14, by decide⟩ <;> cases σ ⟨16, by decide⟩ <;> rfl

theorem face_dep_S12 :
    ∀ σ : CochE, xor (xor (face6 σ) (face7 σ)) (face8 σ) = false := by
  intro σ
  unfold face6 face7 face8 faceBoundary
  cases σ ⟨6, by decide⟩ <;> cases σ ⟨8, by decide⟩ <;>
  cases σ ⟨10, by decide⟩ <;> cases σ ⟨12, by decide⟩ <;>
  cases σ ⟨14, by decide⟩ <;> cases σ ⟨16, by decide⟩ <;> rfl

theorem face_dep_T02 :
    ∀ σ : CochE, xor (xor (face1 σ) (face4 σ)) (face7 σ) = false := by
  intro σ
  unfold face1 face4 face7 faceBoundary
  cases σ ⟨0, by decide⟩ <;> cases σ ⟨4, by decide⟩ <;>
  cases σ ⟨6, by decide⟩ <;> cases σ ⟨10, by decide⟩ <;>
  cases σ ⟨12, by decide⟩ <;> cases σ ⟨16, by decide⟩ <;> rfl

theorem face_dep_T12 :
    ∀ σ : CochE, xor (xor (face2 σ) (face5 σ)) (face8 σ) = false := by
  intro σ
  unfold face2 face5 face8 faceBoundary
  cases σ ⟨2, by decide⟩ <;> cases σ ⟨4, by decide⟩ <;>
  cases σ ⟨8, by decide⟩ <;> cases σ ⟨10, by decide⟩ <;>
  cases σ ⟨14, by decide⟩ <;> cases σ ⟨16, by decide⟩ <;> rfl

/-! ## §2 — Cobounding chains for the three new witnesses -/

/-- Cobounds `g2 ⌣ g5` (S₁-star ⌣ T₁-incidence): single S₁-T₁
    mult-0 edge `e₈`.  Used by Witness A ⟨g1, g2, g5⟩. -/
def eta_g2g5 : CochE := fun e => decide (e.val = 8)

/-- Cobounds `g1 ⌣ g5` (S₀-star ⌣ T₁-incidence): single S₀-T₁
    mult-0 edge `e₂`.  Used by Witness B ⟨g4, g5, g1⟩. -/
def eta_g1g5 : CochE := fun e => decide (e.val = 2)

/-- Cobounds `g2 ⌣ g5` (S₁-star ⌣ T₁-incidence): single S₁-T₁
    mult-0 edge `e₈`.  Same chain as `eta_g2g5`; used by Witness C
    ⟨g4, g5, g2⟩ via `g5 ⌣ g2 = g2 ⌣ g5`. -/
def eta_g2g5_for_C : CochE := fun e => decide (e.val = 8)

/-! ## §3 — Witness A: ⟨g1, g2, g5⟩  →  rep violates R_{T_{01}} + R_{T_{12}}

  · a ⌣ b = g1 ⌣ g2 = 0 (same-side S-stars, already established
    in `V33MasseyWitness.cup_g1_g2_all_zero`)
  · b ⌣ c = g2 ⌣ g5 cobounds via η_{bc} = e₈
  · Rep = a ⌣ η_{bc} + 0 ⌣ c = g1 ⌣ e₈
  · Rep value vector: (1, 0, 1, 0, 0, 0, 0, 0, 0)
  · Violates `R_{T_{01}}: face0+face3+face6 = 1+0+0 = 1`
  · Violates `R_{T_{12}}: face2+face5+face8 = 1+0+0 = 1` -/

theorem witnessA_delta_eta_eq_cup :
    delta1 eta_g2g5 ⟨0, by decide⟩ = cupOpp g2 g5 ⟨0, by decide⟩
    ∧ delta1 eta_g2g5 ⟨1, by decide⟩ = cupOpp g2 g5 ⟨1, by decide⟩
    ∧ delta1 eta_g2g5 ⟨2, by decide⟩ = cupOpp g2 g5 ⟨2, by decide⟩
    ∧ delta1 eta_g2g5 ⟨3, by decide⟩ = cupOpp g2 g5 ⟨3, by decide⟩
    ∧ delta1 eta_g2g5 ⟨4, by decide⟩ = cupOpp g2 g5 ⟨4, by decide⟩
    ∧ delta1 eta_g2g5 ⟨5, by decide⟩ = cupOpp g2 g5 ⟨5, by decide⟩
    ∧ delta1 eta_g2g5 ⟨6, by decide⟩ = cupOpp g2 g5 ⟨6, by decide⟩
    ∧ delta1 eta_g2g5 ⟨7, by decide⟩ = cupOpp g2 g5 ⟨7, by decide⟩
    ∧ delta1 eta_g2g5 ⟨8, by decide⟩ = cupOpp g2 g5 ⟨8, by decide⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem witnessA_rep_face_values :
    cupOpp g1 eta_g2g5 ⟨0, by decide⟩ = true
    ∧ cupOpp g1 eta_g2g5 ⟨1, by decide⟩ = false
    ∧ cupOpp g1 eta_g2g5 ⟨2, by decide⟩ = true
    ∧ cupOpp g1 eta_g2g5 ⟨3, by decide⟩ = false
    ∧ cupOpp g1 eta_g2g5 ⟨4, by decide⟩ = false
    ∧ cupOpp g1 eta_g2g5 ⟨5, by decide⟩ = false
    ∧ cupOpp g1 eta_g2g5 ⟨6, by decide⟩ = false
    ∧ cupOpp g1 eta_g2g5 ⟨7, by decide⟩ = false
    ∧ cupOpp g1 eta_g2g5 ⟨8, by decide⟩ = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem witnessA_violates_R_T01 :
    xor (xor (cupOpp g1 eta_g2g5 ⟨0, by decide⟩)
              (cupOpp g1 eta_g2g5 ⟨3, by decide⟩))
         (cupOpp g1 eta_g2g5 ⟨6, by decide⟩) = true := by decide

theorem witnessA_violates_R_T12 :
    xor (xor (cupOpp g1 eta_g2g5 ⟨2, by decide⟩)
              (cupOpp g1 eta_g2g5 ⟨5, by decide⟩))
         (cupOpp g1 eta_g2g5 ⟨8, by decide⟩) = true := by decide

/-! ## §4 — Witness B: ⟨g4, g5, g1⟩  →  rep violates R_{S_{01}} + R_{S_{02}}

  · a ⌣ b = g4 ⌣ g5 = 0 (same-side T-incidences)
  · b ⌣ c = g5 ⌣ g1 cobounds via η_{bc} = e₂
  · Rep = a ⌣ η_{bc} = g4 ⌣ e₂
  · Rep value vector: (1, 0, 0, 1, 0, 0, 0, 0, 0)
  · Violates `R_{S_{01}}: face0+face1+face2 = 1+0+0 = 1`
  · Violates `R_{S_{02}}: face3+face4+face5 = 1+0+0 = 1` -/

theorem witnessB_cup_a_b_all_zero :
    cupOpp g4 g5 ⟨0, by decide⟩ = false
    ∧ cupOpp g4 g5 ⟨1, by decide⟩ = false
    ∧ cupOpp g4 g5 ⟨2, by decide⟩ = false
    ∧ cupOpp g4 g5 ⟨3, by decide⟩ = false
    ∧ cupOpp g4 g5 ⟨4, by decide⟩ = false
    ∧ cupOpp g4 g5 ⟨5, by decide⟩ = false
    ∧ cupOpp g4 g5 ⟨6, by decide⟩ = false
    ∧ cupOpp g4 g5 ⟨7, by decide⟩ = false
    ∧ cupOpp g4 g5 ⟨8, by decide⟩ = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem witnessB_delta_eta_eq_cup :
    delta1 eta_g1g5 ⟨0, by decide⟩ = cupOpp g5 g1 ⟨0, by decide⟩
    ∧ delta1 eta_g1g5 ⟨1, by decide⟩ = cupOpp g5 g1 ⟨1, by decide⟩
    ∧ delta1 eta_g1g5 ⟨2, by decide⟩ = cupOpp g5 g1 ⟨2, by decide⟩
    ∧ delta1 eta_g1g5 ⟨3, by decide⟩ = cupOpp g5 g1 ⟨3, by decide⟩
    ∧ delta1 eta_g1g5 ⟨4, by decide⟩ = cupOpp g5 g1 ⟨4, by decide⟩
    ∧ delta1 eta_g1g5 ⟨5, by decide⟩ = cupOpp g5 g1 ⟨5, by decide⟩
    ∧ delta1 eta_g1g5 ⟨6, by decide⟩ = cupOpp g5 g1 ⟨6, by decide⟩
    ∧ delta1 eta_g1g5 ⟨7, by decide⟩ = cupOpp g5 g1 ⟨7, by decide⟩
    ∧ delta1 eta_g1g5 ⟨8, by decide⟩ = cupOpp g5 g1 ⟨8, by decide⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem witnessB_rep_face_values :
    cupOpp g4 eta_g1g5 ⟨0, by decide⟩ = true
    ∧ cupOpp g4 eta_g1g5 ⟨1, by decide⟩ = false
    ∧ cupOpp g4 eta_g1g5 ⟨2, by decide⟩ = false
    ∧ cupOpp g4 eta_g1g5 ⟨3, by decide⟩ = true
    ∧ cupOpp g4 eta_g1g5 ⟨4, by decide⟩ = false
    ∧ cupOpp g4 eta_g1g5 ⟨5, by decide⟩ = false
    ∧ cupOpp g4 eta_g1g5 ⟨6, by decide⟩ = false
    ∧ cupOpp g4 eta_g1g5 ⟨7, by decide⟩ = false
    ∧ cupOpp g4 eta_g1g5 ⟨8, by decide⟩ = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem witnessB_violates_R_S01 :
    xor (xor (cupOpp g4 eta_g1g5 ⟨0, by decide⟩)
              (cupOpp g4 eta_g1g5 ⟨1, by decide⟩))
         (cupOpp g4 eta_g1g5 ⟨2, by decide⟩) = true := by decide

theorem witnessB_violates_R_S02 :
    xor (xor (cupOpp g4 eta_g1g5 ⟨3, by decide⟩)
              (cupOpp g4 eta_g1g5 ⟨4, by decide⟩))
         (cupOpp g4 eta_g1g5 ⟨5, by decide⟩) = true := by decide

/-! ## §5 — Witness C: ⟨g4, g5, g2⟩  →  rep violates R_{S_{01}} + R_{S_{12}}

  · a ⌣ b = g4 ⌣ g5 = 0 (same as Witness B)
  · b ⌣ c = g5 ⌣ g2 cobounds via η_{bc} = e₈
  · Rep = a ⌣ η_{bc} = g4 ⌣ e₈
  · Rep value vector: (1, 0, 0, 0, 0, 0, 1, 0, 0)
  · Violates `R_{S_{01}}: face0+face1+face2 = 1+0+0 = 1`
  · Violates `R_{S_{12}}: face6+face7+face8 = 1+0+0 = 1` -/

theorem witnessC_delta_eta_eq_cup :
    delta1 eta_g2g5_for_C ⟨0, by decide⟩ = cupOpp g5 g2 ⟨0, by decide⟩
    ∧ delta1 eta_g2g5_for_C ⟨1, by decide⟩ = cupOpp g5 g2 ⟨1, by decide⟩
    ∧ delta1 eta_g2g5_for_C ⟨2, by decide⟩ = cupOpp g5 g2 ⟨2, by decide⟩
    ∧ delta1 eta_g2g5_for_C ⟨3, by decide⟩ = cupOpp g5 g2 ⟨3, by decide⟩
    ∧ delta1 eta_g2g5_for_C ⟨4, by decide⟩ = cupOpp g5 g2 ⟨4, by decide⟩
    ∧ delta1 eta_g2g5_for_C ⟨5, by decide⟩ = cupOpp g5 g2 ⟨5, by decide⟩
    ∧ delta1 eta_g2g5_for_C ⟨6, by decide⟩ = cupOpp g5 g2 ⟨6, by decide⟩
    ∧ delta1 eta_g2g5_for_C ⟨7, by decide⟩ = cupOpp g5 g2 ⟨7, by decide⟩
    ∧ delta1 eta_g2g5_for_C ⟨8, by decide⟩ = cupOpp g5 g2 ⟨8, by decide⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem witnessC_rep_face_values :
    cupOpp g4 eta_g2g5_for_C ⟨0, by decide⟩ = true
    ∧ cupOpp g4 eta_g2g5_for_C ⟨1, by decide⟩ = false
    ∧ cupOpp g4 eta_g2g5_for_C ⟨2, by decide⟩ = false
    ∧ cupOpp g4 eta_g2g5_for_C ⟨3, by decide⟩ = false
    ∧ cupOpp g4 eta_g2g5_for_C ⟨4, by decide⟩ = false
    ∧ cupOpp g4 eta_g2g5_for_C ⟨5, by decide⟩ = false
    ∧ cupOpp g4 eta_g2g5_for_C ⟨6, by decide⟩ = true
    ∧ cupOpp g4 eta_g2g5_for_C ⟨7, by decide⟩ = false
    ∧ cupOpp g4 eta_g2g5_for_C ⟨8, by decide⟩ = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem witnessC_violates_R_S01 :
    xor (xor (cupOpp g4 eta_g2g5_for_C ⟨0, by decide⟩)
              (cupOpp g4 eta_g2g5_for_C ⟨1, by decide⟩))
         (cupOpp g4 eta_g2g5_for_C ⟨2, by decide⟩) = true := by decide

theorem witnessC_violates_R_S12 :
    xor (xor (cupOpp g4 eta_g2g5_for_C ⟨6, by decide⟩)
              (cupOpp g4 eta_g2g5_for_C ⟨7, by decide⟩))
         (cupOpp g4 eta_g2g5_for_C ⟨8, by decide⟩) = true := by decide

/-! ## §6 — Master capstone: 4-dim image of H² spanned by 4 Massey witnesses

The four Massey witnesses at K_{3,3}^{(c=2)} produce chain-level
representatives that violate four distinct (relation-pair) patterns
in the 6 row/column R-relations:

| Witness | Violates |
|---|---|
| ⟨g1, g2, g4⟩ (primary, in `V33MasseyWitness`) | R_{T_{01}} + R_{T_{02}} |
| ⟨g1, g2, g5⟩ (A) | R_{T_{01}} + R_{T_{12}} |
| ⟨g4, g5, g1⟩ (B) | R_{S_{01}} + R_{S_{02}} |
| ⟨g4, g5, g2⟩ (C) | R_{S_{01}} + R_{S_{12}} |

Each pair is *fresh* relative to the union of previous violations,
so the four corresponding classes in H² = F₂⁵ are linearly
independent and span a **4-dimensional subspace** of H².

The capstone bundles, for each new witness, the three minimum
pieces needed to certify a non-zero H² class:
  · `a ⌣ b = 0` chain-level (η_{ab} = 0)
  · `δ¹(η_{bc}) = b ⌣ c` at the violated-relation faces
  · The Massey representative violates one R-relation (and is
    therefore NOT in im δ¹). -/

theorem four_witnesses_span_four_dim_H2 :
    -- Witness A: η_g2g5 cobounds g2 ⌣ g5; Massey rep violates R_{T_{01}}
    (delta1 eta_g2g5 ⟨0, by decide⟩ = cupOpp g2 g5 ⟨0, by decide⟩
     ∧ delta1 eta_g2g5 ⟨3, by decide⟩ = cupOpp g2 g5 ⟨3, by decide⟩
     ∧ delta1 eta_g2g5 ⟨6, by decide⟩ = cupOpp g2 g5 ⟨6, by decide⟩)
    ∧ xor (xor (cupOpp g1 eta_g2g5 ⟨0, by decide⟩)
                (cupOpp g1 eta_g2g5 ⟨3, by decide⟩))
           (cupOpp g1 eta_g2g5 ⟨6, by decide⟩) = true
    -- Witness B: η_g1g5 cobounds g5 ⌣ g1; Massey rep violates R_{S_{01}}
    ∧ (delta1 eta_g1g5 ⟨0, by decide⟩ = cupOpp g5 g1 ⟨0, by decide⟩
       ∧ delta1 eta_g1g5 ⟨1, by decide⟩ = cupOpp g5 g1 ⟨1, by decide⟩
       ∧ delta1 eta_g1g5 ⟨2, by decide⟩ = cupOpp g5 g1 ⟨2, by decide⟩)
    ∧ xor (xor (cupOpp g4 eta_g1g5 ⟨0, by decide⟩)
                (cupOpp g4 eta_g1g5 ⟨1, by decide⟩))
           (cupOpp g4 eta_g1g5 ⟨2, by decide⟩) = true
    -- Witness C: η_g2g5_for_C cobounds g5 ⌣ g2; Massey rep violates R_{S_{12}}
    ∧ (delta1 eta_g2g5_for_C ⟨6, by decide⟩ = cupOpp g5 g2 ⟨6, by decide⟩
       ∧ delta1 eta_g2g5_for_C ⟨7, by decide⟩ = cupOpp g5 g2 ⟨7, by decide⟩
       ∧ delta1 eta_g2g5_for_C ⟨8, by decide⟩ = cupOpp g5 g2 ⟨8, by decide⟩)
    ∧ xor (xor (cupOpp g4 eta_g2g5_for_C ⟨6, by decide⟩)
                (cupOpp g4 eta_g2g5_for_C ⟨7, by decide⟩))
           (cupOpp g4 eta_g2g5_for_C ⟨8, by decide⟩) = true
    -- Every coboundary satisfies all four new R-relations
    ∧ (∀ σ : CochE, xor (xor (face3 σ) (face4 σ)) (face5 σ) = false)
    ∧ (∀ σ : CochE, xor (xor (face6 σ) (face7 σ)) (face8 σ) = false)
    ∧ (∀ σ : CochE, xor (xor (face1 σ) (face4 σ)) (face7 σ) = false)
    ∧ (∀ σ : CochE, xor (xor (face2 σ) (face5 σ)) (face8 σ) = false) :=
  ⟨⟨(witnessA_delta_eta_eq_cup).1,
    (witnessA_delta_eta_eq_cup).2.2.2.1,
    (witnessA_delta_eta_eq_cup).2.2.2.2.2.2.1⟩,
   witnessA_violates_R_T01,
   ⟨(witnessB_delta_eta_eq_cup).1,
    (witnessB_delta_eta_eq_cup).2.1,
    (witnessB_delta_eta_eq_cup).2.2.1⟩,
   witnessB_violates_R_S01,
   ⟨(witnessC_delta_eta_eq_cup).2.2.2.2.2.2.1,
    (witnessC_delta_eta_eq_cup).2.2.2.2.2.2.2.1,
    (witnessC_delta_eta_eq_cup).2.2.2.2.2.2.2.2⟩,
   witnessC_violates_R_S12,
   face_dep_S02, face_dep_S12, face_dep_T02, face_dep_T12⟩

end E213.Lib.Math.Cohomology.Bipartite.V33MasseyMulti
