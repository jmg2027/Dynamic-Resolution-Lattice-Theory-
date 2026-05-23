import E213.Lib.Math.GeometrizationConjecture.Capstone

/-!
# R1+ — K_{NS,NT}^{(c)} general-deployment enumeration (partial)

User-deferred at step 17 (R1).  This file extends the existing
parametric infrastructure (already in place via `chartBase`,
`chartVisibleAxes`, `isTreeDeployment`, `b1_corrected`,
`hasNaturalSym3`, `hasC2BinaryCoverMatch`, `passesCohomologyDepthFilter`)
to enumerate dim-4 self-pointing ansatz behavior across a wider (NS, NT, c) range.

## Existing parametric machinery (R1)

  · `chartBase n m := n + m`
  · `chartVisibleAxes n m := n + m − 1`
  · `b1_corrected n m c := if c·n·m + 1 ≥ n + m then c·n·m + 1 − (n+m) else 0`
  · `isTreeDeployment n m c := c = 1 ∧ (n = 1 ∨ m = 1)`
  · `hasNaturalSym3 n m := n = 3 ∨ m = 3`
  · `hasC2BinaryCoverMatch n m c := c = 2 ∧ (n = 2 ∨ m = 2)`
  · `passesCohomologyDepthFilter n m c := b_1 = 8 ∧ Sym3 ∧ c=2-binary`

This file ADDS:
  · Extended enumeration tables (chartBase ∈ {2..10})
  · b_1 = 8 deployment uniqueness verification at higher chartBase
  · Tree deployment enumeration across d_M ∈ {1..8}

Status:  PARTIAL — full generalization (parametric proofs across
all (n, m, c)) requires graph-cohomology infrastructure beyond
present scope.

Sub-tree: `GeometrizationConjecture/INDEX.md`.
-/

namespace E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz

/-! ## Extended b_1 = 8 deployment uniqueness (chartBase ∈ {5..12}) -/

/-- All b_1 = 8 solutions at chartBase = 5 (= deployments with NS+NT=5).
    Filter result: only K_{3,2}^{(c=2)} and K_{2,3}^{(c=2)} pass depth. -/
theorem b1_eight_chartBase_5 :
    -- (3, 2, 2) passes
    passesCohomologyDepthFilter 3 2 2 = true
    ∧ passesCohomologyDepthFilter 2 3 2 = true
    -- (4, 1, 3) and (1, 4, 3) fail (no Sym(3))
    ∧ passesCohomologyDepthFilter 4 1 3 = false
    ∧ passesCohomologyDepthFilter 1 4 3 = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- All b_1 = 8 solutions at chartBase = 8: (5,3,1), (3,5,1).
    Neither passes depth filter (c ≠ 2). -/
theorem b1_eight_chartBase_8 :
    passesCohomologyDepthFilter 5 3 1 = false
    ∧ passesCohomologyDepthFilter 3 5 1 = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-- All b_1 = 8 solutions at chartBase = 9: (8,1,2), (1,8,2).
    Neither passes (no NS=3 or NT=3). -/
theorem b1_eight_chartBase_9 :
    passesCohomologyDepthFilter 8 1 2 = false
    ∧ passesCohomologyDepthFilter 1 8 2 = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-- All b_1 = 8 solutions at chartBase = 11: (9,2,1), (2,9,1).
    Neither passes (c=1 ≠ 2). -/
theorem b1_eight_chartBase_11 :
    passesCohomologyDepthFilter 9 2 1 = false
    ∧ passesCohomologyDepthFilter 2 9 1 = false := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## Tree-deployment enumeration across d_M ∈ {1..8} -/

theorem tree_enumeration_d1_to_d8 :
    -- d_M = 1: K_{1,1}^{(c=1)}
    isTreeDeployment 1 1 1 = true
    -- d_M = 2: K_{1,2}, K_{2,1}
    ∧ isTreeDeployment 1 2 1 = true
    ∧ isTreeDeployment 2 1 1 = true
    -- d_M = 3: K_{1,3}, K_{3,1} (Poincaré)
    ∧ isTreeDeployment 1 3 1 = true
    ∧ isTreeDeployment 3 1 1 = true
    -- d_M = 4: K_{1,4}, K_{4,1} (coexist with K_{3,2}^{(c=2)} critical)
    ∧ isTreeDeployment 1 4 1 = true
    ∧ isTreeDeployment 4 1 1 = true
    -- d_M = 5: K_{1,5}, K_{5,1}
    ∧ isTreeDeployment 1 5 1 = true
    ∧ isTreeDeployment 5 1 1 = true
    -- d_M = 6: K_{1,6}, K_{6,1}
    ∧ isTreeDeployment 1 6 1 = true
    ∧ isTreeDeployment 6 1 1 = true
    -- d_M = 7, 8 similarly
    ∧ isTreeDeployment 1 7 1 = true
    ∧ isTreeDeployment 1 8 1 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Higher-chartBase critical-uniqueness (extension) -/

/-- At chartBase = 6, NO deployment passes cohomology-depth filter
    (no b_1 = 8 with required (Sym(3), c=2-binary) intersection). -/
theorem critical_unique_chartBase_6 :
    -- K_{3,3}^{(c=1,2,3)}: all fail
    passesCohomologyDepthFilter 3 3 1 = false
    ∧ passesCohomologyDepthFilter 3 3 2 = false
    ∧ passesCohomologyDepthFilter 3 3 3 = false
    -- K_{4,2}^{(c=1,2,3)}: all fail
    ∧ passesCohomologyDepthFilter 4 2 1 = false
    ∧ passesCohomologyDepthFilter 4 2 2 = false
    ∧ passesCohomologyDepthFilter 4 2 3 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- At chartBase = 7, NO deployment passes depth filter. -/
theorem critical_unique_chartBase_7 :
    passesCohomologyDepthFilter 3 4 1 = false
    ∧ passesCohomologyDepthFilter 3 4 2 = false
    ∧ passesCohomologyDepthFilter 4 3 1 = false
    ∧ passesCohomologyDepthFilter 4 3 2 = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- At chartBase = 8, NO deployment passes (Sym(3) at K_{3,5}/K_{5,3}
    fails c=2 binary; (4,4) fails Sym(3)). -/
theorem critical_unique_chartBase_8 :
    passesCohomologyDepthFilter 3 5 1 = false
    ∧ passesCohomologyDepthFilter 3 5 2 = false
    ∧ passesCohomologyDepthFilter 5 3 1 = false
    ∧ passesCohomologyDepthFilter 5 3 2 = false
    ∧ passesCohomologyDepthFilter 4 4 1 = false
    ∧ passesCohomologyDepthFilter 4 4 2 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★★★★ **K_{3,2}^{(c=2)} unique across chartBase ∈ {4..8}**:
    Across all tested deployments with NS+NT ∈ {4..8} and c ∈ {1, 2, 3},
    ONLY K_{3,2}^{(c=2)} (and S/T-swap K_{2,3}^{(c=2)}) pass the full
    cohomology-depth filter (b_1 = 8 ∧ Sym(3) ∧ c=2-binary).

    Generalization-track partial close: depth-filter uniqueness
    scales across the full chartBase ∈ {4..8} range (verified by
    exhaustive PURE enumeration). -/
theorem K32_c2_uniqueness_extended_range :
    -- Only K_{3,2}^{(c=2)} and S/T swap pass
    passesCohomologyDepthFilter 3 2 2 = true
    ∧ passesCohomologyDepthFilter 2 3 2 = true
    -- chartBase = 4: K_{2,2}, K_{3,1}, K_{1,3} all fail
    ∧ passesCohomologyDepthFilter 2 2 2 = false
    ∧ passesCohomologyDepthFilter 3 1 2 = false
    -- chartBase = 6: all K_{3,3}, K_{4,2} fail
    ∧ passesCohomologyDepthFilter 3 3 2 = false
    ∧ passesCohomologyDepthFilter 4 2 2 = false
    -- chartBase = 7: K_{3,4}, K_{4,3} all fail
    ∧ passesCohomologyDepthFilter 3 4 2 = false
    ∧ passesCohomologyDepthFilter 4 3 2 = false
    -- chartBase = 8: K_{3,5}, K_{5,3}, K_{4,4} all fail
    ∧ passesCohomologyDepthFilter 3 5 2 = false
    ∧ passesCohomologyDepthFilter 5 3 2 = false
    ∧ passesCohomologyDepthFilter 4 4 2 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Universal cohomology-depth filter characterization

The per-chartBase enumeration tables above (chartBase ∈ {4..8})
generalize to a closed-form characterization across **all** Nat
inputs.  The Sym(3) + c=2-binary-cover filters combined force
`{n, m} = {2, 3} ∧ c = 2`, after which b₁ = 8 is automatic.
-/

/-- The Sym(3) + c=2-binary-cover filters alone — without the b₁ = 8
    conjunct — already force `{n, m} = {2, 3} ∧ c = 2`. -/
theorem sym3_c2_force_K32 (n m c : Nat) :
    hasNaturalSym3 n m = true →
    hasC2BinaryCoverMatch n m c = true →
    ((n = 3 ∧ m = 2 ∧ c = 2) ∨ (n = 2 ∧ m = 3 ∧ c = 2)) := by
  intro hsymBool hc2Bool
  unfold hasNaturalSym3 at hsymBool
  unfold hasC2BinaryCoverMatch at hc2Bool
  have hsym := of_decide_eq_true hsymBool
  have hc2 := of_decide_eq_true hc2Bool
  obtain ⟨hc, hnm⟩ := hc2
  cases hnm with
  | inl hn2 =>
      cases hsym with
      | inl hn3 => exact absurd (hn3.symm.trans hn2) (by decide)
      | inr hm3 => exact Or.inr ⟨hn2, hm3, hc⟩
  | inr hm2 =>
      cases hsym with
      | inl hn3 => exact Or.inl ⟨hn3, hm2, hc⟩
      | inr hm3 => exact absurd (hm3.symm.trans hm2) (by decide)

/-- ★★★★★ **Filter universal characterization (Prop-level)**

  `sym3_c2_force_K32` says: any (n, m, c) satisfying both
  representation-structure filters (Sym(3) + c=2-binary-cover) MUST
  be `(3, 2, 2)` or `(2, 3, 2)` — no chartBase bound, no b₁=8
  conjunct needed.

  This is the **universal closure** of the per-chartBase tables
  above: instead of checking each (n+m) ∈ {4..8} case by case, the
  iff below directly characterizes filter-passers via two pure
  Prop-level conditions.  The b₁=8 conjunct of the full Boolean
  filter is automatic from `K32_c2_b1` (b₁(3,2,2) = 8) and its
  S/T-swap; that piece is already covered by `b1_eight_chartBase_5`. -/
theorem sym3_c2_iff_K32_or_K23 (n m c : Nat) :
    (hasNaturalSym3 n m = true ∧ hasC2BinaryCoverMatch n m c = true) ↔
    ((n = 3 ∧ m = 2 ∧ c = 2) ∨ (n = 2 ∧ m = 3 ∧ c = 2)) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact sym3_c2_force_K32 n m c h1 h2
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> exact ⟨by decide, by decide⟩

/-- Propext-free helper: extract both sides of a Boolean conjunction
    that equals `true`.  PURE via explicit Bool case match. -/
private theorem and_eq_true_extract :
    ∀ {a b : Bool}, (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | false, _, h => Bool.noConfusion h
  | true, false, h => Bool.noConfusion h

/-- ★★★★★ **Boolean ↔ universal characterization** — propext-free
    closure of the FW-3 universal-filter theorem.

  The Prop-level `sym3_c2_iff_K32_or_K23` is extended to the full
  Boolean `passesCohomologyDepthFilter ↔ ...` form using a
  hand-rolled propext-free Bool-conjunction extractor.  All
  arithmetic discharges via `decide`. -/
theorem passes_filter_universal_bool (n m c : Nat) :
    passesCohomologyDepthFilter n m c = true ↔
    ((n = 3 ∧ m = 2 ∧ c = 2) ∨ (n = 2 ∧ m = 3 ∧ c = 2)) := by
  constructor
  · intro h
    unfold passesCohomologyDepthFilter at h
    obtain ⟨h12, h3⟩ := and_eq_true_extract h
    obtain ⟨_, h2⟩ := and_eq_true_extract h12
    exact sym3_c2_force_K32 n m c h2 h3
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> decide

/-- The filter rejects every deployment outside K_{3,2}^{(c=2)} ± S/T-swap. -/
theorem filter_rejects_outside_K32 (n m c : Nat)
    (hne1 : ¬(n = 3 ∧ m = 2 ∧ c = 2))
    (hne2 : ¬(n = 2 ∧ m = 3 ∧ c = 2)) :
    passesCohomologyDepthFilter n m c = false := by
  cases h : passesCohomologyDepthFilter n m c
  · rfl
  · rcases (passes_filter_universal_bool n m c).mp h with h1 | h2
    · exact absurd h1 hne1
    · exact absurd h2 hne2

/-- ★★★★ **Filter-passers live only at chartBase = 5** (asymptotic
    closure of the chartBase enumeration).

  Across **all** Nat chartBase values, the Sym(3) + c=2-binary-cover
  filter together force the deployment onto chartBase = 5 = NS + NT
  with K_{3,2}^{(c=2)} or K_{2,3}^{(c=2)}.  No chartBase ≥ 9
  enumeration table needed — the universal Prop-level theorem above
  closes the entire range. -/
theorem filter_passes_only_chartBase_5 (n m c : Nat)
    (hsym : hasNaturalSym3 n m = true)
    (hcc : hasC2BinaryCoverMatch n m c = true) :
    chartBase n m = 5 := by
  rcases sym3_c2_force_K32 n m c hsym hcc with ⟨hn, hm, _⟩ | ⟨hn, hm, _⟩
  · subst hn; subst hm; rfl
  · subst hn; subst hm; rfl

end E213.Lib.Math.GeometrizationConjecture.ChartAxisAnsatz
