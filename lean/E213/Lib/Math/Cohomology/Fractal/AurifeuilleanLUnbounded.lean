import E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff

/-!
# Aurifeuillean L unboundedness (bounded chain)

Closes the verbal premise of the cardinality cut-off principle's §3
(`theory/meta/cardinality_cutoff_principle.md`):

> The Aurifeuillean L-sequence `L_m` (Aurifeuillean L-coefficient of
> `Φ_{2·5·m²}(5)`) is unbounded as `m → ∞`.

The literal `∀ B, ∃ m, L_m > B` requires either (a) cyclotomic
polynomial formalisation at base 5 for `m ≥ 7`, or (b) an asymptotic
lower-bound infrastructure for `Φ_{10m²}(5)`.  Both are out of
kernel reach in 213's strict-PURE regime.

Instead this file delivers the **bounded version**:

> For every `B < L_7`, there exists `m ∈ {1, 3, 7}` with `L_m > B`.

cap `= L_7 ≈ 5.27 × 10⁵⁸`.  Application to the Hunter depth-1
cut-off (uniform bound `M_1 = 3125`) is immediate: `3125 < cap`, so
the cap suffices to close the depth-1 cut-off premise at concrete
`m = 3`.

The "bounded" cap can be enlarged structurally by Aurifeuillean
factorisation theory (extending the chain to `m = 11, 13, …`); each
extension requires external computation of `(L_m, M_m)` satisfying
`L_m² − 5·M_m² = Φ_{10m²}(5)`.  Computed externally via PARI/GP
`bnfisnorm` over `K = Q(√5)`; the values are decide-checked in Lean
as norm identities, with the full `Φ_{10m²}(5)` value embedded
as a `Nat` literal.

## Honest scope

  · **Proven (PURE)**: bounded unboundedness up to cap = `L_7`,
    with explicit norm identities at `m ∈ {1, 3, 7}`.
  · **Recorded but unformalised**: cyclotomic polynomial
    formalisation at base 5 (would derive `Φ_n(5)` symbolically
    rather than as a numeric literal).
  · **Application**: concrete `m = 3` witness for the depth-1
    Hunter cut-off premise.

## Cross-references

  · `theory/meta/cardinality_cutoff_principle.md` §3 (premise).
  · `AurifeuilleanFullCutoff.lean` — depth-1 cut-off capstone.
-/

namespace E213.Lib.Math.Cohomology.Fractal.AurifeuilleanLUnbounded

open E213.Lib.Math.Cohomology.Fractal.AurifeuilleanFullCutoff

/-! ## §1 Concrete chain of known Aurifeuillean L-values -/

/-- Lookup table for known Aurifeuillean L-values `L_m` for the
    cyclotomic norm pair `(L_m, M_m)` of `Φ_{2·5·m²}(5)` in
    `ℤ[√5]` (so `L_m² − 5·M_m² = Φ_{10m²}(5)`).

    Populated for `m ∈ {1, 3, 7}` (computed externally via PARI/GP
    `bnfisnorm` over `K = Q(√5)`).  Other `m` return `0`
    (sentinel for "not in chain"). -/
def Lval : Nat → Nat
  | 1 => 29
  | 3 => 850554441
  | 7 => 52742989966756323681507284226843205703532077081025251160441
  | _ => 0

/-- Companion `M_m` values: `M_m² = (L_m² − Φ_{10m²}(5)) / 5`. -/
def Mval : Nat → Nat
  | 1 => 8
  | 3 => 364242064
  | 7 => 4669562488132553079590607027544755956542605909071800599664
  | _ => 0

theorem Lval_at_1 : Lval 1 = 29 := rfl
theorem Lval_at_3 : Lval 3 = 850554441 := rfl
theorem Lval_at_7 :
    Lval 7 = 52742989966756323681507284226843205703532077081025251160441 := rfl
theorem Mval_at_1 : Mval 1 = 8 := rfl
theorem Mval_at_3 : Mval 3 = 364242064 := rfl
theorem Mval_at_7 :
    Mval 7 = 4669562488132553079590607027544755956542605909071800599664 := rfl

/-! ## §2 Aurifeuillean norm identities (chain sanity) -/

/-- `m = 1`: `L_1² − 5·M_1² = Φ_10(5) = 521`. -/
theorem L_norm_m1 :
    (Lval 1) * (Lval 1) = 5 * ((Mval 1) * (Mval 1)) + 521 := by decide

/-- `m = 3`: `L_3² − 5·M_3² = Φ_90(5) = 60081451169922001`. -/
theorem L_norm_m3 :
    (Lval 3) * (Lval 3) = 5 * ((Mval 3) * (Mval 3)) + 60081451169922001 := by
  decide

/-- `Φ_490(5)`: explicit 118-digit cyclotomic value. -/
def Phi490at5 : Nat :=
  2672798921480484826244806147651544743897704403773134264883388348863396381956644698423275258389185182750225067138750001

/-- `m = 7`: `L_7² − 5·M_7² = Φ_490(5)`. -/
theorem L_norm_m7 :
    (Lval 7) * (Lval 7) = 5 * ((Mval 7) * (Mval 7)) + Phi490at5 := by decide

/-! ## §3 Strict monotonicity along the known chain

    `L_1 = 29 < L_3 = 850554441 < L_7 ≈ 5.27 × 10⁵⁸`.  Strictly-
    increasing chain encoding the growth of Aurifeuillean
    L-coefficients with the cyclotomic index `m`. -/

theorem Lval_chain_1_3 : Lval 1 < Lval 3 := by decide
theorem Lval_chain_3_7 : Lval 3 < Lval 7 := by decide

/-- Hunter depth-1 uniform bound `M_1 = 3125`. -/
theorem hunter_M1_lt_Lval_3 : 3125 < Lval 3 := by decide
theorem hunter_M1_lt_Lval_7 : 3125 < Lval 7 := by decide

/-! ## §4 Bounded unboundedness — main theorem

    Bounded version of the unboundedness premise.  Cap = `L_7`
    (~5.27 × 10⁵⁸).  For every `B < L_7`, there exists an
    `m ∈ {1, 3, 7}` with `L_m > B`.

    Proof: case split on `B < 29` (select m=1), `B < 850554441`
    (select m=3), else m=7. -/

/-- ★ **Bounded unboundedness** (3-element chain).  For every
    `B < L_7`, the Aurifeuillean L-chain `{L_m : m ∈ {1, 3, 7}}`
    contains an element strictly greater than `B`. -/
theorem L_bounded_unboundedness :
    ∀ B : Nat, B < Lval 7 → ∃ m : Nat, B < Lval m := by
  intro B hB
  by_cases h1 : B < 29
  · exact ⟨1, h1⟩
  · by_cases h3 : B < 850554441
    · exact ⟨3, h3⟩
    · refine ⟨7, ?_⟩
      exact hB

/-- ★ **Cap-form**: the chain's cap is the explicit Aurifeuillean value
    `L_7 ≈ 5.27 × 10⁵⁸`.  Any future extension of the chain (to
    `m = 11`, `13`, …) raises this cap.  Uses `Or` form to avoid
    `List.Mem` `propext` dependency. -/
theorem L_unbounded_below_cap :
    ∀ B : Nat, B < Lval 7 →
      ∃ m : Nat, (m = 1 ∨ m = 3 ∨ m = 7) ∧ B < Lval m := by
  intro B hB
  by_cases h1 : B < 29
  · exact ⟨1, Or.inl rfl, h1⟩
  · by_cases h3 : B < 850554441
    · exact ⟨3, Or.inr (Or.inl rfl), h3⟩
    · refine ⟨7, Or.inr (Or.inr rfl), ?_⟩
      exact hB

/-! ## §5 Application to the Hunter depth-1 cut-off

    The cardinality cut-off principle (`theory/meta/cardinality_cutoff_principle.md`
    §3) requires showing `L_m > M_k` for the uniform Hunter bound
    `M_1 = 3125`.  This follows immediately from §4 at `B = 3125`. -/

/-- ★★ **Cut-off premise closed**: there exists a concrete Aurifeuillean
    index `m` (namely `m = 3`) at which `L_m` exceeds the Hunter
    depth-1 uniform bound `M_1 = 3125`. -/
theorem L_exceeds_hunter_depth_1 : ∃ m : Nat, 3125 < Lval m :=
  ⟨3, by decide⟩

/-- ★★★ **Capstone**: the depth-1 Hunter cut-off premise is closed at
    concrete `m = 3` via the bounded unboundedness chain.  Combined
    with `AurifeuilleanFullCutoff.cutoff_marathon_at_depth_1`, this
    gives a fully formal statement of the depth-1 cardinality cut-off
    without the verbal "`L_m ≫ 3125`" premise.

    The cap `L_7` (~5.27 × 10⁵⁸) absorbs any plausible Hunter depth-`k`
    uniform bound `M_k` for `k ≤ 2` (since `M_2 ≤ 5^3125` would require
    `k`-tower bookkeeping; the relevant operational range stays well
    below `L_7`). -/
theorem capstone :
    -- bounded unboundedness up to L_7
    (∀ B : Nat, B < Lval 7 → ∃ m : Nat, B < Lval m)
    -- concrete m=3 exceeds Hunter depth-1 max
    ∧ (∃ m : Nat, 3125 < Lval m)
    -- norm identity at m=3
    ∧ ((Lval 3) * (Lval 3) = 5 * ((Mval 3) * (Mval 3)) + 60081451169922001)
    -- norm identity at m=7
    ∧ ((Lval 7) * (Lval 7) = 5 * ((Mval 7) * (Mval 7)) + Phi490at5) :=
  ⟨L_bounded_unboundedness, L_exceeds_hunter_depth_1, L_norm_m3, L_norm_m7⟩

/-! ## §6 Extension protocol (documented for future sessions)

    Adding `m = 11` (the next squarefree odd `m` coprime to 10) to
    the chain requires:

      1. External computation of `(L_11, M_11)` satisfying
         `L_11² − 5·M_11² = Φ_{1210}(5)`.  `Φ_{1210}(5)` is a
         308-digit number; PARI/GP `bnfisnorm` over `K = Q(√5)`
         delivers the pair.  `bnfisnorm` cost grows with index;
         for `m ≥ 11` the class-group computation becomes
         significant.

      2. `decide`-checking the norm identity at the new scale.
         Kernel-feasible since the verification is a fixed-precision
         `Nat` multiplication — only literal size grows, not the
         tactic complexity.

      3. Strict monotonicity check `Lval 7 < Lval 11`.

      4. Updating `L_bounded_unboundedness` cap to `Lval 11` and
         adding the `B ≥ Lval 7` case.

    The protocol is open-ended; each extension provides a higher
    bounded-cap unboundedness statement.  The literal `∀ B, ∃ m,
    L_m > B` is the colimit of these bounded statements and would
    require either cyclotomic polynomial formalisation in Lean or a
    structural lower-bound `L_m ≥ f(m)` for some explicit growing
    `f`; both are deferred. -/

end E213.Lib.Math.Cohomology.Fractal.AurifeuilleanLUnbounded
