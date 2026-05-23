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

> For every `B < 850_554_441`, there exists `m ∈ {1, 3}` with
> `L_m > B`.

cap `= L_3 = 850_554_441`.  Application to the Hunter depth-1 cut-off
(uniform bound `M_1 = 3125`) is immediate: `3125 < cap`, so the cap
suffices to close the depth-1 cut-off premise at concrete `m = 3`.

The "bounded" cap can be enlarged structurally by Aurifeuillean
factorisation theory (extending the chain to `m = 7, 11, …`); each
extension requires external computation of `(L_m, M_m)` satisfying
`L_m² − 5·M_m² = Φ_{10m²}(5)`.  The chain is open-ended.

## Honest scope

  · **Proven (PURE)**: bounded unboundedness up to cap = `L_3`.
  · **Recorded but unformalised**: full Aurifeuillean theory for
    `m ≥ 7` (would require `Φ_{490}(5)` ~ 10^118 in kernel).
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

    Only `m ∈ {1, 3}` are populated (kernel-feasible values).
    Other `m` return `0` (sentinel for "not in chain"). -/
def Lval : Nat → Nat
  | 1 => 29
  | 3 => 850554441
  | _ => 0

/-- Companion `M_m` values: `M_m² = (L_m² − Φ_{10m²}(5)) / 5`. -/
def Mval : Nat → Nat
  | 1 => 8
  | 3 => 364242064
  | _ => 0

theorem Lval_at_1 : Lval 1 = 29 := rfl
theorem Lval_at_3 : Lval 3 = 850554441 := rfl
theorem Mval_at_1 : Mval 1 = 8 := rfl
theorem Mval_at_3 : Mval 3 = 364242064 := rfl

/-! ## §2 Aurifeuillean norm identities (chain sanity) -/

/-- `m = 1`: `L_1² − 5·M_1² = Φ_10(5) = 521`. -/
theorem L_norm_m1 :
    (Lval 1) * (Lval 1) = 5 * ((Mval 1) * (Mval 1)) + 521 := by decide

/-- `m = 3`: `L_3² − 5·M_3² = Φ_90(5) = 60081451169922001`. -/
theorem L_norm_m3 :
    (Lval 3) * (Lval 3) = 5 * ((Mval 3) * (Mval 3)) + 60081451169922001 := by
  decide

/-! ## §3 Strict monotonicity along the known chain

    `L_1 = 29 < L_3 = 850554441`.  The strictly-increasing chain
    encodes the structural fact that the Aurifeuillean L-coefficient
    grows with the cyclotomic index `m`. -/

theorem Lval_strict_chain : Lval 1 < Lval 3 := by decide

/-- Hunter depth-1 uniform bound `M_1 = 3125`. -/
theorem hunter_M1_lt_Lval_3 : 3125 < Lval 3 := by decide

/-! ## §4 Bounded unboundedness — main theorem

    The bounded version of the unboundedness premise.  For every
    bound `B` strictly below the chain's cap `L_3 = 850554441`,
    there exists an `m ∈ {1, 3}` with `L_m > B`.

    The proof is a single case split: `B < 29` selects `m = 1`,
    otherwise `m = 3`. -/

/-- ★ **Bounded unboundedness**: for every `B < L_3`, the Aurifeuillean
    L-chain `{L_m : m ∈ {1, 3}}` contains an element strictly greater
    than `B`. -/
theorem L_bounded_unboundedness :
    ∀ B : Nat, B < 850554441 → ∃ m : Nat, B < Lval m := by
  intro B hB
  by_cases h : B < 29
  · exact ⟨1, h⟩
  · refine ⟨3, ?_⟩
    show B < 850554441
    exact hB

/-- ★ **Cap-form**: the chain's cap is the explicit Aurifeuillean value
    `L_3 = 850554441`.  Any future extension of the chain (to `m = 7`,
    `11`, …) raises this cap.  Uses `Or` form to avoid `List.Mem`
    `propext` dependency. -/
theorem L_unbounded_below_cap :
    ∀ B : Nat, B < 850554441 →
      ∃ m : Nat, (m = 1 ∨ m = 3) ∧ B < Lval m := by
  intro B hB
  by_cases h : B < 29
  · exact ⟨1, Or.inl rfl, h⟩
  · refine ⟨3, Or.inr rfl, ?_⟩
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
    without the verbal "`L_m ≫ 3125`" premise. -/
theorem capstone :
    -- bounded unboundedness up to L_3
    (∀ B : Nat, B < 850554441 → ∃ m : Nat, B < Lval m)
    -- concrete m=3 exceeds Hunter depth-1 max
    ∧ (∃ m : Nat, 3125 < Lval m)
    -- norm identity at m=3
    ∧ ((Lval 3) * (Lval 3) = 5 * ((Mval 3) * (Mval 3)) + 60081451169922001) :=
  ⟨L_bounded_unboundedness, L_exceeds_hunter_depth_1, L_norm_m3⟩

/-! ## §6 Extension protocol (documentation, not Lean content)

    Adding `m = 7` to the chain requires:

      1. External computation of `(L_7, M_7)` satisfying
         `L_7² − 5·M_7² = Φ_{490}(5)`.  `Φ_{490}(5) ≈ 5.17 × 10^117`,
         a 118-digit number; `L_7 ≈ 7.2 × 10^58`.

      2. `decide`-checking the norm identity at this scale (kernel
         feasible since the verification is a fixed-precision `Nat`
         multiplication).

      3. Strict monotonicity check `Lval 3 < Lval 7`.

      4. Rephrasing `L_bounded_unboundedness` cap as `Lval 7` and
         adding the `B ≥ 850554441` case.

    The protocol is open-ended; each extension provides a higher
    bounded-cap unboundedness statement.  The literal `∀ B, ∃ m,
    L_m > B` is the colimit of these bounded statements and would
    require Aurifeuillean infrastructure beyond what is kernel-feasible. -/

end E213.Lib.Math.Cohomology.Fractal.AurifeuilleanLUnbounded
