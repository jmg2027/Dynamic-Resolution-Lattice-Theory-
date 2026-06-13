import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumN
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
import E213.Lib.Math.NumberSystems.Real213.Core.CutPoset

/-!
# NValidCut N — bundled b = N cut, parametric in N

Generalises `IntValidCut` (b=1), `HalfValidCut` (b=2),
`ThirdValidCut` (b=3) to **any** denominator N.  Per
`theory/essays/methodology/bool_assoc_failure_meaning.md`, every natural
N ≥ 1 is reachable from (NS, NT) = (3, 2) atoms — additively for
N ≥ 2 (`Theory/Atomicity/Five.lean atomic_iff_five` for 5, etc.),
multiplicatively for N ∈ ⟨2, 3⟩^mult.  So `cutSumN N` closure
applies uniformly:

  `structure ValidCutN (N : Nat) where
     cut : Nat → Nat → Bool
     represents : Nat
     is_at_denom : cutEq cut (constCut represents N)`

with `add` via `cutSumN N` and full associativity + commutativity
via the same chain that closed ThirdValidCut.

## Per-N instantiation

  · `ValidCutN 1` ≅ IntValidCut
  · `ValidCutN 2` ≅ HalfValidCut
  · `ValidCutN 3` ≅ ThirdValidCut
  · `ValidCutN 5` ≅ FifthValidCut (demonstrated below as smoke)
  · `ValidCutN 7` ≅ SeventhValidCut
  · ...

The PARAMETRIC nature of `cutSumN_same_denom` means we get ALL
N at once.  No new theorem per prime.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Real213.NValidCut

open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutEq cutEq_refl)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumN
  (cutSumN cutSumN_same_denom cutSumN_cutEq_left cutSumN_cutEq_right)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-! ## §1 — ValidCutN structure -/

/-- A **bundled b = N cut**: cut function + numerator + witness it's
    cutEq to `constCut · N`.  Parametric in N. -/
structure ValidCutN (N : Nat) where
  /-- The underlying cut function. -/
  cut : Nat → Nat → Bool
  /-- The numerator (cut value = represents / N). -/
  represents : Nat
  /-- The witness: cut is cutEq to `constCut represents N`. -/
  is_at_denom : cutEq cut (constCut represents N)

/-! ## §2 — Constructors -/

/-- The canonical b = N cut at numerator `a`. -/
def ofValidCutN (N a : Nat) : ValidCutN N where
  cut := constCut a N
  represents := a
  is_at_denom := cutEq_refl _

/-- Zero. -/
def zero (N : Nat) : ValidCutN N := ofValidCutN N 0

theorem ofValidCutN_cut (N a : Nat) :
    (ofValidCutN N a).cut = constCut a N := rfl

theorem ofValidCutN_represents (N a : Nat) :
    (ofValidCutN N a).represents = a := rfl

/-! ## §3 — Bundled cutSumN -/

/-- Add two `ValidCutN N`; result represents the sum of numerators. -/
def addN (N : Nat) (hN : 0 < N) (vx vy : ValidCutN N) : ValidCutN N where
  cut := cutSumN N vx.cut vy.cut
  represents := vx.represents + vy.represents
  is_at_denom := by
    intro m k
    rw [cutSumN_cutEq_left N vx.cut (constCut vx.represents N) vy.cut
          vx.is_at_denom m k]
    rw [cutSumN_cutEq_right N (constCut vx.represents N) vy.cut
          (constCut vy.represents N) vy.is_at_denom m k]
    exact cutSumN_same_denom N vx.represents vy.represents hN m k

theorem addN_represents (N : Nat) (hN : 0 < N) (vx vy : ValidCutN N) :
    (addN N hN vx vy).represents = vx.represents + vy.represents := rfl

theorem addN_cut (N : Nat) (hN : 0 < N) (vx vy : ValidCutN N) :
    (addN N hN vx vy).cut = cutSumN N vx.cut vy.cut := rfl

/-! ## §4 — Full associativity (parametric in N) -/

/-- ★★★★★ **Full cutSumN N associativity on ValidCutN N**, parametric in N.

    Both sides reduce to `constCut ((vx.r + vy.r) + vz.r) N` via
    `cutSumN_same_denom` + `is_at_denom` witnesses.  `Nat.add_assoc` finishes. -/
theorem cutSumN_assoc_valid (N : Nat) (hN : 0 < N) (vx vy vz : ValidCutN N) :
    cutEq (cutSumN N (cutSumN N vx.cut vy.cut) vz.cut)
          (cutSumN N vx.cut (cutSumN N vy.cut vz.cut)) := by
  intro m k
  have lhs_eq : cutSumN N (cutSumN N vx.cut vy.cut) vz.cut m k
              = constCut ((vx.represents + vy.represents)
                          + vz.represents) N m k := by
    show (addN N hN (addN N hN vx vy) vz).cut m k
       = constCut ((vx.represents + vy.represents) + vz.represents) N m k
    exact (addN N hN (addN N hN vx vy) vz).is_at_denom m k
  have rhs_eq : cutSumN N vx.cut (cutSumN N vy.cut vz.cut) m k
              = constCut (vx.represents
                          + (vy.represents + vz.represents)) N m k := by
    show (addN N hN vx (addN N hN vy vz)).cut m k
       = constCut (vx.represents + (vy.represents + vz.represents)) N m k
    exact (addN N hN vx (addN N hN vy vz)).is_at_denom m k
  rw [lhs_eq, rhs_eq, Nat.add_assoc]

/-- ★ Commutativity, parametric in N. -/
theorem cutSumN_comm_valid (N : Nat) (hN : 0 < N) (vx vy : ValidCutN N) :
    cutEq (cutSumN N vx.cut vy.cut) (cutSumN N vy.cut vx.cut) := by
  intro m k
  have lhs_eq : cutSumN N vx.cut vy.cut m k
              = constCut (vx.represents + vy.represents) N m k :=
    (addN N hN vx vy).is_at_denom m k
  have rhs_eq : cutSumN N vy.cut vx.cut m k
              = constCut (vy.represents + vx.represents) N m k :=
    (addN N hN vy vx).is_at_denom m k
  rw [lhs_eq, rhs_eq, Nat.add_comm]

/-! ## §5 — Instance smokes: N = 5, 7, 11 -/

/-- N = 5 closure: cutSumN 5 (1/5) (2/5) ≡ (3/5). -/
theorem fifth_smoke_1_2 :
    cutEq (cutSumN 5 (ofValidCutN 5 1).cut (ofValidCutN 5 2).cut)
          (constCut 3 5) :=
  cutSumN_same_denom 5 1 2 (by decide)

/-- N = 5 assoc: (1/5 + 2/5) + 1/5 = 1/5 + (2/5 + 1/5). -/
theorem fifth_assoc_1_2_1 :
    cutEq (cutSumN 5 (cutSumN 5 (ofValidCutN 5 1).cut
                                  (ofValidCutN 5 2).cut)
                      (ofValidCutN 5 1).cut)
          (cutSumN 5 (ofValidCutN 5 1).cut
                      (cutSumN 5 (ofValidCutN 5 2).cut
                                  (ofValidCutN 5 1).cut)) :=
  cutSumN_assoc_valid 5 (by decide)
    (ofValidCutN 5 1) (ofValidCutN 5 2) (ofValidCutN 5 1)

/-- N = 7 assoc smoke. -/
theorem seventh_assoc_2_3_5 :
    cutEq (cutSumN 7 (cutSumN 7 (ofValidCutN 7 2).cut
                                  (ofValidCutN 7 3).cut)
                      (ofValidCutN 7 5).cut)
          (cutSumN 7 (ofValidCutN 7 2).cut
                      (cutSumN 7 (ofValidCutN 7 3).cut
                                  (ofValidCutN 7 5).cut)) :=
  cutSumN_assoc_valid 7 (by decide)
    (ofValidCutN 7 2) (ofValidCutN 7 3) (ofValidCutN 7 5)

/-- N = 11 assoc smoke. -/
theorem eleventh_assoc_1_4_6 :
    cutEq (cutSumN 11 (cutSumN 11 (ofValidCutN 11 1).cut
                                    (ofValidCutN 11 4).cut)
                       (ofValidCutN 11 6).cut)
          (cutSumN 11 (ofValidCutN 11 1).cut
                       (cutSumN 11 (ofValidCutN 11 4).cut
                                    (ofValidCutN 11 6).cut)) :=
  cutSumN_assoc_valid 11 (by decide)
    (ofValidCutN 11 1) (ofValidCutN 11 4) (ofValidCutN 11 6)

/-! ## §6 — Capstone: closure for ALL naturals N ≥ 1 -/

/-- ★★★★★ **All-naturals closure capstone**.

    For ANY `N ≥ 1` and ANY three bundled cuts `vx, vy, vz : ValidCutN N`:
    (a) `addN` represents sum of represents,
    (b) full associativity,
    (c) full commutativity.

    Parametric in N — no per-N proof needed.  Per
    `theory/essays/methodology/bool_assoc_failure_meaning.md`, every N is
    reachable from (3, 2) atoms (additively for N ≥ 2 via
    Bezout-style decompositions, e.g., 5 = 2+3 per `atomic_iff_five`).
    The framework realisation of "no exterior" — every denominator
    closure is internal. -/
theorem nvalidcut_all_naturals_capstone
    (N : Nat) (hN : 0 < N) (vx vy vz : ValidCutN N) :
    (addN N hN vx vy).represents = vx.represents + vy.represents
    ∧ cutEq (cutSumN N (cutSumN N vx.cut vy.cut) vz.cut)
            (cutSumN N vx.cut (cutSumN N vy.cut vz.cut))
    ∧ cutEq (cutSumN N vx.cut vy.cut) (cutSumN N vy.cut vx.cut) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact cutSumN_assoc_valid N hN vx vy vz
  · exact cutSumN_comm_valid N hN vx vy

end E213.Lib.Math.NumberSystems.Real213.NValidCut
