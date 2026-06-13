import E213.Lib.Math.NumberSystems.Real213.ValidCut.NValidCut

/-!
# FifthValidCut — bundled b = 5 cut, explicit instance of ValidCutN

Direct demonstration that **b = 5 closes inside the framework**.
5 is not a "new atom outside (3, 2)" — `Theory/Atomicity/Five.lean`
`atomic_iff_five` proves 5 = 2·1 + 3·1 is the unique alive
atomic decomposition from (NS, NT) = (3, 2).

This file specialises `ValidCutN 5` with named constructors and
shows the same closure pattern that worked for b = 1, 2, 3 applies
verbatim to b = 5.  No new theorem — just instantiation.

The same applies to any prime: b = 7, 11, 13, ... — each gets its
own `ValidCutN p` self-algebra automatically.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ValidCut.FifthValidCut

open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutEq)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumN (cutSumN)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.ValidCut.NValidCut
  (ValidCutN ofValidCutN addN cutSumN_assoc_valid cutSumN_comm_valid
   nvalidcut_all_naturals_capstone)

/-- Type alias: FifthValidCut = ValidCutN 5. -/
abbrev FifthValidCut : Type := ValidCutN 5

/-! ## §1 — Named constructors -/

/-- 1/5 as a FifthValidCut. -/
def oneFifth : FifthValidCut := ofValidCutN 5 1

/-- 2/5. -/
def twoFifths : FifthValidCut := ofValidCutN 5 2

/-- 3/5. -/
def threeFifths : FifthValidCut := ofValidCutN 5 3

/-- 4/5. -/
def fourFifths : FifthValidCut := ofValidCutN 5 4

/-- 5/5 = 1. -/
def one : FifthValidCut := ofValidCutN 5 5

/-! ## §2 — Add via ValidCutN.addN -/

/-- Add two FifthValidCuts. -/
def add (vx vy : FifthValidCut) : FifthValidCut :=
  addN 5 (by decide) vx vy

/-! ## §3 — Algebra (instances of parametric capstones) -/

/-- ★ Full associativity for FifthValidCut. -/
theorem cutSumN_assoc_fifthValidCut (vx vy vz : FifthValidCut) :
    cutEq (cutSumN 5 (cutSumN 5 vx.cut vy.cut) vz.cut)
          (cutSumN 5 vx.cut (cutSumN 5 vy.cut vz.cut)) :=
  cutSumN_assoc_valid 5 (by decide) vx vy vz

/-- ★ Commutativity for FifthValidCut. -/
theorem cutSumN_comm_fifthValidCut (vx vy : FifthValidCut) :
    cutEq (cutSumN 5 vx.cut vy.cut) (cutSumN 5 vy.cut vx.cut) :=
  cutSumN_comm_valid 5 (by decide) vx vy

/-! ## §4 — Concrete sanity -/

/-- 1/5 + 2/5 = 3/5. -/
theorem one_plus_two_eq_three :
    cutEq (cutSumN 5 oneFifth.cut twoFifths.cut)
          (constCut 3 5) :=
  (add oneFifth twoFifths).is_at_denom

/-- 2/5 + 3/5 = 5/5 (= 1). -/
theorem two_plus_three_eq_five :
    cutEq (cutSumN 5 twoFifths.cut threeFifths.cut)
          (constCut 5 5) :=
  (add twoFifths threeFifths).is_at_denom

/-- Associativity smoke at (1/5, 2/5, 4/5). -/
theorem assoc_smoke_1_2_4 :
    cutEq (cutSumN 5 (cutSumN 5 oneFifth.cut twoFifths.cut) fourFifths.cut)
          (cutSumN 5 oneFifth.cut
                    (cutSumN 5 twoFifths.cut fourFifths.cut)) :=
  cutSumN_assoc_fifthValidCut oneFifth twoFifths fourFifths

/-! ## §5 — Capstone instance -/

/-- ★★★★★ **5 is closed inside framework** — full instance of
    parametric capstone at N = 5.

    Demonstrates: 5 is not framework-external.  Per
    `Theory/Atomicity/Five.lean atomic_iff_five`, 5 is derived
    from (3, 2) as 2·1 + 3·1 (alive atomic).  Per
    `nvalidcut_all_naturals_capstone`, ValidCutN closes for every
    N ≥ 1 — including N = 5. -/
theorem fifthValidCut_closure_capstone (vx vy vz : FifthValidCut) :
    (add vx vy).represents = vx.represents + vy.represents
    ∧ cutEq (cutSumN 5 (cutSumN 5 vx.cut vy.cut) vz.cut)
            (cutSumN 5 vx.cut (cutSumN 5 vy.cut vz.cut))
    ∧ cutEq (cutSumN 5 vx.cut vy.cut) (cutSumN 5 vy.cut vx.cut) :=
  nvalidcut_all_naturals_capstone 5 (by decide) vx vy vz

end E213.Lib.Math.NumberSystems.Real213.ValidCut.FifthValidCut
