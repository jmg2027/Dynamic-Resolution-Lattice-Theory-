import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumN
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest
import E213.Lib.Math.NumberSystems.Real213.Core.CutPoset

/-!
# ThirdValidCut — bundled b = 3 cut, closing cutSumN 3 associativity

Parallel to `IntValidCut` (b = 1) and `HalfValidCut` (b = 2),
this bundles the b = 3 case using the parametric `cutSumN 3`
(factor-3 search granularity).  Per `theory/essays/bool_assoc_failure_meaning.md`,
b = 3 corresponds to the NS atom of (NS, NT) = (3, 2); the
original `cutSum` (factor-2 hardcode) only read the NT atom and
missed NS, blocking b = 3 closure.

`cutSumN 3` reads both atoms appropriately, so:

  `structure ThirdValidCut where
     cut : Nat → Nat → Bool
     represents : Nat
     is_third : cutEq cut (constCut represents 3)`

closes full associativity via `cutSumN_same_denom`.

This closes the b = 3 frontier identified in
`CutSumAssocB3.lean` — not as new theorem inside the old `cutSum`,
but as the **right operation** for the b = 3 atom.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ThirdValidCut

open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutEq cutEq_refl)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumN
  (cutSumN cutSumN_same_denom cutSumN_cutEq_left cutSumN_cutEq_right)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-! ## §1 — ThirdValidCut structure -/

/-- A **bundled b = 3 cut**: cut function + numerator + witness that
    it's cutEq to `constCut · 3`. -/
structure ThirdValidCut where
  /-- The underlying cut function. -/
  cut : Nat → Nat → Bool
  /-- The numerator (cut value = represents / 3). -/
  represents : Nat
  /-- The witness: cut is cutEq to `constCut represents 3`. -/
  is_third : cutEq cut (constCut represents 3)

/-! ## §2 — Constructors -/

/-- The canonical b = 3 cut at numerator `a` (value a/3). -/
def ofThird (a : Nat) : ThirdValidCut where
  cut := constCut a 3
  represents := a
  is_third := cutEq_refl _

/-- Zero. -/
def zero : ThirdValidCut := ofThird 0

/-- The unit fraction 1/3. -/
def oneThird : ThirdValidCut := ofThird 1

/-- Two thirds. -/
def twoThirds : ThirdValidCut := ofThird 2

/-- Unity = 3/3. -/
def one : ThirdValidCut := ofThird 3

theorem ofThird_cut (a : Nat) : (ofThird a).cut = constCut a 3 := rfl

theorem ofThird_represents (a : Nat) : (ofThird a).represents = a := rfl

/-! ## §3 — Bundled cutSumN -/

/-- Add two ThirdValidCuts; the result represents the sum of numerators. -/
def add (vx vy : ThirdValidCut) : ThirdValidCut where
  cut := cutSumN 3 vx.cut vy.cut
  represents := vx.represents + vy.represents
  is_third := by
    intro m k
    rw [cutSumN_cutEq_left 3 vx.cut (constCut vx.represents 3) vy.cut
          vx.is_third m k]
    rw [cutSumN_cutEq_right 3 (constCut vx.represents 3) vy.cut
          (constCut vy.represents 3) vy.is_third m k]
    exact cutSumN_same_denom 3 vx.represents vy.represents
            (by decide : (0:Nat) < 3) m k

theorem add_represents (vx vy : ThirdValidCut) :
    (add vx vy).represents = vx.represents + vy.represents := rfl

theorem add_cut (vx vy : ThirdValidCut) :
    (add vx vy).cut = cutSumN 3 vx.cut vy.cut := rfl

/-! ## §4 — Full associativity -/

/-- ★★★★★ **Full cutSumN 3 associativity on ThirdValidCut**.

    For any three bundled thirds cuts vx, vy, vz:
    `cutSumN 3 (cutSumN 3 vx.cut vy.cut) vz.cut`
    cutEq `cutSumN 3 vx.cut (cutSumN 3 vy.cut vz.cut)`.

    Both sides reduce to `constCut ((vx.r + vy.r) + vz.r) 3`
    via `cutSumN_same_denom` + the `is_third` witnesses.
    Associativity is then `Nat.add_assoc`. -/
theorem cutSumN_assoc_thirdValidCut (vx vy vz : ThirdValidCut) :
    cutEq (cutSumN 3 (cutSumN 3 vx.cut vy.cut) vz.cut)
          (cutSumN 3 vx.cut (cutSumN 3 vy.cut vz.cut)) := by
  intro m k
  have lhs_eq : cutSumN 3 (cutSumN 3 vx.cut vy.cut) vz.cut m k
              = constCut ((vx.represents + vy.represents)
                          + vz.represents) 3 m k := by
    show (add (add vx vy) vz).cut m k
       = constCut ((vx.represents + vy.represents) + vz.represents) 3 m k
    exact (add (add vx vy) vz).is_third m k
  have rhs_eq : cutSumN 3 vx.cut (cutSumN 3 vy.cut vz.cut) m k
              = constCut (vx.represents
                          + (vy.represents + vz.represents)) 3 m k := by
    show (add vx (add vy vz)).cut m k
       = constCut (vx.represents + (vy.represents + vz.represents)) 3 m k
    exact (add vx (add vy vz)).is_third m k
  rw [lhs_eq, rhs_eq, Nat.add_assoc]

/-! ## §5 — Commutativity bonus -/

/-- ★ **Commutativity** for ThirdValidCut. -/
theorem cutSumN_comm_thirdValidCut (vx vy : ThirdValidCut) :
    cutEq (cutSumN 3 vx.cut vy.cut) (cutSumN 3 vy.cut vx.cut) := by
  intro m k
  have lhs_eq : cutSumN 3 vx.cut vy.cut m k
              = constCut (vx.represents + vy.represents) 3 m k :=
    (add vx vy).is_third m k
  have rhs_eq : cutSumN 3 vy.cut vx.cut m k
              = constCut (vy.represents + vx.represents) 3 m k :=
    (add vy vx).is_third m k
  rw [lhs_eq, rhs_eq, Nat.add_comm]

/-! ## §6 — Smoke -/

theorem assoc_smoke_thirds_1_2_1 :
    cutEq (cutSumN 3 (cutSumN 3 oneThird.cut twoThirds.cut) oneThird.cut)
          (cutSumN 3 oneThird.cut (cutSumN 3 twoThirds.cut oneThird.cut)) :=
  cutSumN_assoc_thirdValidCut oneThird twoThirds oneThird

theorem comm_smoke_thirds_1_2 :
    cutEq (cutSumN 3 oneThird.cut twoThirds.cut)
          (cutSumN 3 twoThirds.cut oneThird.cut) :=
  cutSumN_comm_thirdValidCut oneThird twoThirds

/-- ★ Direct counter-witness: the `CutSumAssocB3.lean` failure case
    (a=2, c=1, b=3, m=1, k=1) where old `cutSum (constCut 2 3) (constCut 1 3) 1 1 = false`
    becomes `cutSumN 3 (constCut 2 3) (constCut 1 3) 1 1 = true`.

    Old failure: search range `[0, 2]` cannot hold `i ≥ 4/3` AND `i ≤ 4/3`.
    New success: search range `[0, 3]` accepts `i = 2`. -/
theorem cutSumN_3_2_1_at_1_1 :
    cutSumN 3 (constCut 2 3) (constCut 1 3) 1 1 = true := by decide

/-! ## §7 — Capstone -/

/-- ★★★★★ **Full cutSumN 3 closure via bundled ThirdValidCut**.

    Bundles: (a) `ThirdValidCut` structure with cut + represents
    + is_third witness, (b) `ofThird / zero / one / add`
    constructors, (c) full associativity on b = 3 class,
    (d) commutativity, (e) smoke at (1/3, 2/3, 1/3).

    Reading: per `theory/essays/bool_assoc_failure_meaning.md`,
    the original `cutSum`'s factor-2 hardcode read only NT and
    missed NS = 3; using the right operation `cutSumN 3` (NS-aware
    factor-3 search) closes the b = 3 algebra exactly as
    IntValidCut closed b = 1 and HalfValidCut closed b = 2. -/
theorem thirdvalidcut_full_assoc_capstone (vx vy vz : ThirdValidCut) :
    (add vx vy).represents = vx.represents + vy.represents
    ∧ cutEq (cutSumN 3 (cutSumN 3 vx.cut vy.cut) vz.cut)
            (cutSumN 3 vx.cut (cutSumN 3 vy.cut vz.cut))
    ∧ cutEq (cutSumN 3 vx.cut vy.cut) (cutSumN 3 vy.cut vx.cut)
    ∧ zero.represents = 0
    ∧ one.represents = 3 := by
  refine ⟨rfl, ?_, ?_, rfl, rfl⟩
  · exact cutSumN_assoc_thirdValidCut vx vy vz
  · exact cutSumN_comm_thirdValidCut vx vy

end E213.Lib.Math.NumberSystems.Real213.ThirdValidCut
