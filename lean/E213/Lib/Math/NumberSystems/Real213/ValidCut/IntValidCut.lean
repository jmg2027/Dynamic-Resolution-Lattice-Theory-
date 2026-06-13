import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumAssocInt
import E213.Lib.Math.NumberSystems.Real213.ValidCut.ValidCutFramework
/-!
# IntValidCut — bundled integer cut closing full cutSum_assoc

Realises the full cutSum_assoc closure on the integer-cut-extended
class: cuts that are extensionally equal to some `constCut a 1`.

  `structure IntValidCut where
     cut : Nat → Nat → Bool
     represents : Nat
     is_integer : cutEq cut (constCut represents 1)`

This is **stronger than ValidCut**: not just monotone, but
literally an integer cut up to cutEq.  All integer addition lifts
back to cut-level, so associativity reduces to `Nat.add_assoc`.

  `cutSum_assoc_intValidCut`:
    `cutSum (cutSum vx.cut vy.cut) vz.cut`
    cutEq `cutSum vx.cut (cutSum vy.cut vz.cut)`

via reducing both sides to `constCut ((vx.r + vy.r) + vz.r) 1`.

This closes the precision-doubling artifact at the meaningful
"integer-extended" subset of ValidCut.  Beyond this subset
(non-integer monotone cuts), full assoc requires search-index
reorganization (out of scope).

All declarations PURE.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ValidCut.IntValidCut

open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutEq cutEq_refl cutEq_symm cutEq_trans)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumOne (cutSum_int_int)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumEq
  (cutSum_cutEq_left cutSum_cutEq_right)

/-! ## §1 — IntValidCut structure -/

/-- A **bundled integer cut**: a cut function with a witness that
    it's cutEq to some `constCut · 1`. -/
structure IntValidCut where
  /-- The underlying cut function. -/
  cut : Nat → Nat → Bool
  /-- The integer this cut represents. -/
  represents : Nat
  /-- The witness: cut is cutEq to `constCut represents 1`. -/
  is_integer : cutEq cut (constCut represents 1)

/-! ## §2 — Constructors -/

/-- The canonical integer cut at value `a`. -/
def ofNat (a : Nat) : IntValidCut where
  cut := constCut a 1
  represents := a
  is_integer := cutEq_refl _

/-- Zero. -/
def zero : IntValidCut := ofNat 0

/-- One. -/
def one : IntValidCut := ofNat 1

theorem ofNat_cut (a : Nat) : (ofNat a).cut = constCut a 1 := rfl

theorem ofNat_represents (a : Nat) : (ofNat a).represents = a := rfl

/-! ## §3 — Bundled cutSum -/

/-- Add two IntValidCuts; the result represents the sum. -/
def add (vx vy : IntValidCut) : IntValidCut where
  cut := cutSum vx.cut vy.cut
  represents := vx.represents + vy.represents
  is_integer := by
    intro m k
    -- cutSum vx.cut vy.cut m k = ?
    -- We have cutEq vx.cut (constCut vx.r 1), same for vy.
    -- So cutSum vx.cut vy.cut m k = cutSum (constCut vx.r 1) (constCut vy.r 1) m k
    -- = constCut (vx.r + vy.r) 1 m k  [by cutSum_int_int]
    rw [cutSum_cutEq_left vx.cut (constCut vx.represents 1) vy.cut
          vx.is_integer m k]
    rw [cutSum_cutEq_right (constCut vx.represents 1) vy.cut
          (constCut vy.represents 1) vy.is_integer m k]
    exact cutSum_int_int vx.represents vy.represents m k

theorem add_represents (vx vy : IntValidCut) :
    (add vx vy).represents = vx.represents + vy.represents := rfl

theorem add_cut (vx vy : IntValidCut) :
    (add vx vy).cut = cutSum vx.cut vy.cut := rfl

/-! ## §4 — Full associativity -/

/-- ★★★★★ **Full cutSum associativity on IntValidCut**.

    For any three bundled integer cuts vx, vy, vz:
    `cutSum (cutSum vx.cut vy.cut) vz.cut`
    cutEq `cutSum vx.cut (cutSum vy.cut vz.cut)`.

    Both sides reduce to `constCut ((vx.r + vy.r) + vz.r) 1`
    via `cutSum_int_int` + the `is_integer` witnesses.
    Associativity is then `Nat.add_assoc`. -/
theorem cutSum_assoc_intValidCut (vx vy vz : IntValidCut) :
    cutEq (cutSum (cutSum vx.cut vy.cut) vz.cut)
          (cutSum vx.cut (cutSum vy.cut vz.cut)) := by
  intro m k
  -- LHS: reduce via add structure
  -- cutSum (cutSum vx.cut vy.cut) vz.cut m k
  --   = cutSum (add vx vy).cut vz.cut m k
  --   = (add (add vx vy) vz).cut m k
  --   = constCut ((vx.r + vy.r) + vz.r) 1 m k
  have lhs_eq : cutSum (cutSum vx.cut vy.cut) vz.cut m k
              = constCut ((vx.represents + vy.represents)
                          + vz.represents) 1 m k := by
    show (add (add vx vy) vz).cut m k
       = constCut ((vx.represents + vy.represents) + vz.represents) 1 m k
    exact (add (add vx vy) vz).is_integer m k
  -- RHS: similarly
  have rhs_eq : cutSum vx.cut (cutSum vy.cut vz.cut) m k
              = constCut (vx.represents
                          + (vy.represents + vz.represents)) 1 m k := by
    show (add vx (add vy vz)).cut m k
       = constCut (vx.represents + (vy.represents + vz.represents)) 1 m k
    exact (add vx (add vy vz)).is_integer m k
  rw [lhs_eq, rhs_eq]
  -- (a + b) + c = a + (b + c) by Nat.add_assoc
  rw [Nat.add_assoc]

/-! ## §5 — Commutativity bonus -/

/-- ★ **Commutativity** for IntValidCut: same chain, Nat.add_comm. -/
theorem cutSum_comm_intValidCut (vx vy : IntValidCut) :
    cutEq (cutSum vx.cut vy.cut) (cutSum vy.cut vx.cut) := by
  intro m k
  have lhs_eq : cutSum vx.cut vy.cut m k
              = constCut (vx.represents + vy.represents) 1 m k :=
    (add vx vy).is_integer m k
  have rhs_eq : cutSum vy.cut vx.cut m k
              = constCut (vy.represents + vx.represents) 1 m k :=
    (add vy vx).is_integer m k
  rw [lhs_eq, rhs_eq]
  rw [Nat.add_comm]

/-! ## §6 — Smoke -/

theorem assoc_smoke_1_2_3 :
    cutEq (cutSum (cutSum (ofNat 1).cut (ofNat 2).cut) (ofNat 3).cut)
          (cutSum (ofNat 1).cut (cutSum (ofNat 2).cut (ofNat 3).cut)) :=
  cutSum_assoc_intValidCut (ofNat 1) (ofNat 2) (ofNat 3)

theorem comm_smoke_5_7 :
    cutEq (cutSum (ofNat 5).cut (ofNat 7).cut)
          (cutSum (ofNat 7).cut (ofNat 5).cut) :=
  cutSum_comm_intValidCut (ofNat 5) (ofNat 7)

/-! ## §7 — Capstone -/

/-- ★★★★★ **Full cutSum_assoc closure via bundled IntValidCut**.

    Bundles: (a) `IntValidCut` structure with cut + represents +
    integer witness, (b) `ofNat / zero / one / add` constructors,
    (c) full associativity on the integer-extended class,
    (d) commutativity bonus, (e) smoke at (1,2,3).

    Reading: the precision-doubling artifact blocking general
    `cutSum_assoc` is **eliminated for the integer-extended
    class**.  Bundle structure carries the cutEq-to-integer
    witness; cutSum on IntValidCut closes the integer class
    (add_represents = +); both sides of associativity reduce to
    `constCut (a + b + c) 1` via the witnesses + `cutSum_int_int`,
    and `Nat.add_assoc` finishes.

    This is the cleanest realisation of Gemini's blocker-2
    bundled-subtype prescription: pull the precision-monotonicity
    invariant into a stronger "represents an integer" invariant
    that closes the algebra. -/
theorem intvalidcut_full_assoc_capstone (vx vy vz : IntValidCut) :
    -- (a) Add preserves integer class
    (add vx vy).represents = vx.represents + vy.represents
    -- (b) Full associativity
    ∧ cutEq (cutSum (cutSum vx.cut vy.cut) vz.cut)
            (cutSum vx.cut (cutSum vy.cut vz.cut))
    -- (c) Commutativity
    ∧ cutEq (cutSum vx.cut vy.cut) (cutSum vy.cut vx.cut)
    -- (d) Zero / one canonical
    ∧ zero.represents = 0
    ∧ one.represents = 1 := by
  refine ⟨rfl, ?_, ?_, rfl, rfl⟩
  · exact cutSum_assoc_intValidCut vx vy vz
  · exact cutSum_comm_intValidCut vx vy

end E213.Lib.Math.NumberSystems.Real213.ValidCut.IntValidCut
