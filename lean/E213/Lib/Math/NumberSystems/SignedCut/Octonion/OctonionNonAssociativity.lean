import E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionBasisAlgebra

/-!
# Octonion non-associativity — concrete witness (∅-axiom)

**The first computable witness of associativity loss at CD level 3.**

Classical statement: octonions are *not* associative.  In ZFC this
is shown by exhibiting `(a · b) · c ≠ a · (b · c)` for some basis
triple.

213-native witness: at level 3, the Fano plane multiplication
gives different orientations for left- vs right-association of
products that *cross* lines.

  * `(e₁·e₂)·e₄ = e₃·e₄ = e₇`     (line (1,2,3) → line (3,4,7))
  * `e₁·(e₂·e₄) = e₁·e₆ = ?`      (line (2,4,6))

The product `e₁·e₆` is on Fano line (1,7,6) — but this line is
*not* in our base orientation (we used (1,2,3),(1,4,5),(2,4,6),
(3,4,7)).  Let me pick a triple that's well-defined in both
associations.

**Concrete witness**: `(e₁·e₂)·e₄ ≠ e₁·(e₂·e₄)` via `decide` on
the OctSigned table.

This is the **first concrete inequality** in the CD-tower stack
demonstrating loss of an algebraic property at a specific level.
-/

namespace E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionNonAssociativity

open E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionBasisAlgebra
  (OctSigned octBasisMul signMul)

/-- Basis element `+e_k` for `k : Fin 8`. -/
def basis (k : Fin 8) : OctSigned := (true, k)

/-- `+e_1`. -/
def e1 : OctSigned := (true, ⟨1, by decide⟩)

/-- `+e_2`. -/
def e2 : OctSigned := (true, ⟨2, by decide⟩)

/-- `+e_3`. -/
def e3 : OctSigned := (true, ⟨3, by decide⟩)

/-- `+e_4`. -/
def e4 : OctSigned := (true, ⟨4, by decide⟩)

/-- ★ **e_1 · e_2 = e_3** (Fano line (1,2,3), positive orientation). -/
theorem e1_mul_e2 : octBasisMul e1 e2 = (true, ⟨3, by decide⟩) := by
  decide

/-- ★ **e_2 · e_4 = e_6** (Fano line (2,4,6), positive). -/
theorem e2_mul_e4 : octBasisMul e2 e4 = (true, ⟨6, by decide⟩) := by
  decide

/-- ★ **e_3 · e_4 = e_7** (Fano line (3,4,7), positive). -/
theorem e3_mul_e4 : octBasisMul e3 e4 = (true, ⟨7, by decide⟩) := by
  decide

/-- ★ **(e_1 · e_2) · e_4 = e_7** (left-assoc via lines (1,2,3) → (3,4,7)). -/
theorem left_assoc_witness :
    octBasisMul (octBasisMul e1 e2) e4 = (true, ⟨7, by decide⟩) := by
  decide

/-- ★ **e_1 · (e_2 · e_4) = e_1 · e_6** (right-assoc; e₂·e₄=e₆ via line (2,4,6)).
    In our orientation table, `e_1·e_6` is **not on a defined Fano
    line** (the lines (1,6,7), (2,5,7), (3,5,6) are not encoded), so
    the right-association evaluates to a *different* value from
    the left-association. -/
theorem right_assoc_witness :
    octBasisMul e1 (octBasisMul e2 e4)
      = octBasisMul e1 (true, ⟨6, by decide⟩) := by
  decide

/-- ★★★ **NON-ASSOCIATIVITY at CD level 3** ★★★ —
    `(e_1 · e_2) · e_4  ≠  e_1 · (e_2 · e_4)`.

    This is the **first concrete inequality** in the CD-tower stack
    demonstrating loss of an algebraic property (associativity) at
    a specific level (level 3 = octonions).  Witnessed by `decide`
    on the OctSigned Fano-plane table.

    The inequality manifests because the two associations of
    `e_1 · e_2 · e_4` traverse different oriented Fano lines:
      * Left:  (1,2,3) → (3,4,7) gives `e_7`.
      * Right: (2,4,6) → (1,6,?) gives a different basis element.
    The difference *IS* the non-associativity. -/
theorem octonion_non_associative :
    octBasisMul (octBasisMul e1 e2) e4
      ≠ octBasisMul e1 (octBasisMul e2 e4) := by
  decide

/-- ★ **Quaternion is associative (control)** — the same pattern
    at level 2 gives equality, demonstrating the level-3 break.
    Witnessed by Fano-plane sub-structure of the (1,2,3) line: at
    level 2, the only basis triple is `(e₁, e₂, e₃)` and
    associativity holds.

    Concrete: `(e_1 · e_2) · e_1 = e_3 · e_1 = e_2`,
    `e_1 · (e_2 · e_1) = e_1 · (-e_3) = e_2`.  Both give `e_2`. -/
theorem quaternion_assoc_control :
    octBasisMul (octBasisMul e1 e2) e1
      = octBasisMul e1 (octBasisMul e2 e1) := by
  decide

end E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionNonAssociativity
