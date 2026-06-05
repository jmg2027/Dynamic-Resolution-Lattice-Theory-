/-!
# Metallic Threshold — the one-knob family M_a and where the constants live (∅-axiom)

`Mobius213OneAsGlue` fixes the Möbius `P = [[2,1],[1,1]]` (the `a = 2` point).
This file generalizes by one knob — the top-left entry `a`, which §3.5 reads as
"two somethings" (the count-Lens reading of the distinguishing) — keeping the
off-diagonal glue fixed at `1`:

        M_a = [[a, 1], [1, 1]],   det = a·1 − 1·1 = a − 1,   trace = a + 1,
        disc = trace² − 4·det = (a+1)² − 4(a−1) = a² − 2a + 5.

This is the C1 test of the slash-reading atlas
(`research-notes/frontiers/G205_slash_reading_atlas.md`) as a theorem:

  · `a = 1` → `det = 0`: the rank-1 collapse (`M_1` sends everything to one
    value) — the averaging / midpoint degenerate end, structurally a point.
  · `a = 2` → `det = 1`, `trace = 3 = N_S`, `disc = 5 = N_S + N_T`: the 213
    constants, exactly — simultaneously the forced count-Lens minimum ("two +
    binary", §3.2) and the unimodular glue (`det = 1`, §3.5).  Not tuned.
  · `a = 3` → `det = 2`, `disc = 8`: the silver point (fixed point `1 + √2`);
    integer `a ≥ 2` give the metallic-ratio tower, of which golden (`a = 2`) is
    the minimal member.

So the constants are blind ⟺ `det = 0` (`a = 1`), and the specific `3,5` sit at
the forced `a = 2`.  `detMa` is defined as its closed value `a − 1` (the
determinant of `M_a`); `det_matrix_form_at_two` anchors that value to the matrix
form `a·1 − 1·1` concretely.  All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Algebra.Mobius213.Px.MetallicThreshold

/-- Determinant of `M_a = [[a,1],[1,1]]`: `a·1 − 1·1 = a − 1` (closed value). -/
def detMa (a : Int) : Int := a - 1

/-- Trace of `M_a`: `a + 1`. -/
def traceMa (a : Int) : Int := a + 1

/-- Discriminant of `M_a`: `trace² − 4·det`. -/
def discMa (a : Int) : Int := traceMa a * traceMa a - 4 * detMa a

/-- ★ **The knob's determinant**: `det M_a = a − 1` for every `a` (definitional).
    `det = 1 ⟺ a = 2`, `det = 0 ⟺ a = 1` — the glue as a function of the count. -/
theorem detMa_eq (a : Int) : detMa a = a - 1 := rfl

/-- ★ **Matrix-form anchor**: at the golden point the closed value agrees with
    the literal determinant `a·1 − 1·1`. -/
theorem det_matrix_form_at_two : (2 : Int) * 1 - 1 * 1 = detMa 2 := by decide

/-- ★ **Collapse end** (`a = 1`): `det = 0`.  `M_1` is rank-1 — the
    averaging / midpoint degenerate reading, blind to the constants. -/
theorem detMa_collapse : detMa 1 = 0 := by decide

/-- ★ **Golden point** (`a = 2`): `det = 1` (the unimodular glue). -/
theorem detMa_golden : detMa 2 = 1 := by decide

/-- ★ **Silver point** (`a = 3`): `det = 2` (the next metallic rung). -/
theorem detMa_silver : detMa 3 = 2 := by decide

/-- ★★ **The 213 constants sit exactly at `a = 2`**: `trace = 3 = N_S`,
    `det = 1` (glue), `disc = 5 = N_S + N_T = d`.  By §3.2 the count `a = 2` is
    forced; this point is the golden one — the constants are not tuned. -/
theorem golden_signature :
    traceMa 2 = 3 ∧ detMa 2 = 1 ∧ discMa 2 = 5 := by decide

/-- ★ **Metallic tower** of discriminants: golden `5` (a=2), silver `8` (a=3),
    bronze `13` (a=4) — the `a²−2a+5` family, golden the minimal member. -/
theorem metallic_discriminants :
    discMa 2 = 5 ∧ discMa 3 = 8 ∧ discMa 4 = 13 := by decide

/-- ★★★ **Threshold master.**  The one knob `a` carries det = a−1; the collapse
    (det 0) sits at the one-something end `a = 1`, the golden 213 constants
    (det 1, trace 3, disc 5) at the forced two-somethings point `a = 2`, and the
    metallic tower beyond. -/
theorem metallic_threshold_master :
    (∀ a : Int, detMa a = a - 1)
    ∧ detMa 1 = 0
    ∧ (traceMa 2 = 3 ∧ detMa 2 = 1 ∧ discMa 2 = 5)
    ∧ detMa 3 = 2 :=
  ⟨detMa_eq, detMa_collapse, golden_signature, detMa_silver⟩

end E213.Lib.Math.Algebra.Mobius213.Px.MetallicThreshold
