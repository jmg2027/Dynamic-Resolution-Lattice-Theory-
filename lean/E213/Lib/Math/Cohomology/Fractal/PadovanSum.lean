import E213.Lib.Math.Cohomology.Fractal.PadovanCutoff
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Meta.Nat.PolyNatMTactic

/-!
# Padovan partial-sum identity (∅-axiom)

Reusing the corpus Padovan sequence `PadovanCutoff.Pad` (`Pad 0=Pad 1=Pad 2=1`,
`Pad (n+3)=Pad (n+1)+Pad n`), two genuinely-absent identities (the corpus had the
sequence + cut-off tables but no `sumTo`-based partial sum):

  * **`Pad_cross`** : `Pad (n+5) = Pad (n+4) + Pad n` (the cross-recurrence).
  * ★ **`sumPad_succ_two`** : `(Σ_{k=0}^{n} Pad k) + 2 = Pad (n+5)` — the Padovan
    partial sums hit a later Padovan minus 2.  Induction via the cross-recurrence.

All ∅-axiom.
-/

namespace E213.Lib.Math.Cohomology.Fractal.PadovanSum

open E213.Lib.Math.Cohomology.Fractal.PadovanCutoff (Pad)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)

/-- **Cross-recurrence**: `Pad (n+5) = Pad (n+4) + Pad n`. -/
theorem Pad_cross (n : Nat) : Pad (n + 5) = Pad (n + 4) + Pad n := by
  have h5 : Pad (n + 5) = Pad (n + 3) + Pad (n + 2) := rfl
  have h4 : Pad (n + 4) = Pad (n + 2) + Pad (n + 1) := rfl
  have h3 : Pad (n + 3) = Pad (n + 1) + Pad n := rfl
  rw [h5, h4, h3]
  ring_nat

/-- `sumPad n = Pad 0 + … + Pad n` (inclusive). -/
def sumPad (n : Nat) : Nat := sumTo (n + 1) Pad

/-- ★ **Padovan partial-sum identity** `(Σ_{k=0}^{n} Pad k) + 2 = Pad (n+5)`.
    Offset `+2` (Σ_{≤0}=1, Pad 5=3; Σ_{≤1}=2, Pad 6=4; …).  Induction via the
    cross-recurrence `Pad(n+6) = Pad(n+5) + Pad(n+1)`. -/
theorem sumPad_succ_two (n : Nat) : sumPad n + 2 = Pad (n + 5) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show sumTo (k + 2) Pad + 2 = Pad (k + 6)
    rw [sumTo_succ]
    have ih' : sumTo (k + 1) Pad + 2 = Pad (k + 5) := ih
    have hc : Pad (k + 6) = Pad (k + 5) + Pad (k + 1) := Pad_cross (k + 1)
    rw [hc, ← ih']
    ring_nat

/-- Smoke: `(1+1+1+2+2) + 2 = 9 = Pad 9`. -/
theorem sumPad_smoke : sumPad 4 + 2 = Pad 9 := by decide

end E213.Lib.Math.Cohomology.Fractal.PadovanSum
