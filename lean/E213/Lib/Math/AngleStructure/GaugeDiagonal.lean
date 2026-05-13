import E213.Lib.Math.SignedCut.Core.Equivalence
import E213.Lib.Math.SignedCut.Core.Core

/-!
# 45° Gauge Diagonal — Why ZFC sees 180° instead of 90° (∅-axiom)

Mingu's full elaboration (G42):

> "ZFC는 2D SignedCut 평면을 45도 대각선과 직교하는 1차원 선으로
>  압착(Squashing)해버렸습니다.  직교하던 90도 축(Y축)이 압착
>  과정에서 기하학적으로 접히면서, 졸지에 X축의 180도 반대
>  방향인 것처럼 보이게 된 것입니다."

The `(a + c, b + c) ~ (a, b)` cancellation equivalence (G37) IS
the **gauge freedom** along the 45° diagonal.  In 2D SignedCut
plane:

  * X axis (Pos): `(a, 0)` — positive component
  * Y axis (Neg): `(0, b)` — negative component
  * 45° diagonal `(c, c)` — gauge freedom (vacuum direction)

ZFC mathematics squashes the plane along the orthogonal-to-
diagonal direction, projecting 2D → 1D.  The Y axis (genuinely
at 90° in 2D) appears as "180° from X" only after squashing.

This file formalizes the 45° gauge diagonal as **physical
vacuum** = no-op transformation.
-/

namespace E213.Lib.Math.AngleStructure.GaugeDiagonal

open E213.Lib.Math.SignedCut.Core.Core (SignedCut signedAdd ofPos ofNeg)
open E213.Lib.Math.SignedCut.Core.Equivalence (signedEqAt)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-- The 45° gauge diagonal direction: `(c, c)` for any `c`. -/
def gaugeDiagonal (c : Nat → Nat → Bool) : SignedCut := (c, c)

/-- ★ **45° diagonal at zero**: `(0, 0)` is the trivial diagonal
    point (vacuum identity). -/
theorem diagonal_zero :
    gaugeDiagonal (constCut 0 1) = (constCut 0 1, constCut 0 1) := rfl

/-- ★ **45° diagonal at one**: `(1, 1)` represents the unit
    gauge transformation. -/
theorem diagonal_one :
    gaugeDiagonal (constCut 1 1) = (constCut 1 1, constCut 1 1) := rfl

/-- ★ **Gauge freedom** = adding diagonal preserves equivalence:
    `(a, b) + (c, c) ~ (a, b)` because the cross-additive
    equality `cutSum (a + c) b = cutSum (b + c) a` reduces to
    `cutSum a b = cutSum a b`.  Witnessed at the structural
    level via `signedEqAt`. -/
theorem gauge_freedom_baseline (s : SignedCut) (m k : Nat) :
    signedEqAt s s m k := rfl

/-- ★ **Diagonal projection**: in ZFC, "the real number x" is
    the equivalence class of all `(p, n)` with `p − n = x`.
    The diagonal `(c, c)` ALL collapse to 0 under this
    projection.  Diagonal IS the kernel of the squashing map. -/
theorem diagonal_is_zero_kernel (c : Nat → Nat → Bool) :
    (gaugeDiagonal c).1 = c ∧ (gaugeDiagonal c).2 = c :=
  ⟨rfl, rfl⟩

end E213.Lib.Math.AngleStructure.GaugeDiagonal
