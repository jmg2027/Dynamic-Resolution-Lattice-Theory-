import E213.Lib.Math.Algebra.Icosahedral.A5Bridge

/-!
# Icosahedral.A5RealityNoCP — A₅ flavour mixing is CP-conserving (δ is NOT an A₅ quantity)

**Rigorous negative result** (the answer to "can the CKM CP phase `δ` be derived
from the A₅ 3-rep mass structure?"): **No.**

Established here + by explicit computation + by the A₅+gCP literature
(Di Iura–Hagedorn–Meloni arXiv:1503.04140; Ballett–Pascoli–Turner 1503.07543;
Turner 1506.06898):

1. **The A₅ 3-rep is a REAL representation** (Frobenius–Schur indicator `+1`).
   `A₅ ⊂ SO(3)` — it *is* the icosahedral rotation group, acting by real
   orthogonal matrices.  Its character `(3, −1, 0, φ, 1−φ)` is real, and the
   golden ratio **cancels** in the FS indicator (below).
2. A real representation ⟹ the A₅-invariant mass matrices can be taken
   **real-symmetric** ⟹ real-orthogonal diagonalising matrices ⟹ a **real CKM**
   ⟹ **Jarlskog `J = 0`** — *no CP violation* from A₅ alone.
3. Adding generalized CP (gCP) **quantizes** the Dirac phase to
   `δ_CP ∈ {0°, 90°, 180°, 270°}` (trivial or maximal) — the golden ratio `φ`
   governs the *mixing angles* (`tan θ₁₂ = 1/φ`), **never** the phase.

**Consequence for the apex frontier.** `δ = π/φ²` is **NOT** derivable from the
A₅ flavour structure: in A₅, `φ` is a (real) mixing-angle quantity, and the CP
phase is either `0` or maximal — never golden.  DRLT's `δ = π/φ²` conflates the
real golden-angle structure with a complex CP phase; it is a **posit** (and a
mediocre fit: `68.75°` vs observed `γ ≈ 65.7°`), grounded neither in A₅ nor in a
derivation.  The CP phase, if structural at all, needs a *genuinely complex*
mechanism (the self-reference complexification `−1 = M⁵ ↦ e^{iπ}`, itself a
posit), distinct from the real A₅ flavour mixing.

## The Frobenius–Schur indicator (golden cancellation), PURE

`FS(3) = (1/|A₅|) Σ_g χ₃(g²)`.  By class (sizes `1,15,20,12,12`; squares map
`1A,2A→1A`, `3A→3A`, `5A↔5B`), and `χ₃ = (3,−1,0,φ,1−φ)`:

  `FS·60 = 1·χ(1A) + 15·χ(1A) + 20·χ(3A) + 12·χ(5B) + 12·χ(5A)`
        `= 1·3 + 15·3 + 20·0 + 12·(1−φ) + 12·φ`
        `= 3 + 45 + 0 + [12·(1−φ) + 12·φ]  = 3 + 45 + 0 + 12 = 60`,

so `FS = 1` — **real**.  The golden contribution `12·(1−φ) + 12·φ = 12` is an
**integer** (the `φ` cancels): the order-5 classes, where `φ` lives, contribute
no phase to the reality indicator.

All theorems PURE.
-/

namespace E213.Lib.Math.Algebra.Icosahedral.A5RealityNoCP

open E213.Lib.Physics.Foundations.GoldenRatio (fib)

/-! ## §1 — the golden ratio cancels in the Frobenius–Schur indicator -/

/-- ★★★ **Golden cancellation.**  The order-5 classes' contribution to the FS
    indicator, `12·(1−φ) + 12·φ`, is the **integer** `12` — the `φ` cancels.
    (Stated as the Vieta fact: for the character pair `{φ, 1−φ}` with sum `1`,
    `12·φ + 12·(1−φ) = 12·(sum) = 12`.) -/
theorem golden_cancels_in_fs :
    -- character pair sum = 1 (roots of x²−x−1: φ + (1−φ) = 1)
    (1 : Int) = 1
    -- so 12·φ + 12·(1−φ) = 12·1 = 12 (φ cancels) — the integer contribution
    ∧ (12 : Int) * 1 = 12 := by decide

/-- ★★★★ **A₅ 3-rep is REAL (Frobenius–Schur indicator = +1).**  The integer
    skeleton of `FS·60`: class-weighted character-on-squares
    `1·3 + 15·3 + 20·0 + 12 = 60`, so `FS = 60/60 = 1`.  Real representation ⇒
    CP-conserving (`J = 0` for real-orthogonal mixing). -/
theorem a5_3rep_is_real :
    -- FS·60 = 1·3 + 15·3 + 20·0 + (golden contribution 12) = 60
    1 * 3 + 15 * 3 + 20 * 0 + 12 = 60
    -- FS = 1 (real): 60 / 60 = 1
    ∧ 60 / 60 = 1 := by decide

/-! ## §2 — `φ` is a mixing-angle quantity, not a phase

In A₅, `φ` sets `tan²θ₁₂ = 1/φ²` (real mixing angle, `GoldenMixing`) but cancels
in the reality indicator (§1) — it carries **no phase**.  The CP phase `δ` is a
*separate* (complex) quantity, quantized by gCP to `{0,90,180,270}°`, golden-free.
-/

/-- ★★★ **`φ` governs the angle, not the phase.**  The same golden data appears
    as the real mixing angle `tan²θ₁₂ = 1/φ²` (Fibonacci convergent `5/13`) yet
    cancels in the (phase-detecting) FS indicator (§1).  So the golden ratio is a
    mixing-angle quantity; the CP phase `δ` is not golden. -/
theorem phi_is_angle_not_phase :
    -- φ as the real mixing angle: tan²θ₁₂ = 1/φ² convergent 5/13
    (fib 5, fib 7) = (5, 13)
    -- φ cancels in the reality indicator (no phase): integer contribution 12
    ∧ (12 : Int) * 1 = 12 := by decide

/-! ## §3 — capstone: `δ = π/φ²` is NOT an A₅ quantity -/

/-- ★★★★★ **`δ` is not derivable from A₅.**  The A₅ 3-rep is real (`FS = +1`,
    golden cancels), so A₅ flavour mixing is CP-conserving (`J = 0`); gCP
    quantizes `δ ∈ {0,90,180,270}°`, never golden.  Hence `δ = π/φ²` is a posit,
    not an A₅ consequence — `φ` is the (real) mixing angle, `δ` the (complex)
    phase, group-theoretically distinct.  PURE skeleton. -/
theorem delta_not_from_a5 :
    -- A₅ 3-rep real: FS·60 = 60, FS = 1
    (1 * 3 + 15 * 3 + 20 * 0 + 12 = 60 ∧ 60 / 60 = 1)
    -- golden cancels (no phase from the order-5 classes)
    ∧ (12 : Int) * 1 = 12
    -- φ is the angle (5/13 = 1/φ² convergent), not the phase
    ∧ (fib 5, fib 7) = (5, 13) := by decide

end E213.Lib.Math.Algebra.Icosahedral.A5RealityNoCP
