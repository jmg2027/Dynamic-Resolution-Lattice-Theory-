import E213.Lens.Number.FoundingDynamicBridge
import E213.Lens.Number.RatioLensFounding
import E213.Lens.Number.CauchyLensFounding

/-!
# FoundingDialUnification — the founding unit floors the dial; the trace runs the tiers

`FoundingDynamicBridge` pinned one meeting point: the founding invert-swap is the *elliptic
floor* (`comp 0 1 = S`) of the discriminant dial.  This file deepens the meeting to the **whole
dial**, and shows the two marathons split the order-2 companion `comp p q` between them along its
two coordinates:

  * the **founding** fixes the **determinant** — `det (comp p q) = q`, and the founding unit is
    `q = NS − NT = 1` (the count-difference glue, the static invert-completion unit, shared by
    every tier);
  * the **dial** varies the **trace** — `disc (comp p q) = p² − 4q`, so on the founding unit
    floor `q = 1` the discriminant is `p² − 4`, dialed purely by the trace `p`.

Then the **atomic counts are the tier boundaries** of the trace dial:

  * `p = 0` — **elliptic** (the founding swap `S`, `disc = −4 < 0`, period);
  * `p = NT = 2` — **parabolic** (`disc = 0`, the boundary);
  * `p = NS = 3` — **hyperbolic** (the golden/Pell growth, `disc = NS² − 4 = NS + NT = d > 0`).

So the static "invert is one move" (founding) and the dynamic discriminant trichotomy (dial) are
one structure read on the two coordinates of one matrix: the founding sets the unit (det), the
dial sweeps the trace, and the forced atomic counts `(NT, NS)` land exactly on the parabolic
boundary and the hyperbolic golden orbit.

**Honesty.** The first two facts (det = founding unit; disc = trace dial on that floor) are
*parametric*.  That `p = NT` is the parabolic boundary and `p = NS` gives `disc = d` are *atomic*
— they hold because `(NS, NT) = (3, 2)` is forced (`NT² = 4(NS − NT)` and `NS² − 4 = NS + NT`
both pin `NS = 3`), not for free.  All ∅-axiom.
-/

namespace E213.Lens.Number.FoundingDialUnification

open E213.Lib.Math.Cauchy.EllipticPeriodicTier (comp comp_tr comp_det comp_disc parabolic_iff_depth1)
open E213.Lib.Math.Cauchy.NewtonGregory (polyDepthZ liftKZ)
open E213.Lib.Math.Real213.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Physics.Simplex.Counts (NS NT)
open E213.Lib.Math.Mobius213.Px.PnFibonacciUniversal (Q00 Q01 Q11)
open E213.Lens.Number.RatioLensFounding (convergent_lowest_terms_is_det)
open E213.Lib.Math.Real213.PhiCauchyLimit (phiConvergentSeq phiCauchy_limit_eq_phiCut)

/-- ★★★★★ **The founding unit floors the dial; the trace runs the tiers.**  The number-tower
    founding and the discriminant dial are one order-2 companion `comp p q` split along its two
    coordinates — the founding fixes the determinant (`= q`, the unit `NS − NT`), the dial varies
    the trace (`disc = p² − 4q`).  On the founding unit floor `q = NS − NT (= 1)`:

      1. **det floor** — every tier shares the founding unit: `det (comp p (NS−NT)) = NS − NT`;
      2. **trace dial** — `disc (comp p (NS−NT)) = p² − 4·(NS−NT)`;
      3. **elliptic** at trace `0` (the founding swap `S`): `disc < 0`;
      4. **parabolic** at trace `NT`: `disc = 0` (the boundary — atomic, `NT = 2`);
      5. **hyperbolic** at trace `NS` (the golden orbit): `disc = NS + NT = d` (atomic, `NS = 3`).

    The forced atomic counts `(NT, NS)` are exactly the parabolic boundary and the hyperbolic
    golden trace of the founding-unit dial. -/
theorem founding_unit_floors_dial_trace_runs_tiers :
    (∀ p : Int, Mat2.det (comp p ((NS : Int) - NT)) = (NS : Int) - NT)
    ∧ (∀ p : Int, Mat2.disc (comp p ((NS : Int) - NT)) = p * p - 4 * ((NS : Int) - NT))
    ∧ Mat2.disc (comp 0 ((NS : Int) - NT)) < 0
    ∧ Mat2.disc (comp (NT : Int) ((NS : Int) - NT)) = 0
    ∧ Mat2.disc (comp (NS : Int) ((NS : Int) - NT)) = (NS : Int) + NT := by
  refine ⟨fun p => comp_det p _, fun p => comp_disc p _, ?_, ?_, ?_⟩
  · rw [comp_disc]; decide
  · rw [comp_disc]; decide
  · rw [comp_disc]; decide

/-- ★★★★ **The parabolic tier (trace `NT`) is the difference-Lens rung.**  The founding's first
    bundling, the **difference-Lens** (`ℤ`), is read on a sequence as its first finite difference
    `liftKZ 1 s n = s(n+1) − s n` — exactly the `m − n` of the directed count-pair.  The
    discriminant dial's **parabolic** tier sits at trace `NT` (`disc (comp NT 1) = 0`), and a
    sequence is parabolic iff that difference-Lens output is **constant** — `polyDepthZ 1`, depth-1
    (`parabolic_iff_depth1`).  So:

      * elliptic (trace `0`) = the difference-Lens **sign** (the period-2 swap, `S² = −I`);
      * **parabolic (trace `NT`) = the difference-Lens applied once reaching a constant** (depth-1,
        `Δ²s = 0`) — the `ℤ` magnitude rung;
      * hyperbolic (trace `NS`) = the ratio/Pell growth (`ℚ`/`ℝ`).

    The founding number-rungs *are* the discriminant tiers: `ℤ`'s sign and magnitude are the
    elliptic and parabolic floors, the golden ratio the hyperbolic growth.  The parabolic trace is
    `NT` because the second-difference middle coefficient is `NT = 2` (`Δ²s = s(n+2) − NT·s(n+1) +
    s n`). -/
theorem parabolic_at_NT_is_difference_lens_depth1 (s : Nat → Int) :
    Mat2.disc (comp (NT : Int) 1) = 0
    ∧ ((∀ n, s (n + 2) = (NT : Int) * s (n + 1) - s n) ↔ polyDepthZ 1 s)
    ∧ (∀ n, liftKZ 1 s n = s (n + 1) - s n) :=
  ⟨by rw [comp_disc]; decide, parabolic_iff_depth1 s, fun _ => rfl⟩

/-- ★★★★ **The hyperbolic tier (trace `NS`) is the ratio/Cauchy rung (`ℚ`/`ℝ`).**  The hyperbolic
    companion `comp NS 1` has trace `NS`, determinant the founding unit `NS − NT`, and discriminant
    `NS + NT = d > 0` (the golden/Pell characteristic, growth).  Its founding reading is the top of
    the tower: the **ratio-Lens** (`ℚ`) reads the convergents `Q01/Q00`, whose cross-determinant is
    the *same* unit `NS − NT` (`convergent_lowest_terms_is_det`); the **Cauchy-Lens** (`ℝ`)
    completes them to the golden cut `φ` (`phiCauchy_limit_eq_phiCut`).

    With the elliptic (`ℤ`-sign) and parabolic (`ℤ`-difference) tiers, the correspondence is
    complete: **the founding number-rungs are the discriminant tiers** — `ℤ` splits as sign
    (elliptic) and difference (parabolic), `ℚ`/`ℝ` is the hyperbolic growth; the count `ℕ` is the
    base they are all read from. -/
theorem hyperbolic_at_NS_is_ratio_cauchy_rung :
    Mat2.tr (comp (NS : Int) 1) = (NS : Int)
    ∧ Mat2.det (comp (NS : Int) 1) = (NS : Int) - NT
    ∧ Mat2.disc (comp (NS : Int) 1) = (NS : Int) + NT
    ∧ (∀ n, Q00 n * Q11 n = Q01 n * Q01 n + (NS - NT))
    ∧ (∀ m k, phiConvergentSeq.limit m k = E213.Lib.Math.Real213.PhiAsCut.phiCut m k) :=
  ⟨comp_tr (NS : Int) 1, by rw [comp_det]; decide, by rw [comp_disc]; decide,
   convergent_lowest_terms_is_det, phiCauchy_limit_eq_phiCut⟩

end E213.Lens.Number.FoundingDialUnification
