import E213.Lib.Math.NumberSystems.SignedCut.Core.Equivalence
import E213.Lib.Math.NumberSystems.Real213.Mobius213SternBrocotApps

/-!
# SignedCut Stern-Brocot bridge

The signed cut equivalence (`signedEqAt` — pointwise cross-additive
equality of `cutSum`-shaped cuts) factors directly through Stern-Brocot
equivalence on `Nat → Nat → Bool` via the cross-sum cuts
`cutSum (pos s) (neg t)` and `cutSum (pos t) (neg s)`.

  `signedEq s t  :=  ∀ m k, signedEqAt s t m k`
                 =   `cutEq (cutSum (pos s) (neg t)) (cutSum (pos t) (neg s))`
                ⇔   `sternBrocotEq … ∧ (cross-sum 0 0 values agree)`

For signed cuts built from canonical components — `ofPos`, `ofNeg`,
the constants `zero`, `one`, `negOne`, and anything obtained from
them via `signedAdd`, `signedSub`, `signedMul` — every underlying
component evaluates to `true` at `(0, 0)` (each is a `cutSum`, `cutMul`,
or `constCut` chain bottoming out at `constCut a N` with
`a * 0 ≤ N * 0` trivially), so the (0, 0) side condition is automatic.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.NumberSystems.SignedCut.Core.SternBrocotBridge

open E213.Lib.Math.NumberSystems.SignedCut.Core.Core (SignedCut pos neg)
open E213.Lib.Math.NumberSystems.SignedCut.Core.Equivalence (signedEqAt)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutEq)
open E213.Lib.Math.NumberSystems.Real213.Mobius213SternBrocot
  (sternBrocotEq cutEq_iff_sternBrocotEq_and_zero)

/-! ## §1 — Full signed equivalence -/

/-- **signedEq**: the ∀-quantified version of `signedEqAt`.  Two
    signed cuts agree at every cut coordinate iff their cross-sum
    cuts coincide.  Equivalently `cutEq (cutSum (pos s) (neg t))
    (cutSum (pos t) (neg s))`. -/
def signedEq (s t : SignedCut) : Prop := ∀ m k, signedEqAt s t m k

/-- `signedEq` unfolds to `cutEq` of the cross-sum cuts.  `rfl`
    by definition of `signedEqAt`. -/
theorem signedEq_iff_cutEq (s t : SignedCut) :
    signedEq s t
      ↔ cutEq (cutSum (pos s) (neg t)) (cutSum (pos t) (neg s)) :=
  Iff.rfl

/-! ## §2 — `cutSum` at (0, 0) -/

/-- `cutSum cx cy 0 0` is `cx 0 0 && cy 0 0`.  Unfolds by
    definition of `cutSumAux`. -/
theorem cutSum_zero_zero (cx cy : Nat → Nat → Bool) :
    cutSum cx cy 0 0 = (cx 0 0 && cy 0 0) := rfl

/-- If both component cuts agree at (0, 0), so do their cutSums. -/
theorem cutSum_zero_zero_eq (cx cy cx' cy' : Nat → Nat → Bool)
    (h1 : cx 0 0 = cx' 0 0) (h2 : cy 0 0 = cy' 0 0) :
    cutSum cx cy 0 0 = cutSum cx' cy' 0 0 := by
  rw [cutSum_zero_zero, cutSum_zero_zero, h1, h2]

/-! ## §3 — Bridge to Stern-Brocot equivalence -/

/-- ★★★★★ **Stern-Brocot bridge**: `signedEq` factors through
    Stern-Brocot equivalence on the cross-sum cuts plus the
    canonical (0, 0) side condition.  Direct application of
    `cutEq_iff_sternBrocotEq_and_zero` to the unfolded
    `signedEq = cutEq …`. -/
theorem signedEq_iff_sternBrocotEq_and_zero (s t : SignedCut) :
    signedEq s t
      ↔ sternBrocotEq (cutSum (pos s) (neg t)) (cutSum (pos t) (neg s))
        ∧ cutSum (pos s) (neg t) 0 0 = cutSum (pos t) (neg s) 0 0 :=
  cutEq_iff_sternBrocotEq_and_zero _ _

/-! ## §4 — Automatic (0, 0) condition for canonical inputs

If the four underlying component cuts (`pos s`, `neg t`, `pos t`,
`neg s`) all evaluate to `true` at `(0, 0)`, then both cross-sum
cuts evaluate to `true` at `(0, 0)`, so the (0, 0) side condition
in `signedEq_iff_sternBrocotEq_and_zero` is automatic.  Every
signed cut built from `constCut a N` ingredients via
`ofPos`/`ofNeg`/`signedAdd`/`signedSub`/`signedMul` satisfies this
hypothesis. -/

/-- ★★★★ **Auto-zero condition**: if all four component cuts are
    `true` at (0, 0), the cross-sum cuts agree at (0, 0). -/
theorem cross_sum_zero_zero_of_components
    (s t : SignedCut)
    (hps : (pos s) 0 0 = true) (hnt : (neg t) 0 0 = true)
    (hpt : (pos t) 0 0 = true) (hns : (neg s) 0 0 = true) :
    cutSum (pos s) (neg t) 0 0 = cutSum (pos t) (neg s) 0 0 := by
  rw [cutSum_zero_zero, cutSum_zero_zero, hps, hnt, hpt, hns]

/-- ★★★★★ **Reduced bridge**: when all four component cuts are
    `true` at (0, 0), `signedEq` reduces to pure Stern-Brocot
    equivalence on the cross-sum cuts.  Realisation of the
    canonical-equivalence claim on signed cuts: the equality of
    signed cuts IS Stern-Brocot equivalence on their cross-sum
    cut representatives, with no residual boundary condition. -/
theorem signedEq_iff_sternBrocotEq_of_canonical
    (s t : SignedCut)
    (hps : (pos s) 0 0 = true) (hnt : (neg t) 0 0 = true)
    (hpt : (pos t) 0 0 = true) (hns : (neg s) 0 0 = true) :
    signedEq s t
      ↔ sternBrocotEq (cutSum (pos s) (neg t)) (cutSum (pos t) (neg s)) :=
  ⟨fun h => ((signedEq_iff_sternBrocotEq_and_zero s t).mp h).1,
   fun h => (signedEq_iff_sternBrocotEq_and_zero s t).mpr
     ⟨h, cross_sum_zero_zero_of_components s t hps hnt hpt hns⟩⟩

end E213.Lib.Math.NumberSystems.SignedCut.Core.SternBrocotBridge
