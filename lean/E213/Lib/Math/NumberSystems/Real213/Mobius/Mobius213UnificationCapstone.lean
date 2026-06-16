import E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213PellInvariant
import E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213SternBrocotApps
import E213.Lib.Math.NumberSystems.SignedCut.Core.SternBrocotBridge

/-!
# Mobius213UnificationCapstone — bundle of Stern-Brocot bridge lemmas

A theorem whose proof term bundles the already-proven Stern-Brocot
bridge lemmas: every 213 equality definition over `Nat → Nat → Bool`
cuts factors through the mediant-closure equivalence `sternBrocotEq`
of the two Möbius seeds `(0, 1)` and `(1, 0)`, plus a `(0, 0)`
boundary condition automatic on canonical 213 cuts.

The same matrix `P = [[2,1],[1,1]]` provides:
  · the orbit structure on cuts (`sternBrocotEq`, via mediant
    closure of the two P-seeds);
  · the algebraic invariants `(trace, det, disc) = (NS, NS−NT, d)`
    realising the 213 atomic signature `(NS, NT) = (3, 2)`;
  · the Pell unit cross-product `±1` on consecutive P-orbit pairs,
    matching the `det = 1` symplectic invariant.

This file recombines the existing bridges into a single bundle (a
convenience re-export, not an independent result).
All ingredients PURE (∅-axiom) — see the parent modules.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213UnificationCapstone

open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutEq)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213Equiv (Pseq seedZero seedInf)
open E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213SternBrocot
  (sternBrocotEq cutEq_iff_sternBrocotEq_and_zero reachable_of_pos)
open E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213SternBrocotApps
  (validCutN_cutEq_iff_sternBrocotEq addN_sternBrocotEq)
open E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213PellInvariant
  (Pseq_cross_pell_invariant Pseq_seedZero_pell_invariant)
open E213.Lib.Math.NumberSystems.SignedCut.Core.SternBrocotBridge
  (signedEq signedEq_iff_sternBrocotEq_and_zero)
open E213.Lib.Math.NumberSystems.SignedCut.Core.Core (SignedCut pos neg)
open E213.Lib.Math.NumberSystems.Real213.ValidCut.NValidCut (ValidCutN)

/-! ## §1 — Bundled unification capstone -/

/-- ★★ **Bundle of Stern-Brocot bridge lemmas**: every 213
    equality definition over `Nat → Nat → Bool` cuts established so
    far factors through `sternBrocotEq`, and the P-orbits carry the
    Pell unit cross-product invariant.  Proof term = tuple of the
    existing bridge lemmas (convenience re-export).

    Six conjuncts:
    (a) `cutEq ↔ sternBrocotEq ∧ (0, 0)-cond` (general cuts);
    (b) `cutEq ↔ sternBrocotEq` on `ValidCutN N` cut fields;
    (c) `signedEq ↔ sternBrocotEq ∧ (0, 0)-cond` on cross-sum cuts;
    (d) Full coverage: every `(m, k)` with `m + k ≥ 1` is SB-reachable;
    (e) Pell-orbit identity: `a² + 1 = ab + b²` on seedZero;
    (f) Pell cross-orbit identity: `a · k' + 1 = b · m'` (the
        symplectic det = -1 cross-product across the two orbits). -/
theorem unification_capstone :
    -- (a) General cut equality
    (∀ cx cy : Nat → Nat → Bool,
        cutEq cx cy ↔ sternBrocotEq cx cy ∧ cx 0 0 = cy 0 0)
    -- (b) ValidCutN N
    ∧ (∀ {N : Nat} (vx vy : ValidCutN N),
        cutEq vx.cut vy.cut ↔ sternBrocotEq vx.cut vy.cut)
    -- (c) Signed cut equivalence
    ∧ (∀ s t : SignedCut,
        signedEq s t
          ↔ sternBrocotEq (cutSum (pos s) (neg t)) (cutSum (pos t) (neg s))
            ∧ cutSum (pos s) (neg t) 0 0 = cutSum (pos t) (neg s) 0 0)
    -- (d) Stern-Brocot covers ℕ × ℕ \ {(0, 0)}
    ∧ (∀ (m k : Nat), 1 ≤ m + k →
        E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213SternBrocot.SternBrocotReachable (m, k))
    -- (e) Pell identity on the seedZero orbit
    ∧ (∀ n : Nat,
        (Pseq seedZero n).1 * (Pseq seedZero n).1 + 1
          = (Pseq seedZero n).1 * (Pseq seedZero n).2
            + (Pseq seedZero n).2 * (Pseq seedZero n).2)
    -- (f) Pell cross-product invariant across orbits
    ∧ (∀ n : Nat,
        (Pseq seedZero n).1 * (Pseq seedInf n).2 + 1
          = (Pseq seedZero n).2 * (Pseq seedInf n).1) :=
  ⟨cutEq_iff_sternBrocotEq_and_zero,
   @validCutN_cutEq_iff_sternBrocotEq,
   signedEq_iff_sternBrocotEq_and_zero,
   reachable_of_pos,
   Pseq_seedZero_pell_invariant,
   Pseq_cross_pell_invariant⟩

/-! ## §2 — Algebra preservation capstone

The bundled `ValidCutN N` addition `addN` respects
`sternBrocotEq` in both arguments simultaneously, lifting Wave 13's
entire `cutSumN N` closure (associativity, commutativity, parametric
capstone) to Stern-Brocot-orbit form. -/

/-- ★★ **Algebra preservation lemma** (re-export): `ValidCutN N`'s
    bundled addition is Stern-Brocot congruent.  The cutSumN-based
    algebra structure is therefore realised inside the Stern-Brocot
    equivalence class. -/
theorem algebra_preservation_capstone
    {N : Nat} (hN : 0 < N) {vx vx' vy vy' :
      E213.Lib.Math.NumberSystems.Real213.ValidCut.NValidCut.ValidCutN N}
    (hx : sternBrocotEq vx.cut vx'.cut)
    (hy : sternBrocotEq vy.cut vy'.cut) :
    sternBrocotEq
      (E213.Lib.Math.NumberSystems.Real213.ValidCut.NValidCut.addN N hN vx vy).cut
      (E213.Lib.Math.NumberSystems.Real213.ValidCut.NValidCut.addN N hN vx' vy').cut :=
  addN_sternBrocotEq hN hx hy

/-! ## §3 — Atomic-five / discriminant cross-reference

The Möbius matrix `P = [[2,1],[1,1]]` has discriminant
`trace² − 4·det = 3² − 4·1 = 5`.  Independently,
`Theory.Atomicity.Five.atomic_iff_five` proves that `5` is the
unique Nat satisfying the alive-decomposition atomicity.  These
two readings of `5` — `disc(P)` and `unique atomic Nat` — meet
at `NS + NT = d` in the 213 signature. -/

/-- The matrix `P = [[2,1],[1,1]]` has discriminant `5` as a Nat
    identity (Int form in `Lib/Math/Algebra/Mobius213.lean`). -/
theorem disc_P_eq_five : 3 * 3 = 4 * 1 + 5 := by decide

/-- `5 = NS + NT = d` in 213 signature terms (NS = 3, NT = 2). -/
theorem disc_P_eq_NS_plus_NT : 3 * 3 - 4 * 1 = 3 + 2 := by decide

end E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213UnificationCapstone
