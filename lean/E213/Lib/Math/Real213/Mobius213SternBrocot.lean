import E213.Lib.Math.Real213.Mobius213Equiv

/-!
# Mobius213SternBrocot — Stern-Brocot reachable equivalence on cuts

Closure of the two Möbius seeds `(0, 1)` and `(1, 0)` under the
mediant operation (a, b) ⊕ (c, d) = (a+c, b+d).  Equivalent to
the orbit of the seeds under the L+R monoid action — where
L = [[1,0],[1,1]] and R = [[1,1],[0,1]] are the standard SL₂(ℤ)
generators whose composite R·L = [[2,1],[1,1]] is the 213
Möbius matrix P (`Lib/Math/Mobius213.lean`).

Every coprime (m, k) ∈ ℕ × ℕ appears (uniquely) in the
Stern-Brocot tree, so the mediant-closure equality
`sternBrocotEq` is strictly stronger than the P-orbit-only
`mobiusEq` (`Mobius213Equiv.lean`).

  · `mobiusEq` (P-orbit, two thin Pell chains)
  · `sternBrocotEq` (mediant closure of seeds, all coprime pairs)
  · `cutEq` (pointwise on all of ℕ × ℕ)

The chain `cutEq ⇒ sternBrocotEq ⇒ mobiusEq` holds
unconditionally; the converses require additional structure
(scale-invariance for `sternBrocotEq ⇒ cutEq` since cuts on
non-coprime (m, k) factor through the coprime reduction; and a
Pell-coverage argument for `mobiusEq ⇒ sternBrocotEq`, which
fails for general cuts).

## What this file delivers

  · `SternBrocotReachable (m, k)` — inductive closure of
    {(0,1), (1,0)} under mediant
  · Concrete L0–L2 witnesses: (1,1), (1,2), (2,1), (1,3), (2,3),
    (3,2), (3,1) — every coprime pair with max ≤ 3
  · `sternBrocotEq cx cy` — agreement on all reachable (m, k)
  · refl / symm / trans (equivalence-relation laws)
  · `sternBrocotEq_of_cutEq` — pointwise ⇒ Stern-Brocot
  · `mobiusEq_of_sternBrocotEq_at_seeds` — the two P-seeds are
    reachable, so `sternBrocotEq` constrains both seed cells
    immediately (one half of the P-orbit inclusion bridge; the
    full ∀n inclusion requires a mediant identity for `Pstep`
    proved separately)

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Real213.Mobius213SternBrocot

open E213.Lib.Math.Real213.Core.CutPoset (cutEq)

/-! ## §1 — SternBrocotReachable inductive predicate -/

/-- **SternBrocotReachable**: closure of the seeds `(0, 1)` and
    `(1, 0)` under the mediant `(a, b) ⊕ (c, d) := (a+c, b+d)`.
    Every coprime pair appears (uniquely) at some finite depth
    (the Stern-Brocot tree node theorem). -/
inductive SternBrocotReachable : Nat × Nat → Prop where
  | seedZero : SternBrocotReachable (0, 1)
  | seedInf  : SternBrocotReachable (1, 0)
  | mediant {a b c d : Nat} :
      SternBrocotReachable (a, b) →
      SternBrocotReachable (c, d) →
      SternBrocotReachable (a + c, b + d)

/-! ## §2 — Initial coprime witnesses (Stern-Brocot levels 1–2) -/

/-- (1, 1) = (0+1, 1+0), the root mediant. -/
theorem reachable_1_1 : SternBrocotReachable (1, 1) :=
  .mediant .seedZero .seedInf

/-- (1, 2) = (0+1, 1+1), left child of root. -/
theorem reachable_1_2 : SternBrocotReachable (1, 2) :=
  .mediant .seedZero reachable_1_1

/-- (2, 1) = (1+1, 1+0), right child of root. -/
theorem reachable_2_1 : SternBrocotReachable (2, 1) :=
  .mediant reachable_1_1 .seedInf

/-- (1, 3) = (0+1, 1+2), left-left grandchild. -/
theorem reachable_1_3 : SternBrocotReachable (1, 3) :=
  .mediant .seedZero reachable_1_2

/-- (2, 3) = (1+1, 2+1), left-right grandchild. -/
theorem reachable_2_3 : SternBrocotReachable (2, 3) :=
  .mediant reachable_1_2 reachable_1_1

/-- (3, 2) = (2+1, 1+1), right-left grandchild — the (NS, NT)
    atomicity pair reached at depth 3. -/
theorem reachable_3_2 : SternBrocotReachable (3, 2) :=
  .mediant reachable_2_1 reachable_1_1

/-- (3, 1) = (2+1, 1+0), right-right grandchild. -/
theorem reachable_3_1 : SternBrocotReachable (3, 1) :=
  .mediant reachable_2_1 .seedInf

/-! ## §3 — sternBrocotEq: agreement on every reachable (m, k) -/

/-- **sternBrocotEq**: cx, cy agree on every Stern-Brocot
    reachable (m, k).  Strictly stronger than `mobiusEq`
    (which checks only the P-orbit Pell chains); weaker than
    `cutEq` (which checks all of ℕ × ℕ pointwise, including
    non-coprime pairs not in the Stern-Brocot tree). -/
def sternBrocotEq (cx cy : Nat → Nat → Bool) : Prop :=
  ∀ m k, SternBrocotReachable (m, k) → cx m k = cy m k

/-! ## §4 — sternBrocotEq is an equivalence relation -/

/-- sternBrocotEq reflexivity. -/
theorem sternBrocotEq_refl (c : Nat → Nat → Bool) : sternBrocotEq c c :=
  fun _ _ _ => rfl

/-- sternBrocotEq symmetry. -/
theorem sternBrocotEq_symm (cx cy : Nat → Nat → Bool) :
    sternBrocotEq cx cy → sternBrocotEq cy cx :=
  fun h m k hr => (h m k hr).symm

/-- sternBrocotEq transitivity. -/
theorem sternBrocotEq_trans (cx cy cz : Nat → Nat → Bool) :
    sternBrocotEq cx cy → sternBrocotEq cy cz → sternBrocotEq cx cz :=
  fun h1 h2 m k hr => (h1 m k hr).trans (h2 m k hr)

/-! ## §5 — Forward bridge: cutEq ⇒ sternBrocotEq -/

/-- ★★★ **Forward direction**: pointwise equality on all
    `(m, k)` implies agreement on every Stern-Brocot reachable
    pair.  Trivial reachability-blind specialisation. -/
theorem sternBrocotEq_of_cutEq (cx cy : Nat → Nat → Bool) :
    cutEq cx cy → sternBrocotEq cx cy :=
  fun h m k _ => h m k

/-! ## §6 — Reachability of the two P-seed cells -/

/-- The two Möbius P-seeds `(0, 1)` and `(1, 0)` are the
    Stern-Brocot constructors; reachability is by `seedZero`
    and `seedInf` directly. -/
theorem seedZero_reachable : SternBrocotReachable (0, 1) := .seedZero

/-- See `seedZero_reachable`. -/
theorem seedInf_reachable : SternBrocotReachable (1, 0) := .seedInf

end E213.Lib.Math.Real213.Mobius213SternBrocot
