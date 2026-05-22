import E213.Lib.Math.Cohomology.Cup.SelfRefDepth

/-!
# Cohomology.Cup.CupAtomic — Cup-closed cochain pair classification

A cochain pair `(α, β)` at bidegree `(k, l)` on Δ^(d-1) is
**cup-closed** if `δ(α ⌣ β) = 0`.  This is the natural "atomic"
class — pairs whose cup product is a cocycle, not just any
cochain.

For closed α, β (where δα = δβ = 0), the twisted Leibniz reduces
to `δ(α ⌣ β) = (α ⌣ β)(τ \ {τ[k]})` — the self-ref correction
alone.  Cup-closed iff correction vanishes for all τ iff α(a) ∧
β(b) = 0 for all `(a, b)` arising as middle-removed pairs.

At bidegree (1, 1) on Δ⁴, the middle-removed pairs of 3-subsets
of {0..4} are precisely the 2-subsets `(a, b)` with `b - a ≥ 2`:

  (0,2), (0,3), (0,4), (1,3), (1,4), (2,4)

— six pairs.  The cup-closed condition restricts (α, β) to
avoid all six (1, 1) products.

This file enumerates and counts the cup-closed cochain pairs at
(1, 1) on Δ⁴ via decide.

PURE.
-/

namespace E213.Lib.Math.Cohomology.Cup.CupAtomic

open E213.Lib.Math.Cohomology.Cup.SelfRefDepth (α_e)

/-- The six middle-removed pairs at (1, 1) on Δ⁴: 2-subsets `(a, b)`
    with `b - a ≥ 2`. -/
def middleRemovedPairs_d5 : List (Nat × Nat) :=
  [(0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (2, 4)]

/-- A pair of single-vertex indicators is **cup-closed-trivially**
    if no middle-removed pair `(a, b)` lies in α_supp × β_supp. -/
def isCupClosedTrivial_d5_11
    (α_supp β_supp : List Nat) : Bool :=
  middleRemovedPairs_d5.all
    (fun p => !(α_supp.contains p.1 && β_supp.contains p.2))

/-- Smoke: support pair `({0}, {4})` fails the cup-closed condition
    (because `(0, 4)` is in the forbidden list).  PURE. -/
theorem cupClosed_fail_e0_e4 :
    isCupClosedTrivial_d5_11 [0] [4] = false := by decide

/-- Smoke: support pair `({0}, {1})` passes (adjacent vertices —
    `(0, 1)` is not in the forbidden list since `1 - 0 < 2`).  PURE. -/
theorem cupClosed_pass_e0_e1 :
    isCupClosedTrivial_d5_11 [0] [1] = true := by decide

/-- Smoke: support pair `({0, 1, 2}, {3, 4})` fails (since
    `(0, 3), (0, 4), (1, 3), (1, 4), (2, 4)` all in α × β).  PURE. -/
theorem cupClosed_fail_012_34 :
    isCupClosedTrivial_d5_11 [0, 1, 2] [3, 4] = false := by decide

/-- Smoke: support pair `({0, 1}, {0, 1})` — α and β both
    supported on the first two vertices, no large gaps.  PASSES.  PURE. -/
theorem cupClosed_pass_01_01 :
    isCupClosedTrivial_d5_11 [0, 1] [0, 1] = true := by decide

/-! ## §2.  All-cochain enumeration (Bool 5-tuples) -/

/-- A cochain at bidegree 1 on Δ⁴ is encoded as a Bool 5-tuple
    `(b0, b1, b2, b3, b4)`.  PURE. -/
abbrev Cochain1_d5 := Bool × Bool × Bool × Bool × Bool

/-- Convert a Bool 5-tuple to a support list (`[i]` for each i
    with `b_i = true`).  PURE. -/
def cochainSupport (c : Cochain1_d5) : List Nat :=
  let (b0, b1, b2, b3, b4) := c
  (if b0 then [0] else []) ++ (if b1 then [1] else [])
  ++ (if b2 then [2] else []) ++ (if b3 then [3] else [])
  ++ (if b4 then [4] else [])

/-- Smoke: support of `(true, false, true, false, true)` is `[0, 2, 4]`. -/
theorem cochainSupport_smoke :
    cochainSupport (true, false, true, false, true) = [0, 2, 4] := by decide

/-! ## §3.  Full enumeration of cochain pairs at (1, 1) on Δ⁴ -/

set_option maxRecDepth 4096

/-- All 32 Bool 5-tuples (= 2^5 cochains at degree 1 on Δ⁴).  PURE. -/
def allCochains1_d5 : List Cochain1_d5 :=
  let bools := [false, true]
  bools.flatMap (fun b0 =>
    bools.flatMap (fun b1 =>
      bools.flatMap (fun b2 =>
        bools.flatMap (fun b3 =>
          bools.map (fun b4 => (b0, b1, b2, b3, b4))))))

/-- Smoke: 32 cochains in total.  PURE. -/
theorem allCochains1_d5_length : allCochains1_d5.length = 32 := by decide

/-- Cup-closed-trivially predicate on the Bool encoding.  PURE. -/
def isCupClosed (α β : Cochain1_d5) : Bool :=
  isCupClosedTrivial_d5_11 (cochainSupport α) (cochainSupport β)

/-- Count of cup-closed-trivially pairs over the full enumeration.  PURE. -/
def cupClosedCount_d5_11 : Nat :=
  (allCochains1_d5.flatMap (fun α =>
    allCochains1_d5.map (fun β =>
      isCupClosed α β))).foldl
        (fun n b => if b then n + 1 else n) 0

/-- ★★★★★ **Cup-closed-trivially pair count at (1, 1) on Δ⁴ = 320**.

    Across all `32 × 32 = 1024` cochain pairs `(α, β) : Cochain⁽¹⁾(Δ⁴)²`,
    the number satisfying the cup-closed-trivially condition (no
    α(a) ∧ β(b) = 1 for any middle-removed pair (a, b) with
    b - a ≥ 2) is exactly **320**.

    Decide-verified over the full 1024-pair enumeration.  PURE. -/
theorem cupClosedCount_d5_11_eq : cupClosedCount_d5_11 = 320 := by decide

/-- The total cochain pair count at (1, 1) on Δ⁴ is `32 × 32 = 1024`. -/
theorem total_pair_count_d5_11 : 32 * 32 = 1024 := by decide

/-- ★★★ **Cup-closed density** at (1, 1) on Δ⁴ is `320 / 1024 = 5/16`.

    Specifically, `cupClosedCount_d5_11 · 16 = 1024 · 5`.  This
    density `5/16` is a count-Lens output of the (1, 1) subspace:
    of all cochain pairs, `5/16 = 0.3125` are cup-closed-trivially.
    PURE. -/
theorem cup_closed_density_d5_11 :
    cupClosedCount_d5_11 * 16 = 1024 * 5 := by decide

end E213.Lib.Math.Cohomology.Cup.CupAtomic
