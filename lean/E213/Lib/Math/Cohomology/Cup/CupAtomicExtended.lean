import E213.Lib.Math.Cohomology.Cup.CupAtomic

/-!
# Cohomology.Cup.CupAtomicExtended — `d ∈ {3, 4}` density validation

Validates the conjectured `d / 2^(d-1)` cup-closed density formula
at lower-dimensional simplices.

  · d = 3:  density = 3/4   (48 out of 64 pairs)
  · d = 4:  density = 1/2   (128 out of 256 pairs)
  · d = 5:  density = 5/16  (320 out of 1024 pairs)  [in CupAtomic.lean]

The pattern `count · 2^(d-1) = total · d` is decide-verified at
d ∈ {3, 4, 5}.

PURE.
-/

namespace E213.Lib.Math.Cohomology.Cup.CupAtomicExtended

set_option maxRecDepth 16384

/-! ## §1.  d = 3 — single forbidden pair (0, 2) -/

abbrev Cochain1_d3 := Bool × Bool × Bool

def cochainSupport_d3 (c : Cochain1_d3) : List Nat :=
  let (b0, b1, b2) := c
  (if b0 then [0] else []) ++ (if b1 then [1] else [])
  ++ (if b2 then [2] else [])

def isCupClosedTrivial_d3_11 (αs βs : List Nat) : Bool :=
  !(αs.contains 0 && βs.contains 2)

def allCochains1_d3 : List Cochain1_d3 :=
  let bools := [false, true]
  bools.flatMap (fun b0 =>
    bools.flatMap (fun b1 =>
      bools.map (fun b2 => (b0, b1, b2))))

def cupClosedCount_d3_11 : Nat :=
  (allCochains1_d3.flatMap (fun α =>
    allCochains1_d3.map (fun β =>
      isCupClosedTrivial_d3_11 (cochainSupport_d3 α) (cochainSupport_d3 β)))).foldl
        (fun n b => if b then n + 1 else n) 0

theorem cupClosedCount_d3_11_eq : cupClosedCount_d3_11 = 48 := by decide

/-- ★★ **Density at d = 3**: `48 / 64 = 3/4`.  Confirms
    `count · 2^(d-1) = total · d`: `48 · 4 = 64 · 3 = 192`.  PURE. -/
theorem cup_closed_density_d3_11 :
    cupClosedCount_d3_11 * 4 = 64 * 3 := by decide

/-! ## §2.  d = 4 — three forbidden pairs (0,2), (0,3), (1,3) -/

abbrev Cochain1_d4 := Bool × Bool × Bool × Bool

def cochainSupport_d4 (c : Cochain1_d4) : List Nat :=
  let (b0, b1, b2, b3) := c
  (if b0 then [0] else []) ++ (if b1 then [1] else [])
  ++ (if b2 then [2] else []) ++ (if b3 then [3] else [])

def middleRemovedPairs_d4 : List (Nat × Nat) :=
  [(0, 2), (0, 3), (1, 3)]

def isCupClosedTrivial_d4_11 (αs βs : List Nat) : Bool :=
  middleRemovedPairs_d4.all
    (fun p => !(αs.contains p.1 && βs.contains p.2))

def allCochains1_d4 : List Cochain1_d4 :=
  let bools := [false, true]
  bools.flatMap (fun b0 =>
    bools.flatMap (fun b1 =>
      bools.flatMap (fun b2 =>
        bools.map (fun b3 => (b0, b1, b2, b3)))))

def cupClosedCount_d4_11 : Nat :=
  (allCochains1_d4.flatMap (fun α =>
    allCochains1_d4.map (fun β =>
      isCupClosedTrivial_d4_11 (cochainSupport_d4 α) (cochainSupport_d4 β)))).foldl
        (fun n b => if b then n + 1 else n) 0

theorem cupClosedCount_d4_11_eq : cupClosedCount_d4_11 = 128 := by decide

/-- ★★ **Density at d = 4**: `128 / 256 = 1/2`.  Confirms
    `count · 2^(d-1) = total · d`: `128 · 8 = 256 · 4 = 1024`.  PURE. -/
theorem cup_closed_density_d4_11 :
    cupClosedCount_d4_11 * 8 = 256 * 4 := by
  rw [cupClosedCount_d4_11_eq]

/-! ## §3.  Density formula validation ∀d ∈ {3, 4, 5}

Cup-closed density at bidegree (1, 1) on Δ^(d-1):

| d | count   | total      | density       | count · 2^(d-1) = total · d |
|---|---------|------------|---------------|---|
| 3 |  48     |  64        | 3/4 = 0.75    | 48 · 4   = 64 · 3   = 192   |
| 4 | 128     | 256        | 1/2 = 0.50    | 128 · 8  = 256 · 4  = 1024  |
| 5 | 320     | 1024       | 5/16 = 0.3125 | 320 · 16 = 1024 · 5 = 5120  |

The pattern `count = (total · d) / 2^(d-1) = 2^d · d / 2 = d · 2^(d-1)`
holds at d ∈ {3, 4, 5}.  Conjectured ∀d ≥ 2.

Note the **count = d · 2^(d-1)** structural formula:
  · d = 3: 3 · 4 = 12 ... wait that's not 48.

Re-checking: `count · 2^(d-1) = total · d = 2^d · 2^d · d / d_or_something`...

Actually `count · 2^(d-1) = total · d = 2^(2d) · d`.  So
`count = 2^(2d) · d / 2^(d-1) = 2^(d+1) · d`.

For d=3: 2^4 · 3 = 16 · 3 = 48.  ✓
For d=4: 2^5 · 4 = 32 · 4 = 128.  ✓
For d=5: 2^6 · 5 = 64 · 5 = 320.  ✓

So **count(d) = d · 2^(d+1)**.  This is a clean ∀d formula. -/

/-- Conjectured ∀d formula: cup-closed-trivially count at (1, 1)
    on Δ^(d-1) is `d · 2^(d+1)`.  PURE.

    Derived via the explicit counts:
      d = 3:  48 = 3 · 16 = 3 · 2^4
      d = 4: 128 = 4 · 32 = 4 · 2^5
      d = 5: 320 = 5 · 64 = 5 · 2^6
-/
theorem cupClosedCount_formula_d3 :
    cupClosedCount_d3_11 = 3 * 16 := by
  rw [cupClosedCount_d3_11_eq]

theorem cupClosedCount_formula_d4 :
    cupClosedCount_d4_11 = 4 * 32 := by
  rw [cupClosedCount_d4_11_eq]

theorem cupClosedCount_formula_d5 :
    E213.Lib.Math.Cohomology.Cup.CupAtomic.cupClosedCount_d5_11 = 5 * 64 :=
  by rw [E213.Lib.Math.Cohomology.Cup.CupAtomic.cupClosedCount_d5_11_eq]

end E213.Lib.Math.Cohomology.Cup.CupAtomicExtended
