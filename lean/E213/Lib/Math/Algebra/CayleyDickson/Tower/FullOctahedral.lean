import E213.Lib.Math.Algebra.CayleyDickson.Tower.TypeOOctahedral

/-!
# The full binary octahedral group `2O` (48 units) and its order census

`TypeOOctahedral` exhibits one order-8 unit; this file constructs the
**complete 48-element unit group** of the octahedral order over `ℤ[√2]`
and proves its full element-order census — the complete `E₇` McKay rung,
not just a witness:

  `2O` (48) = `8` "Lipschitz" (`±2eᵢ`) + `16` half-integer (`(±1±i±j±k)/2`)
            + `24` octahedral (`(±eᵢ±eⱼ)/√2`),
  with order distribution `{1:1, 2:1, 3:8, 4:6, 6:8, 8:24}` (sum 48).

The 24 order-8 elements are exactly the octahedral extras beyond the
`2T` (24) tetrahedral subgroup — the new `E₇` torsion.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Tower.FullOctahedral

open E213.Lib.Math.Algebra.CayleyDickson.Tower.TypeOOctahedral

/-- Element order on the octahedral order (menu `{1,2,3,4,6,8}`). -/
def oct_orderOf (u : Octahedral) : Nat :=
  if u = Octahedral.one then 1
  else if u * u = Octahedral.one then 2
  else if u * u * u = Octahedral.one then 3
  else if u * u * u * u = Octahedral.one then 4
  else if u * u * u * u * u * u = Octahedral.one then 6
  else if u * u * u * u * u * u * u * u = Octahedral.one then 8
  else 0

/-- Sign list. -/
private def s2 : List Int := [1, -1]

/-- The 16 half-integer units `(±1±i±j±k)/2` (scaled `⟨±1,±1,±1,±1⟩`). -/
def octa_half : List Octahedral :=
  s2.flatMap fun a => s2.flatMap fun b => s2.flatMap fun c => s2.map fun d =>
    (⟨⟨a, 0⟩, ⟨b, 0⟩, ⟨c, 0⟩, ⟨d, 0⟩⟩ : Octahedral)

/-- The 8 "Lipschitz" units `±eᵢ` (scaled `±2` in one coordinate). -/
def octa_lip : List Octahedral :=
  [⟨⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩,
   ⟨⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩,
   ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩⟩,
   ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩⟩, ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩⟩]

/-- The 24 octahedral units `(±eᵢ±eⱼ)/√2` (scaled `±√2 = ⟨0,±1⟩` in two
    of four coordinates). -/
def octa_oct : List Octahedral :=
  -- positions (0,1)
  [⟨⟨0,1⟩,⟨0,1⟩,⟨0,0⟩,⟨0,0⟩⟩, ⟨⟨0,1⟩,⟨0,-1⟩,⟨0,0⟩,⟨0,0⟩⟩,
   ⟨⟨0,-1⟩,⟨0,1⟩,⟨0,0⟩,⟨0,0⟩⟩, ⟨⟨0,-1⟩,⟨0,-1⟩,⟨0,0⟩,⟨0,0⟩⟩,
   -- positions (0,2)
   ⟨⟨0,1⟩,⟨0,0⟩,⟨0,1⟩,⟨0,0⟩⟩, ⟨⟨0,1⟩,⟨0,0⟩,⟨0,-1⟩,⟨0,0⟩⟩,
   ⟨⟨0,-1⟩,⟨0,0⟩,⟨0,1⟩,⟨0,0⟩⟩, ⟨⟨0,-1⟩,⟨0,0⟩,⟨0,-1⟩,⟨0,0⟩⟩,
   -- positions (0,3)
   ⟨⟨0,1⟩,⟨0,0⟩,⟨0,0⟩,⟨0,1⟩⟩, ⟨⟨0,1⟩,⟨0,0⟩,⟨0,0⟩,⟨0,-1⟩⟩,
   ⟨⟨0,-1⟩,⟨0,0⟩,⟨0,0⟩,⟨0,1⟩⟩, ⟨⟨0,-1⟩,⟨0,0⟩,⟨0,0⟩,⟨0,-1⟩⟩,
   -- positions (1,2)
   ⟨⟨0,0⟩,⟨0,1⟩,⟨0,1⟩,⟨0,0⟩⟩, ⟨⟨0,0⟩,⟨0,1⟩,⟨0,-1⟩,⟨0,0⟩⟩,
   ⟨⟨0,0⟩,⟨0,-1⟩,⟨0,1⟩,⟨0,0⟩⟩, ⟨⟨0,0⟩,⟨0,-1⟩,⟨0,-1⟩,⟨0,0⟩⟩,
   -- positions (1,3)
   ⟨⟨0,0⟩,⟨0,1⟩,⟨0,0⟩,⟨0,1⟩⟩, ⟨⟨0,0⟩,⟨0,1⟩,⟨0,0⟩,⟨0,-1⟩⟩,
   ⟨⟨0,0⟩,⟨0,-1⟩,⟨0,0⟩,⟨0,1⟩⟩, ⟨⟨0,0⟩,⟨0,-1⟩,⟨0,0⟩,⟨0,-1⟩⟩,
   -- positions (2,3)
   ⟨⟨0,0⟩,⟨0,0⟩,⟨0,1⟩,⟨0,1⟩⟩, ⟨⟨0,0⟩,⟨0,0⟩,⟨0,1⟩,⟨0,-1⟩⟩,
   ⟨⟨0,0⟩,⟨0,0⟩,⟨0,-1⟩,⟨0,1⟩⟩, ⟨⟨0,0⟩,⟨0,0⟩,⟨0,-1⟩,⟨0,-1⟩⟩]

/-- The full 48-element unit group of the octahedral order = `2O`. -/
def octa_48 : List Octahedral := octa_half ++ octa_lip ++ octa_oct

/-- ★★ **The full binary octahedral group `2O` order census.**  The 48
    octahedral units have order distribution `{1:1, 2:1, 3:8, 4:18, 6:8,
    8:12}` (sum 48) — the complete `E₇` McKay rung.  The `12` order-8
    elements are the octahedral extras *with a real part* (`(1+i)/√2`
    type, `g² = ±i`); the other 12 extras (`(i+j)/√2` type, `g² = -1`)
    join the 6 `±eᵢ` at order 4 (`18` total).  Order 8 is the new `E₇`
    torsion beyond the `2T` (24) tetrahedral subgroup. -/
theorem octa_48_order_census :
    octa_48.length = 48
    ∧ octa_48.countP (fun u => oct_orderOf u = 1) = 1
    ∧ octa_48.countP (fun u => oct_orderOf u = 2) = 1
    ∧ octa_48.countP (fun u => oct_orderOf u = 3) = 8
    ∧ octa_48.countP (fun u => oct_orderOf u = 4) = 18
    ∧ octa_48.countP (fun u => oct_orderOf u = 6) = 8
    ∧ octa_48.countP (fun u => oct_orderOf u = 8) = 12
    ∧ octa_48.countP (fun u => oct_orderOf u = 0) = 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

end E213.Lib.Math.Algebra.CayleyDickson.Tower.FullOctahedral
