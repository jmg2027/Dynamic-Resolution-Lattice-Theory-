import E213.Lib.Math.CayleyDickson.Tower.TypeEIcosian

/-!
# The icosian order spectrum `{1,2,3,4,5,6,10}` (the `E₈` / `2I` menu)

`TypeEIcosian` exhibits the order-5 and order-10 units `g5, g10`.  This
file completes the **order spectrum** of the icosian order `2I`: an
explicit unit of *each* binary-icosahedral order `1,2,3,4,5,6,10` —
showing `2I` realises the full McKay `E₈` torsion menu, distinct from
`2T` (`{1,2,3,4,6}`) and `2O` (`{1,2,3,4,6,8}`).

(The full 120-element per-order count census — `{1:1,2:1,3:20,4:30,5:24,
6:20,10:24}` — needs the exact even-permutation/sign enumeration of the
96 golden icosians over `ℤ[φ]` and a heavy `decide`; it is deferred.
What is proved here is that every order in the menu is realised.)
-/

namespace E213.Lib.Math.CayleyDickson.Tower.FullIcosian

open E213.Lib.Math.CayleyDickson.Tower.TypeEIcosian

/-- Element order on the icosian order (menu `{1,2,3,4,5,6,10}`). -/
def icos_orderOf (u : Icosian) : Nat :=
  if u = Icosian.one then 1
  else if u * u = Icosian.one then 2
  else if u * u * u = Icosian.one then 3
  else if u * u * u * u = Icosian.one then 4
  else if u * u * u * u * u = Icosian.one then 5
  else if u * u * u * u * u * u = Icosian.one then 6
  else if u * u * u * u * u * u * u * u * u * u = Icosian.one then 10
  else 0

/-- `-1` (scaled `⟨⟨-2,0⟩,0,0,0⟩`), order 2. -/
def icos_neg_one : Icosian := ⟨⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
/-- `i` (scaled `⟨0,2,0,0⟩`), order 4. -/
def icos_i : Icosian := ⟨⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩⟩
/-- `(-1+i+j+k)/2`, order 3. -/
def icos_w3 : Icosian := ⟨⟨-1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩⟩
/-- `(1+i+j+k)/2`, order 6. -/
def icos_w6 : Icosian := ⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩⟩

/-- ★★ **The icosian order realises the full `E₈` spectrum
    `{1,2,3,4,5,6,10}`.**  An explicit unit of each order:
    `1` (`one`), `2` (`-1`), `3` (`(-1+i+j+k)/2`), `4` (`i`),
    `5` (`g5`), `6` (`(1+i+j+k)/2`), `10` (`g10`).  Every binary-
    icosahedral order is present — the menu `2T` and `2O` do not reach
    (orders 5 and 10 are new at `E₈`). -/
theorem icosian_full_order_menu :
    icos_orderOf Icosian.one = 1
    ∧ icos_orderOf icos_neg_one = 2
    ∧ icos_orderOf icos_w3 = 3
    ∧ icos_orderOf icos_i = 4
    ∧ icos_orderOf g5 = 5
    ∧ icos_orderOf icos_w6 = 6
    ∧ icos_orderOf g10 = 10 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end E213.Lib.Math.CayleyDickson.Tower.FullIcosian
