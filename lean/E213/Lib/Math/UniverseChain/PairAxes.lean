import E213.Lib.Math.UniverseChain.Decomposition
import E213.Lib.Physics.Simplex.Counts

/-!
# Step 3 — Two axes of sizes 3 and 2 (∅-axiom)

Step 2 isolates the unique alive decomposition `5 = 2 + 3`.
This step *names* the two pieces:

  * `NS = 3`  (the 3-axis: factor of size 3)
  * `NT = 2`  (the 2-axis: factor of size 2)
  * `d  = 5`  (the total: `NS + NT = d`)

The names `NS` / `NT` come from `Lib/Physics/Simplex/Counts.lean`,
which already pins them as `Nat` values.  No physics meaning is
imported here — the names are just labels for the two atomic
pieces of the unique decomposition.

The single ∅-axiom fact at this layer: **NS + NT = d**.  The
*uniqueness* statement (that the pair `(p, q) = (2, 3)` is the
only coprime pair admitting a single atomic decomposition) lives
in `Theory.Atomicity.PairForcing.lean`, which currently leaks
`propext` via `omega`.  We record only the clean `partition_sum`
identity here and treat full pair forcing as a separate (later)
∅-axiom marathon.
-/

namespace E213.Lib.Math.UniverseChain.PairAxes

open E213.Lib.Physics.Simplex.Counts (d NS NT partition_sum)

/-- ★ The 3-axis size = 3. -/
theorem three_axis_size : NS = 3 := rfl

/-- ★ The 2-axis size = 2. -/
theorem two_axis_size : NT = 2 := rfl

/-- ★ The total = 5. -/
theorem total_size : d = 5 := rfl

/-- ★★ **Step 3** core identity: `NS + NT = d` (3 + 2 = 5). -/
theorem axes_sum_eq_total : NS + NT = d := partition_sum

/-- ★ Equivalent flat form: 3 + 2 = 5. -/
theorem three_plus_two_eq_five : (3 : Nat) + 2 = 5 := rfl

/-- ★★ Bundle: the two-axis structure has sizes 3 and 2,
    summing to the total 5. -/
theorem two_axes_bundle :
    NS = 3 ∧ NT = 2 ∧ d = 5 ∧ NS + NT = d :=
  ⟨rfl, rfl, rfl, partition_sum⟩

end E213.Lib.Math.UniverseChain.PairAxes
