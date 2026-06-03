import E213.Theory.Raw.API
import E213.Lib.Math.CayleyDickson.Tower.DiscNegTwoSkipped

/-!
# FirstSlashGrounding — the "disc −2 skip" descends to the residue's first distinguishing

The whole imported edifice ("imaginary-quadratic disc −2 is skipped between the order-4 and
order-6 axes") has a residue-native floor reached by descending the Lens tower, `ℤ`-free:

  * **Addition is the count-Lens reading of the slash** (`Raw.leaves_slash`): the residue's one
    primitive, the distinguishing `x/y`, counted by `Lens.leaves = ⟨1,1,+⟩`, *is* `+` —
    `leaves(x/y) = leaves x + leaves y`.  So `+` is not a primitive; it is the slash counted.
  * The **first distinguishing** `a/b` (the two atoms, `leaves a = leaves b = 1`) has count
    `1 + 1 = NT = 2` — the atomic count `NT` is the count-Lens reading of the first slash.
  * `NT` is a **non-square count** (`¬ ∃ m, m·m = NT`, `1² < NT < 2²`): no count squares to it.

That last `ℕ` fact — *the first distinguishing's count is non-square* — is the entire residue-native
content of "disc −2 is skipped".  Everything above it ("discriminant `t² − 4`", "imaginary
quadratic field", "elliptic SL₂ trace", "order 8 lift") is difference-Lens (`ℤ`) and number-Lens
dressing of this one count-Lens fact: `2 = leaves(a/b) = 1+1` is not `m·m` for any count `m`.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.FirstSlashGrounding

open E213.Theory (Raw)
open E213.Lib.Physics.Simplex.Counts (NT)
open E213.Lib.Math.CayleyDickson.Tower.DiscNegTwoSkipped (NT_is_nonsquare_count)

/-- ★★★ **The "disc −2 skip" descends to the residue's first distinguishing (`ℤ`-free).**  Three
    facts, each one Lens-step lower than the last:

    1. **`+` is the slash counted** — `leaves(x/y) = leaves x + leaves y` (the residue's
       distinguishing read by the count-Lens `⟨1,1,+⟩`); addition is *not* a primitive;
    2. the **first distinguishing** `a/b` counts to `1 + 1 = NT` (the atomic count `NT` *is* the
       count-Lens reading of the first slash);
    3. `NT` is a **non-square count** — `¬ ∃ m, m·m = NT` — no count squares to it.

    Fact 3 is the whole residue-native content of "disc −2 skipped": the first distinguishing's
    count is non-square.  The `ℤ`/"discriminant"/"imaginary-quadratic"/"trace" framing is the
    difference- and number-Lens dressing of this single count-Lens fact. -/
theorem disc_neg_two_descends_to_first_slash :
    (∀ (x y : Raw) (h : x ≠ y), (Raw.slash x y h).leaves = x.leaves + y.leaves)
    ∧ (Raw.a.leaves + Raw.b.leaves = NT)
    ∧ (¬ ∃ m : Nat, m * m = NT) :=
  ⟨Raw.leaves_slash, by decide, NT_is_nonsquare_count.2⟩

end E213.Lib.Math.CayleyDickson.Tower.FirstSlashGrounding
