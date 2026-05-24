import E213.Lib.Math.Cohomology.CupAW.LeibnizSmall
import E213.Lib.Math.Cohomology.CupAW.LeibnizMid
import E213.Lib.Math.Cohomology.CupAW.Leibniz
import E213.Lib.Math.Cohomology.CupAW.Leibniz4Mixed
import E213.Lib.Math.Cohomology.CupAW.Leibniz21Final
import E213.Lib.Math.Cohomology.CupAW.Leibniz22Final
import E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_2
import E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_3
import E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_4
import E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.CupAW.Core
import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts

/-!
# CupAW universal-Leibniz family closure capstone

Master capstone for the 12 closed CupAW Leibniz bidegrees on
the (n, a, b) family.  Each bidegree `(n, a, b)` is proved as
the universal-`∀ α : Cochain n a, ∀ β : Cochain n b` Leibniz
identity

  `δ(α ⌣ β) = (δα) ⌣ β + α ⌣ (δβ)`

at every output face `i : Fin (binom n (a + b))`.

## Closed bidegrees

```
                  α-degree
                  1     2     3
            ┌─────────────────────
        1   │  (3,1,1) (4,1,1) (5,1,1)
        2   │  (4,1,2) (4,2,1) (4,2,2)
β-deg   3   │  (5,1,2) (5,2,1) (5,2,2)
        4   │  (5,1,3)
        5   │  (5,1,4) (5,3,1)
            └─────────────────────
```

12 closures.  Stratification by `n` (simplex dim):
  · n=3: 1 bidegree (the seed (3,1,1))
  · n=4: 4 bidegrees (1,1)(1,2)(2,1)(2,2)
  · n=5: 7 bidegrees (1,1..4)(2,1..2)(3,1)

The meta-strategy: when full ∀-pattern decide OOMs, fix α to a
basis indicator + bilinearity lift (LeibnizUniversalLift +
combine_5 / combine_10).

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.CupAW.UniversalFamilyCapstone

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.CupAW.Core (cupAW)
open E213.Lib.Math.Cohomology.Delta.Core (delta)

/-- ★★★★★★★★★★★ **CupAW universal-Leibniz family closure** —
    12 closed `(n, a, b)` bidegrees, each a `∀ α, ∀ β, ∀ i`
    universal Leibniz identity.

    The single capstone bundles all entries of the closed grid
    via the 12 corresponding universal theorems.  Stratification:
      · n=3: (1,1)
      · n=4: (1,1), (1,2), (2,1), (2,2)
      · n=5: (1,1), (1,2), (1,3), (1,4), (2,1), (2,2), (3,1)

    STRICT ∅-AXIOM. -/
theorem cupaw_universal_family_capstone :
    -- n=3 stratum
    (∀ α β : Cochain 3 1, ∀ i : Fin (binom 3 2),
      delta (cupAW 3 1 1 α β) i
        = xor (cupAW 3 2 1 (delta α) β i)
              (cupAW 3 1 2 α (delta β) i))
    -- n=4 stratum
    ∧ (∀ α β : Cochain 4 1, ∀ i : Fin (binom 4 2),
        delta (cupAW 4 1 1 α β) i
          = xor (cupAW 4 2 1 (delta α) β i)
                (cupAW 4 1 2 α (delta β) i))
    ∧ (∀ (α : Cochain 4 1) (β : Cochain 4 2), ∀ i : Fin (binom 4 3),
        delta (cupAW 4 1 2 α β) i
          = xor (cupAW 4 2 2 (delta α) β i)
                (cupAW 4 1 3 α (delta β) i))
    ∧ (∀ (α : Cochain 4 2) (β : Cochain 4 1), ∀ i : Fin (binom 4 3),
        delta (cupAW 4 2 1 α β) i
          = xor (cupAW 4 3 1 (delta α) β i)
                (cupAW 4 2 2 α (delta β) i))
    ∧ (∀ α β : Cochain 4 2, ∀ i : Fin (binom 4 4),
        delta (cupAW 4 2 2 α β) i
          = xor (cupAW 4 3 2 (delta α) β i)
                (cupAW 4 2 3 α (delta β) i))
    -- n=5 stratum
    ∧ (∀ α β : Cochain 5 1, ∀ i : Fin (binom 5 2),
        delta (cupAW 5 1 1 α β) i
          = xor (cupAW 5 2 1 (delta α) β i)
                (cupAW 5 1 2 α (delta β) i))
    ∧ (∀ (α : Cochain 5 1) (β : Cochain 5 2), ∀ i : Fin (binom 5 3),
        delta (cupAW 5 1 2 α β) i
          = xor (cupAW 5 2 2 (delta α) β i)
                (cupAW 5 1 3 α (delta β) i))
    ∧ (∀ (α : Cochain 5 1) (β : Cochain 5 3), ∀ i : Fin (binom 5 4),
        delta (cupAW 5 1 3 α β) i
          = xor (cupAW 5 2 3 (delta α) β i)
                (cupAW 5 1 4 α (delta β) i))
    ∧ (∀ (α : Cochain 5 1) (β : Cochain 5 4), ∀ i : Fin (binom 5 5),
        delta (cupAW 5 1 4 α β) i
          = xor (cupAW 5 2 4 (delta α) β i)
                (cupAW 5 1 5 α (delta β) i))
    ∧ (∀ (α : Cochain 5 2) (β : Cochain 5 1), ∀ i : Fin (binom 5 3),
        delta (cupAW 5 2 1 α β) i
          = xor (cupAW 5 3 1 (delta α) β i)
                (cupAW 5 2 2 α (delta β) i))
    ∧ (∀ α β : Cochain 5 2, ∀ i : Fin (binom 5 4),
        delta (cupAW 5 2 2 α β) i
          = xor (cupAW 5 3 2 (delta α) β i)
                (cupAW 5 2 3 α (delta β) i))
    ∧ (∀ (α : Cochain 5 3) (β : Cochain 5 1), ∀ i : Fin (binom 5 4),
        delta (cupAW 5 3 1 α β) i
          = xor (cupAW 5 4 1 (delta α) β i)
                (cupAW 5 3 2 α (delta β) i)) :=
  ⟨E213.Lib.Math.Cohomology.CupAW.LeibnizSmall.leibniz_universal_3_1_1,
   E213.Lib.Math.Cohomology.CupAW.LeibnizMid.leibniz_universal_4_1_1,
   E213.Lib.Math.Cohomology.CupAW.Leibniz4Mixed.leibniz_universal_4_1_2,
   E213.Lib.Math.Cohomology.CupAW.Leibniz4Mixed.leibniz_universal_4_2_1,
   E213.Lib.Math.Cohomology.CupAW.Leibniz4Mixed.leibniz_universal_4_2_2,
   E213.Lib.Math.Cohomology.CupAW.Leibniz.leibniz_universal_5_1_1,
   E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_2.leibniz_universal_5_1_2,
   E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_3.leibniz_universal_5_1_3,
   E213.Lib.Math.Cohomology.CupAW.Leibniz5_1_4.leibniz_universal_5_1_4,
   E213.Lib.Math.Cohomology.CupAW.Leibniz21Final.leibniz_universal_5_2_1,
   E213.Lib.Math.Cohomology.CupAW.Leibniz22Final.leibniz_universal_5_2_2,
   E213.Lib.Math.Cohomology.CupAW.Leibniz5_3_1.leibniz_universal_5_3_1⟩

end E213.Lib.Math.Cohomology.CupAW.UniversalFamilyCapstone
