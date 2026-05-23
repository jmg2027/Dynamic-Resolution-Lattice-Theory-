import E213.Lib.Math.AkbulutCork.Foundation
import E213.Lib.Math.AkbulutCork.Twist
import E213.Lib.Math.AkbulutCork.SignedOrbits
import E213.Lib.Math.AkbulutCork.CorkTheorem
import E213.Lib.Math.AkbulutCork.HigherTwist

/-!
# AkbulutCork — umbrella

213-native realization of the Akbulut–Curtis–Freedman–Hsiang–Stong
cork theorem for closed simply-connected 4-manifolds.

`Cork213` data type with contractible_b1, boundary_size,
twist_parity fields; M_S01 = Z/2 cork-twist endomorphism;
signed orbit count `+4` as the 213-internal exotic-structure
witness; cork-embedding + cork-uniqueness capstones.

See `AkbulutCork/INDEX.md` for the file-by-file map and
`theory/math/exotic_4mfd_cork.md` for the narrative.
-/
