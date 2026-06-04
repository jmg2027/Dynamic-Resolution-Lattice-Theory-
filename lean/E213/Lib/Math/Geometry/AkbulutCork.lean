import E213.Lib.Math.Geometry.AkbulutCork.Foundation
import E213.Lib.Math.Geometry.AkbulutCork.Twist
import E213.Lib.Math.Geometry.AkbulutCork.SignedOrbits
import E213.Lib.Math.Geometry.AkbulutCork.CorkTheorem
import E213.Lib.Math.Geometry.AkbulutCork.HigherTwist
import E213.Lib.Math.Geometry.AkbulutCork.H3Twist
import E213.Lib.Math.Geometry.AkbulutCork.MultiCork
import E213.Lib.Math.Geometry.AkbulutCork.CrossFrame

/-!
# AkbulutCork — umbrella

213-native realization of the Akbulut–Curtis–Freedman–Hsiang–Stong
cork theorem for closed simply-connected 4-manifolds.

`Cork213` data type with contractible_b1, boundary_size,
twist_parity fields; M_S01 = Z/2 cork-twist endomorphism;
signed orbit count `+4` as the 213-internal exotic-structure
witness; cork-embedding + cork-uniqueness capstones.

See `AkbulutCork/INDEX.md` for the file-by-file map and
`theory/math/geometry/exotic_4mfd_cork.md` for the narrative.
-/
