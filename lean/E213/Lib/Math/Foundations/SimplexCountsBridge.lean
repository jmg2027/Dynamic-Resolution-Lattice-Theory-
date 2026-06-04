import E213.Lib.Physics.Simplex.Counts

/-!
# Math ↔ Physics bridge: Simplex counts

Math-side shim for `E213.Lib.Physics.Simplex.Counts`.
Keeps cross-context import discoverable through a `*Bridge*.lean`
module while exposing the same constants/functions to Math files.
-/

namespace E213.Lib.Math.Foundations.SimplexCountsBridge

abbrev NS : Nat := E213.Lib.Physics.Simplex.Counts.NS
abbrev NT : Nat := E213.Lib.Physics.Simplex.Counts.NT
abbrev d  : Nat := E213.Lib.Physics.Simplex.Counts.d
abbrev binom : Nat → Nat → Nat := E213.Lib.Physics.Simplex.Counts.binom

end E213.Lib.Math.Foundations.SimplexCountsBridge

