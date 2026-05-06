import E213.Math.DyadicFSM.ArithFSM.V1to2

import E213.Math.DyadicFSM.ArithFSM
import E213.Math.DyadicFSM.ArithFSM.V1
import E213.Math.DyadicFSM.ArithFSM.V3
/-!
# ArithFSM hierarchy — algebraic degree tower

Combines `ArithFSM1.padTo2` and `ArithFSM2.padTo3` into a single
chain of bit-stream-faithful inclusions:

  ArithFSM₁ ⊂ ArithFSM₂ ⊂ ArithFSM₃

The composition `padTo2 ∘ padTo3` gives ArithFSM₁ ⊂ ArithFSM₃
directly — one less than the algebraic degree of cubic numbers.

This is the basis for the 213-native algebraic-degree definition:

  deg(bs) := minimum d such that bs ∈ ArithFSM_d

For the streams we have:
  - legendreFSM ∈ ArithFSM₁  (degree 0/1, multiplicative)
  - pellFSMmod_p ∈ ArithFSM₂ (degree 2, quadratic algebraic)
  - tribFSMmod_n ∈ ArithFSM₃ (degree 3, cubic algebraic)
-/

namespace E213.Math.DyadicFSM.ArithFSM.Hierarchy

open E213.Math.DyadicFSM.ArithFSM.V1 (ArithFSM1)
open E213.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Math.DyadicFSM.ArithFSM.V3 (ArithFSM3)


/-- Composed padding: ArithFSM₁(n) ↪ ArithFSM₃(n) via ArithFSM₂. -/
def ArithFSM1.padTo3 {n : Nat} (hn : 0 < n) (m : ArithFSM1 n) : ArithFSM3 n :=
  (m.padTo2 hn).padTo3 hn

/-- ★★★★ Composed padding preserves bit stream (1 → 2 → 3). -/
theorem padTo3_via_2_bits_eq {n : Nat} (hn : 0 < n) (m : ArithFSM1 n) (k : Nat) :
    (m.padTo3 hn).bits k = m.bits k := by
  show ((m.padTo2 hn).padTo3 hn).bits k = m.bits k
  rw [padTo3_bits_eq hn (m.padTo2 hn) k, padTo2_bits_eq hn m k]

/-- ★★★★★★ ArithFSM hierarchy: every degree-d FSM embeds into
    degree-(d+1) bit-stream-faithfully.  Combined with the existing
    period bound (5n^d) and Tier-2 hardness theorems, this yields
    the 213-native definition of algebraic degree as the *minimum
    state-space dimension* of a generating ArithFSM. -/
theorem arithFSM_hierarchy_capstone :
    -- ArithFSM₁ ↪ ArithFSM₂
    (∀ {n : Nat} (hn : 0 < n) (m : ArithFSM1 n) (k : Nat),
      (m.padTo2 hn).bits k = m.bits k)
    -- ArithFSM₂ ↪ ArithFSM₃
    ∧ (∀ {n : Nat} (hn : 0 < n) (m : ArithFSM2 n) (k : Nat),
        (m.padTo3 hn).bits k = m.bits k)
    -- ArithFSM₁ ↪ ArithFSM₃ (composition)
    ∧ (∀ {n : Nat} (hn : 0 < n) (m : ArithFSM1 n) (k : Nat),
        (m.padTo3 hn).bits k = m.bits k) :=
  ⟨@padTo2_bits_eq, @padTo3_bits_eq, @padTo3_via_2_bits_eq⟩

end E213.Math.DyadicFSM.ArithFSM.Hierarchy
