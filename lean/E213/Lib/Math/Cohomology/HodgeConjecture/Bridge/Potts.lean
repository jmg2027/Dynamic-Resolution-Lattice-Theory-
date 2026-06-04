import E213.Lib.Math.Cohomology.HodgeConjecture.Bridge.Ising

import E213.Lib.Math.Cohomology.HodgeConjecture.Bridge.PhaseRouting
import E213.Lib.Physics.Simplex.Counts
/-!
# Potts (q=3) model on K_5 in 213-native form

Generalizes Ising²¹³ from Bool spins (q=2) to `Fin 3` spins (q=3),
keeping the K_5 lattice (5 sites, all 10 pairs as edges).  The
routing language is unchanged — only the spin alphabet and energy
spectrum widen.

Energy E(σ) := # disagreeing K_5 edges (Kronecker-δ form):
  if σ_i = σ_j the edge contributes 0; else 1.

Energy spectrum on K_5 q=3 is determined by the color partition
(n₀, n₁, n₂) with n₀+n₁+n₂ = 5.  Five partition shapes give five
discrete energy levels:

  · (5,0,0)  → E = 0  ground states (3 color-permutation copies)
  · (4,1,0)  → E = 4  count = 3·2·5 = 30
  · (3,2,0)  → E = 6  count = 3·2·binom(5,3) = 60
  · (3,1,1)  → E = 7  count = 3·binom(5,3)·2 = 60
  · (2,2,1)  → E = 8  count = 3·5·binom(4,2) = 90

Total = 3 + 30 + 60 + 60 + 90 = 243 = 3⁵.  Z/3 symmetry breaking
splits the 3 ground states into three coexisting σ-routes.

STRICT ∅-AXIOM by `decide`.
-/

namespace E213.Lib.Math.Cohomology.HodgeConjecture.Bridge.Potts

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.HodgeConjecture.Bridge.PhaseRouting (Route)

/-! §1  q=3 spin lattice on K_5. -/

abbrev Spin : Type := Fin 5 → Fin 3

def mkSpin (a b c d e : Fin 3) : Spin
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d
  | _      => e

/-! §2  Edge disagreement (Kronecker delta) and total energy. -/

def disagree (σ : Spin) (i j : Fin 5) : Nat :=
  if (σ i).val = (σ j).val then 0 else 1

def energy (σ : Spin) : Nat :=
  disagree σ ⟨0, by decide⟩ ⟨1, by decide⟩
  + disagree σ ⟨0, by decide⟩ ⟨2, by decide⟩
  + disagree σ ⟨0, by decide⟩ ⟨3, by decide⟩
  + disagree σ ⟨0, by decide⟩ ⟨4, by decide⟩
  + disagree σ ⟨1, by decide⟩ ⟨2, by decide⟩
  + disagree σ ⟨1, by decide⟩ ⟨3, by decide⟩
  + disagree σ ⟨1, by decide⟩ ⟨4, by decide⟩
  + disagree σ ⟨2, by decide⟩ ⟨3, by decide⟩
  + disagree σ ⟨2, by decide⟩ ⟨4, by decide⟩
  + disagree σ ⟨3, by decide⟩ ⟨4, by decide⟩

/-! §3  Representative configurations at each level. -/

abbrev c0 : Fin 3 := ⟨0, by decide⟩
abbrev c1 : Fin 3 := ⟨1, by decide⟩
abbrev c2 : Fin 3 := ⟨2, by decide⟩

def color0    : Spin := mkSpin c0 c0 c0 c0 c0
def color1    : Spin := mkSpin c1 c1 c1 c1 c1
def color2    : Spin := mkSpin c2 c2 c2 c2 c2
def s_4_1_0   : Spin := mkSpin c0 c0 c0 c0 c1   -- (4,1,0)
def s_3_2_0   : Spin := mkSpin c0 c0 c0 c1 c1   -- (3,2,0)
def s_3_1_1   : Spin := mkSpin c0 c0 c0 c1 c2   -- (3,1,1)
def s_2_2_1   : Spin := mkSpin c0 c0 c1 c1 c2   -- (2,2,1)

/-! §4  Z/3 cyclic colour rotation: c0 → c1 → c2 → c0. -/

def rotate (s : Fin 3) : Fin 3 := match s with
  | ⟨0, _⟩ => c1 | ⟨1, _⟩ => c2 | _ => c0

def rotateSpin (σ : Spin) : Spin := fun i => rotate (σ i)

/-! §5  Energy-level multiplicities on K_5 q=3 Potts: {3, 30, 60, 60, 90}. -/

def levelMult (E : Nat) : Nat :=
  if E = 0 then 3
  else if E = 4 then 30
  else if E = 6 then 60
  else if E = 7 then 60
  else if E = 8 then 90
  else 0

/-! §6  Partition function as Nat polynomial Z(t) = Σ mult·t^E. -/

def Z (t : Nat) : Nat :=
  3 + 30 * t^4 + 60 * t^6 + 60 * t^7 + 90 * t^8

/-! §7  Routing on Potts trajectory: Z/3 ground split + cumulative routes. -/

def routeGround_0 : Nat := 1   -- {color0}
def routeGround_1 : Nat := 1   -- {color1}
def routeGround_2 : Nat := 1   -- {color2}

def routeUpTo (E_max : Nat) : Nat :=
  (List.range (E_max + 1)).foldl (fun acc E => acc + levelMult E) 0

/-! §10  ★★★★★ Potts²¹³ on K_5 q=3 capstone — STRICT ∅-AXIOM. -/

theorem potts_213_capstone :
    -- Energy values across the 5 partition shapes
    energy color0 = 0 ∧ energy color1 = 0 ∧ energy color2 = 0
    ∧ energy s_4_1_0 = 4 ∧ energy s_3_2_0 = 6
    ∧ energy s_3_1_1 = 7 ∧ energy s_2_2_1 = 8
    -- Z/3 cyclic rotation preserves energy (point + energy witnesses)
    ∧ rotateSpin color0 ⟨0, by decide⟩ = color1 ⟨0, by decide⟩
    ∧ energy (rotateSpin color0) = energy color1
    ∧ energy (rotateSpin s_4_1_0) = energy s_4_1_0
    -- Level multiplicities sum to 3⁵
    ∧ levelMult 0 = 3 ∧ levelMult 4 = 30
    ∧ levelMult 6 = 60 ∧ levelMult 7 = 60 ∧ levelMult 8 = 90
    ∧ levelMult 0 + levelMult 4 + levelMult 6 + levelMult 7 + levelMult 8 = 243
    ∧ (243 : Nat) = 3 ^ 5
    -- Partition function values
    ∧ Z 0 = 3 ∧ Z 1 = 243
    ∧ Z 2 = 3 + 30*16 + 60*64 + 60*128 + 90*256
    -- Cumulative routing values
    ∧ routeUpTo 0 = 3 ∧ routeUpTo 3 = 3
    ∧ routeUpTo 4 = 33 ∧ routeUpTo 5 = 33
    ∧ routeUpTo 6 = 93 ∧ routeUpTo 7 = 153
    ∧ routeUpTo 8 = 243
    -- at exactly the 4 energy levels {4, 6, 7, 8}
    ∧ routeUpTo 3 ≠ routeUpTo 4 ∧ routeUpTo 5 ≠ routeUpTo 6
    ∧ routeUpTo 6 ≠ routeUpTo 7 ∧ routeUpTo 7 ≠ routeUpTo 8
    -- stable bands
    ∧ routeUpTo 0 = routeUpTo 3 ∧ routeUpTo 4 = routeUpTo 5
    ∧ routeUpTo 8 = routeUpTo 10
    -- Z/3 ground-state route partition (vs Ising's Z/2)
    ∧ routeGround_0 + routeGround_1 + routeGround_2 = levelMult 0
    -- Bridge: full route = q^N = 3^5
    ∧ routeUpTo 8 = 3 ^ 5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.Cohomology.HodgeConjecture.Bridge.Potts
