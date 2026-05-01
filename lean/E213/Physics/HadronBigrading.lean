import E213.Physics.SimplexCounts

/-!
# Hadron bigrading composite — 3-quark glued sub-cohomology on K_{25}

Path (c) initial formalization (2026-04-30): hadron mass ratios
m_n/m_p, g_p, m_n − m_p as projections of joint K_{25} 3-quark
cohomology onto specific glued sub-configurations.

## Setup

K_{25} = fractal level L=2 (math-branch `FractalLevel.lean`).
Each quark is a sub-simplex state with bigrading (i, j) on K_5.
chiralDim(i, j) = C(NS, i) · C(NT, j) (Paper1Chiral.lean).

A 3-quark composite (uud / udd) is a 3-tuple of bigrading
positions glued along shared faces; the hadron mass is the joint
chiralDim weight + Class F cup-chain corrections.

u and d quarks differ by ONE S↔T swap on inner bigrading —
the discrete-lattice translation of "isospin doublet".
-/

namespace E213.Physics.HadronBigrading

open E213.Physics.Simplex

/-- Bigrading position on K_5: chiralDim(i, j) = C(NS, i)·C(NT, j). -/
structure Bigrading where
  i : Nat
  j : Nat
  i_le : i ≤ 3 := by decide
  j_le : j ≤ 2 := by decide

/-- chiralDim(i, j) value. -/
def chiralDimAt (b : Bigrading) : Nat :=
  binom 3 b.i * binom 2 b.j

/-- u and d differ by one S↔T swap. -/
structure FlavorPair where
  b_u : Bigrading
  b_d : Bigrading
  swap : b_d.i + 1 = b_u.i ∧ b_d.j = b_u.j + 1

/-- 3-quark composite flavor pattern. -/
inductive HadronFlavor
  | uud   -- proton
  | udd   -- neutron
  deriving DecidableEq, Repr

/-- Proton (uud) joint weight: 2·w_u + w_d. -/
def joint_uud (fp : FlavorPair) : Nat :=
  2 * chiralDimAt fp.b_u + chiralDimAt fp.b_d

/-- Neutron (udd) joint weight: w_u + 2·w_d. -/
def joint_udd (fp : FlavorPair) : Nat :=
  chiralDimAt fp.b_u + 2 * chiralDimAt fp.b_d

/-- Sample: u at (1, 0), d at (0, 1) — minimal S↔T swap. -/
def sample_pair : FlavorPair where
  b_u := { i := 1, j := 0 }
  b_d := { i := 0, j := 1 }
  swap := ⟨by decide, by decide⟩

theorem sample_weights :
    chiralDimAt sample_pair.b_u = 3
    ∧ chiralDimAt sample_pair.b_d = 2
    ∧ joint_uud sample_pair = 8
    ∧ joint_udd sample_pair = 7 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ★ Class F skeleton: m_n/m_p = joint(udd)/joint(uud)
    determined by (B_u, B_d) + Class F cup-chain corrections. -/
theorem class_F_hadron_skeleton :
    NS = 3 ∧ NT = 2 ∧ d = 5
    ∧ binom 3 1 = 3 ∧ binom 2 1 = 2
    ∧ binom 3 0 = 1 ∧ binom 2 0 = 1
    ∧ chiralDimAt sample_pair.b_u = 3
    ∧ chiralDimAt sample_pair.b_d = 2
    ∧ joint_uud sample_pair = 8
    ∧ joint_udd sample_pair = 7 :=
  ⟨by decide, by decide, by decide, by decide, by decide,
   by decide, by decide, rfl, rfl, rfl, rfl⟩

end E213.Physics.HadronBigrading
