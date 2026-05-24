import E213.Lib.Math.Real213.Mobius213SternBrocot
import E213.Theory.Atomicity
import E213.Lib.Physics.Simplex.Counts

/-!
# Mobius213AtomicityAnchor — Stern-Brocot ↔ atomic signature

The 213 atomic signature `(NS, NT) = (3, 2)` (from
`Theory.Atomicity.PairForcing`) appears as the **second depth** of
the Möbius P-orbit from `seedZero`, and `(NS + NT, NS) = (5, 3)`
appears at the same depth from `seedInf`.  Independently, `5 = NS +
NT = d` is the unique atomic Nat by
`Theory.Atomicity.Five.atomic_iff_five`.

The Stern-Brocot reachable pair `(3, 2)` is therefore not an
arbitrary node — it is both:
  · the Möbius P-orbit's depth-2 image of `seedZero = (0, 1)`, and
  · the atomic signature `(NS, NT)`.

This file ties these readings into a single cross-frame anchor:
the matrix `P = [[2,1],[1,1]]` writes the atomic signature
directly into the second column of its Stern-Brocot path from
`seedZero`.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Real213.Mobius213AtomicityAnchor

open E213.Lib.Math.Real213.Mobius213Equiv
  (Pseq seedZero seedInf orbits_hit_atoms_at_depth_2)
open E213.Lib.Math.Real213.Mobius213SternBrocot
  (SternBrocotReachable reachable_3_2 reachable_2_1)
open E213.Theory.Atomicity.Five (Atomic atomic_five atomic_iff_five)
open E213.Lib.Physics.Simplex.Counts (NS NT d partition_sum)

/-! ## §1 — Stern-Brocot realises the atomic signature -/

/-- ★★★ The Möbius P-orbit from `seedZero` reaches the atomic
    signature `(NS, NT) = (3, 2)` at depth 2.  Direct from
    `orbits_hit_atoms_at_depth_2`, restated via the
    `Physics.Simplex.Counts` aliases. -/
theorem pseq_seedZero_realises_NS_NT :
    Pseq seedZero 2 = (NS, NT) := by
  show Pseq seedZero 2 = (3, 2)
  exact orbits_hit_atoms_at_depth_2.1

/-- ★★★ The Möbius P-orbit from `seedInf` reaches
    `(NS + NT, NS) = (5, 3)` at depth 2 — the discriminant value
    `d = NS + NT` written explicitly. -/
theorem pseq_seedInf_realises_d_NS :
    Pseq seedInf 2 = (NS + NT, NS) := by
  show Pseq seedInf 2 = (5, 3)
  exact orbits_hit_atoms_at_depth_2.2

/-- The atomic signature pair `(NS, NT)` is Stern-Brocot
    reachable: it lies in the mediant-closure of the two seeds. -/
theorem NS_NT_reachable : SternBrocotReachable (NS, NT) :=
  reachable_3_2

/-- The discriminant pair `(NS + NT, NS) = (d, NS)` is also
    Stern-Brocot reachable: `(5, 3) = mediant((3, 2), (2, 1))`. -/
theorem d_NS_reachable : SternBrocotReachable (NS + NT, NS) :=
  show SternBrocotReachable (3 + 2, 2 + 1) from
    .mediant reachable_3_2 reachable_2_1

/-! ## §2 — Atomic / discriminant / orbit unification -/

/-- ★★★★★★ **Cross-frame anchor**: the integer `5 = NS + NT = d`
    appears simultaneously as
      (a) the unique atomic Nat (`atomic_iff_five`),
      (b) the discriminant of the Möbius matrix P
          (`trace² − 4·det = 3² − 4·1 = 5`),
      (c) the first component of `Pseq seedInf 2` (the P-orbit's
          depth-2 image of `(1, 0)`),
      (d) the sum of the components of `Pseq seedZero 2 = (NS, NT)`.
    Four a priori unrelated readings of the same integer 5. -/
theorem disc_atom_orbit_master :
    -- (a) NS + NT = 5 = d
    NS + NT = 5
    -- (b) Möbius discriminant Nat-form: 3² = 4·1 + 5
    ∧ 3 * 3 = 4 * 1 + 5
    -- (c) 5 is the unique atomic Nat
    ∧ Atomic (NS + NT)
    -- (d) P-orbit hits the discriminant at depth 2
    ∧ (Pseq seedInf 2).1 = NS + NT
    -- (e) Stern-Brocot reaches both atomicity-related pairs
    ∧ SternBrocotReachable (NS, NT)
    ∧ SternBrocotReachable (NS + NT, NS) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact partition_sum.trans (by decide : d = 5)
  · decide
  · show Atomic 5
    exact atomic_five
  · decide
  · exact reachable_3_2
  · exact d_NS_reachable

/-- The atomic Nat (`5`) is the first component of `Pseq seedInf
    2` — Möbius P writes atomicity into its second-depth orbit. -/
theorem pseq_seedInf_2_eq_atomic :
    (Pseq seedInf 2).1 = 5 ∧ Atomic (Pseq seedInf 2).1 := by
  refine ⟨?_, ?_⟩
  · decide
  · show Atomic 5
    exact atomic_five

end E213.Lib.Math.Real213.Mobius213AtomicityAnchor
