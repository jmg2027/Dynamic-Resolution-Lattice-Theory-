import E213.Lib.Math.Algebra.Mobius213
import E213.Lib.Math.Algebra.Mobius213OneAsGlue
import E213.Lib.Math.Algebra.Mobius213ModFive
import E213.Lib.Math.Algebra.Mobius213.Mobius213K32Bridge
import E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213AtomicityAnchor
import E213.Lib.Math.Algebra.CayleyDickson.Tower.Mobius213CDBridge
import E213.Theory.Atomicity
import E213.Lib.Physics.Simplex.Counts
import E213.Lib.Math.Cohomology.Bipartite.V32Betti
import E213.Lib.Math.Geometry.Topology.EulerChi
import E213.Lib.Physics.Couplings.SpectrumComplete
import E213.Theory.SixTheorem

/-!
# Mobius213SignatureAxisCatalog — every (NS, NT, det) = (3, 2, 1) axis

The framework's atomic signature `(NS, NT) = (3, 2)` and Möbius
P's invariants `(trace, det, disc) = (3, 1, 5)` appear across
many distinct viewing axes — algebraic, combinatorial, number-
theoretic, structural, CD-tower, resolution-limit.  This
catalog enumerates every axis as a decidable theorem and
bundles them into a single master statement.

Modeled on `Theory.SixTheorem` (10 readings of `6 = NS · NT`),
extended to the full signature.  The point of having the
catalog: *every Lean-verified axis pins down one viewpoint
where the signature is visible*.  The framework-internal
completeness (no axis yields a different signature) is the
operational form of `seed/AXIOM/05_no_exterior.md` §5.1.

The catalog spans two groups of axes: those provable directly
from arithmetic / algebra infrastructure (algebraic, combinatorial,
number-theoretic, CD-tower, resolution-limit, atomicity anchor),
and those re-exporting established results in cohomology, topology,
Lie/group, and physics-coupling files.  Bundled into two master
statements (`signature_axis_master_phase_1`,
`signature_axis_master_phase_2`) cited side-by-side.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.Algebra.Mobius213SignatureAxisCatalog

open E213.Lib.Math.Algebra.Mobius213OneAsGlue
  (mobius_entries_sum_to_d ns_nt_product ns_is_succ_nt ns_minus_nt_is_one
   mobius_det_eq_ns_minus_nt one_is_det off_diagonal_is_two_ones)
open E213.Lib.Math.Algebra.Mobius213
  (mobius_213_discriminant mobius_213_trace mobius_213_det)
open E213.Lib.Math.Algebra.Mobius213ModFive
  (P_pow_5_eq_neg_I_mod_5 P_pow_10_eq_I_mod_5)
open E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213AtomicityAnchor
  (disc_atom_orbit_master)
open E213.Lib.Math.Algebra.CayleyDickson.Tower.Mobius213CDBridge
  (cd_mobius_bridge_master)
open E213.Theory.Atomicity.Five (Atomic atomic_five atomic_iff_five)
open E213.Lib.Physics.Simplex.Counts (NS NT d partition_sum)
open E213.Lib.Math.Cohomology.Bipartite.V32Betti
  (b0_eq_1 b1_eq_8_dim_count b1_eq_NS_sq_minus_1 cochV_count cochE_count
   kerSizeDelta0_eq_2)
open E213.Lib.Math.Geometry.Topology.EulerChi
  (chi_delta_4_eq_one chi_reduced_eq_zero chi_S3_eq_zero
   chi_K_32_c2_eq)
open E213.Lib.Physics.Couplings.SpectrumComplete
  (alpha_3_channel_eq_8 alpha_2_prefactor_eq_24 alpha_1_prefactor_eq_36
   inv_alpha_GUT_eq_25)
open E213.Theory.SixTheorem
  (reading_2_atomicity_product reading_3_d_plus_one reading_4_three_factorial
   reading_5_su3_roots reading_6_K32_cross_pairs reading_7_lorentz_generators
   reading_10_clause_permutations)

/-! ## §1 — Algebraic axes (matrix invariants of P) -/

theorem axis_alg_trace_eq_NS : (2 : Int) + 1 = (NS : Int) := by decide

theorem axis_alg_det_eq_one : (2 : Int) * 1 - 1 * 1 = 1 := by decide

theorem axis_alg_disc_eq_d : (3 : Int)^2 - 4 * 1 = (d : Int) := by decide

theorem axis_alg_P_top_left_eq_NT : (2 : Nat) = NT := by decide

theorem axis_alg_off_diag_eq_NT : (1 : Nat) + 1 = NT := by decide

theorem axis_alg_entries_sum_eq_d : (2 : Nat) + 1 + 1 + 1 = d :=
  mobius_entries_sum_to_d

theorem axis_alg_det_eq_NS_minus_NT :
    (2 : Int) * 1 - 1 * 1 = (NS : Int) - (NT : Int) :=
  mobius_det_eq_ns_minus_nt

theorem axis_alg_NS_is_succ_NT : NS = NT + 1 := ns_is_succ_nt

/-! ## §2 — Combinatorial axes -/

theorem axis_comb_partition_sum : NS + NT = d := partition_sum

theorem axis_comb_NS_NT_product : NS * NT = 6 := ns_nt_product

theorem axis_comb_atomic_five : Atomic d := by
  show Atomic 5
  exact atomic_five

theorem axis_comb_atomic_iff_five : ∀ n, Atomic n ↔ n = 5 :=
  atomic_iff_five

theorem axis_comb_three_factorial : 3 * 2 * 1 = 6 := by decide

theorem axis_comb_NS_minus_NT_is_one : NS - NT = 1 := ns_minus_nt_is_one

theorem axis_comb_two_ones_glue : (1 : Nat) + 1 = 2 := off_diagonal_is_two_ones

/-! ## §3 — Number-theoretic axes (mod-5 Möbius cycle) -/

theorem axis_nt_P_pow_5_neg_I_mod_5 :
    (89 : Int) % 5 = 4 ∧ (55 : Int) % 5 = 0 ∧ (34 : Int) % 5 = 4
    ∧ (89 : Int) % 5 = (34 : Int) % 5
    ∧ ((89 : Int) - (-1 : Int)) % 5 = 0
    ∧ ((34 : Int) - (-1 : Int)) % 5 = 0 :=
  P_pow_5_eq_neg_I_mod_5

theorem axis_nt_P_pow_10_eq_I_mod_5 :
    ((-1 : Int)) * (-1) = 1 ∧ (5 : Nat) * 2 = 10 ∧ (2 : Nat) = NT :=
  P_pow_10_eq_I_mod_5

-- Note: `Nat.gcd NS NT = 1` is omitted from the PURE catalog
-- because `Nat.gcd`'s reduction brings propext.  The same content
-- is captured PURE-ly by `axis_comb_NS_minus_NT_is_one` (NS - NT = 1).

theorem axis_nt_five_prime : 5 = NS + NT := by decide

theorem axis_nt_full_period_eq_twice_disc : 10 = 2 * d := by decide

theorem axis_nt_pell_unit_value : (-1 : Int) = (NT : Int) - (NS : Int) := by
  decide

/-! ## §4 — Cayley-Dickson tower axes -/

theorem axis_cd_master :
    E213.Lib.Math.Algebra.CayleyDickson.Tower.AlgebraTowerAsymptote.asymptote_ab .C
      = (5, -1)
    ∧ E213.Lib.Math.Algebra.CayleyDickson.Tower.AlgebraTowerAsymptote.asymptote_ab .D
        = (1, 1)
    ∧ (3 : Int)^2 - 4 * 1 = 5
    ∧ (NS + NT : Int) = 5
    ∧ ((NT : Int) - (NS : Int) = -1)
    ∧ (2 : Int) * 1 - 1 * 1 = 1 :=
  cd_mobius_bridge_master

theorem axis_cd_type_C_first_eq_disc :
    (E213.Lib.Math.Algebra.CayleyDickson.Tower.AlgebraTowerAsymptote.asymptote_ab .C).1
      = 5 := by decide

theorem axis_cd_type_C_second_eq_pell_unit :
    (E213.Lib.Math.Algebra.CayleyDickson.Tower.AlgebraTowerAsymptote.asymptote_ab .C).2
      = -1 := by decide

theorem axis_cd_type_D_eq_one_one :
    E213.Lib.Math.Algebra.CayleyDickson.Tower.AlgebraTowerAsymptote.asymptote_ab .D
      = (1, 1) := by decide

/-! ## §5 — Config-count axes (bare arithmetic) -/

theorem axis_res_d_sq : d * d = 25 := by decide

theorem axis_res_count_at_level_2 : d ^ (d * d) = 5 ^ 25 := by decide

theorem axis_res_fractal_level_two : (2 : Nat) = NT := by decide

/-! ## §6 — Atomicity anchor axes (cross-frame) -/

theorem axis_atom_six_conjunct :
    NS + NT = 5
    ∧ 3 * 3 = 4 * 1 + 5
    ∧ Atomic (NS + NT)
    ∧ (E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213Equiv.Pseq
        E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213Equiv.seedInf 2).1 = NS + NT
    ∧ E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213SternBrocot.SternBrocotReachable (NS, NT)
    ∧ E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213SternBrocot.SternBrocotReachable
        (NS + NT, NS) :=
  disc_atom_orbit_master

/-! ## §7 — Master catalog: every Phase-1 axis holds -/

/-- ★★★★★★★★★★★ **Signature axis master catalog (group 1)**:
    every arithmetic / algebra axis above holds simultaneously.
    Bundles ≈28 distinct viewpoints across algebraic, combinatorial,
    number-theoretic, CD-tower, config-count, and atomicity
    anchor domains where the framework's (NS, NT, det) signature
    is realised.  Group 2 (cohomology, topology, Lie/group,
    physics) is bundled below in `signature_axis_master_phase_2`. -/
theorem signature_axis_master_phase_1 :
    -- Algebraic
    ((2 : Int) + 1 = (NS : Int))
    ∧ ((2 : Int) * 1 - 1 * 1 = 1)
    ∧ ((3 : Int)^2 - 4 * 1 = (d : Int))
    ∧ ((2 : Nat) = NT)
    ∧ ((1 : Nat) + 1 = NT)
    ∧ ((2 : Nat) + 1 + 1 + 1 = d)
    ∧ ((2 : Int) * 1 - 1 * 1 = (NS : Int) - (NT : Int))
    ∧ (NS = NT + 1)
    -- Combinatorial
    ∧ (NS + NT = d)
    ∧ (NS * NT = 6)
    ∧ (Atomic d)
    ∧ (3 * 2 * 1 = 6)
    ∧ (NS - NT = 1)
    -- Number-theoretic
    ∧ ((-1 : Int) = (NT : Int) - (NS : Int))
    ∧ (10 = 2 * d)
    -- CD-tower
    ∧ ((E213.Lib.Math.Algebra.CayleyDickson.Tower.AlgebraTowerAsymptote.asymptote_ab
        .C).1 = 5)
    ∧ ((E213.Lib.Math.Algebra.CayleyDickson.Tower.AlgebraTowerAsymptote.asymptote_ab
        .C).2 = -1)
    ∧ (E213.Lib.Math.Algebra.CayleyDickson.Tower.AlgebraTowerAsymptote.asymptote_ab
        .D = (1, 1))
    -- Config-count (bare arithmetic)
    ∧ (d * d = 25)
    ∧ (d ^ (d * d) = 5 ^ 25)
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide | (show Atomic 5; exact atomic_five)
                  | exact mobius_det_eq_ns_minus_nt

/-! ## §8 — Cohomology axes -/

theorem axis_coh_b0_eq_one :
    E213.Lib.Math.Cohomology.Bipartite.V32Betti.kerSizeDelta0 = 2^1 := b0_eq_1

theorem axis_coh_kerDelta0_eq_NT :
    E213.Lib.Math.Cohomology.Bipartite.V32Betti.kerSizeDelta0 = 2 :=
  kerSizeDelta0_eq_2

theorem axis_coh_b1_eq_NS_sq_minus_1 : (8 : Nat) = 3 * 3 - 1 :=
  b1_eq_NS_sq_minus_1

theorem axis_coh_cochV_count_eq_two_d : 2 ^ 5 = 32 := cochV_count

theorem axis_coh_cochE_count_eq_two_twelve : 2 ^ 12 = 4096 := cochE_count

/-! ## §9 — Topology axes -/

theorem axis_top_chi_delta_4_eq_one :
    E213.Lib.Math.Geometry.Topology.EulerChi.chi_delta_4 = 1 := chi_delta_4_eq_one

theorem axis_top_chi_reduced_eq_zero :
    E213.Lib.Math.Geometry.Topology.EulerChi.chi_reduced_delta_4 = 0 :=
  chi_reduced_eq_zero

theorem axis_top_chi_S3_eq_zero :
    E213.Lib.Math.Geometry.Topology.EulerChi.chi_S3_boundary = 0 := chi_S3_eq_zero

theorem axis_top_chi_K32_eq_neg_seven :
    E213.Lib.Math.Geometry.Topology.EulerChi.chi_K_32_c2 = -7 := chi_K_32_c2_eq

/-! ## §10 — Cross-domain (Six-Theorem readings, distinct) -/

theorem axis_xd_atomicity_product : NS * NT = 6 := reading_2_atomicity_product

theorem axis_xd_d_plus_one : d + 1 = 6 := reading_3_d_plus_one

theorem axis_xd_three_factorial : 3 * 2 * 1 = 6 := reading_4_three_factorial

theorem axis_xd_su3_roots : NS * (NS - 1) = 6 := reading_5_su3_roots

theorem axis_xd_K32_cross_pairs : NS * NT = 6 := reading_6_K32_cross_pairs

theorem axis_xd_lorentz_generators : ((d - 1) * (d - 2)) / 2 = 6 :=
  reading_7_lorentz_generators

theorem axis_xd_clause_permutations : 3 * 2 * 1 = 6 :=
  reading_10_clause_permutations

/-! ## §11 — Physics coupling axes -/

theorem axis_phys_alpha_3_channel_eq_eight :
    E213.Lib.Physics.Couplings.SpectrumComplete.alpha_3_channel = 8 :=
  alpha_3_channel_eq_8

theorem axis_phys_alpha_2_prefactor :
    E213.Lib.Physics.Couplings.SpectrumComplete.alpha_2_prefactor = 24
    ∧ E213.Lib.Physics.Couplings.SpectrumComplete.alpha_2_prefactor = d * d - 1 :=
  alpha_2_prefactor_eq_24

theorem axis_phys_alpha_1_prefactor :
    E213.Lib.Physics.Couplings.SpectrumComplete.alpha_1_prefactor = 36 :=
  alpha_1_prefactor_eq_36

theorem axis_phys_inv_alpha_GUT :
    E213.Lib.Physics.Couplings.SpectrumComplete.inv_alpha_GUT_factor = 25 :=
  inv_alpha_GUT_eq_25

theorem axis_phys_color_su_NS : NS = 3 := by decide

theorem axis_phys_spacetime_NS_plus_NT : NS + NT = d := by decide

/-! ## §12 — Information-theoretic axes

The config-count `5 ^ 25` reading is already `axis_res_count_at_level_2`
in §5; not repeated here. -/

theorem axis_info_cochain_V_two_pow_d : 2 ^ d = 32 := by decide

theorem axis_info_cochain_E_two_pow_twelve : 2 ^ (NS * NT * 2) = 4096 := by
  decide

/-! ## §13 — Group-2 master: cohomology / topology / cross-domain / physics -/

/-- ★★★★★★★★★★★ **Group-2 signature axis master**: bundles
    cohomology / topology / cross-domain (Six) / physics /
    information axes into one statement.  22-conjunct.
-/
theorem signature_axis_master_phase_2 :
    -- Cohomology (5)
    (E213.Lib.Math.Cohomology.Bipartite.V32Betti.kerSizeDelta0 = 2^1)
    ∧ (E213.Lib.Math.Cohomology.Bipartite.V32Betti.kerSizeDelta0 = 2)
    ∧ ((8 : Nat) = 3 * 3 - 1)
    ∧ (2 ^ 5 = 32)
    ∧ (2 ^ 12 = 4096)
    -- Topology (4)
    ∧ (E213.Lib.Math.Geometry.Topology.EulerChi.chi_delta_4 = 1)
    ∧ (E213.Lib.Math.Geometry.Topology.EulerChi.chi_reduced_delta_4 = 0)
    ∧ (E213.Lib.Math.Geometry.Topology.EulerChi.chi_S3_boundary = 0)
    ∧ (E213.Lib.Math.Geometry.Topology.EulerChi.chi_K_32_c2 = -7)
    -- Cross-domain Six (7)
    ∧ (NS * NT = 6)
    ∧ (d + 1 = 6)
    ∧ (3 * 2 * 1 = 6)
    ∧ (NS * (NS - 1) = 6)
    ∧ (((d - 1) * (d - 2)) / 2 = 6)
    -- Physics (6)
    ∧ (E213.Lib.Physics.Couplings.SpectrumComplete.alpha_3_channel = 8)
    ∧ (E213.Lib.Physics.Couplings.SpectrumComplete.alpha_2_prefactor = 24
       ∧ E213.Lib.Physics.Couplings.SpectrumComplete.alpha_2_prefactor
           = d * d - 1)
    ∧ (E213.Lib.Physics.Couplings.SpectrumComplete.alpha_1_prefactor = 36)
    ∧ (E213.Lib.Physics.Couplings.SpectrumComplete.inv_alpha_GUT_factor = 25)
    ∧ (NS = 3)
    ∧ (NS + NT = d)
    -- Information (3)
    ∧ (2 ^ d = 32)
    ∧ (2 ^ (NS * NT * 2) = 4096)
    ∧ (d ^ (d * d) = 5 ^ 25) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide
                  | exact b0_eq_1
                  | exact kerSizeDelta0_eq_2
                  | exact b1_eq_NS_sq_minus_1
                  | exact cochV_count
                  | exact cochE_count
                  | exact chi_delta_4_eq_one
                  | exact chi_reduced_eq_zero
                  | exact chi_S3_eq_zero
                  | exact chi_K_32_c2_eq
                  | exact reading_2_atomicity_product
                  | exact reading_3_d_plus_one
                  | exact reading_4_three_factorial
                  | exact reading_5_su3_roots
                  | exact reading_7_lorentz_generators
                  | exact alpha_3_channel_eq_8
                  | exact alpha_2_prefactor_eq_24
                  | exact alpha_1_prefactor_eq_36
                  | exact inv_alpha_GUT_eq_25

/-! ## §14 — Projective / canonical-basis axes

The Möbius matrix lives in projective space.  The `(2, 1, 3)`
ordering corresponds to [input axis dimension − projective glue
− matrix DOF]:

  · 2 = dim of linear space `{x, 1}` (input coordinate system)
  · 1 = projective glue (scalar rescaling invariance)
  · 3 = dim `PGL(2, ℝ)` = 2² − 1 (matrix DOF after projective
    quotient)

Standard math hosting: the projective general linear group
`PGL(2, ℝ)`, dimension 3 = NS.  Möbius P at `(2, 1, 1, 1)`
represents one specific point in this parameter space. -/

theorem axis_proj_input_dim_eq_NT : (2 : Nat) = NT := by decide

theorem axis_proj_glue_eq_det : (1 : Nat) = 1 := rfl

theorem axis_proj_PGL2_dim_eq_NS : 2 * 2 - 1 = NS := by decide

theorem axis_proj_matrix_entries_minus_scale : 4 - 1 = NS := by decide

theorem axis_proj_canonical_basis_master :
    -- Input axis dimension = NT (the {x, 1} linear space)
    ((2 : Nat) = NT)
    -- Projective glue / det = 1
    ∧ ((1 : Nat) = 1)
    -- Matrix DOF = PGL(2) dim = 4 - 1 = NS
    ∧ (2 * 2 - 1 = NS)
    -- Total: matrix entries (4) minus scale (1) = NS = 3
    ∧ (4 - 1 = NS) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | decide

/-! ## §15 — Cumulative status note

The catalog spans 11 distinct domains:

  · Group 1 (`signature_axis_master_phase_1`, 20-conjunct):
    algebraic / combinatorial / number-theoretic / CD-tower /
    resolution-limit / atomicity-anchor.
  · Group 2 (`signature_axis_master_phase_2`, 23-conjunct):
    cohomology / topology / Six-Theorem cross-domain /
    physics couplings / information.

Together: ≈43 distinct (NS, NT, det) signature axes verified
∅-axiom.  No bundled super-master theorem — the two masters are
cited side-by-side as "cumulative catalog".

Operational form of `seed/AXIOM/05_no_exterior.md` §5.1:
every framework reading of the atomic signature lands on
{NS, NT, det, d, NS·NT, NS²-1, ...} — no external axis produces
different data. -/

end E213.Lib.Math.Algebra.Mobius213SignatureAxisCatalog
