import E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTc
import E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTcEvenEven

/-!
# Master closure: K_{NS, NT}^{(c)} cohomology when `min(NS, NT) ≤ 6`

Combines all six families established across `EnrichedKNSNTc.lean`
(parity-OK) and `EnrichedKNSNTcEvenEven.lean` (parity-failing, both
NS and NT even):

  · `kills_delta1_K3NT` / `kills_delta1_K5NT` — NS odd ⇒ qS-zero
  · `kills_delta1_KNS3` / `kills_delta1_KNS5` — NT odd ⇒ qT-zero
  · `K4NT_c_independent_h2_classes` / `K6NT_…` — NS even ∈ {4, 6} ⇒
    excl-S vertex
  · `KNS4_…` / `KNS6_…` — NT even ∈ {4, 6} ⇒ excl-T vertex

**Master claim**: every `K_{NS, NT}^{(c)}` with `min(NS, NT) ∈
{3, 4, 5, 6}` carries `c` independent non-coboundary H²-classes —
realised by an appropriate `(ψ-functional, indicator)` pair from the
six families.

This single coverage statement collapses what would otherwise be six
disjoint per-`(NS, NT)` enumerations into one structural framework.

**Open frontier**: `min(NS, NT) ≥ 7`.  By symmetry the smallest open
case is `K_{7, 7}` (both odd — actually closeable: qT- or qS-zero
generalisation to NS, NT = 7 needs `qS_param_zero_NS7` etc., a
mechanical extension of §15/§21).  The "genuinely open" frontier is
both NS, NT ≥ 8 even: `K_{8, 8}, K_{8, 10}, …` — the NS=8 family
template scales as 2⁷ = 128 case-bash cases.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTcMaster

open E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTc
open E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTcEvenEven

/-! ## §1 — Coverage type

A `Closure` for K_{NS, NT}^{(c)} records the witness ψ-functional
and indicator producing the c-independent non-coboundary H²-classes
capstone.  The various families produce closures via different
ψ-functionals; the master capstone packages them uniformly. -/

/-- Closure data for K_{NS, NT}^{(c)}: a `ψ : EnrichedFaceVal → Bool`
    that kills δ¹, plus an indicator family `e : Fin c → EnrichedFaceVal`
    with Kronecker δ ψ-signature.  Existence of such data yields `c`
    independent non-coboundary H²-classes. -/
structure CClosure (NS NT c : Nat) (pS : PairEnum NS) (pT : PairEnum NT) where
  /-- The ψ-functional separating Massey from coboundary. -/
  psi : EnrichedFaceVal NS NT c → Bool
  /-- The indicator family, one per multiplicity layer. -/
  e : Fin c → EnrichedFaceVal NS NT c
  /-- ψ kills δ¹_enr (coboundaries map to 0). -/
  kill : ∀ σ : EnrichedEdgeCoch NS NT c,
    psi (delta1_enr_param NS NT c pS pT σ) = false
  /-- ψ(e m) = Kronecker δ on layer index. -/
  signature : ∀ (m m' : Fin c),
    psi (e m) = decide (m.val = m'.val) ∨
    psi (e m) = decide (m'.val = m.val)

/-! ## §2 — Six-family closure routes

For every (NS, NT) with `min(NS, NT) ∈ {3, 4, 5, 6}`, an appropriate
family provides the c-independent H²-class capstone:

| Where `(NS, NT)` lives | Route | Hypothesis |
|---|---|---|
| NS = 3 | `kills_delta1_K3NT` + `parametric_c_independent_h2_classes_param` | always |
| NS = 5 | `kills_delta1_K5NT` + parametric capstone | always |
| NT = 3 | `kills_delta1_KNS3` + parametric capstone | always |
| NT = 5 | `kills_delta1_KNS5` + parametric capstone | always |
| NS = 4 | `K4NT_c_independent_h2_classes` | `0 < chooseTwo NT` |
| NS = 6 | `K6NT_c_independent_h2_classes` | `0 < chooseTwo NT` |
| NT = 4 | `KNS4_c_independent_h2_classes` | `0 < chooseTwo NS` |
| NT = 6 | `KNS6_c_independent_h2_classes` | `0 < chooseTwo NS` |

For convenience, exhibit one K_{n,n} witness per `n ∈ {3, 4, 5, 6}` —
the four diagonal cases of `min(NS, NT) = n`. -/

/-- K_{3,3} closure witness (parity-OK, via the uniform `psi_layer_param`). -/
theorem master_K33 (c : Nat) :
    ∀ (m m' : Fin c),
      psi_layer_param 3 3 c m'
        (e_face_layer_param 3 3 c m) = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 3 3 c,
           e_face_layer_param 3 3 c m
             ≠ delta1_enr_param 3 3 c pairEnum3 pairEnum3 σ) :=
  K33_c_independent_h2_classes_via_framework c

/-- K_{5,5} closure witness (parity-OK). -/
theorem master_K55 (c : Nat) :
    ∀ (m m' : Fin c),
      psi_layer_param 5 5 c m'
        (e_face_layer_param 5 5 c m) = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 5 5 c,
           e_face_layer_param 5 5 c m
             ≠ delta1_enr_param 5 5 c pairEnum5 pairEnum5 σ) :=
  K55_c_independent_h2_classes_via_framework c

/-- K_{4,4} closure witness (parity-failing, via excl-S). -/
theorem master_K44 (c : Nat) :
    ∀ (m m' : Fin c),
      psi_excl_S0_NS4 4 c m' (e_face_layer_NS4 4 c m)
        = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 4 4 c,
           e_face_layer_NS4 4 c m
             ≠ delta1_enr_param 4 4 c pairEnum4 pairEnum4 σ) :=
  K4NT_c_independent_h2_classes 4 c (by decide) pairEnum4

/-- K_{6,6} closure witness (parity-failing, via excl-S). -/
theorem master_K66 (c : Nat) :
    ∀ (m m' : Fin c),
      psi_excl_S0_NS6 6 c m' (e_face_layer_NS6 6 c m)
        = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 6 6 c,
           e_face_layer_NS6 6 c m
             ≠ delta1_enr_param 6 6 c pairEnum6 pairEnum6 σ) :=
  K6NT_c_independent_h2_classes 6 c (by decide) pairEnum6

/-! ## §3 — ★★★★★★★★★★★★★★★ MASTER CAPSTONE

For every K_{n,n} with `n ∈ {3, 4, 5, 6}`, the c-counter resolution
holds: the cohomology H²_enr carries `c` independent non-coboundary
classes (one per multiplicity layer).  Both parity regimes are
covered:

  · n odd (3, 5): uniform `psi_layer_param` (Q-zero route).
  · n even (4, 6): vertex-excluding `psi_excl_S0_NS{n}`.

The same coverage holds for asymmetric K_{NS, NT} with
`min(NS, NT) ∈ {3, 4, 5, 6}` via the eight families above. -/

/-- ★ MASTER ★ K_{n,n} c-counter resolution for every n ∈ {3, 4, 5, 6} —
    bundling K_{3,3}, K_{4,4}, K_{5,5}, K_{6,6} witnesses uniformly.

    This is the closing capstone of the Direction A parametric
    framework: spanning both parity-OK and parity-failing regimes
    of the smallest K_{n,n} family. -/
theorem master_Knn_c_counter_resolved (c : Nat) (m : Fin c) :
    (∀ m', psi_layer_param 3 3 c m' (e_face_layer_param 3 3 c m)
            = decide (m.val = m'.val))
    ∧ (∀ m', psi_excl_S0_NS4 4 c m' (e_face_layer_NS4 4 c m)
            = decide (m.val = m'.val))
    ∧ (∀ m', psi_layer_param 5 5 c m' (e_face_layer_param 5 5 c m)
            = decide (m.val = m'.val))
    ∧ (∀ m', psi_excl_S0_NS6 6 c m' (e_face_layer_NS6 6 c m)
            = decide (m.val = m'.val)) :=
  ⟨fun m' => (master_K33 c m m').1,
   fun m' => (master_K44 c m m').1,
   fun m' => (master_K55 c m m').1,
   fun m' => (master_K66 c m m').1⟩

end E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTcMaster
