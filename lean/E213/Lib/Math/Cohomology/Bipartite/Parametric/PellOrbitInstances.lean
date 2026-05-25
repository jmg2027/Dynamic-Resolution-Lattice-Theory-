import E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTc
import E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTcEvenEven

/-!
# Pell-orbit Stern-Brocot extension: K_{7, 4}, K_{8, 5}, K_{5, 4}

★★★★★★★★★★★★★★★ **Direction A transports to the next
Stern-Brocot mediant layer.** ★★★★★★★★★★★★★★★

The existing `master_Knn_c_counter_resolved` covers the four diagonal
K_{n, n}^{(c)} for `n ∈ {3, 4, 5, 6}` plus asymmetric instances via
the `K3NT / K5NT / KNS3 / KNS4 / KNS5 / KNS6` families (NS or NT in
{3, 5} odd, or {4, 6} even).

Stern-Brocot mediants `(2, 1) + (3, 2) = (5, 3)`, `(3, 2) + (5, 3) =
(8, 5)`, `(1, 1) + (3, 2) = (4, 3)`, etc., produce K_{NS, NT}^{(c)}
witnesses at every Stern-Brocot position.  This file instantiates the
universal framework at **(5, 4), (7, 4), (8, 5)** — three positions
on the next Stern-Brocot layer beyond the n ∈ {3, 4, 5, 6} diagonal:

  · **K_{5, 4}** — already closed via `K54_c_independent_h2_classes_via_framework`
    (NT=4 even, KNS4 family).  Re-exported here for symmetry.
  · **K_{8, 5}** — NT=5 odd, KNS5 family.  Requires `pairEnum8`
    (no `IsLexFold` needed on the NS=8 side because the NT=5 route
    cancels at the NT level).
  · **K_{7, 4}** — NT=4 even, KNS4 excl-T family.  Requires `pairEnum7`
    (NS=7 odd, any PairEnum 7 works since the family is NS-agnostic).

The Pell-orbit position **(13, 8)** has min(NS, NT) = 8: both
NS = 13 (odd, ∉ {3, 5} so qS-zero needs §6 universal extension to
n = 13) and NT = 8 (even, ∉ {4, 6} so excl-T needs a fresh §13 NT=8
analogue).  Both routes are mechanical extensions of existing
patterns but require additional pairEnum13 + IsLexFold or
psi_excl_T0_NT8 + 28-fold XOR cancellation.  Tracked as the next
extension target.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.Parametric.PellOrbitInstances

open E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTc
open E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTcEvenEven

/-! ## §1 — Concrete pair enumeration on `Fin 7`

`chooseTwo 7 = 21` pairs in lex order:
`(0,1), (0,2), …, (0,6), (1,2), …, (1,6), (2,3), …, (2,6),
 (3,4), (3,5), (3,6), (4,5), (4,6), (5,6)`. -/

/-- Low endpoint of the `s`-th pair of `Fin 7` (21 pairs lex). -/
def pair7_lo : Fin (chooseTwo 7) → Fin 7
  | ⟨0,  _⟩ => ⟨0, by decide⟩ | ⟨1,  _⟩ => ⟨0, by decide⟩
  | ⟨2,  _⟩ => ⟨0, by decide⟩ | ⟨3,  _⟩ => ⟨0, by decide⟩
  | ⟨4,  _⟩ => ⟨0, by decide⟩ | ⟨5,  _⟩ => ⟨0, by decide⟩
  | ⟨6,  _⟩ => ⟨1, by decide⟩ | ⟨7,  _⟩ => ⟨1, by decide⟩
  | ⟨8,  _⟩ => ⟨1, by decide⟩ | ⟨9,  _⟩ => ⟨1, by decide⟩
  | ⟨10, _⟩ => ⟨1, by decide⟩
  | ⟨11, _⟩ => ⟨2, by decide⟩ | ⟨12, _⟩ => ⟨2, by decide⟩
  | ⟨13, _⟩ => ⟨2, by decide⟩ | ⟨14, _⟩ => ⟨2, by decide⟩
  | ⟨15, _⟩ => ⟨3, by decide⟩ | ⟨16, _⟩ => ⟨3, by decide⟩
  | ⟨17, _⟩ => ⟨3, by decide⟩
  | ⟨18, _⟩ => ⟨4, by decide⟩ | ⟨19, _⟩ => ⟨4, by decide⟩
  | ⟨_+20, _⟩ => ⟨5, by decide⟩

/-- High endpoint of the `s`-th pair of `Fin 7`. -/
def pair7_hi : Fin (chooseTwo 7) → Fin 7
  | ⟨0,  _⟩ => ⟨1, by decide⟩ | ⟨1,  _⟩ => ⟨2, by decide⟩
  | ⟨2,  _⟩ => ⟨3, by decide⟩ | ⟨3,  _⟩ => ⟨4, by decide⟩
  | ⟨4,  _⟩ => ⟨5, by decide⟩ | ⟨5,  _⟩ => ⟨6, by decide⟩
  | ⟨6,  _⟩ => ⟨2, by decide⟩ | ⟨7,  _⟩ => ⟨3, by decide⟩
  | ⟨8,  _⟩ => ⟨4, by decide⟩ | ⟨9,  _⟩ => ⟨5, by decide⟩
  | ⟨10, _⟩ => ⟨6, by decide⟩
  | ⟨11, _⟩ => ⟨3, by decide⟩ | ⟨12, _⟩ => ⟨4, by decide⟩
  | ⟨13, _⟩ => ⟨5, by decide⟩ | ⟨14, _⟩ => ⟨6, by decide⟩
  | ⟨15, _⟩ => ⟨4, by decide⟩ | ⟨16, _⟩ => ⟨5, by decide⟩
  | ⟨17, _⟩ => ⟨6, by decide⟩
  | ⟨18, _⟩ => ⟨5, by decide⟩ | ⟨19, _⟩ => ⟨6, by decide⟩
  | ⟨_+20, _⟩ => ⟨6, by decide⟩

/-- Concrete `PairEnum 7` (21 pairs in lex order). -/
def pairEnum7 : PairEnum 7 where
  lo := pair7_lo
  hi := pair7_hi

/-! ## §2 — Concrete pair enumeration on `Fin 8`

`chooseTwo 8 = 28` pairs in lex order:
`(0,1)…(0,7), (1,2)…(1,7), (2,3)…(2,7), (3,4)…(3,7),
 (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)`. -/

/-- Low endpoint of the `s`-th pair of `Fin 8` (28 pairs lex). -/
def pair8_lo : Fin (chooseTwo 8) → Fin 8
  | ⟨0,  _⟩ => ⟨0, by decide⟩ | ⟨1,  _⟩ => ⟨0, by decide⟩
  | ⟨2,  _⟩ => ⟨0, by decide⟩ | ⟨3,  _⟩ => ⟨0, by decide⟩
  | ⟨4,  _⟩ => ⟨0, by decide⟩ | ⟨5,  _⟩ => ⟨0, by decide⟩
  | ⟨6,  _⟩ => ⟨0, by decide⟩
  | ⟨7,  _⟩ => ⟨1, by decide⟩ | ⟨8,  _⟩ => ⟨1, by decide⟩
  | ⟨9,  _⟩ => ⟨1, by decide⟩ | ⟨10, _⟩ => ⟨1, by decide⟩
  | ⟨11, _⟩ => ⟨1, by decide⟩ | ⟨12, _⟩ => ⟨1, by decide⟩
  | ⟨13, _⟩ => ⟨2, by decide⟩ | ⟨14, _⟩ => ⟨2, by decide⟩
  | ⟨15, _⟩ => ⟨2, by decide⟩ | ⟨16, _⟩ => ⟨2, by decide⟩
  | ⟨17, _⟩ => ⟨2, by decide⟩
  | ⟨18, _⟩ => ⟨3, by decide⟩ | ⟨19, _⟩ => ⟨3, by decide⟩
  | ⟨20, _⟩ => ⟨3, by decide⟩ | ⟨21, _⟩ => ⟨3, by decide⟩
  | ⟨22, _⟩ => ⟨4, by decide⟩ | ⟨23, _⟩ => ⟨4, by decide⟩
  | ⟨24, _⟩ => ⟨4, by decide⟩
  | ⟨25, _⟩ => ⟨5, by decide⟩ | ⟨26, _⟩ => ⟨5, by decide⟩
  | ⟨_+27, _⟩ => ⟨6, by decide⟩

/-- High endpoint of the `s`-th pair of `Fin 8`. -/
def pair8_hi : Fin (chooseTwo 8) → Fin 8
  | ⟨0,  _⟩ => ⟨1, by decide⟩ | ⟨1,  _⟩ => ⟨2, by decide⟩
  | ⟨2,  _⟩ => ⟨3, by decide⟩ | ⟨3,  _⟩ => ⟨4, by decide⟩
  | ⟨4,  _⟩ => ⟨5, by decide⟩ | ⟨5,  _⟩ => ⟨6, by decide⟩
  | ⟨6,  _⟩ => ⟨7, by decide⟩
  | ⟨7,  _⟩ => ⟨2, by decide⟩ | ⟨8,  _⟩ => ⟨3, by decide⟩
  | ⟨9,  _⟩ => ⟨4, by decide⟩ | ⟨10, _⟩ => ⟨5, by decide⟩
  | ⟨11, _⟩ => ⟨6, by decide⟩ | ⟨12, _⟩ => ⟨7, by decide⟩
  | ⟨13, _⟩ => ⟨3, by decide⟩ | ⟨14, _⟩ => ⟨4, by decide⟩
  | ⟨15, _⟩ => ⟨5, by decide⟩ | ⟨16, _⟩ => ⟨6, by decide⟩
  | ⟨17, _⟩ => ⟨7, by decide⟩
  | ⟨18, _⟩ => ⟨4, by decide⟩ | ⟨19, _⟩ => ⟨5, by decide⟩
  | ⟨20, _⟩ => ⟨6, by decide⟩ | ⟨21, _⟩ => ⟨7, by decide⟩
  | ⟨22, _⟩ => ⟨5, by decide⟩ | ⟨23, _⟩ => ⟨6, by decide⟩
  | ⟨24, _⟩ => ⟨7, by decide⟩
  | ⟨25, _⟩ => ⟨6, by decide⟩ | ⟨26, _⟩ => ⟨7, by decide⟩
  | ⟨_+27, _⟩ => ⟨7, by decide⟩

/-- Concrete `PairEnum 8` (28 pairs in lex order). -/
def pairEnum8 : PairEnum 8 where
  lo := pair8_lo
  hi := pair8_hi

/-! ## §3 — K_{5, 4}: NT=4 even, KNS4 family (already closed; re-exported)

`K54_c_independent_h2_classes_via_framework` lives in
`EnrichedKNSNTc.lean` §22 via the NT=5 odd route.  Equivalent witness
through the KNS4 excl-T route is shown here for symmetry. -/

/-- K_{5, 4}^{(c)} c-counter via the NT=4 even KNS4 family. -/
theorem K54_via_KNS4 (c : Nat) :
    ∀ (m m' : Fin c),
      psi_excl_T0_NT4 5 c m' (e_face_layer_NT4 5 c m)
        = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 5 4 c,
           e_face_layer_NT4 5 c m
             ≠ delta1_enr_param 5 4 c pairEnum5 pairEnum4 σ) :=
  KNS4_c_independent_h2_classes 5 c (by decide) pairEnum5

/-! ## §4 — K_{8, 5}: NT=5 odd via `kills_delta1_KNS5` -/

/-- `KillsDelta1` at K_{8, 5} via the `kills_delta1_KNS5` family. -/
theorem kills_delta1_K85 (c : Nat) :
    KillsDelta1 8 5 c pairEnum8 pairEnum5 :=
  kills_delta1_KNS5 8 c pairEnum8

/-- For K_{8, 5}^{(c)}: every layer carries an independent
    non-coboundary H²-class.  NT=5 odd uses the uniform
    `psi_layer_param` (no vertex-excluding ψ needed). -/
theorem K85_c_independent_h2_classes_via_framework (c : Nat) :
    ∀ (m m' : Fin c),
      psi_layer_param 8 5 c m'
        (e_face_layer_param 8 5 c m) = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 8 5 c,
           e_face_layer_param 8 5 c m
             ≠ delta1_enr_param 8 5 c pairEnum8 pairEnum5 σ) :=
  parametric_c_independent_h2_classes_param 8 5 c
    (by decide) (by decide) pairEnum8 pairEnum5 (kills_delta1_K85 c)

/-! ## §5 — K_{7, 4}: NT=4 even via `KNS4_c_independent_h2_classes` -/

/-- K_{7, 4}^{(c)} c-counter via the NT=4 even KNS4 family.  NS=7
    odd is irrelevant to the excl-T route (any `PairEnum NS` works). -/
theorem K74_c_independent_h2_classes_via_framework (c : Nat) :
    ∀ (m m' : Fin c),
      psi_excl_T0_NT4 7 c m' (e_face_layer_NT4 7 c m)
        = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 7 4 c,
           e_face_layer_NT4 7 c m
             ≠ delta1_enr_param 7 4 c pairEnum7 pairEnum4 σ) :=
  KNS4_c_independent_h2_classes 7 c (by decide) pairEnum7

/-! ## §6 — Pell-orbit extension capstone

Bundle the three new closures (5, 4), (7, 4), (8, 5) — the next
Stern-Brocot mediant layer beyond the n ∈ {3, 4, 5, 6} diagonal of
`master_Knn_c_counter_resolved`.  Each carries `c` independent
non-coboundary H²-classes for every multiplicity `c`. -/

/-- ★ Pell-orbit Stern-Brocot extension capstone: K_{5, 4}, K_{7, 4},
    K_{8, 5} each carry `c` independent non-coboundary H²-classes
    for every `c` and every layer index `m : Fin c`. -/
theorem pell_orbit_stern_brocot_extension_capstone (c : Nat) (m : Fin c) :
    (∀ m', psi_excl_T0_NT4 5 c m' (e_face_layer_NT4 5 c m)
            = decide (m.val = m'.val))
    ∧ (∀ m', psi_excl_T0_NT4 7 c m' (e_face_layer_NT4 7 c m)
            = decide (m.val = m'.val))
    ∧ (∀ m', psi_layer_param 8 5 c m' (e_face_layer_param 8 5 c m)
            = decide (m.val = m'.val)) :=
  ⟨fun m' => (K54_via_KNS4 c m m').1,
   fun m' => (K74_c_independent_h2_classes_via_framework c m m').1,
   fun m' => (K85_c_independent_h2_classes_via_framework c m m').1⟩

end E213.Lib.Math.Cohomology.Bipartite.Parametric.PellOrbitInstances
