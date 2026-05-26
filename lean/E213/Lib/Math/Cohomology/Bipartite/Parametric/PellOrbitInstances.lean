import E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTc
import E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTcEvenEven

/-!
# Pell-orbit Stern-Brocot extension: K_{7, 4}, K_{8, 5}, K_{5, 4}, K_{13, 8}

★★★★★★★★★★★★★★★ **Direction A transports to the next
Stern-Brocot mediant layer — ALL FOUR positions CLOSED.** ★★★★★★★★★★★★★★★

The existing `master_Knn_c_counter_resolved` covers the four diagonal
K_{n, n}^{(c)} for `n ∈ {3, 4, 5, 6}` plus asymmetric instances via
the `K3NT / K5NT / KNS3 / KNS4 / KNS5 / KNS6 / KNS8` families (NS or
NT in {3, 5} odd, or {4, 6, 8} even).

Stern-Brocot mediants `(2, 1) + (3, 2) = (5, 3)`, `(3, 2) + (5, 3) =
(8, 5)`, `(1, 1) + (3, 2) = (4, 3)`, etc., produce K_{NS, NT}^{(c)}
witnesses at every Stern-Brocot position.  This file instantiates the
universal framework at **(5, 4), (7, 4), (8, 5), (13, 8)** — four
positions on the next Stern-Brocot layer beyond the n ∈ {3, 4, 5, 6}
diagonal:

  · **K_{5, 4}** — NT=4 even, KNS4 family.  Re-exported here.
  · **K_{8, 5}** — NT=5 odd, KNS5 family.
  · **K_{7, 4}** — NT=4 even, KNS4 excl-T family.
  · **K_{13, 8}** — NT=8 even, KNS8 excl-T family.  Requires
    `pairEnum13` (NS=13 odd, any PairEnum 13 works since the NT=8
    family is NS-agnostic given `0 < chooseTwo NS`).

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

/-! ## §2 — `pairEnum8` is now in `EnrichedKNSNTcEvenEven.lean` §13.5. -/

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

Bundle the four closures (5, 4), (7, 4), (8, 5), (13, 8) — the next
Stern-Brocot mediant layer beyond the n ∈ {3, 4, 5, 6} diagonal of
`master_Knn_c_counter_resolved`.  Each carries `c` independent
non-coboundary H²-classes for every multiplicity `c`. -/

/-! ## §6.5 — Concrete pair enumeration on `Fin 13`

`chooseTwo 13 = 78` pairs in lex order.  Needed for K_{13, 8}. -/

/-- Low endpoint of the `s`-th pair of `Fin 13` (78 pairs lex). -/
def pair13_lo : Fin (chooseTwo 13) → Fin 13
  | ⟨s, _⟩ =>
    -- Each vertex i contributes 12-i pairs; accumulated:
    -- i=0: 0..11, i=1: 12..22, i=2: 23..32, i=3: 33..41,
    -- i=4: 42..49, i=5: 50..56, i=6: 57..62, i=7: 63..67,
    -- i=8: 68..71, i=9: 72..74, i=10: 75..76, i=11: 77
    if s < 12 then ⟨0, by decide⟩
    else if s < 23 then ⟨1, by decide⟩
    else if s < 33 then ⟨2, by decide⟩
    else if s < 42 then ⟨3, by decide⟩
    else if s < 50 then ⟨4, by decide⟩
    else if s < 57 then ⟨5, by decide⟩
    else if s < 63 then ⟨6, by decide⟩
    else if s < 68 then ⟨7, by decide⟩
    else if s < 72 then ⟨8, by decide⟩
    else if s < 75 then ⟨9, by decide⟩
    else if s < 77 then ⟨10, by decide⟩
    else ⟨11, by decide⟩

/-- High endpoint of the `s`-th pair of `Fin 13`. -/
def pair13_hi : Fin (chooseTwo 13) → Fin 13
  | ⟨s, _⟩ =>
    if s < 12 then ⟨s + 1, by omega⟩
    else if s < 23 then ⟨s - 12 + 2, by omega⟩
    else if s < 33 then ⟨s - 23 + 3, by omega⟩
    else if s < 42 then ⟨s - 33 + 4, by omega⟩
    else if s < 50 then ⟨s - 42 + 5, by omega⟩
    else if s < 57 then ⟨s - 50 + 6, by omega⟩
    else if s < 63 then ⟨s - 57 + 7, by omega⟩
    else if s < 68 then ⟨s - 63 + 8, by omega⟩
    else if s < 72 then ⟨s - 68 + 9, by omega⟩
    else if s < 75 then ⟨s - 72 + 10, by omega⟩
    else if s < 77 then ⟨s - 75 + 11, by omega⟩
    else ⟨12, by decide⟩

/-- Concrete `PairEnum 13` (78 pairs in lex order). -/
def pairEnum13 : PairEnum 13 where
  lo := pair13_lo
  hi := pair13_hi

/-! ## §7 — K_{13, 8}: NT=8 even via `KNS8_c_independent_h2_classes` -/

/-- K_{13, 8}^{(c)} c-counter via the NT=8 even KNS8 family.  NS=13
    odd is irrelevant to the excl-T route (any `PairEnum NS` works). -/
theorem K13_8_c_independent_h2_classes_via_framework (c : Nat) :
    ∀ (m m' : Fin c),
      psi_excl_T0_NT8 13 c m' (e_face_layer_NT8 13 c m)
        = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 13 8 c,
           e_face_layer_NT8 13 c m
             ≠ delta1_enr_param 13 8 c pairEnum13 pairEnum8 σ) :=
  KNS8_c_independent_h2_classes 13 c (by decide) pairEnum13

/-! ## §8 — Pell-orbit extension capstone (FULL — 4/4 positions)

Bundle ALL FOUR closures (5, 4), (7, 4), (8, 5), (13, 8) — the
complete next Stern-Brocot mediant layer. -/

/-- ★ Pell-orbit Stern-Brocot extension capstone: K_{5, 4}, K_{7, 4},
    K_{8, 5}, K_{13, 8} each carry `c` independent non-coboundary
    H²-classes for every `c` and every layer index `m : Fin c`. -/
theorem pell_orbit_stern_brocot_extension_capstone (c : Nat) (m : Fin c) :
    (∀ m', psi_excl_T0_NT4 5 c m' (e_face_layer_NT4 5 c m)
            = decide (m.val = m'.val))
    ∧ (∀ m', psi_excl_T0_NT4 7 c m' (e_face_layer_NT4 7 c m)
            = decide (m.val = m'.val))
    ∧ (∀ m', psi_layer_param 8 5 c m' (e_face_layer_param 8 5 c m)
            = decide (m.val = m'.val))
    ∧ (∀ m', psi_excl_T0_NT8 13 c m' (e_face_layer_NT8 13 c m)
            = decide (m.val = m'.val)) :=
  ⟨fun m' => (K54_via_KNS4 c m m').1,
   fun m' => (K74_c_independent_h2_classes_via_framework c m m').1,
   fun m' => (K85_c_independent_h2_classes_via_framework c m m').1,
   fun m' => (K13_8_c_independent_h2_classes_via_framework c m m').1⟩

end E213.Lib.Math.Cohomology.Bipartite.Parametric.PellOrbitInstances
