import E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTc

/-!
# Parity-failing closures via vertex-excluding ψ — K_{4,4} etc.

The uniform `psi_layer_param` (XOR over all `(s, t)` faces) kills δ¹
only when `(NS−1)(NT−1)` is even, i.e., NS odd OR NT odd
(`EnrichedKNSNTc.kills_delta1_*` family).

**Parity-failing case**: both `NS` and `NT` even.  Each edge then
appears in (NS−1)(NT−1) = odd × odd = **odd** faces, so the
uniform XOR sum does NOT cancel.

## Vertex-excluding ψ

Fix `i₀ : Fin NS`.  Define
  `ψ_excl_S(i₀, m, v) := ⊕_{s : i₀ ∉ pair s} ⊕_t v s t m`

(XOR over S-pairs NOT containing `i₀`).  Per-edge count:
  · For `i = i₀`: appears in 0 pairs s ⇒ contribution = 0.
  · For `i ≠ i₀`: appears in `(NS−1) − 1 = NS−2` such pairs.
    So count = `(NS−2)(NT−1)` per layer-`m` edge.

**Key**: when `NS` is even, `NS−2` is even, so `(NS−2)(NT−1)` is
even regardless of NT parity.  The vertex-excluding ψ closes the
gap.

This file specialises the argument to K_{4,4} (the smallest
parity-failing case).  The `e_face_layer` indicator is repositioned
to `(s = 3, t = 0)` so that `i₀ = 0 ∉ pair 3 = {1, 2}` and the
signature theorem still gives a Kronecker δ on layer index.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTcEvenEven

open E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTc

/-! ## §1 — `foldXor_6` expansion (helper for NT = 4, 6 T-pair folds) -/

/-- `foldXor 6 f = f 0 ⊕ f 1 ⊕ f 2 ⊕ f 3 ⊕ f 4 ⊕ f 5` (left-associated). -/
theorem foldXor_6 (f : Fin 6 → Bool) :
    foldXor 6 f
      = xor (xor (xor (xor (xor (f ⟨0, by decide⟩) (f ⟨1, by decide⟩))
                              (f ⟨2, by decide⟩)) (f ⟨3, by decide⟩))
                  (f ⟨4, by decide⟩)) (f ⟨5, by decide⟩) := by
  have h : foldXor 6 f
      = xor (xor (xor (xor (xor (xor false
            (f ⟨0, by decide⟩)) (f ⟨1, by decide⟩))
            (f ⟨2, by decide⟩)) (f ⟨3, by decide⟩))
            (f ⟨4, by decide⟩)) (f ⟨5, by decide⟩) := rfl
  rw [h]
  cases f ⟨0, by decide⟩ <;> rfl

/-! ## §2 — Vertex-excluding ψ for K_{4,4}: exclude S-vertex `0`

`pairEnum4` enumerates pairs of `Fin 4` in lex order:
  s=0: {0,1}    s=1: {0,2}    s=2: {0,3}    -- contain 0
  s=3: {1,2}    s=4: {1,3}    s=5: {2,3}    -- do NOT contain 0

`ψ_excl_S0_K44 m v` sums faces only at s ∈ {3, 4, 5}. -/

/-- ψ-functional for K_{4,4} excluding S-pairs that contain vertex 0.
    Sums layer-`m` face values over (s, t) with `s ∈ {3, 4, 5}`. -/
def psi_excl_S0_K44 (c : Nat) (m : Fin c) (v : EnrichedFaceVal 4 4 c) : Bool :=
  xor (xor (foldXor 6 (fun t => v ⟨3, by decide⟩ t m))
           (foldXor 6 (fun t => v ⟨4, by decide⟩ t m)))
      (foldXor 6 (fun t => v ⟨5, by decide⟩ t m))

/-! ## §3 — `psi_excl_S0_K44` kills δ¹

Strategy:
  1. Each inner `foldXor 6 (fun t => face_boundary 4 4 c pE4 pE4 σ s t m)`
     factors as `qT(lo s, m) ⊕ qT(hi s, m)` via the existing
     `foldXor_t_face_eq_qT_decomposition`.
  2. With `s ∈ {3, 4, 5}` and `pairEnum4` (lo, hi) values `(1,2), (1,3),
     (2,3)`, the total becomes
       `[qT 1 ⊕ qT 2] ⊕ [qT 1 ⊕ qT 3] ⊕ [qT 2 ⊕ qT 3] = 0`
     by structural XOR-cancellation (each `qT i` appears twice). -/

set_option maxHeartbeats 800000 in
theorem psi_excl_S0_K44_kills_delta1
    (c : Nat) (σ : EnrichedEdgeCoch 4 4 c) (m : Fin c) :
    psi_excl_S0_K44 c m
      (delta1_enr_param 4 4 c pairEnum4 pairEnum4 σ) = false := by
  unfold psi_excl_S0_K44
  -- Rewrite `delta1_enr_param σ s t m = face_boundary_param σ s t m`
  -- and decompose each inner sum via `foldXor_t_face_eq_qT_decomposition`.
  show xor (xor (foldXor 6 (fun t =>
                  face_boundary_param 4 4 c pairEnum4 pairEnum4 σ
                    ⟨3, by decide⟩ t m))
                (foldXor 6 (fun t =>
                  face_boundary_param 4 4 c pairEnum4 pairEnum4 σ
                    ⟨4, by decide⟩ t m)))
           (foldXor 6 (fun t =>
              face_boundary_param 4 4 c pairEnum4 pairEnum4 σ
                ⟨5, by decide⟩ t m)) = false
  rw [foldXor_t_face_eq_qT_decomposition 4 4 c pairEnum4 pairEnum4 σ
        ⟨3, by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 4 4 c pairEnum4 pairEnum4 σ
        ⟨4, by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 4 4 c pairEnum4 pairEnum4 σ
        ⟨5, by decide⟩ m]
  -- After decomposition, the goal is in terms of `pairEnum4.lo`/`hi`
  -- at s = 3, 4, 5.  Unfold to get concrete Fin 4 values.
  show xor (xor (xor (qT_param 4 4 c pairEnum4 σ ⟨1, by decide⟩ m)
                      (qT_param 4 4 c pairEnum4 σ ⟨2, by decide⟩ m))
                (xor (qT_param 4 4 c pairEnum4 σ ⟨1, by decide⟩ m)
                      (qT_param 4 4 c pairEnum4 σ ⟨3, by decide⟩ m)))
           (xor (qT_param 4 4 c pairEnum4 σ ⟨2, by decide⟩ m)
                (qT_param 4 4 c pairEnum4 σ ⟨3, by decide⟩ m)) = false
  -- Case-bash on the 3 abstract `qT` values: 8 cases.
  cases qT_param 4 4 c pairEnum4 σ ⟨1, by decide⟩ m <;>
    cases qT_param 4 4 c pairEnum4 σ ⟨2, by decide⟩ m <;>
    cases qT_param 4 4 c pairEnum4 σ ⟨3, by decide⟩ m <;> rfl

/-! ## §4 — Repositioned face indicator at `(s = 3, t = 0)`

`e_face_layer_param` places its non-zero entry at `(s = 0, t = 0)`,
but pair `s = 0 = {0, 1}` contains the excluded vertex `i₀ = 0`,
so the indicator is *invisible* to `ψ_excl_S0_K44` (would yield 0
signature).

Reposition to `s = 3` (pair `{1, 2}`, doesn't contain 0): indicator
is `true` exactly at `(s.val = 3, t.val = 0, m' = m)`. -/

/-- Single-face indicator at `(s = 3, t = 0)` for the K_{4,4}
    parity-failing scenario.  Compatible with `ψ_excl_S0_K44`. -/
def e_face_layer_K44 (c : Nat) (m : Fin c) : EnrichedFaceVal 4 4 c :=
  fun s t m' =>
    match s.val, t.val with
    | 3, 0 => decide (m.val = m'.val)
    | _, _ => false

/-! ## §5 — Signature: `ψ_excl_S0_K44(e_face_layer_K44 m) = δ_{m,m'}`

For each `s ∈ {3, 4, 5}`, evaluate the inner `foldXor 6` on
`e_face_layer_K44 m s t m'`:
  · s = 3: only `t = 0` carries `decide(m=m')`; rest `false`.
    foldXor over t = decide(m=m').
  · s = 4, 5: indicator is `false` for all t.  foldXor = false. -/

theorem psi_excl_S0_K44_signature (c : Nat) (m m' : Fin c) :
    psi_excl_S0_K44 c m' (e_face_layer_K44 c m)
      = decide (m.val = m'.val) := by
  unfold psi_excl_S0_K44
  -- Inner foldXor for s = 3: only t.val=0 carries decide.
  have hs3 :
      foldXor 6 (fun t => e_face_layer_K44 c m ⟨3, by decide⟩ t m')
        = decide (m.val = m'.val) := by
    apply foldXor_only_first_pos 6 (by decide) (decide (m.val = m'.val))
    · -- t = ⟨0, _⟩: e_face_layer_K44 c m ⟨3, _⟩ ⟨0, _⟩ m' = decide(m=m').
      rfl
    · -- t.val ≠ 0: e_face_layer_K44 returns false.
      intro t ht
      unfold e_face_layer_K44
      match hv : t.val, ht with
      | 0, hcontra => exact absurd rfl hcontra
      | _+1, _ => rfl
  -- Inner foldXor for s = 4, 5: indicator is false everywhere.
  have hs4 :
      foldXor 6 (fun t => e_face_layer_K44 c m ⟨4, by decide⟩ t m') = false := by
    apply (foldXor_congr_all 6 _ (fun _ => false) ?_).trans
        (foldXor_const_false _)
    intro t
    unfold e_face_layer_K44
    cases t.val <;> rfl
  have hs5 :
      foldXor 6 (fun t => e_face_layer_K44 c m ⟨5, by decide⟩ t m') = false := by
    apply (foldXor_congr_all 6 _ (fun _ => false) ?_).trans
        (foldXor_const_false _)
    intro t
    unfold e_face_layer_K44
    cases t.val <;> rfl
  rw [hs3, hs4, hs5]
  cases decide (m.val = m'.val) <;> rfl

/-! ## §6 — Non-coboundary + c-independent H²-classes for K_{4,4} -/

/-- `decide (n = n) = true`. -/
private theorem decide_self_true_K44 (n : Nat) : decide (n = n) = true := by
  cases h : decide (n = n) with
  | true => rfl
  | false => exact absurd rfl (of_decide_eq_false h)

/-- `e_face_layer_K44 m` is not in the image of `δ¹_enr` at K_{4,4}. -/
theorem e_face_layer_K44_not_coboundary (c : Nat) (m : Fin c) :
    ∀ σ : EnrichedEdgeCoch 4 4 c,
      e_face_layer_K44 c m
        ≠ delta1_enr_param 4 4 c pairEnum4 pairEnum4 σ := by
  intro σ heq
  have h := congrArg (psi_excl_S0_K44 c m) heq
  rw [psi_excl_S0_K44_signature, psi_excl_S0_K44_kills_delta1] at h
  rw [decide_self_true_K44] at h
  exact Bool.noConfusion h

/-- ★★★★★★ Capstone for K_{4,4}: every layer carries an independent
    non-coboundary H²-class, separated by `ψ_excl_S0_K44`.

    Closes the parity-failing case `NS = NT = 4` (where the uniform
    `psi_layer_param` cannot distinguish coboundaries, because each
    edge appears (NS-1)(NT-1) = 9 times = odd).  The vertex-excluding
    ψ restricts the s-fold so each remaining S-vertex appears
    NS-2 = 2 times = even ⇒ kill. -/
theorem K44_c_independent_h2_classes (c : Nat) :
    ∀ (m m' : Fin c),
      psi_excl_S0_K44 c m' (e_face_layer_K44 c m)
        = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 4 4 c,
           e_face_layer_K44 c m
             ≠ delta1_enr_param 4 4 c pairEnum4 pairEnum4 σ) :=
  fun m m' =>
    ⟨psi_excl_S0_K44_signature c m m',
     e_face_layer_K44_not_coboundary c m⟩

/-! ## §7 — K_{6,4} parity-failing closure via vertex-excluding ψ

`pairEnum6` of `Fin 6` (15 pairs lex order): S-pairs containing 0 are
`s ∈ {0, 1, 2, 3, 4}` (= {0,1}, {0,2}, {0,3}, {0,4}, {0,5});
S-pairs NOT containing 0 are `s ∈ {5, …, 14}` (10 pairs).

`ψ_excl_S0_K64` sums faces only at those 10 S-pairs.  For
`NS = 6, NT = 4`: each remaining S-vertex (1, 2, 3, 4, 5) appears in
`NS-2 = 4` (even) of those 10 pairs.  Kill via structural
XOR-cancellation on the 5 abstract `qT` values. -/

/-- ψ-functional for K_{6,4} excluding S-pairs containing vertex 0. -/
def psi_excl_S0_K64 (c : Nat) (m : Fin c) (v : EnrichedFaceVal 6 4 c) : Bool :=
  xor (xor (xor (xor (xor (xor (xor (xor (xor
    (foldXor 6 (fun t => v ⟨5,  by decide⟩ t m))
    (foldXor 6 (fun t => v ⟨6,  by decide⟩ t m)))
    (foldXor 6 (fun t => v ⟨7,  by decide⟩ t m)))
    (foldXor 6 (fun t => v ⟨8,  by decide⟩ t m)))
    (foldXor 6 (fun t => v ⟨9,  by decide⟩ t m)))
    (foldXor 6 (fun t => v ⟨10, by decide⟩ t m)))
    (foldXor 6 (fun t => v ⟨11, by decide⟩ t m)))
    (foldXor 6 (fun t => v ⟨12, by decide⟩ t m)))
    (foldXor 6 (fun t => v ⟨13, by decide⟩ t m)))
    (foldXor 6 (fun t => v ⟨14, by decide⟩ t m))

set_option maxHeartbeats 2000000 in
/-- ψ_excl_S0_K64 kills δ¹: same structural mechanism as K_{4,4},
    expanded to 10 S-pairs and 5-bool case-bash (each qT i for i ∈
    {1, 2, 3, 4, 5} appears NS-2 = 4 (even) times). -/
theorem psi_excl_S0_K64_kills_delta1
    (c : Nat) (σ : EnrichedEdgeCoch 6 4 c) (m : Fin c) :
    psi_excl_S0_K64 c m
      (delta1_enr_param 6 4 c pairEnum6 pairEnum4 σ) = false := by
  unfold psi_excl_S0_K64 delta1_enr_param
  rw [foldXor_t_face_eq_qT_decomposition 6 4 c pairEnum6 pairEnum4 σ ⟨5,  by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 4 c pairEnum6 pairEnum4 σ ⟨6,  by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 4 c pairEnum6 pairEnum4 σ ⟨7,  by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 4 c pairEnum6 pairEnum4 σ ⟨8,  by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 4 c pairEnum6 pairEnum4 σ ⟨9,  by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 4 c pairEnum6 pairEnum4 σ ⟨10, by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 4 c pairEnum6 pairEnum4 σ ⟨11, by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 4 c pairEnum6 pairEnum4 σ ⟨12, by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 4 c pairEnum6 pairEnum4 σ ⟨13, by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 4 c pairEnum6 pairEnum4 σ ⟨14, by decide⟩ m]
  unfold pairEnum6 pair6_lo pair6_hi
  -- After unfolding, the goal is a 10-term xor sum where qT(i) for
  -- i ∈ {1, 2, 3, 4, 5} each appears exactly 4 times.  Case-bash
  -- on the 5 abstract values closes it (2^5 = 32 cases).
  cases qT_param 6 4 c pairEnum4 σ ⟨1, by decide⟩ m <;>
    cases qT_param 6 4 c pairEnum4 σ ⟨2, by decide⟩ m <;>
    cases qT_param 6 4 c pairEnum4 σ ⟨3, by decide⟩ m <;>
    cases qT_param 6 4 c pairEnum4 σ ⟨4, by decide⟩ m <;>
    cases qT_param 6 4 c pairEnum4 σ ⟨5, by decide⟩ m <;> rfl

/-! ## §8 — Repositioned face indicator at `(s = 5, t = 0)` for K_{6,4}

`pair 5 = {1, 2}` doesn't contain the excluded S-vertex `0`, so
the indicator is visible to `ψ_excl_S0_K64`. -/

/-- Single-face indicator at `(s = 5, t = 0)` for K_{6,4}. -/
def e_face_layer_K64 (c : Nat) (m : Fin c) : EnrichedFaceVal 6 4 c :=
  fun s t m' =>
    match s.val, t.val with
    | 5, 0 => decide (m.val = m'.val)
    | _, _ => false

/-- ψ-signature: `ψ_excl_S0_K64(e_face_layer_K64 m) = decide(m = m')`. -/
theorem psi_excl_S0_K64_signature (c : Nat) (m m' : Fin c) :
    psi_excl_S0_K64 c m' (e_face_layer_K64 c m) = decide (m.val = m'.val) := by
  unfold psi_excl_S0_K64
  have hs5 :
      foldXor 6 (fun t => e_face_layer_K64 c m ⟨5, by decide⟩ t m')
        = decide (m.val = m'.val) := by
    apply foldXor_only_first_pos 6 (by decide) (decide (m.val = m'.val))
    · rfl
    · intro t ht
      unfold e_face_layer_K64
      match hv : t.val, ht with
      | 0, hcontra => exact absurd rfl hcontra
      | _+1, _ => rfl
  -- Helper: for any concrete `s.val ≠ 5`, the inner foldXor is false.
  have hsk : ∀ (k : Fin (chooseTwo 6)) (hne : k.val ≠ 5),
      foldXor 6 (fun t => e_face_layer_K64 c m k t m') = false := by
    intro k hne
    apply (foldXor_congr_all 6 _ (fun _ => false) ?_).trans
        (foldXor_const_false _)
    intro t
    unfold e_face_layer_K64
    -- Match on s.val: concrete s.val ≠ 5 ⇒ falls through to false branch.
    -- We use a generic `split` + decide-style discharge.
    rcases hkv : k.val with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals (first | (cases t.val <;> rfl) | exact absurd hkv hne |
      exact absurd k.isLt (by decide))
  rw [hsk ⟨6,  by decide⟩ (by decide),
      hsk ⟨7,  by decide⟩ (by decide),
      hsk ⟨8,  by decide⟩ (by decide),
      hsk ⟨9,  by decide⟩ (by decide),
      hsk ⟨10, by decide⟩ (by decide),
      hsk ⟨11, by decide⟩ (by decide),
      hsk ⟨12, by decide⟩ (by decide),
      hsk ⟨13, by decide⟩ (by decide),
      hsk ⟨14, by decide⟩ (by decide),
      hs5]
  cases decide (m.val = m'.val) <;> rfl

/-- `e_face_layer_K64 m` is not in the image of `δ¹_enr` at K_{6,4}. -/
theorem e_face_layer_K64_not_coboundary (c : Nat) (m : Fin c) :
    ∀ σ : EnrichedEdgeCoch 6 4 c,
      e_face_layer_K64 c m
        ≠ delta1_enr_param 6 4 c pairEnum6 pairEnum4 σ := by
  intro σ heq
  have h := congrArg (psi_excl_S0_K64 c m) heq
  rw [psi_excl_S0_K64_signature, psi_excl_S0_K64_kills_delta1] at h
  rw [decide_self_true_K44] at h
  exact Bool.noConfusion h

/-- ★★★★★★ Capstone for K_{6,4}: every layer carries an independent
    non-coboundary H²-class, via the vertex-excluding ψ. -/
theorem K64_c_independent_h2_classes (c : Nat) :
    ∀ (m m' : Fin c),
      psi_excl_S0_K64 c m' (e_face_layer_K64 c m)
        = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 6 4 c,
           e_face_layer_K64 c m
             ≠ delta1_enr_param 6 4 c pairEnum6 pairEnum4 σ) :=
  fun m m' =>
    ⟨psi_excl_S0_K64_signature c m m',
     e_face_layer_K64_not_coboundary c m⟩

/-! ## §9 — Parametric `psi_excl_S0_NS4`: family kill for K_{4, NT}

Generalises `psi_excl_S0_K44` over `NT : Nat`.  The kill argument
only depends on NS=4 (3-bool case-bash on `qT 1, qT 2, qT 3`); NT
factors through `foldXor_t_face_eq_qT_decomposition` parametrically.

Closes K_{4, NT} for every NT ≥ 2 via the vertex-excluding ψ —
both parity-failing (NT even) and (redundantly) parity-OK (NT odd)
cases. -/

/-- ψ-functional for K_{4, NT} excluding S-pairs containing vertex 0.
    Sums layer-`m` face values over `s ∈ {3, 4, 5}` and all
    T-pairs (chooseTwo NT). -/
def psi_excl_S0_NS4 (NT c : Nat) (m : Fin c) (v : EnrichedFaceVal 4 NT c) : Bool :=
  xor (xor (foldXor (chooseTwo NT) (fun t => v ⟨3, by decide⟩ t m))
           (foldXor (chooseTwo NT) (fun t => v ⟨4, by decide⟩ t m)))
      (foldXor (chooseTwo NT) (fun t => v ⟨5, by decide⟩ t m))

set_option maxHeartbeats 800000 in
/-- ψ_excl_S0_NS4 kills δ¹ for any T-side pair enumeration.  Proof
    by qT-decomposition at each of s ∈ {3, 4, 5} + 3-bool case-bash
    on `qT 1, qT 2, qT 3` (structural cancellation: each appears
    twice). -/
theorem psi_excl_S0_NS4_kills_delta1
    (NT c : Nat) (pT : PairEnum NT) (σ : EnrichedEdgeCoch 4 NT c) (m : Fin c) :
    psi_excl_S0_NS4 NT c m
      (delta1_enr_param 4 NT c pairEnum4 pT σ) = false := by
  unfold psi_excl_S0_NS4 delta1_enr_param
  rw [foldXor_t_face_eq_qT_decomposition 4 NT c pairEnum4 pT σ ⟨3, by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 4 NT c pairEnum4 pT σ ⟨4, by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 4 NT c pairEnum4 pT σ ⟨5, by decide⟩ m]
  unfold pairEnum4 pair4_lo pair4_hi
  cases qT_param 4 NT c pT σ ⟨1, by decide⟩ m <;>
    cases qT_param 4 NT c pT σ ⟨2, by decide⟩ m <;>
    cases qT_param 4 NT c pT σ ⟨3, by decide⟩ m <;> rfl

/-- Single-face indicator at `(s = 3, t = 0)` for K_{4, NT}. -/
def e_face_layer_NS4 (NT c : Nat) (m : Fin c) : EnrichedFaceVal 4 NT c :=
  fun s t m' =>
    match s.val, t.val with
    | 3, 0 => decide (m.val = m'.val)
    | _, _ => false

/-- ψ-signature: `ψ_excl_S0_NS4(e_face_layer_NS4 m) = decide(m = m')`.
    Requires `chooseTwo NT ≥ 1` (i.e., NT ≥ 2). -/
theorem psi_excl_S0_NS4_signature
    (NT c : Nat) (hNT : 0 < chooseTwo NT) (m m' : Fin c) :
    psi_excl_S0_NS4 NT c m' (e_face_layer_NS4 NT c m)
      = decide (m.val = m'.val) := by
  unfold psi_excl_S0_NS4
  have hs3 :
      foldXor (chooseTwo NT)
        (fun t => e_face_layer_NS4 NT c m ⟨3, by decide⟩ t m')
        = decide (m.val = m'.val) := by
    apply foldXor_only_first_pos (chooseTwo NT) hNT (decide (m.val = m'.val))
    · rfl
    · intro t ht
      unfold e_face_layer_NS4
      match hv : t.val, ht with
      | 0, hcontra => exact absurd rfl hcontra
      | _+1, _ => rfl
  have hsf : ∀ (sval : Nat) (hsv : sval = 4 ∨ sval = 5)
        (hbnd : sval < chooseTwo 4),
      foldXor (chooseTwo NT)
        (fun t => e_face_layer_NS4 NT c m ⟨sval, hbnd⟩ t m') = false := by
    intro sval hsv hbnd
    apply (foldXor_congr_all (chooseTwo NT) _ (fun _ => false) ?_).trans
        (foldXor_const_false _)
    intro t
    unfold e_face_layer_NS4
    rcases hsv with rfl | rfl <;> cases t.val <;> rfl
  rw [hs3,
      hsf 4 (Or.inl rfl) (by decide),
      hsf 5 (Or.inr rfl) (by decide)]
  cases decide (m.val = m'.val) <;> rfl

/-- `e_face_layer_NS4 NT m` is not in the image of `δ¹_enr` at K_{4, NT}. -/
theorem e_face_layer_NS4_not_coboundary
    (NT c : Nat) (hNT : 0 < chooseTwo NT) (pT : PairEnum NT) (m : Fin c) :
    ∀ σ : EnrichedEdgeCoch 4 NT c,
      e_face_layer_NS4 NT c m
        ≠ delta1_enr_param 4 NT c pairEnum4 pT σ := by
  intro σ heq
  have h := congrArg (psi_excl_S0_NS4 NT c m) heq
  rw [psi_excl_S0_NS4_signature NT c hNT m m,
      psi_excl_S0_NS4_kills_delta1 NT c pT σ m] at h
  rw [decide_self_true_K44] at h
  exact Bool.noConfusion h

/-- ★★★★★★ Family capstone: K_{4, NT} for every NT ≥ 2 carries `c`
    independent non-coboundary H²-classes — both parity-failing (NT
    even) and parity-OK (NT odd) cases covered uniformly. -/
theorem K4NT_c_independent_h2_classes
    (NT c : Nat) (hNT : 0 < chooseTwo NT) (pT : PairEnum NT) :
    ∀ (m m' : Fin c),
      psi_excl_S0_NS4 NT c m' (e_face_layer_NS4 NT c m)
        = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 4 NT c,
           e_face_layer_NS4 NT c m
             ≠ delta1_enr_param 4 NT c pairEnum4 pT σ) :=
  fun m m' =>
    ⟨psi_excl_S0_NS4_signature NT c hNT m m',
     e_face_layer_NS4_not_coboundary NT c hNT pT m⟩

/-! ## §10 — K_{4,6} instance from the family

K_{4,6}: NS=4, NT=6, (NS-1)(NT-1) = 3·5 = 15 odd (parity-failing).
Closed via the vertex-excluding family `K4NT_c_independent_h2_classes`. -/

/-- `K_{4,6}^{(c)}` c-independent H²-classes via `psi_excl_S0_NS4`. -/
theorem K46_c_independent_h2_classes (c : Nat) :
    ∀ (m m' : Fin c),
      psi_excl_S0_NS4 6 c m' (e_face_layer_NS4 6 c m)
        = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 4 6 c,
           e_face_layer_NS4 6 c m
             ≠ delta1_enr_param 4 6 c pairEnum4 pairEnum6 σ) :=
  K4NT_c_independent_h2_classes 6 c (by decide) pairEnum6

/-! ## §11 — Parametric `psi_excl_S0_NS6`: family kill for K_{6, NT}

Mirror of `psi_excl_S0_NS4`: NS=6 case.  10 excluded S-pairs (s ∈
{5, …, 14}), 5 abstract qT values, 32 case-bash cases. -/

/-- ψ-functional for K_{6, NT} excluding S-pairs containing vertex 0. -/
def psi_excl_S0_NS6 (NT c : Nat) (m : Fin c) (v : EnrichedFaceVal 6 NT c) : Bool :=
  xor (xor (xor (xor (xor (xor (xor (xor (xor
    (foldXor (chooseTwo NT) (fun t => v ⟨5,  by decide⟩ t m))
    (foldXor (chooseTwo NT) (fun t => v ⟨6,  by decide⟩ t m)))
    (foldXor (chooseTwo NT) (fun t => v ⟨7,  by decide⟩ t m)))
    (foldXor (chooseTwo NT) (fun t => v ⟨8,  by decide⟩ t m)))
    (foldXor (chooseTwo NT) (fun t => v ⟨9,  by decide⟩ t m)))
    (foldXor (chooseTwo NT) (fun t => v ⟨10, by decide⟩ t m)))
    (foldXor (chooseTwo NT) (fun t => v ⟨11, by decide⟩ t m)))
    (foldXor (chooseTwo NT) (fun t => v ⟨12, by decide⟩ t m)))
    (foldXor (chooseTwo NT) (fun t => v ⟨13, by decide⟩ t m)))
    (foldXor (chooseTwo NT) (fun t => v ⟨14, by decide⟩ t m))

set_option maxHeartbeats 2000000 in
/-- ψ_excl_S0_NS6 kills δ¹ for any T-side pair enumeration. -/
theorem psi_excl_S0_NS6_kills_delta1
    (NT c : Nat) (pT : PairEnum NT) (σ : EnrichedEdgeCoch 6 NT c) (m : Fin c) :
    psi_excl_S0_NS6 NT c m
      (delta1_enr_param 6 NT c pairEnum6 pT σ) = false := by
  unfold psi_excl_S0_NS6 delta1_enr_param
  rw [foldXor_t_face_eq_qT_decomposition 6 NT c pairEnum6 pT σ ⟨5,  by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 NT c pairEnum6 pT σ ⟨6,  by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 NT c pairEnum6 pT σ ⟨7,  by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 NT c pairEnum6 pT σ ⟨8,  by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 NT c pairEnum6 pT σ ⟨9,  by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 NT c pairEnum6 pT σ ⟨10, by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 NT c pairEnum6 pT σ ⟨11, by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 NT c pairEnum6 pT σ ⟨12, by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 NT c pairEnum6 pT σ ⟨13, by decide⟩ m,
      foldXor_t_face_eq_qT_decomposition 6 NT c pairEnum6 pT σ ⟨14, by decide⟩ m]
  unfold pairEnum6 pair6_lo pair6_hi
  cases qT_param 6 NT c pT σ ⟨1, by decide⟩ m <;>
    cases qT_param 6 NT c pT σ ⟨2, by decide⟩ m <;>
    cases qT_param 6 NT c pT σ ⟨3, by decide⟩ m <;>
    cases qT_param 6 NT c pT σ ⟨4, by decide⟩ m <;>
    cases qT_param 6 NT c pT σ ⟨5, by decide⟩ m <;> rfl

/-- Single-face indicator at `(s = 5, t = 0)` for K_{6, NT}. -/
def e_face_layer_NS6 (NT c : Nat) (m : Fin c) : EnrichedFaceVal 6 NT c :=
  fun s t m' =>
    match s.val, t.val with
    | 5, 0 => decide (m.val = m'.val)
    | _, _ => false

/-- ψ-signature: `ψ_excl_S0_NS6(e_face_layer_NS6 m) = decide(m = m')`. -/
theorem psi_excl_S0_NS6_signature
    (NT c : Nat) (hNT : 0 < chooseTwo NT) (m m' : Fin c) :
    psi_excl_S0_NS6 NT c m' (e_face_layer_NS6 NT c m)
      = decide (m.val = m'.val) := by
  unfold psi_excl_S0_NS6
  have hs5 :
      foldXor (chooseTwo NT)
        (fun t => e_face_layer_NS6 NT c m ⟨5, by decide⟩ t m')
        = decide (m.val = m'.val) := by
    apply foldXor_only_first_pos (chooseTwo NT) hNT (decide (m.val = m'.val))
    · rfl
    · intro t ht
      unfold e_face_layer_NS6
      match hv : t.val, ht with
      | 0, hcontra => exact absurd rfl hcontra
      | _+1, _ => rfl
  have hsk : ∀ (k : Fin (chooseTwo 6)) (hne : k.val ≠ 5),
      foldXor (chooseTwo NT)
        (fun t => e_face_layer_NS6 NT c m k t m') = false := by
    intro k hne
    apply (foldXor_congr_all (chooseTwo NT) _ (fun _ => false) ?_).trans
        (foldXor_const_false _)
    intro t
    unfold e_face_layer_NS6
    rcases hkv : k.val with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals (first | (cases t.val <;> rfl) | exact absurd hkv hne |
      exact absurd k.isLt (by decide))
  rw [hsk ⟨6,  by decide⟩ (by decide),
      hsk ⟨7,  by decide⟩ (by decide),
      hsk ⟨8,  by decide⟩ (by decide),
      hsk ⟨9,  by decide⟩ (by decide),
      hsk ⟨10, by decide⟩ (by decide),
      hsk ⟨11, by decide⟩ (by decide),
      hsk ⟨12, by decide⟩ (by decide),
      hsk ⟨13, by decide⟩ (by decide),
      hsk ⟨14, by decide⟩ (by decide),
      hs5]
  cases decide (m.val = m'.val) <;> rfl

/-- `e_face_layer_NS6 NT m` is not in the image of `δ¹_enr` at K_{6, NT}. -/
theorem e_face_layer_NS6_not_coboundary
    (NT c : Nat) (hNT : 0 < chooseTwo NT) (pT : PairEnum NT) (m : Fin c) :
    ∀ σ : EnrichedEdgeCoch 6 NT c,
      e_face_layer_NS6 NT c m
        ≠ delta1_enr_param 6 NT c pairEnum6 pT σ := by
  intro σ heq
  have h := congrArg (psi_excl_S0_NS6 NT c m) heq
  rw [psi_excl_S0_NS6_signature NT c hNT m m,
      psi_excl_S0_NS6_kills_delta1 NT c pT σ m] at h
  rw [decide_self_true_K44] at h
  exact Bool.noConfusion h

/-- ★★★★★★ Family capstone: K_{6, NT} for every NT ≥ 2 carries `c`
    independent non-coboundary H²-classes — covers K_{6,3}, K_{6,4},
    K_{6,5}, K_{6,6}, K_{6,7}, … uniformly. -/
theorem K6NT_c_independent_h2_classes
    (NT c : Nat) (hNT : 0 < chooseTwo NT) (pT : PairEnum NT) :
    ∀ (m m' : Fin c),
      psi_excl_S0_NS6 NT c m' (e_face_layer_NS6 NT c m)
        = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 6 NT c,
           e_face_layer_NS6 NT c m
             ≠ delta1_enr_param 6 NT c pairEnum6 pT σ) :=
  fun m m' =>
    ⟨psi_excl_S0_NS6_signature NT c hNT m m',
     e_face_layer_NS6_not_coboundary NT c hNT pT m⟩

/-- `K_{6,6}^{(c)}` c-independent H²-classes via the NS=6 family. -/
theorem K66_c_independent_h2_classes (c : Nat) :
    ∀ (m m' : Fin c),
      psi_excl_S0_NS6 6 c m' (e_face_layer_NS6 6 c m)
        = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 6 6 c,
           e_face_layer_NS6 6 c m
             ≠ delta1_enr_param 6 6 c pairEnum6 pairEnum6 σ) :=
  K6NT_c_independent_h2_classes 6 c (by decide) pairEnum6

/-! ## §12 — Symmetric dual: K_{NS, 4} family via `psi_excl_T0_NT4`

Mirror of `psi_excl_S0_NS4` under S ↔ T swap.  Sums over `s : Fin (chooseTwo NS)`
(all S-pairs) and `t ∈ {3, 4, 5}` (T-pairs of Fin 4 NOT containing T-vertex 0).
Kill via `foldXor_s_face_eq_qS_decomposition` + 3-bool case-bash on `qS i`. -/

/-- ψ-functional for K_{NS, 4} excluding T-pairs containing vertex 0. -/
def psi_excl_T0_NT4 (NS c : Nat) (m : Fin c) (v : EnrichedFaceVal NS 4 c) : Bool :=
  xor (xor (foldXor (chooseTwo NS) (fun s => v s ⟨3, by decide⟩ m))
           (foldXor (chooseTwo NS) (fun s => v s ⟨4, by decide⟩ m)))
      (foldXor (chooseTwo NS) (fun s => v s ⟨5, by decide⟩ m))

set_option maxHeartbeats 800000 in
/-- ψ_excl_T0_NT4 kills δ¹ for any S-side pair enumeration. -/
theorem psi_excl_T0_NT4_kills_delta1
    (NS c : Nat) (pS : PairEnum NS) (σ : EnrichedEdgeCoch NS 4 c) (m : Fin c) :
    psi_excl_T0_NT4 NS c m
      (delta1_enr_param NS 4 c pS pairEnum4 σ) = false := by
  unfold psi_excl_T0_NT4 delta1_enr_param
  rw [foldXor_s_face_eq_qS_decomposition NS 4 c pS pairEnum4 σ ⟨3, by decide⟩ m,
      foldXor_s_face_eq_qS_decomposition NS 4 c pS pairEnum4 σ ⟨4, by decide⟩ m,
      foldXor_s_face_eq_qS_decomposition NS 4 c pS pairEnum4 σ ⟨5, by decide⟩ m]
  unfold pairEnum4 pair4_lo pair4_hi
  cases qS_param NS 4 c pS σ ⟨1, by decide⟩ m <;>
    cases qS_param NS 4 c pS σ ⟨2, by decide⟩ m <;>
    cases qS_param NS 4 c pS σ ⟨3, by decide⟩ m <;> rfl

/-- Single-face indicator at `(s = 0, t = 3)` for K_{NS, 4}.  Pair t=3
    is `{1, 2}` of `Fin 4` (doesn't contain T-vertex 0). -/
def e_face_layer_NT4 (NS c : Nat) (m : Fin c) : EnrichedFaceVal NS 4 c :=
  fun s t m' =>
    match s.val, t.val with
    | 0, 3 => decide (m.val = m'.val)
    | _, _ => false

/-- ψ-signature for the NT=4 dual family. -/
theorem psi_excl_T0_NT4_signature
    (NS c : Nat) (hNS : 0 < chooseTwo NS) (m m' : Fin c) :
    psi_excl_T0_NT4 NS c m' (e_face_layer_NT4 NS c m)
      = decide (m.val = m'.val) := by
  unfold psi_excl_T0_NT4
  have ht3 :
      foldXor (chooseTwo NS)
        (fun s => e_face_layer_NT4 NS c m s ⟨3, by decide⟩ m')
        = decide (m.val = m'.val) := by
    apply foldXor_only_first_pos (chooseTwo NS) hNS (decide (m.val = m'.val))
    · rfl
    · intro s hs
      unfold e_face_layer_NT4
      match hv : s.val, hs with
      | 0, hcontra => exact absurd rfl hcontra
      | _+1, _ => rfl
  have htf : ∀ (tval : Nat) (htv : tval = 4 ∨ tval = 5)
        (hbnd : tval < chooseTwo 4),
      foldXor (chooseTwo NS)
        (fun s => e_face_layer_NT4 NS c m s ⟨tval, hbnd⟩ m') = false := by
    intro tval htv hbnd
    apply (foldXor_congr_all (chooseTwo NS) _ (fun _ => false) ?_).trans
        (foldXor_const_false _)
    intro s
    unfold e_face_layer_NT4
    rcases htv with rfl | rfl <;> cases s.val <;> rfl
  rw [ht3,
      htf 4 (Or.inl rfl) (by decide),
      htf 5 (Or.inr rfl) (by decide)]
  cases decide (m.val = m'.val) <;> rfl

/-- `e_face_layer_NT4` is not a coboundary at K_{NS, 4}. -/
theorem e_face_layer_NT4_not_coboundary
    (NS c : Nat) (hNS : 0 < chooseTwo NS) (pS : PairEnum NS) (m : Fin c) :
    ∀ σ : EnrichedEdgeCoch NS 4 c,
      e_face_layer_NT4 NS c m
        ≠ delta1_enr_param NS 4 c pS pairEnum4 σ := by
  intro σ heq
  have h := congrArg (psi_excl_T0_NT4 NS c m) heq
  rw [psi_excl_T0_NT4_signature NS c hNS m m,
      psi_excl_T0_NT4_kills_delta1 NS c pS σ m] at h
  rw [decide_self_true_K44] at h
  exact Bool.noConfusion h

/-- ★★★★★★ Family capstone: K_{NS, 4} for every NS ≥ 2 carries `c`
    independent non-coboundary H²-classes.  Closes K_{NS, 4} via
    T-vertex excl regardless of NS parity. -/
theorem KNS4_c_independent_h2_classes
    (NS c : Nat) (hNS : 0 < chooseTwo NS) (pS : PairEnum NS) :
    ∀ (m m' : Fin c),
      psi_excl_T0_NT4 NS c m' (e_face_layer_NT4 NS c m)
        = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch NS 4 c,
           e_face_layer_NT4 NS c m
             ≠ delta1_enr_param NS 4 c pS pairEnum4 σ) :=
  fun m m' =>
    ⟨psi_excl_T0_NT4_signature NS c hNS m m',
     e_face_layer_NT4_not_coboundary NS c hNS pS m⟩

/-! ## §13 — Symmetric dual: K_{NS, 6} family via `psi_excl_T0_NT6` -/

/-- ψ-functional for K_{NS, 6} excluding T-pairs containing vertex 0. -/
def psi_excl_T0_NT6 (NS c : Nat) (m : Fin c) (v : EnrichedFaceVal NS 6 c) : Bool :=
  xor (xor (xor (xor (xor (xor (xor (xor (xor
    (foldXor (chooseTwo NS) (fun s => v s ⟨5,  by decide⟩ m))
    (foldXor (chooseTwo NS) (fun s => v s ⟨6,  by decide⟩ m)))
    (foldXor (chooseTwo NS) (fun s => v s ⟨7,  by decide⟩ m)))
    (foldXor (chooseTwo NS) (fun s => v s ⟨8,  by decide⟩ m)))
    (foldXor (chooseTwo NS) (fun s => v s ⟨9,  by decide⟩ m)))
    (foldXor (chooseTwo NS) (fun s => v s ⟨10, by decide⟩ m)))
    (foldXor (chooseTwo NS) (fun s => v s ⟨11, by decide⟩ m)))
    (foldXor (chooseTwo NS) (fun s => v s ⟨12, by decide⟩ m)))
    (foldXor (chooseTwo NS) (fun s => v s ⟨13, by decide⟩ m)))
    (foldXor (chooseTwo NS) (fun s => v s ⟨14, by decide⟩ m))

set_option maxHeartbeats 2000000 in
/-- ψ_excl_T0_NT6 kills δ¹ for any S-side pair enumeration. -/
theorem psi_excl_T0_NT6_kills_delta1
    (NS c : Nat) (pS : PairEnum NS) (σ : EnrichedEdgeCoch NS 6 c) (m : Fin c) :
    psi_excl_T0_NT6 NS c m
      (delta1_enr_param NS 6 c pS pairEnum6 σ) = false := by
  unfold psi_excl_T0_NT6 delta1_enr_param
  rw [foldXor_s_face_eq_qS_decomposition NS 6 c pS pairEnum6 σ ⟨5,  by decide⟩ m,
      foldXor_s_face_eq_qS_decomposition NS 6 c pS pairEnum6 σ ⟨6,  by decide⟩ m,
      foldXor_s_face_eq_qS_decomposition NS 6 c pS pairEnum6 σ ⟨7,  by decide⟩ m,
      foldXor_s_face_eq_qS_decomposition NS 6 c pS pairEnum6 σ ⟨8,  by decide⟩ m,
      foldXor_s_face_eq_qS_decomposition NS 6 c pS pairEnum6 σ ⟨9,  by decide⟩ m,
      foldXor_s_face_eq_qS_decomposition NS 6 c pS pairEnum6 σ ⟨10, by decide⟩ m,
      foldXor_s_face_eq_qS_decomposition NS 6 c pS pairEnum6 σ ⟨11, by decide⟩ m,
      foldXor_s_face_eq_qS_decomposition NS 6 c pS pairEnum6 σ ⟨12, by decide⟩ m,
      foldXor_s_face_eq_qS_decomposition NS 6 c pS pairEnum6 σ ⟨13, by decide⟩ m,
      foldXor_s_face_eq_qS_decomposition NS 6 c pS pairEnum6 σ ⟨14, by decide⟩ m]
  unfold pairEnum6 pair6_lo pair6_hi
  cases qS_param NS 6 c pS σ ⟨1, by decide⟩ m <;>
    cases qS_param NS 6 c pS σ ⟨2, by decide⟩ m <;>
    cases qS_param NS 6 c pS σ ⟨3, by decide⟩ m <;>
    cases qS_param NS 6 c pS σ ⟨4, by decide⟩ m <;>
    cases qS_param NS 6 c pS σ ⟨5, by decide⟩ m <;> rfl

/-- Single-face indicator at `(s = 0, t = 5)` for K_{NS, 6}. -/
def e_face_layer_NT6 (NS c : Nat) (m : Fin c) : EnrichedFaceVal NS 6 c :=
  fun s t m' =>
    match s.val, t.val with
    | 0, 5 => decide (m.val = m'.val)
    | _, _ => false

/-- ψ-signature for the NT=6 dual family. -/
theorem psi_excl_T0_NT6_signature
    (NS c : Nat) (hNS : 0 < chooseTwo NS) (m m' : Fin c) :
    psi_excl_T0_NT6 NS c m' (e_face_layer_NT6 NS c m)
      = decide (m.val = m'.val) := by
  unfold psi_excl_T0_NT6
  have ht5 :
      foldXor (chooseTwo NS)
        (fun s => e_face_layer_NT6 NS c m s ⟨5, by decide⟩ m')
        = decide (m.val = m'.val) := by
    apply foldXor_only_first_pos (chooseTwo NS) hNS (decide (m.val = m'.val))
    · rfl
    · intro s hs
      unfold e_face_layer_NT6
      match hv : s.val, hs with
      | 0, hcontra => exact absurd rfl hcontra
      | _+1, _ => rfl
  have htk : ∀ (k : Fin (chooseTwo 6)) (hne : k.val ≠ 5),
      foldXor (chooseTwo NS)
        (fun s => e_face_layer_NT6 NS c m s k m') = false := by
    intro k hne
    apply (foldXor_congr_all (chooseTwo NS) _ (fun _ => false) ?_).trans
        (foldXor_const_false _)
    intro s
    unfold e_face_layer_NT6
    rcases hkv : k.val with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
    all_goals (first | (cases s.val <;> rfl) | exact absurd hkv hne |
      exact absurd k.isLt (by decide))
  rw [htk ⟨6,  by decide⟩ (by decide),
      htk ⟨7,  by decide⟩ (by decide),
      htk ⟨8,  by decide⟩ (by decide),
      htk ⟨9,  by decide⟩ (by decide),
      htk ⟨10, by decide⟩ (by decide),
      htk ⟨11, by decide⟩ (by decide),
      htk ⟨12, by decide⟩ (by decide),
      htk ⟨13, by decide⟩ (by decide),
      htk ⟨14, by decide⟩ (by decide),
      ht5]
  cases decide (m.val = m'.val) <;> rfl

/-- `e_face_layer_NT6` is not a coboundary at K_{NS, 6}. -/
theorem e_face_layer_NT6_not_coboundary
    (NS c : Nat) (hNS : 0 < chooseTwo NS) (pS : PairEnum NS) (m : Fin c) :
    ∀ σ : EnrichedEdgeCoch NS 6 c,
      e_face_layer_NT6 NS c m
        ≠ delta1_enr_param NS 6 c pS pairEnum6 σ := by
  intro σ heq
  have h := congrArg (psi_excl_T0_NT6 NS c m) heq
  rw [psi_excl_T0_NT6_signature NS c hNS m m,
      psi_excl_T0_NT6_kills_delta1 NS c pS σ m] at h
  rw [decide_self_true_K44] at h
  exact Bool.noConfusion h

/-- ★★★★★★ Family capstone: K_{NS, 6} for every NS ≥ 2. -/
theorem KNS6_c_independent_h2_classes
    (NS c : Nat) (hNS : 0 < chooseTwo NS) (pS : PairEnum NS) :
    ∀ (m m' : Fin c),
      psi_excl_T0_NT6 NS c m' (e_face_layer_NT6 NS c m)
        = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch NS 6 c,
           e_face_layer_NT6 NS c m
             ≠ delta1_enr_param NS 6 c pS pairEnum6 σ) :=
  fun m m' =>
    ⟨psi_excl_T0_NT6_signature NS c hNS m m',
     e_face_layer_NT6_not_coboundary NS c hNS pS m⟩

end E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTcEvenEven
