/-!
# Enriched 2-complex parametric framework for K_{NS,NT}^{(c)}

Generalizes `V33EnrichedParametric` (NS = NT = 3) to arbitrary
`(NS, NT, c)`.  Provides:

  · `foldXor` — Fin-indexed XOR fold (graph-agnostic)
  · `PairEnum` — `Fin (n.choose 2)` pair enumeration structure
  · `EnrichedEdgeCoch NS NT c` — edge cochain space, `Fin (NS·NT·c)`
  · `EnrichedFaceVal NS NT c` — face value space, `(NS.choose 2) × (NT.choose 2) × c`
  · `face_boundary_param` / `delta1_enr_param` — generic coboundary
  · `psi_layer_param` — layer-`m` ψ-functional via double foldXor
  · `e_face_layer_param` — single-face indicator at layer `m`
  · `psi_layer_signature_param` — Kronecker δ signature theorem
  · `e_face_layer_not_coboundary_param` — non-coboundary under
    abstract kill hypothesis `Hkill`
  · `parametric_c_independent_h2_classes_param` — capstone: `c`
    independent non-coboundary H²-classes under `Hkill`

When `NS = NT = 3`, the kill hypothesis is discharged by
`V33EnrichedParametric.psi_layer_kills_delta1` (the framework
generalises but does NOT re-derive that case-bash result).

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTc

/-! ## §1 — `foldXor`: Fin-indexed XOR fold -/

/-- Left-associated XOR fold over `Fin n → Bool`.
    `foldXor 0 _ = false`; `foldXor (n+1) f = foldXor n (f∘lift) ⊕ f ⟨n, _⟩`. -/
def foldXor : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n+1, f =>
      xor (foldXor n (fun k => f ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩))
          (f ⟨n, Nat.lt_succ_self n⟩)

/-- `foldXor` of the all-false function is `false`. -/
theorem foldXor_const_false : ∀ n : Nat, foldXor n (fun _ => false) = false
  | 0 => rfl
  | n+1 => by
    unfold foldXor
    rw [foldXor_const_false n]
    rfl

/-- Pointwise-agreement congruence — avoids `funext`. -/
theorem foldXor_congr_all : ∀ (n : Nat) (f g : Fin n → Bool),
    (∀ k : Fin n, f k = g k) → foldXor n f = foldXor n g
  | 0, _, _, _ => rfl
  | n+1, f, g, h => by
    show xor (foldXor n (fun k => f ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩))
             (f ⟨n, Nat.lt_succ_self n⟩)
       = xor (foldXor n (fun k => g ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩))
             (g ⟨n, Nat.lt_succ_self n⟩)
    rw [h ⟨n, _⟩]
    rw [foldXor_congr_all n
          (fun k => f ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)
          (fun k => g ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)
          (fun k => h ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)]

/-- `foldXor` over `Fin n` where only `⟨0, _⟩` carries value `a` and every
    higher index is `false` — result is `a`.  Used for "single non-zero
    selector" reductions in the signature theorem. -/
theorem foldXor_only_first : ∀ (n : Nat) (a : Bool) (f : Fin (n+1) → Bool),
    f ⟨0, Nat.succ_pos n⟩ = a →
    (∀ k : Fin (n+1), k.val ≠ 0 → f k = false) →
    foldXor (n+1) f = a
  | 0, a, f, hf0, _ => by
    unfold foldXor
    rw [hf0]
    cases a <;> rfl
  | n+1, a, f, hf0, hfk => by
    show xor (foldXor (n+1) (fun k => f ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩))
             (f ⟨n+1, Nat.lt_succ_self _⟩) = a
    have hlast : f ⟨n+1, Nat.lt_succ_self _⟩ = false :=
      hfk _ (fun h => Nat.noConfusion h)
    rw [hlast]
    have hlift0 :
        (fun (k : Fin (n+1)) => f ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)
          ⟨0, Nat.succ_pos n⟩ = a := hf0
    have hliftk : ∀ k : Fin (n+1), k.val ≠ 0 →
        (fun (k : Fin (n+1)) => f ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩) k = false :=
      fun k hk => hfk ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ hk
    rw [foldXor_only_first n a _ hlift0 hliftk]
    cases a <;> rfl

/-- Variant of `foldXor_only_first` accepting any positive `n` (delegates
    to the `n+1`-form internally). -/
theorem foldXor_only_first_pos (n : Nat) (hn : 0 < n) (a : Bool) (f : Fin n → Bool)
    (hf0 : f ⟨0, hn⟩ = a)
    (hfk : ∀ k : Fin n, k.val ≠ 0 → f k = false) :
    foldXor n f = a := by
  match n, hn, f, hf0, hfk with
  | n'+1, _, f, hf0, hfk => exact foldXor_only_first n' a f hf0 hfk

/-! ### `foldXor` expansion lemmas at small `n`

Explicit reduction `foldXor n f = xor (xor … (f 0)) … (f (n-1))` for
small `n`.  Used to unfold parametric ψ-functionals at concrete
`(NS, NT)` instances so case-bash on edge values proceeds. -/

/-- Recursion equation: `foldXor (n+1) f = foldXor n (f∘lift) ⊕ f ⟨n, _⟩`. -/
theorem foldXor_succ (n : Nat) (f : Fin (n+1) → Bool) :
    foldXor (n+1) f
      = xor (foldXor n (fun k => f ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩))
            (f ⟨n, Nat.lt_succ_self n⟩) := rfl

/-- `foldXor 3 f = (f 0) ⊕ (f 1) ⊕ (f 2)` (left-associated).
    `xor false a = a` is *not* definitional in Lean 4 (Bool.xor case-
    splits on both args), so we expand via the raw form and `cases` out
    the leading `false`. -/
theorem foldXor_3 (f : Fin 3 → Bool) :
    foldXor 3 f
      = xor (xor (f ⟨0, by decide⟩) (f ⟨1, by decide⟩))
            (f ⟨2, by decide⟩) := by
  have h : foldXor 3 f
      = xor (xor (xor false (f ⟨0, by decide⟩)) (f ⟨1, by decide⟩))
            (f ⟨2, by decide⟩) := rfl
  rw [h]
  cases f ⟨0, by decide⟩ <;> rfl

/-! ## §2 — Pair enumeration structure

A pair enumeration on `Fin n` exposes the two endpoints of each
pair indexed by `Fin (chooseTwo n)`.  No order constraint is needed
for the framework — the face boundary uses `lo` and `hi`
symmetrically.

`chooseTwo n = n·(n−1)/2` — local definition since core Lean lacks
`Nat.choose`. -/

/-- Binomial coefficient `n.choose 2 = n·(n−1)/2`.  `abbrev` so that
    `Fin (chooseTwo k)` reduces to a literal `Fin n` at small `k`,
    enabling case-bash proofs of `KillsDelta1` at concrete instances. -/
abbrev chooseTwo (n : Nat) : Nat := n * (n - 1) / 2

/-- Concrete values: `chooseTwo 3 = 3`, `chooseTwo 4 = 6`, `chooseTwo 5 = 10`. -/
theorem chooseTwo_eval :
    chooseTwo 2 = 1 ∧ chooseTwo 3 = 3 ∧ chooseTwo 4 = 6 ∧ chooseTwo 5 = 10 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Enumeration of unordered pairs `{i, j} ⊂ Fin n` indexed by
    `Fin (chooseTwo n)`.  Bundles low and high endpoint selectors. -/
structure PairEnum (n : Nat) where
  /-- Low endpoint of pair `s`. -/
  lo : Fin (chooseTwo n) → Fin n
  /-- High endpoint of pair `s`. -/
  hi : Fin (chooseTwo n) → Fin n

/-! ## §3 — Parametric edge / face cochain types

Edge cochain: `Fin (NS·NT·c) → Bool`.  Encoding for `(i, j, m)`:
  · index `(NS·NT)·m + NT·i + j` (mult `m` is the high block).

Face value: `Fin (NS.choose 2) → Fin (NT.choose 2) → Fin c → Bool`.
3D-indexed by `(S-pair, T-pair, mult)` — no Nat decoding needed. -/

/-- Edge cochain space for the enriched 2-complex on K_{NS,NT}^{(c)}. -/
def EnrichedEdgeCoch (NS NT c : Nat) : Type := Fin (NS * NT * c) → Bool

/-- Face value space for the enriched 2-complex on K_{NS,NT}^{(c)}.
    Indexed by `(s, t, m)` with `s ∈ Fin (chooseTwo NS)`,
    `t ∈ Fin (chooseTwo NT)`, `m ∈ Fin c`. -/
def EnrichedFaceVal (NS NT c : Nat) : Type :=
  Fin (chooseTwo NS) → Fin (chooseTwo NT) → Fin c → Bool

/-! ### Edge index bound -/

/-- Bound: `(NS·NT)·m + NT·i + j < NS·NT·c` for `i < NS, j < NT, m < c`. -/
private theorem edge_index_bound (NS NT c i j m : Nat)
    (hi : i < NS) (hj : j < NT) (hm : m < c) :
    NS * NT * m + NT * i + j < NS * NT * c := by
  have hNTij : NT * i + j < NS * NT := by
    have hisucc : i + 1 ≤ NS := hi
    calc NT * i + j
        < NT * i + NT := Nat.add_lt_add_left hj _
      _ = NT * (i + 1) := (Nat.mul_succ NT i).symm
      _ ≤ NT * NS := Nat.mul_le_mul_left NT hisucc
      _ = NS * NT := Nat.mul_comm _ _
  have hblock : NS * NT * m + NS * NT ≤ NS * NT * c := by
    have hmsucc : m + 1 ≤ c := hm
    calc NS * NT * m + NS * NT
        = NS * NT * (m + 1) := (Nat.mul_succ _ _).symm
      _ ≤ NS * NT * c := Nat.mul_le_mul_left _ hmsucc
  calc NS * NT * m + NT * i + j
      = NS * NT * m + (NT * i + j) := Nat.add_assoc _ _ _
    _ < NS * NT * m + NS * NT := Nat.add_lt_add_left hNTij _
    _ ≤ NS * NT * c := hblock

/-- Edge index in `Fin (NS·NT·c)` from `(i : Fin NS, j : Fin NT, m : Fin c)`. -/
def edge_idx_param (NS NT c : Nat) (i : Fin NS) (j : Fin NT) (m : Fin c) :
    Fin (NS * NT * c) :=
  ⟨NS * NT * m.val + NT * i.val + j.val,
   edge_index_bound NS NT c i.val j.val m.val i.isLt j.isLt m.isLt⟩

/-! ## §4 — Parametric face boundary + δ¹

Face boundary at `(s, t, m)` uses the 4 edges
`(lo s, lo t, m), (lo s, hi t, m), (hi s, lo t, m), (hi s, hi t, m)` —
same XOR pattern as V33EnrichedParametric but with arbitrary pair
enumeration `pS`, `pT`. -/

/-- Face boundary at `(s, t, m)`: XOR over 4 corner-edges of the
    4-cycle on `{pS.lo s, pS.hi s} × {pT.lo t, pT.hi t}`. -/
def face_boundary_param (NS NT c : Nat) (pS : PairEnum NS) (pT : PairEnum NT)
    (σ : EnrichedEdgeCoch NS NT c) (s : Fin (chooseTwo NS))
    (t : Fin (chooseTwo NT)) (m : Fin c) : Bool :=
  xor (xor (xor
    (σ (edge_idx_param NS NT c (pS.lo s) (pT.lo t) m))
    (σ (edge_idx_param NS NT c (pS.lo s) (pT.hi t) m)))
    (σ (edge_idx_param NS NT c (pS.hi s) (pT.lo t) m)))
    (σ (edge_idx_param NS NT c (pS.hi s) (pT.hi t) m))

/-- Parametric enriched coboundary `δ¹_enr : EdgeCoch → FaceVal`. -/
def delta1_enr_param (NS NT c : Nat) (pS : PairEnum NS) (pT : PairEnum NT)
    (σ : EnrichedEdgeCoch NS NT c) : EnrichedFaceVal NS NT c :=
  fun s t m => face_boundary_param NS NT c pS pT σ s t m

/-! ## §5 — Parametric ψ-functional via double foldXor

`psi_layer_param m v` = XOR over all `(s, t) ∈ Fin (chooseTwo NS) ×
Fin (chooseTwo NT)` of `v s t m`.  Probes only the slice at
multiplicity `m`. -/

/-- Layer-`m` ψ-functional, generic in `(NS, NT, c)`. -/
def psi_layer_param (NS NT c : Nat) (m : Fin c)
    (v : EnrichedFaceVal NS NT c) : Bool :=
  foldXor (chooseTwo NS) (fun s =>
    foldXor (chooseTwo NT) (fun t => v s t m))

/-! ## §6 — Single-face indicator + Kronecker signature

`e_face_layer_param NS NT c m` returns `true` only at
`(s.val = 0, t.val = 0, m' = m)`.  Its `ψ_{m'}`-signature is the
Kronecker δ `decide (m.val = m'.val)`. -/

/-- Single-face indicator at layer `m`, position `(s=0, t=0)`. -/
def e_face_layer_param (NS NT c : Nat) (m : Fin c) : EnrichedFaceVal NS NT c :=
  fun s t m' =>
    match s.val, t.val with
    | 0, 0 => decide (m.val = m'.val)
    | _, _ => false

/-- `decide (n = n) = true`.  Used to extract Kronecker δ at `m = m'`. -/
private theorem decide_self_true (n : Nat) : decide (n = n) = true := by
  cases h : decide (n = n) with
  | true => rfl
  | false => exact absurd rfl (of_decide_eq_false h)

/-- ψ-signature: `ψ_{m'}(e_face_layer m) = decide (m = m')`.

    Requires `chooseTwo NS ≥ 1` and `chooseTwo NT ≥ 1` (i.e., `NS ≥ 2`
    and `NT ≥ 2`).  Proof reduces the double `foldXor` to its `(s=0, t=0)`
    component via `foldXor_only_first`. -/
theorem psi_layer_signature_param (NS NT c : Nat)
    (hNS : 0 < chooseTwo NS) (hNT : 0 < chooseTwo NT)
    (m m' : Fin c) :
    psi_layer_param NS NT c m' (e_face_layer_param NS NT c m)
      = decide (m.val = m'.val) := by
  unfold psi_layer_param
  refine foldXor_only_first_pos (chooseTwo NS) hNS (decide (m.val = m'.val)) _ ?_ ?_
  · -- s = ⟨0, _⟩: inner fold reduces to (t = 0) contribution.
    refine foldXor_only_first_pos (chooseTwo NT) hNT (decide (m.val = m'.val)) _ ?_ ?_
    · rfl
    · intro t ht
      unfold e_face_layer_param
      match hval : t.val, ht with
      | 0, hcontra => exact absurd rfl hcontra
      | _+1, _ => rfl
  · intro s hs
    apply (foldXor_congr_all (chooseTwo NT) _ (fun _ => false) ?_).trans
    · exact foldXor_const_false _
    · intro t
      unfold e_face_layer_param
      match hval : s.val, hs with
      | 0, hcontra => exact absurd rfl hcontra
      | _+1, _ => rfl

/-! ## §7 — Kill hypothesis + non-coboundary

The combinatorial heart of "ψ kills coboundaries": each layer-`m`
edge `(i, j, m)` appears in `(NS−1)·(NT−1)` layer-`m` face boundaries
(one per S-pair containing `i` × T-pair containing `j`).  When that
count is even, the XOR sum cancels and `ψ_m(δ¹_enr σ) = false`.

We expose the kill statement as an abstract `Prop`-level hypothesis
`KillsDelta1`.  Concrete instances (e.g. `(NS, NT) = (3, 3)`) discharge
it by case-bash; the framework's structural results (signature, non-
coboundary, c-independent classes) are then immediate. -/

/-- "`ψ_m` kills `imδ¹_enr`" — abstract kill predicate for parameters
    `(NS, NT, c, pS, pT)`.  Holds whenever `(NS−1)·(NT−1)` is even
    (≡ `NS` odd or `NT` odd); the combinatorial argument is discharged
    per instance. -/
def KillsDelta1 (NS NT c : Nat) (pS : PairEnum NS) (pT : PairEnum NT) : Prop :=
  ∀ (σ : EnrichedEdgeCoch NS NT c) (m : Fin c),
    psi_layer_param NS NT c m (delta1_enr_param NS NT c pS pT σ) = false

/-- Non-coboundary: `e_face_layer m` is not in the image of `δ¹_enr`,
    provided `ψ_m` kills `imδ¹_enr` and the pair counts are positive. -/
theorem e_face_layer_not_coboundary_param (NS NT c : Nat)
    (hNS : 0 < chooseTwo NS) (hNT : 0 < chooseTwo NT)
    (pS : PairEnum NS) (pT : PairEnum NT)
    (Hkill : KillsDelta1 NS NT c pS pT) (m : Fin c) :
    ∀ σ : EnrichedEdgeCoch NS NT c,
      e_face_layer_param NS NT c m ≠ delta1_enr_param NS NT c pS pT σ := by
  intro σ heq
  have h := congrArg (psi_layer_param NS NT c m) heq
  rw [psi_layer_signature_param NS NT c hNS hNT m m, Hkill σ m] at h
  rw [decide_self_true] at h
  exact Bool.noConfusion h

/-! ## §8 — Parametric capstone: `c` independent H²-classes

For every `c`, the `c` indicators `e_face_layer_param m` for
`m ∈ Fin c` give `c` mutually distinguishable non-coboundary face
cochains — one per multiplicity layer.  Consequence: cup-image
codim in H²_enr ≥ c. -/

/-- Capstone: under `KillsDelta1`, every layer carries an independent
    non-coboundary H²-class with Kronecker-δ ψ-signature. -/
theorem parametric_c_independent_h2_classes_param (NS NT c : Nat)
    (hNS : 0 < chooseTwo NS) (hNT : 0 < chooseTwo NT)
    (pS : PairEnum NS) (pT : PairEnum NT)
    (Hkill : KillsDelta1 NS NT c pS pT) :
    ∀ (m m' : Fin c),
      psi_layer_param NS NT c m'
        (e_face_layer_param NS NT c m) = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch NS NT c,
           e_face_layer_param NS NT c m
             ≠ delta1_enr_param NS NT c pS pT σ) :=
  fun m m' =>
    ⟨psi_layer_signature_param NS NT c hNS hNT m m',
     e_face_layer_not_coboundary_param NS NT c hNS hNT pS pT Hkill m⟩

/-! ## §9 — Concrete pair enumeration on `Fin 3`

The 3 unordered pairs of `Fin 3`: `{0,1}, {0,2}, {1,2}`.  Matches
the convention used in `V33EnrichedParametric.pair_lo` / `pair_hi`. -/

/-- Low endpoint of the `s`-th pair of `Fin 3`. -/
def pair3_lo : Fin (chooseTwo 3) → Fin 3
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨0, by decide⟩
  | ⟨_+2, _⟩ => ⟨1, by decide⟩

/-- High endpoint of the `s`-th pair of `Fin 3`. -/
def pair3_hi : Fin (chooseTwo 3) → Fin 3
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨_+2, _⟩ => ⟨2, by decide⟩

/-- Concrete `PairEnum 3` matching V33EnrichedParametric. -/
def pairEnum3 : PairEnum 3 where
  lo := pair3_lo
  hi := pair3_hi

/-! ## §10 — Concrete kill at `(NS, NT) = (3, 3)`

Each layer-`m` edge `(i, j, m)` appears in `(3−1)·(3−1) = 4` layer-`m`
face boundaries (even), so `ψ_m(δ¹_enr σ) = false`.  Proven by case-
bash on the 9 layer-`m` edges with `pairEnum3`. -/

set_option maxHeartbeats 1600000 in
theorem psi_layer_param_kills_delta1_K33
    (c : Nat) (σ : EnrichedEdgeCoch 3 3 c) (m : Fin c) :
    psi_layer_param 3 3 c m
      (delta1_enr_param 3 3 c pairEnum3 pairEnum3 σ) = false := by
  unfold psi_layer_param
  rw [foldXor_3, foldXor_3, foldXor_3, foldXor_3]
  unfold delta1_enr_param face_boundary_param pairEnum3 pair3_lo pair3_hi
  cases σ (edge_idx_param 3 3 c ⟨0, by decide⟩ ⟨0, by decide⟩ m) <;>
    cases σ (edge_idx_param 3 3 c ⟨0, by decide⟩ ⟨1, by decide⟩ m) <;>
    cases σ (edge_idx_param 3 3 c ⟨0, by decide⟩ ⟨2, by decide⟩ m) <;>
    cases σ (edge_idx_param 3 3 c ⟨1, by decide⟩ ⟨0, by decide⟩ m) <;>
    cases σ (edge_idx_param 3 3 c ⟨1, by decide⟩ ⟨1, by decide⟩ m) <;>
    cases σ (edge_idx_param 3 3 c ⟨1, by decide⟩ ⟨2, by decide⟩ m) <;>
    cases σ (edge_idx_param 3 3 c ⟨2, by decide⟩ ⟨0, by decide⟩ m) <;>
    cases σ (edge_idx_param 3 3 c ⟨2, by decide⟩ ⟨1, by decide⟩ m) <;>
    cases σ (edge_idx_param 3 3 c ⟨2, by decide⟩ ⟨2, by decide⟩ m) <;> rfl

/-- `KillsDelta1` is discharged at `(NS, NT) = (3, 3)` for every `c`. -/
theorem kills_delta1_K33 (c : Nat) :
    KillsDelta1 3 3 c pairEnum3 pairEnum3 :=
  fun σ m => psi_layer_param_kills_delta1_K33 c σ m

/-! ## §11 — K_{3,3} parametric capstone via the generic framework

Instantiates the generic capstone at `(NS, NT) = (3, 3)`, recovering
the parametric `codim ≥ c` content of `V33EnrichedParametric`. -/

/-- For K_{3,3}^{(c)}: every layer carries an independent non-coboundary
    H²-class.  Discharged through the generic `(NS, NT, c)`-parametric
    framework. -/
theorem K33_c_independent_h2_classes_via_framework (c : Nat) :
    ∀ (m m' : Fin c),
      psi_layer_param 3 3 c m'
        (e_face_layer_param 3 3 c m) = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 3 3 c,
           e_face_layer_param 3 3 c m
             ≠ delta1_enr_param 3 3 c pairEnum3 pairEnum3 σ) :=
  parametric_c_independent_h2_classes_param 3 3 c
    (by decide) (by decide) pairEnum3 pairEnum3 (kills_delta1_K33 c)

end E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTc
