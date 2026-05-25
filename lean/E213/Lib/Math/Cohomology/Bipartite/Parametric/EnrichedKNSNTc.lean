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

/-- `foldXor 10 f` as a 10-fold left-associated XOR.  Used to expand
    parametric ψ-functionals at NS=5 (10 S-pairs). -/
theorem foldXor_10 (f : Fin 10 → Bool) :
    foldXor 10 f
      = xor (xor (xor (xor (xor (xor (xor (xor (xor
          (f ⟨0, by decide⟩) (f ⟨1, by decide⟩))
          (f ⟨2, by decide⟩)) (f ⟨3, by decide⟩))
          (f ⟨4, by decide⟩)) (f ⟨5, by decide⟩))
          (f ⟨6, by decide⟩)) (f ⟨7, by decide⟩))
          (f ⟨8, by decide⟩)) (f ⟨9, by decide⟩) := by
  have h : foldXor 10 f
      = xor (xor (xor (xor (xor (xor (xor (xor (xor (xor false
          (f ⟨0, by decide⟩)) (f ⟨1, by decide⟩))
          (f ⟨2, by decide⟩)) (f ⟨3, by decide⟩))
          (f ⟨4, by decide⟩)) (f ⟨5, by decide⟩))
          (f ⟨6, by decide⟩)) (f ⟨7, by decide⟩))
          (f ⟨8, by decide⟩)) (f ⟨9, by decide⟩) := rfl
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

/-! ## §12 — `foldXor` linearity over pointwise XOR

`foldXor n (k ↦ f k ⊕ g k) = foldXor n f ⊕ foldXor n g` — XOR sum
distributes over pointwise XOR.  Proved by induction on `n` using
the AC pair-swap `(a⊕b)⊕(c⊕d) = (a⊕c)⊕(b⊕d)`. -/

/-- Bool-XOR AC pair swap.  Mirrors `BoolXORFold.xor_pair_swap`. -/
private theorem xor_pair_swap (a b c d : Bool) :
    xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- `foldXor` linearity: distributes over pointwise XOR of the indexed
    family. -/
theorem foldXor_xor_distribute :
    ∀ (n : Nat) (f g : Fin n → Bool),
      foldXor n (fun k => xor (f k) (g k))
        = xor (foldXor n f) (foldXor n g)
  | 0, _, _ => rfl
  | n+1, f, g => by
    unfold foldXor
    rw [foldXor_xor_distribute n
          (fun k => f ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)
          (fun k => g ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩)]
    exact xor_pair_swap _ _ _ _

/-! ## §13 — Row-wise Q functional and t-fold decomposition

`qT_param i m` = XOR over `t ∈ Fin (chooseTwo NT)` of the 2 row-`i`
edges at the two T-pair endpoints:
  ⊕_t [σ(i, lo_t, m) ⊕ σ(i, hi_t, m)]

For fixed S-pair `s`, the t-fold sum of face boundaries factors:
  ⊕_t face_boundary(s, t, m, σ)  =  qT(lo_s, m) ⊕ qT(hi_s, m). -/

/-- Row-wise `Q`-functional at vertex `i ∈ Fin NS`, layer `m ∈ Fin c`.
    XOR over all T-pairs of σ at the two T-pair endpoints. -/
def qT_param (NS NT c : Nat) (pT : PairEnum NT)
    (σ : EnrichedEdgeCoch NS NT c) (i : Fin NS) (m : Fin c) : Bool :=
  foldXor (chooseTwo NT) (fun t =>
    xor (σ (edge_idx_param NS NT c i (pT.lo t) m))
        (σ (edge_idx_param NS NT c i (pT.hi t) m)))

/-- t-fold decomposition: for fixed S-pair `s`, the XOR over T-pairs
    of `face_boundary(s, t, m, σ)` factors as
    `qT(lo_s, m) ⊕ qT(hi_s, m)`. -/
theorem foldXor_t_face_eq_qT_decomposition
    (NS NT c : Nat) (pS : PairEnum NS) (pT : PairEnum NT)
    (σ : EnrichedEdgeCoch NS NT c) (s : Fin (chooseTwo NS)) (m : Fin c) :
    foldXor (chooseTwo NT)
        (fun t => face_boundary_param NS NT c pS pT σ s t m)
      = xor (qT_param NS NT c pT σ (pS.lo s) m)
            (qT_param NS NT c pT σ (pS.hi s) m) := by
  unfold qT_param
  rw [← foldXor_xor_distribute]
  apply foldXor_congr_all
  intro t
  unfold face_boundary_param
  cases σ (edge_idx_param NS NT c (pS.lo s) (pT.lo t) m) <;>
    cases σ (edge_idx_param NS NT c (pS.lo s) (pT.hi t) m) <;>
    cases σ (edge_idx_param NS NT c (pS.hi s) (pT.lo t) m) <;>
    cases σ (edge_idx_param NS NT c (pS.hi s) (pT.hi t) m) <;> rfl

/-! ## §14 — Master kill via Q-decomposition

Under the hypothesis `Q_T ≡ 0` (XOR over T-pairs of row-`i` edges
cancels — equivalent to NT odd given a covering pair enumeration),
`psi_layer_param m (δ¹_enr σ) = false` for all `σ, m`.

This packages the abstract structural argument: NT odd ⇒ each
T-vertex appears in `NT − 1` (even) pairs ⇒ row-wise XOR cancels
⇒ ψ-kill. -/

/-- Master kill via Q-decomposition.  If `qT_param i m σ = false`
    for all `i, m`, then `ψ_m(δ¹_enr σ) = false`. -/
theorem psi_layer_kill_of_qT_zero
    (NS NT c : Nat) (pS : PairEnum NS) (pT : PairEnum NT)
    (σ : EnrichedEdgeCoch NS NT c) (m : Fin c)
    (hQT : ∀ i : Fin NS, qT_param NS NT c pT σ i m = false) :
    psi_layer_param NS NT c m
      (delta1_enr_param NS NT c pS pT σ) = false := by
  unfold psi_layer_param delta1_enr_param
  -- Reduce outer fold via Q-decomposition at each s.
  have hinner : ∀ s : Fin (chooseTwo NS),
      foldXor (chooseTwo NT)
          (fun t => face_boundary_param NS NT c pS pT σ s t m) = false := by
    intro s
    rw [foldXor_t_face_eq_qT_decomposition NS NT c pS pT σ s m,
        hQT (pS.lo s), hQT (pS.hi s)]
    rfl
  -- Now outer foldXor is over all-false; equals false.
  apply (foldXor_congr_all (chooseTwo NS) _ (fun _ => false) hinner).trans
  exact foldXor_const_false _

/-! ## §15 — Concrete `qT = 0` at NT = 3 (any NS, c, i, m)

For `NT = 3` with `pairEnum3`, the row-wise Q-functional vanishes:
each row-`i` edge `σ(i, j, m)` appears twice (once with `j = lo_t`,
once with `j = hi_t`) across the 3 T-pairs, so XOR cancels. -/

set_option maxHeartbeats 400000 in
theorem qT_param_zero_NT3 (NS c : Nat) (σ : EnrichedEdgeCoch NS 3 c)
    (i : Fin NS) (m : Fin c) :
    qT_param NS 3 c pairEnum3 σ i m = false := by
  unfold qT_param pairEnum3 pair3_lo pair3_hi
  rw [foldXor_3]
  cases σ (edge_idx_param NS 3 c i ⟨0, by decide⟩ m) <;>
    cases σ (edge_idx_param NS 3 c i ⟨1, by decide⟩ m) <;>
    cases σ (edge_idx_param NS 3 c i ⟨2, by decide⟩ m) <;> rfl

/-- KillsDelta1 holds for every `(NS, 3)` instance: any NS-side pair
    enumeration `pS`, with `pT = pairEnum3` on the NT=3 side.  This
    is the parity-OK case `NT odd ⇒ (NS−1)·(NT−1) even`. -/
theorem kills_delta1_KNS3 (NS c : Nat) (pS : PairEnum NS) :
    KillsDelta1 NS 3 c pS pairEnum3 := by
  intro σ m
  exact psi_layer_kill_of_qT_zero NS 3 c pS pairEnum3 σ m
    (fun i => qT_param_zero_NT3 NS c σ i m)

/-! ## §16 — Concrete pair enumeration on `Fin 4`

The 6 unordered pairs of `Fin 4` in lex order:
`{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}`.  Matches the convention
used in `V43`. -/

/-- Low endpoint of the `s`-th pair of `Fin 4`. -/
def pair4_lo : Fin (chooseTwo 4) → Fin 4
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨0, by decide⟩
  | ⟨2, _⟩ => ⟨0, by decide⟩
  | ⟨3, _⟩ => ⟨1, by decide⟩
  | ⟨4, _⟩ => ⟨1, by decide⟩
  | ⟨_+5, _⟩ => ⟨2, by decide⟩

/-- High endpoint of the `s`-th pair of `Fin 4`. -/
def pair4_hi : Fin (chooseTwo 4) → Fin 4
  | ⟨0, _⟩ => ⟨1, by decide⟩
  | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨3, by decide⟩
  | ⟨3, _⟩ => ⟨2, by decide⟩
  | ⟨4, _⟩ => ⟨3, by decide⟩
  | ⟨_+5, _⟩ => ⟨3, by decide⟩

/-- Concrete `PairEnum 4` (6 pairs in lex order). -/
def pairEnum4 : PairEnum 4 where
  lo := pair4_lo
  hi := pair4_hi

/-! ## §17 — K_{4,3} kill via abstract Q-decomposition

For `(NS, NT) = (4, 3)`: NT=3 is odd, so the `qT = 0` argument
discharges `KillsDelta1` with no extra case-bash (12-edge brute
force is infeasible; the abstract route via §14 + §15 closes it
in O(8) σ-case-bashes per Q evaluation). -/

/-- `KillsDelta1` at `(NS, NT) = (4, 3)` via the abstract NT=3 kill. -/
theorem kills_delta1_K43 (c : Nat) :
    KillsDelta1 4 3 c pairEnum4 pairEnum3 :=
  kills_delta1_KNS3 4 c pairEnum4

/-- For K_{4,3}^{(c)}: every layer carries an independent non-coboundary
    H²-class.  Discharged via the abstract `(NS, NT=3)` framework
    (avoiding the infeasible 12-edge case-bash). -/
theorem K43_c_independent_h2_classes_via_framework (c : Nat) :
    ∀ (m m' : Fin c),
      psi_layer_param 4 3 c m'
        (e_face_layer_param 4 3 c m) = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 4 3 c,
           e_face_layer_param 4 3 c m
             ≠ delta1_enr_param 4 3 c pairEnum4 pairEnum3 σ) :=
  parametric_c_independent_h2_classes_param 4 3 c
    (by decide) (by decide) pairEnum4 pairEnum3 (kills_delta1_K43 c)

/-! ## §18 — K_{5,3} kill via the same abstract route

NS=5 (with `pairEnum5`) does not even need to be defined for the
kill — the abstract `kills_delta1_KNS3` discharges ANY NS once we
have a `PairEnum NS`.  We construct `pairEnum5` for completeness. -/

/-- Low endpoint of the `s`-th pair of `Fin 5` (10 pairs in lex order). -/
def pair5_lo : Fin (chooseTwo 5) → Fin 5
  | ⟨0, _⟩ => ⟨0, by decide⟩ | ⟨1, _⟩ => ⟨0, by decide⟩
  | ⟨2, _⟩ => ⟨0, by decide⟩ | ⟨3, _⟩ => ⟨0, by decide⟩
  | ⟨4, _⟩ => ⟨1, by decide⟩ | ⟨5, _⟩ => ⟨1, by decide⟩
  | ⟨6, _⟩ => ⟨1, by decide⟩ | ⟨7, _⟩ => ⟨2, by decide⟩
  | ⟨8, _⟩ => ⟨2, by decide⟩ | ⟨_+9, _⟩ => ⟨3, by decide⟩

/-- High endpoint of the `s`-th pair of `Fin 5`. -/
def pair5_hi : Fin (chooseTwo 5) → Fin 5
  | ⟨0, _⟩ => ⟨1, by decide⟩ | ⟨1, _⟩ => ⟨2, by decide⟩
  | ⟨2, _⟩ => ⟨3, by decide⟩ | ⟨3, _⟩ => ⟨4, by decide⟩
  | ⟨4, _⟩ => ⟨2, by decide⟩ | ⟨5, _⟩ => ⟨3, by decide⟩
  | ⟨6, _⟩ => ⟨4, by decide⟩ | ⟨7, _⟩ => ⟨3, by decide⟩
  | ⟨8, _⟩ => ⟨4, by decide⟩ | ⟨_+9, _⟩ => ⟨4, by decide⟩

/-- Concrete `PairEnum 5` (10 pairs in lex order). -/
def pairEnum5 : PairEnum 5 where
  lo := pair5_lo
  hi := pair5_hi

/-- `KillsDelta1` at `(NS, NT) = (5, 3)` via the abstract NT=3 kill. -/
theorem kills_delta1_K53 (c : Nat) :
    KillsDelta1 5 3 c pairEnum5 pairEnum3 :=
  kills_delta1_KNS3 5 c pairEnum5

/-- For K_{5,3}^{(c)}: every layer carries an independent non-coboundary
    H²-class. -/
theorem K53_c_independent_h2_classes_via_framework (c : Nat) :
    ∀ (m m' : Fin c),
      psi_layer_param 5 3 c m'
        (e_face_layer_param 5 3 c m) = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 5 3 c,
           e_face_layer_param 5 3 c m
             ≠ delta1_enr_param 5 3 c pairEnum5 pairEnum3 σ) :=
  parametric_c_independent_h2_classes_param 5 3 c
    (by decide) (by decide) pairEnum5 pairEnum3 (kills_delta1_K53 c)

/-! ## §19 — Symmetric column-wise `qS` decomposition (for NS odd)

Mirror of §13: for fixed T-pair `t`, the s-fold sum of face boundaries
factors via a column-wise Q-functional `qS j m` summing over S-pairs.
Used when NS is odd (so each S-vertex appears in `NS-1` (even) pairs
and the column XOR cancels). -/

/-- Column-wise `Q`-functional at vertex `j ∈ Fin NT`, layer `m ∈ Fin c`. -/
def qS_param (NS NT c : Nat) (pS : PairEnum NS)
    (σ : EnrichedEdgeCoch NS NT c) (j : Fin NT) (m : Fin c) : Bool :=
  foldXor (chooseTwo NS) (fun s =>
    xor (σ (edge_idx_param NS NT c (pS.lo s) j m))
        (σ (edge_idx_param NS NT c (pS.hi s) j m)))

/-- s-fold decomposition: for fixed T-pair `t`, the XOR over S-pairs
    of `face_boundary(s, t, m, σ)` factors as
    `qS(lo_t, m) ⊕ qS(hi_t, m)`. -/
theorem foldXor_s_face_eq_qS_decomposition
    (NS NT c : Nat) (pS : PairEnum NS) (pT : PairEnum NT)
    (σ : EnrichedEdgeCoch NS NT c) (t : Fin (chooseTwo NT)) (m : Fin c) :
    foldXor (chooseTwo NS)
        (fun s => face_boundary_param NS NT c pS pT σ s t m)
      = xor (qS_param NS NT c pS σ (pT.lo t) m)
            (qS_param NS NT c pS σ (pT.hi t) m) := by
  unfold qS_param
  rw [← foldXor_xor_distribute]
  apply foldXor_congr_all
  intro s
  unfold face_boundary_param
  cases σ (edge_idx_param NS NT c (pS.lo s) (pT.lo t) m) <;>
    cases σ (edge_idx_param NS NT c (pS.lo s) (pT.hi t) m) <;>
    cases σ (edge_idx_param NS NT c (pS.hi s) (pT.lo t) m) <;>
    cases σ (edge_idx_param NS NT c (pS.hi s) (pT.hi t) m) <;> rfl

/-! ## §20 — Master kill via `qS = 0` (NS-side)

`psi_layer_param` can equally be reorganised as a double fold with
s on the inside (after swapping fold order — which follows from
`foldXor_xor_distribute` + congruence).  Master kill: if `qS j m σ
= false` for all j, then ψ kills δ¹.

We obtain the symmetric kill by FACTORING THROUGH the t-fold using
the dual relation `psi_layer = ⊕_t ⊕_s face_boundary`.  Since
foldXor is symmetric under fold-order swap when the body factors,
the same argument applies. -/

/-- foldXor symmetry: `⊕_s ⊕_t f s t = ⊕_t ⊕_s f s t` for any
    `f : Fin n → Fin m → Bool`.  Two foldXor's commute because XOR
    is commutative-associative. -/
theorem foldXor_swap :
    ∀ (n m : Nat) (f : Fin n → Fin m → Bool),
      foldXor n (fun s => foldXor m (fun t => f s t))
        = foldXor m (fun t => foldXor n (fun s => f s t))
  | 0, m, _ => (foldXor_const_false m).symm
  | n+1, m, f => by
    show xor (foldXor n
              (fun s => foldXor m (fun t =>
                f ⟨s.val, Nat.lt_succ_of_lt s.isLt⟩ t)))
             (foldXor m (fun t => f ⟨n, Nat.lt_succ_self n⟩ t))
       = foldXor m (fun t => foldXor (n+1) (fun s => f s t))
    rw [foldXor_swap n m
          (fun s t => f ⟨s.val, Nat.lt_succ_of_lt s.isLt⟩ t)]
    rw [← foldXor_xor_distribute]
    apply foldXor_congr_all
    intro t
    rfl

/-- Master kill via `qS`-decomposition.  If `qS_param j m σ = false`
    for all `j, m`, then `ψ_m(δ¹_enr σ) = false`. -/
theorem psi_layer_kill_of_qS_zero
    (NS NT c : Nat) (pS : PairEnum NS) (pT : PairEnum NT)
    (σ : EnrichedEdgeCoch NS NT c) (m : Fin c)
    (hQS : ∀ j : Fin NT, qS_param NS NT c pS σ j m = false) :
    psi_layer_param NS NT c m
      (delta1_enr_param NS NT c pS pT σ) = false := by
  unfold psi_layer_param delta1_enr_param
  rw [foldXor_swap]
  have hinner : ∀ t : Fin (chooseTwo NT),
      foldXor (chooseTwo NS)
          (fun s => face_boundary_param NS NT c pS pT σ s t m) = false := by
    intro t
    rw [foldXor_s_face_eq_qS_decomposition NS NT c pS pT σ t m,
        hQS (pT.lo t), hQS (pT.hi t)]
    rfl
  apply (foldXor_congr_all (chooseTwo NT) _ (fun _ => false) hinner).trans
  exact foldXor_const_false _

/-! ## §21 — Concrete `qS = 0` at NS = 3 (any NT, c, j, m)

Mirror of §15: for `NS = 3` with `pairEnum3`, the column-wise
Q-functional vanishes. -/

set_option maxHeartbeats 400000 in
theorem qS_param_zero_NS3 (NT c : Nat) (σ : EnrichedEdgeCoch 3 NT c)
    (j : Fin NT) (m : Fin c) :
    qS_param 3 NT c pairEnum3 σ j m = false := by
  unfold qS_param pairEnum3 pair3_lo pair3_hi
  rw [foldXor_3]
  cases σ (edge_idx_param 3 NT c ⟨0, by decide⟩ j m) <;>
    cases σ (edge_idx_param 3 NT c ⟨1, by decide⟩ j m) <;>
    cases σ (edge_idx_param 3 NT c ⟨2, by decide⟩ j m) <;> rfl

/-- KillsDelta1 for every `(3, NT)` instance: NS=3 odd ⇒ qS = 0. -/
theorem kills_delta1_K3NT (NT c : Nat) (pT : PairEnum NT) :
    KillsDelta1 3 NT c pairEnum3 pT := by
  intro σ m
  exact psi_layer_kill_of_qS_zero 3 NT c pairEnum3 pT σ m
    (fun j => qS_param_zero_NS3 NT c σ j m)

/-! ## §22 — K_{3,4} and K_{3,5} kill via the dual abstract route

`(3, 4)`: NS=3 odd ⇒ (NS−1)(NT−1) = 2·3 = 6 even.  Kill via qS=0.
`(3, 5)`: NS=3 odd ⇒ (NS−1)(NT−1) = 2·4 = 8 even.  Kill via qS=0. -/

/-- `KillsDelta1` at `(NS, NT) = (3, 4)` via the abstract NS=3 kill. -/
theorem kills_delta1_K34 (c : Nat) :
    KillsDelta1 3 4 c pairEnum3 pairEnum4 :=
  kills_delta1_K3NT 4 c pairEnum4

/-- For K_{3,4}^{(c)}: every layer carries an independent non-coboundary
    H²-class. -/
theorem K34_c_independent_h2_classes_via_framework (c : Nat) :
    ∀ (m m' : Fin c),
      psi_layer_param 3 4 c m'
        (e_face_layer_param 3 4 c m) = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 3 4 c,
           e_face_layer_param 3 4 c m
             ≠ delta1_enr_param 3 4 c pairEnum3 pairEnum4 σ) :=
  parametric_c_independent_h2_classes_param 3 4 c
    (by decide) (by decide) pairEnum3 pairEnum4 (kills_delta1_K34 c)

/-- `KillsDelta1` at `(NS, NT) = (3, 5)` via the abstract NS=3 kill. -/
theorem kills_delta1_K35 (c : Nat) :
    KillsDelta1 3 5 c pairEnum3 pairEnum5 :=
  kills_delta1_K3NT 5 c pairEnum5

/-- For K_{3,5}^{(c)}: every layer carries an independent non-coboundary
    H²-class. -/
theorem K35_c_independent_h2_classes_via_framework (c : Nat) :
    ∀ (m m' : Fin c),
      psi_layer_param 3 5 c m'
        (e_face_layer_param 3 5 c m) = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 3 5 c,
           e_face_layer_param 3 5 c m
             ≠ delta1_enr_param 3 5 c pairEnum3 pairEnum5 σ) :=
  parametric_c_independent_h2_classes_param 3 5 c
    (by decide) (by decide) pairEnum3 pairEnum5 (kills_delta1_K35 c)

/-! ## §23 — Concrete `qS = 0` at NS = 5 (every NT, c, j, m)

For `NS = 5` with `pairEnum5`, each vertex appears in `NS-1 = 4`
(even) pairs across the 10 S-pair endpoints, so column-wise XOR
cancels.  20 σ values per `Q`, but the structural cancellation makes
it `false` after case-bash. -/

set_option maxHeartbeats 800000 in
theorem qS_param_zero_NS5 (NT c : Nat) (σ : EnrichedEdgeCoch 5 NT c)
    (j : Fin NT) (m : Fin c) :
    qS_param 5 NT c pairEnum5 σ j m = false := by
  unfold qS_param pairEnum5 pair5_lo pair5_hi
  rw [foldXor_10]
  -- 10-fold XOR with each Fin 5 endpoint appearing 4 times = even ⇒ cancels.
  -- After expansion, case-bash on the 5 σ-edges (i, j, m) for i ∈ Fin 5.
  cases σ (edge_idx_param 5 NT c ⟨0, by decide⟩ j m) <;>
    cases σ (edge_idx_param 5 NT c ⟨1, by decide⟩ j m) <;>
    cases σ (edge_idx_param 5 NT c ⟨2, by decide⟩ j m) <;>
    cases σ (edge_idx_param 5 NT c ⟨3, by decide⟩ j m) <;>
    cases σ (edge_idx_param 5 NT c ⟨4, by decide⟩ j m) <;> rfl

/-- KillsDelta1 for every `(5, NT)` instance: NS=5 odd ⇒ qS = 0. -/
theorem kills_delta1_K5NT (NT c : Nat) (pT : PairEnum NT) :
    KillsDelta1 5 NT c pairEnum5 pT := by
  intro σ m
  exact psi_layer_kill_of_qS_zero 5 NT c pairEnum5 pT σ m
    (fun j => qS_param_zero_NS5 NT c σ j m)

/-- `KillsDelta1` at `(NS, NT) = (5, 4)` — completes the original
    followup list (3,3), (4,3), (5,3), (5,4). -/
theorem kills_delta1_K54 (c : Nat) :
    KillsDelta1 5 4 c pairEnum5 pairEnum4 :=
  kills_delta1_K5NT 4 c pairEnum4

/-- For K_{5,4}^{(c)}: every layer carries an independent non-coboundary
    H²-class. -/
theorem K54_c_independent_h2_classes_via_framework (c : Nat) :
    ∀ (m m' : Fin c),
      psi_layer_param 5 4 c m'
        (e_face_layer_param 5 4 c m) = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 5 4 c,
           e_face_layer_param 5 4 c m
             ≠ delta1_enr_param 5 4 c pairEnum5 pairEnum4 σ) :=
  parametric_c_independent_h2_classes_param 5 4 c
    (by decide) (by decide) pairEnum5 pairEnum4 (kills_delta1_K54 c)

/-! ## §24 — Symmetric `qT = 0` at NT = 5 (any NS, c, i, m)

Mirror of `qS_param_zero_NS5`: for `NT = 5` with `pairEnum5`, each
T-vertex appears in `NT-1 = 4` (even) pairs across the 10 T-pair
endpoints, so row-wise XOR cancels. -/

set_option maxHeartbeats 800000 in
theorem qT_param_zero_NT5 (NS c : Nat) (σ : EnrichedEdgeCoch NS 5 c)
    (i : Fin NS) (m : Fin c) :
    qT_param NS 5 c pairEnum5 σ i m = false := by
  unfold qT_param pairEnum5 pair5_lo pair5_hi
  rw [foldXor_10]
  cases σ (edge_idx_param NS 5 c i ⟨0, by decide⟩ m) <;>
    cases σ (edge_idx_param NS 5 c i ⟨1, by decide⟩ m) <;>
    cases σ (edge_idx_param NS 5 c i ⟨2, by decide⟩ m) <;>
    cases σ (edge_idx_param NS 5 c i ⟨3, by decide⟩ m) <;>
    cases σ (edge_idx_param NS 5 c i ⟨4, by decide⟩ m) <;> rfl

/-- `KillsDelta1` for every `(NS, 5)` instance via the abstract NT=5
    kill (any S-side pair enumeration). -/
theorem kills_delta1_KNS5 (NS c : Nat) (pS : PairEnum NS) :
    KillsDelta1 NS 5 c pS pairEnum5 := by
  intro σ m
  exact psi_layer_kill_of_qT_zero NS 5 c pS pairEnum5 σ m
    (fun i => qT_param_zero_NT5 NS c σ i m)

/-- `KillsDelta1` at `(NS, NT) = (4, 5)` (parity OK: NT=5 odd). -/
theorem kills_delta1_K45 (c : Nat) :
    KillsDelta1 4 5 c pairEnum4 pairEnum5 :=
  kills_delta1_KNS5 4 c pairEnum4

/-- For K_{4,5}^{(c)}: every layer carries an independent
    non-coboundary H²-class. -/
theorem K45_c_independent_h2_classes_via_framework (c : Nat) :
    ∀ (m m' : Fin c),
      psi_layer_param 4 5 c m'
        (e_face_layer_param 4 5 c m) = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 4 5 c,
           e_face_layer_param 4 5 c m
             ≠ delta1_enr_param 4 5 c pairEnum4 pairEnum5 σ) :=
  parametric_c_independent_h2_classes_param 4 5 c
    (by decide) (by decide) pairEnum4 pairEnum5 (kills_delta1_K45 c)

/-- `KillsDelta1` at `(NS, NT) = (5, 5)` — first K_{n,n} after K_{3,3}. -/
theorem kills_delta1_K55 (c : Nat) :
    KillsDelta1 5 5 c pairEnum5 pairEnum5 :=
  kills_delta1_K5NT 5 c pairEnum5

/-- For K_{5,5}^{(c)}: every layer carries an independent
    non-coboundary H²-class. -/
theorem K55_c_independent_h2_classes_via_framework (c : Nat) :
    ∀ (m m' : Fin c),
      psi_layer_param 5 5 c m'
        (e_face_layer_param 5 5 c m) = decide (m.val = m'.val)
      ∧ (∀ σ : EnrichedEdgeCoch 5 5 c,
           e_face_layer_param 5 5 c m
             ≠ delta1_enr_param 5 5 c pairEnum5 pairEnum5 σ) :=
  parametric_c_independent_h2_classes_param 5 5 c
    (by decide) (by decide) pairEnum5 pairEnum5 (kills_delta1_K55 c)

end E213.Lib.Math.Cohomology.Bipartite.Parametric.EnrichedKNSNTc
