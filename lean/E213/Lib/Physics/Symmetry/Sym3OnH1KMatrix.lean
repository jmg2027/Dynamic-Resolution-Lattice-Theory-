import E213.Lib.Math.Cohomology.Bipartite.V32
import E213.Lib.Math.Cohomology.Bipartite.H1K
import E213.Lib.Physics.Symmetry.Sym3OnH1K

/-!
# Sym(3) representation matrix on H¹(K) — Phase 5

Phase 5 of the **C3 chain** — computes the **explicit 8×8 matrix**
of σ_S01 acting on the H1K basis (the 8 non-tree edge classes).

## Construction

Per `H1K.lean`, H1K basis vectors `e_i` (i = 0..7) correspond to
the 8 non-tree edges {1, 3, 5, 6, 7, 9, 10, 11}.

Most σ_S01 actions are basis-to-basis permutations:
  · σ_S01[e_0] = e_2   (edge 1 ↔ 5)
  · σ_S01[e_1] = e_4   (edge 3 ↔ 7)
  · σ_S01[e_2] = e_0
  · σ_S01[e_4] = e_1
  · σ_S01[e_5] = e_5   (edge 9 fixed)
  · σ_S01[e_6] = e_6   (edge 10 fixed)
  · σ_S01[e_7] = e_7   (edge 11 fixed)

The **exceptional case** is `e_3` (non-tree edge 6, S1-T1 mult 0):
σ_S01 sends edge 6 → edge 2, which is a **tree edge**.  The
cohomology class [edge 2 indicator] is computed by tree decomposition:

  Vertex cochain `v = (0, 0, 0, 0, 1)` (T_1 = vertex 4 only)
  δ⁰(v) = indicators on edges where v(src) ≠ v(tgt)
        = {edges with tgt = vertex 4}
        = {edge 2, 3, 6, 7, 10, 11}.

So modulo coboundaries, [edge 2] = [edge 3 + 6 + 7 + 10 + 11]
in the non-tree basis = [e_1 + e_3 + e_4 + e_6 + e_7].

Therefore σ_S01[e_3] = [e_1 + e_3 + e_4 + e_6 + e_7].

## Verification

  · Involution σ_S01² = I at the matrix level (16 row checks)
  · Trace = 4 (over ℕ, counting fixed basis vectors):
    e_5, e_6, e_7 fixed (3) + e_3 has diagonal entry 1 (in tree
    expansion) = 4.  Over Z/2 this is 0.
  · The non-permutation row (e_3) is the substantive content of
    the tree-coboundary correction.

All theorems below are **PURE** via `decide` or pointwise `rfl`.
-/

namespace E213.Lib.Physics.Symmetry.Sym3OnH1KMatrix

open E213.Lib.Math.Cohomology.Bipartite.V32 (CochV CochE delta0 srcFin tgtFin)
open E213.Lib.Math.Cohomology.Bipartite.H1K (H1K)
open E213.Lib.Physics.Symmetry.Sym3OnH1K (φ_V_S01 φ_act_V)

/-! ## §1.  Matrix encoding

We represent the 8×8 matrix as a function `M : Fin 8 → H1K`
where `M i = σ_S01 e_i` expressed in the basis. -/

/-- The σ_S01 representation matrix on H1K (8 column vectors). -/
def M_S01 : Fin 8 → H1K := fun i =>
  match i.val with
  -- e_0 ↦ e_2 (single 1 at coordinate 2)
  | 0 => fun j => decide (j.val = 2)
  -- e_1 ↦ e_4
  | 1 => fun j => decide (j.val = 4)
  -- e_2 ↦ e_0
  | 2 => fun j => decide (j.val = 0)
  -- e_3 ↦ e_1 + e_3 + e_4 + e_6 + e_7  (tree-coboundary expansion)
  | 3 => fun j => decide (j.val = 1) || decide (j.val = 3)
                  || decide (j.val = 4) || decide (j.val = 6)
                  || decide (j.val = 7)
  -- e_4 ↦ e_1
  | 4 => fun j => decide (j.val = 1)
  -- e_5 ↦ e_5
  | 5 => fun j => decide (j.val = 5)
  -- e_6 ↦ e_6
  | 6 => fun j => decide (j.val = 6)
  -- e_7 ↦ e_7
  | _ => fun j => decide (j.val = 7)

/-! ## §2.  Coboundary witness for the exceptional row

The tree-decomposition witness: vertex cochain
`v_tree = (0, 0, 0, 0, 1)` produces a coboundary that, XOR-ed with
the indicator of edge 2, gives a non-tree-edge-only cochain. -/

/-- Vertex cochain for the coboundary witness: only T_1 (vertex 4) is true. -/
def v_tree_witness : CochV := fun v => decide (v.val = 4)

/-- δ⁰(v_tree_witness) at each edge: 1 iff edge has tgtFin = vertex 4.
    Tree edges: edge 2 has tgt 4 (1), others have tgt 3 (0).
    Non-tree edges: 3 has tgt 4 (1); 6, 7 have tgt 4 (1); 10, 11 have tgt 4 (1). -/
theorem delta0_v_tree_at_each_edge :
    delta0 v_tree_witness ⟨0, by decide⟩ = false   -- tree edge 0 (S0-T0): tgt 3
    ∧ delta0 v_tree_witness ⟨1, by decide⟩ = false  -- non-tree edge 1: tgt 3
    ∧ delta0 v_tree_witness ⟨2, by decide⟩ = true   -- tree edge 2 (S0-T1): tgt 4
    ∧ delta0 v_tree_witness ⟨3, by decide⟩ = true   -- non-tree edge 3: tgt 4
    ∧ delta0 v_tree_witness ⟨4, by decide⟩ = false  -- tree edge 4
    ∧ delta0 v_tree_witness ⟨5, by decide⟩ = false  -- non-tree edge 5
    ∧ delta0 v_tree_witness ⟨6, by decide⟩ = true   -- non-tree edge 6
    ∧ delta0 v_tree_witness ⟨7, by decide⟩ = true   -- non-tree edge 7
    ∧ delta0 v_tree_witness ⟨8, by decide⟩ = false  -- tree edge 8
    ∧ delta0 v_tree_witness ⟨9, by decide⟩ = false  -- non-tree edge 9
    ∧ delta0 v_tree_witness ⟨10, by decide⟩ = true  -- non-tree edge 10
    ∧ delta0 v_tree_witness ⟨11, by decide⟩ = true  -- non-tree edge 11
    := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## §3.  Matrix application -/

/-- M_S01 applied to basis vector e_0 yields e_2 (pointwise). -/
theorem M_S01_e0 :
    M_S01 ⟨0, by decide⟩ ⟨0, by decide⟩ = false
    ∧ M_S01 ⟨0, by decide⟩ ⟨2, by decide⟩ = true := by
  refine ⟨?_, ?_⟩ <;> rfl

/-- M_S01 applied to basis vector e_3 hits e_1, e_3, e_4, e_6, e_7. -/
theorem M_S01_e3 :
    M_S01 ⟨3, by decide⟩ ⟨0, by decide⟩ = false
    ∧ M_S01 ⟨3, by decide⟩ ⟨1, by decide⟩ = true
    ∧ M_S01 ⟨3, by decide⟩ ⟨2, by decide⟩ = false
    ∧ M_S01 ⟨3, by decide⟩ ⟨3, by decide⟩ = true
    ∧ M_S01 ⟨3, by decide⟩ ⟨4, by decide⟩ = true
    ∧ M_S01 ⟨3, by decide⟩ ⟨5, by decide⟩ = false
    ∧ M_S01 ⟨3, by decide⟩ ⟨6, by decide⟩ = true
    ∧ M_S01 ⟨3, by decide⟩ ⟨7, by decide⟩ = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## §4.  Matrix multiplication -/

/-- Matrix-vector product M · ω in H1K (XOR over the support).
    `(M ω) j = XOR over k of (M k j AND ω k)`. -/
def M_mul_vec (M : Fin 8 → H1K) (ω : H1K) : H1K :=
  fun j => xor (xor (xor (xor (xor (xor (xor
    (and (M ⟨0, by decide⟩ j) (ω ⟨0, by decide⟩))
    (and (M ⟨1, by decide⟩ j) (ω ⟨1, by decide⟩)))
    (and (M ⟨2, by decide⟩ j) (ω ⟨2, by decide⟩)))
    (and (M ⟨3, by decide⟩ j) (ω ⟨3, by decide⟩)))
    (and (M ⟨4, by decide⟩ j) (ω ⟨4, by decide⟩)))
    (and (M ⟨5, by decide⟩ j) (ω ⟨5, by decide⟩)))
    (and (M ⟨6, by decide⟩ j) (ω ⟨6, by decide⟩)))
    (and (M ⟨7, by decide⟩ j) (ω ⟨7, by decide⟩))

/-- Matrix-matrix product: `(M · N) i j = (M · (N row i))`. -/
def M_mul_M (M N : Fin 8 → H1K) : Fin 8 → H1K :=
  fun i => M_mul_vec M (N i)

/-! ## §5.  Involution at the matrix level

The substantive verification: `M_S01 · M_S01 = I` at the matrix
level.  Each of the 64 entries verified by `decide`. -/

/-- Identity matrix: `I i j = decide (i = j)`. -/
def IdMatrix : Fin 8 → H1K := fun i j => decide (i.val = j.val)

/-- M_S01 · M_S01 = IdMatrix (the 8×8 involution check).
    PURE via decide on 64 entries. -/
theorem M_S01_squared_pointwise :
    ∀ i j : Fin 8, M_mul_M M_S01 M_S01 i j = IdMatrix i j := by decide

/-! ## §6.  Trace -/

/-- The "Bool-trace" of M: XOR of diagonal entries.  This is the
    Z/2 trace; over Z the actual fixed-basis count is 4 (e_3, e_5,
    e_6, e_7).  In F_2, trace = 0. -/
def boolTrace (M : Fin 8 → H1K) : Bool :=
  xor (xor (xor (xor (xor (xor (xor
    (M ⟨0, by decide⟩ ⟨0, by decide⟩)
    (M ⟨1, by decide⟩ ⟨1, by decide⟩))
    (M ⟨2, by decide⟩ ⟨2, by decide⟩))
    (M ⟨3, by decide⟩ ⟨3, by decide⟩))
    (M ⟨4, by decide⟩ ⟨4, by decide⟩))
    (M ⟨5, by decide⟩ ⟨5, by decide⟩))
    (M ⟨6, by decide⟩ ⟨6, by decide⟩))
    (M ⟨7, by decide⟩ ⟨7, by decide⟩)

/-- ★ Bool-trace of M_S01 = false.  Over ℤ the trace is 4 (= number
    of basis vectors fixed under σ_S01).  Mod 2, trace = 0. -/
theorem boolTrace_M_S01 : boolTrace M_S01 = false := by decide

/-- The integer-trace count of M_S01: number of diagonal `true` entries.
    Sum over i of (1 if M_S01 i i = true else 0). -/
def intTrace (M : Fin 8 → H1K) : Nat :=
  (if M ⟨0, by decide⟩ ⟨0, by decide⟩ then 1 else 0)
  + (if M ⟨1, by decide⟩ ⟨1, by decide⟩ then 1 else 0)
  + (if M ⟨2, by decide⟩ ⟨2, by decide⟩ then 1 else 0)
  + (if M ⟨3, by decide⟩ ⟨3, by decide⟩ then 1 else 0)
  + (if M ⟨4, by decide⟩ ⟨4, by decide⟩ then 1 else 0)
  + (if M ⟨5, by decide⟩ ⟨5, by decide⟩ then 1 else 0)
  + (if M ⟨6, by decide⟩ ⟨6, by decide⟩ then 1 else 0)
  + (if M ⟨7, by decide⟩ ⟨7, by decide⟩ then 1 else 0)

/-- ★ Integer-trace of M_S01 = 4 = # of fixed basis vectors.
    Fixed: e_3 (diagonal 1 from tree-decomp), e_5, e_6, e_7. -/
theorem intTrace_M_S01 : intTrace M_S01 = 4 := by decide

/-! ## §7.  Phase-5 capstone -/

/-- ★★ **Phase-5 capstone**: explicit 8×8 representation matrix of
    σ_S01 on H1K basis, with:

      (a) Tree-decomposition witness (v_tree_witness) yielding the
          exceptional row e_3 ↦ e_1 + e_3 + e_4 + e_6 + e_7
      (b) Matrix involution M_S01 · M_S01 = I (64-entry decide)
      (c) Bool-trace = 0 (mod 2 character)
      (d) Integer-trace = 4 (basis-fixed count)
      (e) Specific row values (e_0, e_3) as sanity checks

    Per Sym(3) modular representation theory over F_2 (which differs
    from the Q-case since char 2 divides |Sym(3)| = 6), the irrep
    decomposition is deferred to a future phase.  Over Q the
    Sym(3)-irreducibles are {1, sign, standard₂}; the F_2 case has
    fewer irreducibles since 1 = sign.

    PURE. -/
theorem Sym3OnH1KMatrix_capstone :
    -- Matrix involution
    (∀ i j : Fin 8, M_mul_M M_S01 M_S01 i j = IdMatrix i j)
    -- Bool-trace = 0
    ∧ boolTrace M_S01 = false
    -- Integer-trace = 4
    ∧ intTrace M_S01 = 4
    -- Sanity check on e_0 row
    ∧ (M_S01 ⟨0, by decide⟩ ⟨2, by decide⟩ = true)
    ∧ (M_S01 ⟨0, by decide⟩ ⟨0, by decide⟩ = false)
    -- Sanity check on e_3 row (the exceptional one)
    ∧ (M_S01 ⟨3, by decide⟩ ⟨1, by decide⟩ = true)
    ∧ (M_S01 ⟨3, by decide⟩ ⟨3, by decide⟩ = true)
    ∧ (M_S01 ⟨3, by decide⟩ ⟨4, by decide⟩ = true)
    ∧ (M_S01 ⟨3, by decide⟩ ⟨6, by decide⟩ = true)
    ∧ (M_S01 ⟨3, by decide⟩ ⟨7, by decide⟩ = true)
    -- Tree-decomposition coboundary witness exists
    ∧ delta0 v_tree_witness ⟨2, by decide⟩ = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact M_S01_squared_pointwise
  · decide
  · decide
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end E213.Lib.Physics.Symmetry.Sym3OnH1KMatrix
