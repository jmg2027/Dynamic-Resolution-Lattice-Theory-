import E213.Lib.Physics.Symmetry.AutKGroup
import E213.Lib.Physics.Symmetry.AutKSemidirect
import E213.Lib.Physics.Symmetry.Sym3Group

/-!
# Full semidirect-product Group axioms for Aut(K) — Phase 18

Phase 15 (`AutKSemidirect.lean`) established the bit-permutation
generators (3 elements) and a sample semidirect multiplication
`mul_semi_S01`.  This phase **extends to all 12 elements of
Sym(3) × Sym(2)** with a complete lookup `bit_perm_of`, proves
the φ-homomorphism property, and uses it to prove **all four
group axioms** on the semidirect product.

## Structure

  · `bit_perm_of : (Sym3 × Sym2) → (Fin 6 → Fin 6)` — 12-element
    lookup of the bit-permutation induced by the external factor
  · `φ_hom`: `bit_perm_of (gh) = bit_perm_of g ∘ bit_perm_of h`
  · `Aut_K.mul_semi`: full semidirect multiplication
  · `Aut_K.inv_semi`: semidirect inverse `(h, n)^-1 = (h^-1, φ(h^-1) n)`
  · Group axioms: `one_mul`, `mul_one`, `inv_mul`, `mul_assoc`
    — proven via the φ-homomorphism + factor-group axioms

This completes the **semidirect Group structure** of
`(Sym(3) × Sym(2)) ⋉ C_2^6 = Aut(K_{3,2}^{(c=2)})`, the true
automorphism group of K_{3,2}^{(c=2)}.

All theorems below are **PURE** via `decide` + structural composition.
-/

namespace E213.Lib.Physics.Symmetry.AutKSemidirectFull

open E213.Lib.Physics.Symmetry.AutKGroup (C2_6 Sym2 Aut_K)
open E213.Lib.Physics.Symmetry.Sym3Group (Sym3)
open E213.Lib.Physics.Symmetry.AutKSemidirect (bit_perm_S01 bit_perm_S12 bit_perm_T bit_act)

/-! ## §1.  Sym(3) action on Fin 3 (S-vertices)

Each Sym(3) element maps to a permutation of `Fin 3`. -/

/-- The action of Sym(3) on S-vertices `Fin 3`. -/
def sym3_act (g : Sym3) (s : Fin 3) : Fin 3 :=
  match g.val, s.val with
  -- e = identity
  | 0, _ => s
  -- a = (01) swap
  | 1, 0 => ⟨1, by decide⟩
  | 1, 1 => ⟨0, by decide⟩
  | 1, _ => s
  -- b = (12) swap
  | 2, 1 => ⟨2, by decide⟩
  | 2, 2 => ⟨1, by decide⟩
  | 2, _ => s
  -- c = (02) swap
  | 3, 0 => ⟨2, by decide⟩
  | 3, 2 => ⟨0, by decide⟩
  | 3, _ => s
  -- x = ρ = b·a (3-cycle 0→2→1→0)
  | 4, 0 => ⟨2, by decide⟩
  | 4, 1 => ⟨0, by decide⟩
  | 4, 2 => ⟨1, by decide⟩
  | 4, _ => s
  -- y = ρ² = a·b (3-cycle 0→1→2→0)
  | _, 0 => ⟨1, by decide⟩
  | _, 1 => ⟨2, by decide⟩
  | _, _ => ⟨0, by decide⟩

/-- sym3_act of identity is identity. -/
theorem sym3_act_one : ∀ s : Fin 3, sym3_act ⟨0, by decide⟩ s = s := by decide

/-- ★ sym3_act is a group homomorphism: `act(g·h)(s) = act(g)(act(h)(s))`.
    36 × 3 = 108 cases via decide. -/
theorem sym3_act_hom :
    ∀ g h : Sym3, ∀ s : Fin 3,
      sym3_act (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul g h) s
      = sym3_act g (sym3_act h s) := by decide

/-! ## §2.  Sym(2) action on Fin 2 (T-vertices) -/

/-- The action of Sym(2) on T-vertices `Fin 2`. -/
def sym2_act (g : Sym2) (t : Fin 2) : Fin 2 :=
  match g.val, t.val with
  | 0, _ => t
  | 1, 0 => ⟨1, by decide⟩
  | _, _ => ⟨0, by decide⟩

theorem sym2_act_one : ∀ t : Fin 2, sym2_act ⟨0, by decide⟩ t = t := by decide

/-- sym2_act is a homomorphism. -/
theorem sym2_act_hom :
    ∀ g h : Sym2, ∀ t : Fin 2,
      sym2_act (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.mul g h) t
      = sym2_act g (sym2_act h t) := by decide

/-! ## §3.  Bit-index encoding / decoding -/

/-- Extract the S-component of a bit index: `s_of i = i / 2`.
    Match-based to avoid `omega`. -/
def s_of (i : Fin 6) : Fin 3 :=
  match i.val with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨0, by decide⟩
  | 2 => ⟨1, by decide⟩
  | 3 => ⟨1, by decide⟩
  | 4 => ⟨2, by decide⟩
  | _ => ⟨2, by decide⟩

/-- Extract the T-component of a bit index: `t_of i = i % 2`. -/
def t_of (i : Fin 6) : Fin 2 :=
  match i.val with
  | 0 => ⟨0, by decide⟩
  | 1 => ⟨1, by decide⟩
  | 2 => ⟨0, by decide⟩
  | 3 => ⟨1, by decide⟩
  | 4 => ⟨0, by decide⟩
  | _ => ⟨1, by decide⟩

/-- Pair-index recombination from (s, t).  Match-based. -/
def pair_idx (s : Fin 3) (t : Fin 2) : Fin 6 :=
  match s.val, t.val with
  | 0, 0 => ⟨0, by decide⟩
  | 0, 1 => ⟨1, by decide⟩
  | 1, 0 => ⟨2, by decide⟩
  | 1, 1 => ⟨3, by decide⟩
  | 2, 0 => ⟨4, by decide⟩
  | _, _ => ⟨5, by decide⟩

/-- Round-trip: pair_idx (s_of i) (t_of i) = i. -/
theorem pair_idx_round_trip : ∀ i : Fin 6, pair_idx (s_of i) (t_of i) = i := by decide

/-! ## §4.  General bit-permutation lookup

`bit_perm_of (g_S, g_T) i = pair_idx (g_S · s_of i) (g_T · t_of i)`. -/

/-- Bit permutation induced by `(g_S, g_T) ∈ Sym(3) × Sym(2)`. -/
def bit_perm_of (g_S : Sym3) (g_T : Sym2) (i : Fin 6) : Fin 6 :=
  pair_idx (sym3_act g_S (s_of i)) (sym2_act g_T (t_of i))

/-- Identity bit-perm. -/
theorem bit_perm_of_one :
    ∀ i : Fin 6,
      bit_perm_of ⟨0, by decide⟩ ⟨0, by decide⟩ i = i := by decide

/-- ★ φ-homomorphism: `bit_perm_of(g·h) = bit_perm_of(g) ∘ bit_perm_of(h)`.
    Verified across all 12 × 12 = 144 (g, h) combinations × 6 bit
    positions = 864 cases via decide. -/
theorem bit_perm_of_hom :
    ∀ g_S h_S : Sym3, ∀ g_T h_T : Sym2, ∀ i : Fin 6,
      bit_perm_of (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul g_S h_S)
                  (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.mul g_T h_T) i
      = bit_perm_of g_S g_T (bit_perm_of h_S h_T i) := by decide

/-- Sample compatibility with Phase 15's `bit_perm_S01`: when
    g_S = a (σ_S01) and g_T = e, the lookup gives the same permutation. -/
theorem bit_perm_of_a_e :
    ∀ i : Fin 6, bit_perm_of ⟨1, by decide⟩ ⟨0, by decide⟩ i = bit_perm_S01 i := by
  decide

/-! ## §5.  Full semidirect multiplication and inverse

`(g_S, g_T, c) · (g_S', g_T', c') = (g_S·g_S', g_T·g_T', c ⊕ φ(g_S, g_T)·c')`. -/

/-- Bit-action pullback on C_2^6 cochains.

    Uses the **inverse** permutation so that φ becomes a true
    homomorphism: pullback by `bit_perm_of g` is naturally an
    anti-homomorphism, so we use `bit_perm_of g⁻¹` to recover
    homomorphism direction.  See `bit_act_of_hom` below. -/
def bit_act_of (g_S : Sym3) (g_T : Sym2) (c : C2_6) : C2_6 :=
  fun i => c (bit_perm_of
              (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv g_S)
              (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv g_T) i)

/-- Helper: `(g·h)⁻¹ = h⁻¹·g⁻¹` in Sym(3).  36-case decide. -/
theorem sym3_inv_mul :
    ∀ g h : Sym3,
      E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv
        (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul g h)
      = E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul
          (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv h)
          (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv g) := by decide

/-- Helper: `(g·h)⁻¹ = h⁻¹·g⁻¹` in Sym(2).  4-case decide. -/
theorem sym2_inv_mul :
    ∀ g h : Sym2,
      E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv
        (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.mul g h)
      = E213.Lib.Physics.Symmetry.AutKGroup.Sym2.mul
          (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv h)
          (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv g) := by decide

/-- ★ bit_act_of is a group homomorphism w.r.t. (g_S, g_T) multiplication.
    `bit_act_of (gh) (c) = bit_act_of g (bit_act_of h c)`.

    Combines `sym3_inv_mul`, `sym2_inv_mul`, and `bit_perm_of_hom`. -/
theorem bit_act_of_hom :
    ∀ g_S h_S : Sym3, ∀ g_T h_T : Sym2, ∀ c : C2_6, ∀ i : Fin 6,
      bit_act_of (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul g_S h_S)
                 (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.mul g_T h_T) c i
      = bit_act_of g_S g_T (bit_act_of h_S h_T c) i := by
  intro g_S h_S g_T h_T c i
  show c (bit_perm_of
            (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv
              (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul g_S h_S))
            (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv
              (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.mul g_T h_T)) i)
       = c (bit_perm_of
              (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv h_S)
              (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv h_T)
              (bit_perm_of
                (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv g_S)
                (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv g_T) i))
  -- LHS: c (bit_perm_of (gh)⁻¹ ...).  Rewrite (gh)⁻¹ = h⁻¹·g⁻¹.
  rw [sym3_inv_mul g_S h_S, sym2_inv_mul g_T h_T]
  -- Goal: c (bit_perm_of (h⁻¹·g⁻¹) (h_T⁻¹·g_T⁻¹) i) = c (bit_perm_of h⁻¹ ... (bit_perm_of g⁻¹ ... i))
  -- Apply bit_perm_of_hom h⁻¹ g⁻¹.
  rw [bit_perm_of_hom
        (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv h_S)
        (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv g_S)
        (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv h_T)
        (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv g_T) i]

/-- Full semidirect multiplication on Aut_K. -/
def mul_semi (g h : Aut_K) : Aut_K :=
  (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul g.1 h.1,
   E213.Lib.Physics.Symmetry.AutKGroup.Sym2.mul g.2.1 h.2.1,
   E213.Lib.Physics.Symmetry.AutKGroup.C2_6.mul g.2.2
     (bit_act_of g.1 g.2.1 h.2.2))

/-- Semidirect identity (= direct identity since φ(e) = id). -/
def one_semi : Aut_K := E213.Lib.Physics.Symmetry.AutKGroup.Aut_K.one

/-- Semidirect inverse: `(h, n)^-1 = (h^-1, φ(h^-1)·n)`.  Note that
    in C_2^6 with characteristic 2, `-n = n`. -/
def inv_semi (g : Aut_K) : Aut_K :=
  let h_S_inv := E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv g.1
  let h_T_inv := E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv g.2.1
  (h_S_inv, h_T_inv, bit_act_of h_S_inv h_T_inv g.2.2)

/-! ## §6.  Group axioms

We state them **component-wise** (with the C_2^6 component
pointwise) — same approach as `AutKGroup.Aut_K.*_mul`. -/

/-- Helper: C_2^6 component of `mul_semi g h` unfolds pointwise.
    Used in the associativity proof. -/
theorem mul_semi_C2_6_at (g h : Aut_K) (i : Fin 6) :
    (mul_semi g h).2.2 i = xor (g.2.2 i)
      (h.2.2 (bit_perm_of
        (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv g.1)
        (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv g.2.1) i)) := rfl

/-- ★ Semidirect identity left: `one · g = g`. -/
theorem mul_semi_one_mul (g : Aut_K) :
    (mul_semi one_semi g).1 = g.1
    ∧ (mul_semi one_semi g).2.1 = g.2.1
    ∧ (∀ i : Fin 6, (mul_semi one_semi g).2.2 i = g.2.2 i) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Sym3 component: e · g.1 = g.1
    exact E213.Lib.Physics.Symmetry.Sym3Group.Sym3.one_mul g.1
  · -- Sym2 component: e · g.2.1 = g.2.1
    exact E213.Lib.Physics.Symmetry.AutKGroup.Sym2.one_mul g.2.1
  · -- C_2^6: 0 XOR (bit_act_of e e g.2.2) i = g.2.2 i.
    -- bit_act_of e e = id since e^-1 = e and bit_perm_of e e = id.
    intro i
    show xor false (g.2.2 (bit_perm_of
            (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv ⟨0, by decide⟩)
            (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv ⟨0, by decide⟩) i))
         = g.2.2 i
    -- e^-1 = e, then bit_perm_of e e = identity (per bit_perm_of_one)
    show xor false (g.2.2 (bit_perm_of ⟨0, by decide⟩ ⟨0, by decide⟩ i)) = g.2.2 i
    rw [bit_perm_of_one i]
    cases g.2.2 i <;> rfl

/-- ★ Semidirect identity right: `g · one = g`. -/
theorem mul_semi_mul_one (g : Aut_K) :
    (mul_semi g one_semi).1 = g.1
    ∧ (mul_semi g one_semi).2.1 = g.2.1
    ∧ (∀ i : Fin 6, (mul_semi g one_semi).2.2 i = g.2.2 i) := by
  refine ⟨?_, ?_, ?_⟩
  · exact E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul_one g.1
  · exact E213.Lib.Physics.Symmetry.AutKGroup.Sym2.mul_one g.2.1
  · -- C_2^6: g.2.2 i XOR (bit_act_of g.1 g.2.1 0) i = g.2.2 i
    intro i
    show xor (g.2.2 i)
         ((fun _ => false) (bit_perm_of g.1 g.2.1 i)) = g.2.2 i
    cases g.2.2 i <;> rfl

/-- ★ Semidirect inverse left: `g^-1 · g = one`. -/
theorem mul_semi_inv_mul (g : Aut_K) :
    (mul_semi (inv_semi g) g).1 = one_semi.1
    ∧ (mul_semi (inv_semi g) g).2.1 = one_semi.2.1
    ∧ (∀ i : Fin 6, (mul_semi (inv_semi g) g).2.2 i = one_semi.2.2 i) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Sym3: g^-1 · g = e
    exact E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv_mul g.1
  · -- Sym2: g^-1 · g = e
    exact E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv_mul g.2.1
  · -- C_2^6:  inv_semi g = (g⁻¹, φ(g⁻¹)(g.n)).
    -- Then mul_semi (inv_semi g) g .n at i
    --   = (inv_semi g).n i  XOR  g.n (bit_perm_of (g⁻¹)⁻¹ ... i)
    --   = g.n (bit_perm_of g.1 g.2.1 i)
    --     XOR g.n (bit_perm_of (Sym3.inv (Sym3.inv g.1)) ... i)
    --   = g.n X XOR g.n X        [(g⁻¹)⁻¹ = g, decide]
    --   = false                  [xor x x = false]
    intro i
    -- Goal: (mul_semi (inv_semi g) g).snd.snd i = one_semi.snd.snd i = false
    -- mul_semi_C2_6_at gives us:
    --   (mul_semi A B).2.2 i = xor (A.2.2 i)
    --     (B.2.2 (bit_perm_of (Sym3.inv A.1) (Sym2.inv A.2.1) i))
    -- where A = inv_semi g, B = g.
    -- A.2.2 i = bit_act_of g.1.inv g.2.1.inv g.2.2 i
    --        = g.2.2 (bit_perm_of (Sym3.inv g.1.inv) (Sym2.inv g.2.1.inv) i)
    -- A.1 = g.1.inv, so Sym3.inv A.1 = Sym3.inv g.1.inv.
    -- So both args of XOR have form g.2.2 (bit_perm_of (inv inv ...) (inv inv ...) i)
    -- = same value, hence XOR = false.
    show xor (g.2.2 (bit_perm_of
              (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv
                (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv g.1))
              (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv
                (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv g.2.1)) i))
         (g.2.2 (bit_perm_of
              (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv
                (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv g.1))
              (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv
                (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv g.2.1)) i))
       = false
    cases g.2.2 (bit_perm_of
              (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv
                (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv g.1))
              (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv
                (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv g.2.1)) i)
    <;> rfl

/-- ★★ Semidirect associativity: `(g·h)·k = g·(h·k)`.

    The C_2^6 component requires the φ-homomorphism property:
      LHS C_2^6 component at i = g.c i XOR φ(g)(h.c) i XOR φ(g·h)(k.c) i
      RHS C_2^6 component at i = g.c i XOR φ(g)(h.c) i XOR φ(g)(φ(h)(k.c)) i

    Equal iff φ(g·h) = φ(g) ∘ φ(h) — the homomorphism property,
    which holds by `bit_perm_of_hom`. -/
theorem mul_semi_assoc (g h k : Aut_K) :
    (mul_semi (mul_semi g h) k).1 = (mul_semi g (mul_semi h k)).1
    ∧ (mul_semi (mul_semi g h) k).2.1 = (mul_semi g (mul_semi h k)).2.1
    ∧ (∀ i : Fin 6,
         (mul_semi (mul_semi g h) k).2.2 i
         = (mul_semi g (mul_semi h k)).2.2 i) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Sym3 component: Sym3.mul_assoc
    exact E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul_assoc g.1 h.1 k.1
  · -- Sym2 component: Sym2.mul_assoc
    exact E213.Lib.Physics.Symmetry.AutKGroup.Sym2.mul_assoc g.2.1 h.2.1 k.2.1
  · -- C_2^6 component: φ-homomorphism via bit_act_of_hom
    intro i
    -- LHS = g.c ⊕ φ(g)(h.c) ⊕ φ(gh)(k.c)   at i
    -- RHS = g.c ⊕ φ(g)(h.c ⊕ φ(h)(k.c))    at i
    --     = g.c ⊕ φ(g)(h.c) ⊕ φ(g)(φ(h)(k.c))  by Bool.xor distributivity
    -- These match iff φ(gh)(k.c) i = (φ(g) ∘ φ(h))(k.c) i — which
    -- is exactly `bit_act_of_hom`.
    show xor (xor (g.2.2 i)
              (h.2.2 (bit_perm_of
                (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv g.1)
                (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv g.2.1) i)))
         (bit_act_of
            (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul g.1 h.1)
            (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.mul g.2.1 h.2.1)
            k.2.2 i)
       = xor (g.2.2 i)
         (xor (h.2.2 (bit_perm_of
                       (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv g.1)
                       (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv g.2.1) i))
              (bit_act_of g.1 g.2.1 (bit_act_of h.1 h.2.1 k.2.2) i))
    rw [bit_act_of_hom g.1 h.1 g.2.1 h.2.1 k.2.2 i]
    cases g.2.2 i
    <;> cases h.2.2 (bit_perm_of
                       (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.inv g.1)
                       (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.inv g.2.1) i)
    <;> cases bit_act_of g.1 g.2.1 (bit_act_of h.1 h.2.1 k.2.2) i
    <;> rfl

/-! ## §7.  Phase-18 capstone -/

/-- ★★★ **Phase-18 capstone**: full semidirect-product Group axioms
    for `Aut(K_{3,2}^{(c=2)}) = (Sym(3) × Sym(2)) ⋉ C_2^6`.

    Substantive content:
      (a) `sym3_act`, `sym2_act` — actions of Sym(3), Sym(2) on
          vertex Fins (Fin 3, Fin 2)
      (b) Both are group homomorphisms (decide on 108, 8 cases)
      (c) `bit_perm_of` — general bit-permutation lookup for all
          12 elements of Sym(3) × Sym(2)
      (d) `★ bit_perm_of_hom` — φ is a group homomorphism
          (864-case decide)
      (e) `mul_semi`, `one_semi`, `inv_semi` — full semidirect ops
      (f) Group axioms: `one_mul`, `mul_one`, `inv_mul`, `mul_assoc`
          — all PROVEN (not just sample); associativity uses the
          φ-homomorphism for the C_2^6 cross-term

    Combined with Phase 12 (direct product) and Phase 15 (twist
    sample), this gives the **complete Group-theoretic realization**
    of Aut(K_{3,2}^{(c=2)}) as a semidirect product.  PURE. -/
theorem AutKSemidirectFull_phase18_capstone :
    -- sym3, sym2 act homomorphisms
    (∀ g h : Sym3, ∀ s : Fin 3,
       sym3_act (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul g h) s
       = sym3_act g (sym3_act h s))
    ∧ (∀ g h : Sym2, ∀ t : Fin 2,
         sym2_act (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.mul g h) t
         = sym2_act g (sym2_act h t))
    -- φ-homomorphism (key for mul_assoc)
    ∧ (∀ g_S h_S : Sym3, ∀ g_T h_T : Sym2, ∀ i : Fin 6,
         bit_perm_of
           (E213.Lib.Physics.Symmetry.Sym3Group.Sym3.mul g_S h_S)
           (E213.Lib.Physics.Symmetry.AutKGroup.Sym2.mul g_T h_T) i
         = bit_perm_of g_S g_T (bit_perm_of h_S h_T i))
    -- Group axioms (component + pointwise)
    ∧ (∀ g : Aut_K, (mul_semi one_semi g).1 = g.1)
    ∧ (∀ g : Aut_K, (mul_semi g one_semi).1 = g.1)
    ∧ (∀ g : Aut_K, ∀ i : Fin 6,
         (mul_semi (inv_semi g) g).2.2 i = one_semi.2.2 i)
    ∧ (∀ g h k : Aut_K, ∀ i : Fin 6,
         (mul_semi (mul_semi g h) k).2.2 i
         = (mul_semi g (mul_semi h k)).2.2 i)
    -- Compatibility with Phase 15 generators
    ∧ (∀ i : Fin 6,
         bit_perm_of ⟨1, by decide⟩ ⟨0, by decide⟩ i = bit_perm_S01 i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sym3_act_hom
  · exact sym2_act_hom
  · exact bit_perm_of_hom
  · intro g; exact (mul_semi_one_mul g).1
  · intro g; exact (mul_semi_mul_one g).1
  · intro g i; exact (mul_semi_inv_mul g).2.2 i
  · intro g h k i; exact (mul_semi_assoc g h k).2.2 i
  · exact bit_perm_of_a_e

end E213.Lib.Physics.Symmetry.AutKSemidirectFull
