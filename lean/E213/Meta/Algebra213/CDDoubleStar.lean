import E213.Meta.Algebra213.CDDouble
import E213.Meta.Algebra213.AlternativeNormed

/-!
# Generic `StarRing213 (CDDouble α)` instance

CD doubling functor as a typeclass-level lift:

  `[CommStarRing213 α] → StarRing213 (CDDouble α)`

This file provides the missing pieces (`mul_add`, `mul_assoc`,
`conj_conj`, `conj_add`, `conj_mul`) needed to register the
generic instance, and the bundled `Ring213` + `StarRing213`
instances at the end.

Once registered, every concrete CD layer over a commutative
star-ring base inherits its ring/star structure mechanically —
no per-layer hand-written axiom proofs required for ONE level
of CD doubling.

Note: a fully generic ∀-n type-level induction is impossible
within the single `StarRing213` class because Cayley-Dickson
construction breaks commutativity at the FIRST step (`CDDouble`
of a comm base is generally non-comm), and breaks associativity
at the SECOND step (`CDDouble` of a non-comm base loses
`mul_assoc`).  So this instance is the *cleanest one-level lift*
within the existing class hierarchy.

For multi-step iteration, see `Theory.CDDouble.UniversalOrder4`
which proves `cdd_lift_squared` at the abstract `StarRing213`
level (the Order-4 mechanism survives at every layer).
-/

namespace E213.Meta.Algebra213.CDDouble

variable {α : Type}

-- ═══ Componentwise add axioms (Ring213 α suffices) ═══
-- Re-proved here for cross-file visibility (private in Algebra213CDDouble.lean).

private theorem add_assoc' [Ring213 α] (u v w : CDDouble α) :
    u + v + w = u + (v + w) := by
  apply ext
  · exact Ring213.add_assoc u.re v.re w.re
  · exact Ring213.add_assoc u.im v.im w.im

private theorem add_comm' [Ring213 α] (u v : CDDouble α) :
    u + v = v + u := by
  apply ext
  · exact Ring213.add_comm u.re v.re
  · exact Ring213.add_comm u.im v.im

private theorem add_zero' [Ring213 α] (u : CDDouble α) : u + 0 = u := by
  apply ext
  · exact Ring213.add_zero u.re
  · exact Ring213.add_zero u.im

private theorem add_left_neg' [Ring213 α] (u : CDDouble α) : -u + u = 0 := by
  apply ext
  · exact Ring213.add_left_neg u.re
  · exact Ring213.add_left_neg u.im

private theorem add_mul' [StarRing213 α] (u v w : CDDouble α) :
    (u + v) * w = u * w + v * w := by
  apply ext
  · show (u.re + v.re) * w.re + -(StarRing213.conj w.im * (u.im + v.im))
       = (u.re * w.re + -(StarRing213.conj w.im * u.im))
       + (v.re * w.re + -(StarRing213.conj w.im * v.im))
    rw [Ring213.add_mul u.re v.re w.re,
        Ring213.mul_add (StarRing213.conj w.im) u.im v.im]
    rw [Ring213.neg_add (StarRing213.conj w.im * u.im)
                         (StarRing213.conj w.im * v.im)]
    exact Ring213.add_4_swap_mid _ _ _ _
  · show w.im * (u.re + v.re) + (u.im + v.im) * StarRing213.conj w.re
       = (w.im * u.re + u.im * StarRing213.conj w.re)
       + (w.im * v.re + v.im * StarRing213.conj w.re)
    rw [Ring213.mul_add w.im u.re v.re,
        Ring213.add_mul u.im v.im (StarRing213.conj w.re)]
    exact Ring213.add_4_swap_mid _ _ _ _

-- ═══ Helpers: conj_zero, conj_neg (generic StarRing213) ═══

/-- `StarRing213` derived: `conj 0 = 0`. -/
private theorem conj_zero_base {α : Type} [StarRing213 α] :
    StarRing213.conj (0 : α) = 0 := by
  have hzz : StarRing213.conj (0 : α)
           = StarRing213.conj 0 + StarRing213.conj 0 := by
    have z : (0 : α) + 0 = 0 := Ring213.add_zero 0
    calc StarRing213.conj (0 : α)
        = StarRing213.conj ((0 : α) + 0) := by rw [z]
      _ = StarRing213.conj 0 + StarRing213.conj 0 := StarRing213.conj_add 0 0
  have h2 : -StarRing213.conj (0 : α) + StarRing213.conj 0 = 0 :=
    Ring213.add_left_neg _
  -- 0 = -conj 0 + conj 0 = -conj 0 + (conj 0 + conj 0)
  --   = (-conj 0 + conj 0) + conj 0 = 0 + conj 0 = conj 0
  calc StarRing213.conj (0 : α)
      = 0 + StarRing213.conj 0 := (Ring213.zero_add _).symm
    _ = (-StarRing213.conj 0 + StarRing213.conj 0) + StarRing213.conj 0 := by rw [h2]
    _ = -StarRing213.conj 0 + (StarRing213.conj 0 + StarRing213.conj 0) :=
          Ring213.add_assoc _ _ _
    _ = -StarRing213.conj 0 + StarRing213.conj 0 := by rw [← hzz]
    _ = 0 := h2

/-- `StarRing213` derived: `conj (-a) = -conj a`.  Follows from
    `conj_add` + uniqueness of additive inverse. -/
private theorem conj_neg {α : Type} [StarRing213 α] (a : α) :
    StarRing213.conj (-a) = -(StarRing213.conj a) := by
  have h0 : StarRing213.conj (-a) + StarRing213.conj a = 0 := by
    rw [← StarRing213.conj_add (-a) a, Ring213.add_left_neg a, conj_zero_base]
  have h1 : -StarRing213.conj a + StarRing213.conj a = 0 :=
    Ring213.add_left_neg _
  calc StarRing213.conj (-a)
      = StarRing213.conj (-a) + 0 := (Ring213.add_zero _).symm
    _ = StarRing213.conj (-a) + (StarRing213.conj a + -StarRing213.conj a) := by
          rw [Ring213.add_comm (StarRing213.conj a) (-StarRing213.conj a), h1]
    _ = (StarRing213.conj (-a) + StarRing213.conj a) + -StarRing213.conj a :=
          (Ring213.add_assoc _ _ _).symm
    _ = 0 + -StarRing213.conj a := by rw [h0]
    _ = -StarRing213.conj a + 0 := Ring213.add_comm _ _
    _ = -StarRing213.conj a := Ring213.add_zero _

-- ═══ Easy generic theorems (StarRing213 sufficient) ═══

private theorem mul_add' [StarRing213 α] (u v w : CDDouble α) :
    u * (v + w) = u * v + u * w := by
  apply ext
  · show u.re * (v.re + w.re)
         + -(StarRing213.conj (v.im + w.im) * u.im)
       = (u.re * v.re + -(StarRing213.conj v.im * u.im))
       + (u.re * w.re + -(StarRing213.conj w.im * u.im))
    rw [StarRing213.conj_add v.im w.im,
        Ring213.mul_add u.re v.re w.re,
        Ring213.add_mul (StarRing213.conj v.im) (StarRing213.conj w.im) u.im,
        Ring213.neg_add (StarRing213.conj v.im * u.im) (StarRing213.conj w.im * u.im)]
    exact Ring213.add_4_swap_mid _ _ _ _
  · show (v.im + w.im) * u.re + u.im * StarRing213.conj (v.re + w.re)
       = (v.im * u.re + u.im * StarRing213.conj v.re)
       + (w.im * u.re + u.im * StarRing213.conj w.re)
    rw [StarRing213.conj_add v.re w.re,
        Ring213.add_mul v.im w.im u.re,
        Ring213.mul_add u.im (StarRing213.conj v.re) (StarRing213.conj w.re)]
    exact Ring213.add_4_swap_mid _ _ _ _

private theorem conj_conj' [StarRing213 α] (u : CDDouble α) :
    conj (conj u) = u := by
  apply ext
  · show StarRing213.conj (StarRing213.conj u.re) = u.re
    exact StarRing213.conj_conj u.re
  · show -(-u.im) = u.im
    exact Ring213.neg_neg u.im

private theorem conj_add' [StarRing213 α] (u v : CDDouble α) :
    conj (u + v) = conj u + conj v := by
  apply ext
  · show StarRing213.conj (u.re + v.re) = StarRing213.conj u.re + StarRing213.conj v.re
    exact StarRing213.conj_add u.re v.re
  · show -(u.im + v.im) = -u.im + -v.im
    exact Ring213.neg_add u.im v.im

-- ═══ Generic Ring213 4-term cycle helper (used in mul_assoc) ═══

private theorem add_4_cycle {β : Type} [Ring213 β] (A B C D : β) :
    A + B + C + D = A + C + D + B := by
  rw [Ring213.add_right_comm A B C, Ring213.add_right_comm (A + C) B D]

-- ═══ Anti-distributive conj_mul ([StarRing213 α] suffices) ═══
-- Proof uses only Ring213 add_comm + neg_add + neg_mul + StarRing213's
-- anti-distributive conj_mul at the base.  No multiplicative commutativity.

private theorem conj_mul' [StarRing213 α] (u v : CDDouble α) :
    conj (u * v) = conj v * conj u := by
  apply ext
  · -- LHS: conj((u*v).re) = conj(u.re * v.re + -(conj v.im * u.im))
    --     = conj(u.re*v.re) + conj(-(conj v.im * u.im))
    --     = (conj v.re) * (conj u.re) + -((conj u.im) * (conj (conj v.im)))
    --     = (conj v.re) * (conj u.re) + -((conj u.im) * v.im)
    -- RHS: ((conj v) * (conj u)).re
    --    = (conj v).re * (conj u).re + -(conj (conj u).im * (conj v).im)
    --    = (conj v.re) * (conj u.re) + -(conj (-u.im) * (-v.im))
    -- Need: -(conj u.im * v.im) = -(conj (-u.im) * (-v.im))
    -- Use conj of -x = - conj x ; (-a)*(-b) = a*b
    show StarRing213.conj (u.re * v.re + -(StarRing213.conj v.im * u.im))
       = StarRing213.conj v.re * StarRing213.conj u.re
         + -(StarRing213.conj (-u.im) * -v.im)
    rw [StarRing213.conj_add (u.re * v.re) (-(StarRing213.conj v.im * u.im)),
        StarRing213.conj_mul u.re v.re]
    -- Goal: conj v.re * conj u.re + conj(-(conj v.im * u.im))
    --     = conj v.re * conj u.re + -(conj(-u.im) * -v.im)
    -- Reduce both sides separately to a common form.
    -- LHS .2nd = conj(-(X)) = -conj(X) = -(conj u.im * conj(conj v.im))
    --         = -(conj u.im * v.im)
    -- RHS .2nd = -(conj(-u.im) * -v.im) = -((-conj u.im) * -v.im)
    --         = -(conj u.im * v.im)
    have h_left : StarRing213.conj (-(StarRing213.conj v.im * u.im))
                = -(StarRing213.conj u.im * v.im) := by
      have h1 : StarRing213.conj (-(StarRing213.conj v.im * u.im))
              = -(StarRing213.conj (StarRing213.conj v.im * u.im)) :=
        conj_neg (StarRing213.conj v.im * u.im)
      have h2 : StarRing213.conj (StarRing213.conj v.im * u.im)
              = StarRing213.conj u.im * v.im := by
        rw [StarRing213.conj_mul (StarRing213.conj v.im) u.im,
            StarRing213.conj_conj v.im]
      rw [h1, h2]
    have h_right : -(StarRing213.conj (-u.im) * -v.im)
                 = -(StarRing213.conj u.im * v.im) := by
      rw [conj_neg u.im,
          Ring213.neg_mul (StarRing213.conj u.im) (-v.im),
          Ring213.mul_neg (StarRing213.conj u.im) v.im,
          Ring213.neg_neg]
    rw [h_left, h_right]
  · -- LHS: -(u*v).im = -(v.im * u.re + u.im * conj v.re)
    -- RHS: ((conj v) * (conj u)).im
    --    = (conj u).im * (conj v).re + (conj v).im * conj((conj u).re)
    --    = -u.im * conj v.re + (-v.im) * conj(conj u.re)
    --    = -u.im * conj v.re + (-v.im) * u.re
    show -(v.im * u.re + u.im * StarRing213.conj v.re)
       = -u.im * StarRing213.conj v.re + -v.im * StarRing213.conj (StarRing213.conj u.re)
    rw [StarRing213.conj_conj u.re,
        Ring213.neg_mul u.im (StarRing213.conj v.re),
        Ring213.neg_mul v.im u.re,
        Ring213.neg_add (v.im * u.re) (u.im * StarRing213.conj v.re),
        Ring213.add_comm (-(v.im * u.re)) (-(u.im * StarRing213.conj v.re))]

-- ═══ Generic mul_assoc.re (requires CommStarRing213 base) ═══
-- Direct port of LipschitzAlgebra213.mul_assoc_re': ZI → α,
-- ZI.conj_* → StarRing213.conj_*, all rewrites translate identically
-- since CommStarRing213 provides everything Lipschitz uses on ZI.

private theorem mul_assoc_re' [CommStarRing213 α] (u v w : CDDouble α) :
    ((u * v) * w).re = (u * (v * w)).re := by
  show (u.re * v.re + -(StarRing213.conj v.im * u.im)) * w.re
       + -(StarRing213.conj w.im
            * (v.im * u.re + u.im * StarRing213.conj v.re))
     = u.re * (v.re * w.re + -(StarRing213.conj w.im * v.im))
       + -(StarRing213.conj (w.im * v.re + v.im * StarRing213.conj w.re)
            * u.im)
  rw [StarRing213.conj_add (w.im * v.re) (v.im * StarRing213.conj w.re),
      StarRing213.conj_mul w.im v.re,
      StarRing213.conj_mul v.im (StarRing213.conj w.re),
      StarRing213.conj_conj w.re]
  rw [Ring213.add_mul (u.re * v.re) (-(StarRing213.conj v.im * u.im)) w.re,
      Ring213.mul_add (StarRing213.conj w.im) (v.im * u.re)
                       (u.im * StarRing213.conj v.re),
      Ring213.mul_add u.re (v.re * w.re) (-(StarRing213.conj w.im * v.im)),
      Ring213.add_mul (StarRing213.conj v.re * StarRing213.conj w.im)
                       (w.re * StarRing213.conj v.im) u.im]
  rw [Ring213.neg_add (StarRing213.conj w.im * (v.im * u.re))
                       (StarRing213.conj w.im * (u.im * StarRing213.conj v.re)),
      Ring213.neg_add (StarRing213.conj v.re * StarRing213.conj w.im * u.im)
                       (w.re * StarRing213.conj v.im * u.im)]
  rw [Ring213.neg_mul (StarRing213.conj v.im * u.im) w.re,
      Ring213.mul_neg u.re (StarRing213.conj w.im * v.im)]
  rw [Ring213.mul_assoc u.re v.re w.re]
  -- Reorganize cross-terms via mul_assoc + mul_comm.
  rw [show StarRing213.conj v.im * u.im * w.re = w.re * StarRing213.conj v.im * u.im
      from by rw [Ring213.mul_assoc (StarRing213.conj v.im) u.im w.re,
                  CommRing213.mul_comm u.im w.re,
                  ← Ring213.mul_assoc (StarRing213.conj v.im) w.re u.im,
                  CommRing213.mul_comm (StarRing213.conj v.im) w.re]]
  rw [show StarRing213.conj w.im * (v.im * u.re) = u.re * (StarRing213.conj w.im * v.im)
      from by rw [← Ring213.mul_assoc (StarRing213.conj w.im) v.im u.re,
                  CommRing213.mul_comm (StarRing213.conj w.im * v.im) u.re]]
  rw [show StarRing213.conj w.im * (u.im * StarRing213.conj v.re)
        = StarRing213.conj v.re * StarRing213.conj w.im * u.im
      from by rw [CommRing213.mul_comm u.im (StarRing213.conj v.re),
                  ← Ring213.mul_assoc (StarRing213.conj w.im)
                       (StarRing213.conj v.re) u.im,
                  CommRing213.mul_comm (StarRing213.conj w.im)
                       (StarRing213.conj v.re)]]
  rw [← Ring213.add_assoc
        (u.re * (v.re * w.re) + -(w.re * StarRing213.conj v.im * u.im))
        (-(u.re * (StarRing213.conj w.im * v.im)))
        (-(StarRing213.conj v.re * StarRing213.conj w.im * u.im))]
  rw [← Ring213.add_assoc
        (u.re * (v.re * w.re) + -(u.re * (StarRing213.conj w.im * v.im)))
        (-(StarRing213.conj v.re * StarRing213.conj w.im * u.im))
        (-(w.re * StarRing213.conj v.im * u.im))]
  exact add_4_cycle _ _ _ _

-- ═══ Generic mul_assoc.im (requires CommStarRing213 base) ═══

private theorem mul_assoc_im' [CommStarRing213 α] (u v w : CDDouble α) :
    ((u * v) * w).im = (u * (v * w)).im := by
  show w.im * (u.re * v.re + -(StarRing213.conj v.im * u.im))
       + (v.im * u.re + u.im * StarRing213.conj v.re) * StarRing213.conj w.re
     = (w.im * v.re + v.im * StarRing213.conj w.re) * u.re
       + u.im * StarRing213.conj
                  (v.re * w.re + -(StarRing213.conj w.im * v.im))
  rw [StarRing213.conj_add (v.re * w.re) (-(StarRing213.conj w.im * v.im)),
      StarRing213.conj_mul v.re w.re,
      conj_neg (StarRing213.conj w.im * v.im),
      StarRing213.conj_mul (StarRing213.conj w.im) v.im,
      StarRing213.conj_conj w.im]
  rw [Ring213.mul_add w.im (u.re * v.re) (-(StarRing213.conj v.im * u.im)),
      Ring213.add_mul (v.im * u.re) (u.im * StarRing213.conj v.re)
                       (StarRing213.conj w.re),
      Ring213.add_mul (w.im * v.re) (v.im * StarRing213.conj w.re) u.re,
      Ring213.mul_add u.im (StarRing213.conj w.re * StarRing213.conj v.re)
                       (-(StarRing213.conj v.im * w.im))]
  rw [Ring213.mul_neg w.im (StarRing213.conj v.im * u.im),
      Ring213.mul_neg u.im (StarRing213.conj v.im * w.im)]
  -- Now reorganize 4 + 4 terms to match.
  rw [show w.im * (u.re * v.re) = w.im * v.re * u.re
      from by rw [CommRing213.mul_comm u.re v.re,
                  ← Ring213.mul_assoc w.im v.re u.re]]
  rw [show w.im * (StarRing213.conj v.im * u.im) = u.im * (StarRing213.conj v.im * w.im)
      from by
        rw [← Ring213.mul_assoc w.im (StarRing213.conj v.im) u.im,
            CommRing213.mul_comm (w.im * StarRing213.conj v.im) u.im,
            CommRing213.mul_comm w.im (StarRing213.conj v.im)]]
  rw [show v.im * u.re * StarRing213.conj w.re
        = v.im * StarRing213.conj w.re * u.re
      from by rw [Ring213.mul_assoc v.im u.re (StarRing213.conj w.re),
                  CommRing213.mul_comm u.re (StarRing213.conj w.re),
                  ← Ring213.mul_assoc v.im (StarRing213.conj w.re) u.re]]
  -- Convert LHS `u.im * conj v.re * conj w.re` to RHS form
  -- `u.im * (conj w.re * conj v.re)` via mul_assoc + mul_comm.
  rw [show u.im * StarRing213.conj v.re * StarRing213.conj w.re
        = u.im * (StarRing213.conj w.re * StarRing213.conj v.re)
      from by rw [Ring213.mul_assoc u.im
                    (StarRing213.conj v.re) (StarRing213.conj w.re),
                  CommRing213.mul_comm
                    (StarRing213.conj v.re) (StarRing213.conj w.re)]]
  rw [← Ring213.add_assoc
        (w.im * v.re * u.re + -(u.im * (StarRing213.conj v.im * w.im)))
        (v.im * StarRing213.conj w.re * u.re)
        (u.im * (StarRing213.conj w.re * StarRing213.conj v.re))]
  rw [add_4_cycle (w.im * v.re * u.re)
        (-(u.im * (StarRing213.conj v.im * w.im)))
        (v.im * StarRing213.conj w.re * u.re)
        (u.im * (StarRing213.conj w.re * StarRing213.conj v.re))]
  rw [Ring213.add_assoc
        (w.im * v.re * u.re + v.im * StarRing213.conj w.re * u.re)
        (u.im * (StarRing213.conj w.re * StarRing213.conj v.re))
        (-(u.im * (StarRing213.conj v.im * w.im)))]

/-- ★ Generic CDDouble mul_assoc (requires CommStarRing213 base). -/
private theorem mul_assoc' [CommStarRing213 α] (u v w : CDDouble α) :
    (u * v) * w = u * (v * w) := by
  apply ext
  · exact mul_assoc_re' u v w
  · exact mul_assoc_im' u v w

-- ═══ Generic CDDouble Ring213/StarRing213 instances ═══
-- Bind the private theorems above into the typeclass record.
-- Note: `Ring213 (CDDouble α)` requires `mul_assoc`, which only
-- holds when the base is *commutative*; hence `[CommStarRing213 α]`.
-- Once registered, every concrete CDDouble^1 over a comm star-ring
-- inherits all Ring213 + StarRing213 structure mechanically.

open E213.Meta.Algebra213.CDDouble in
instance instRing213CDDouble [CommStarRing213 α] : Ring213 (CDDouble α) where
  add_assoc    := add_assoc'
  add_comm     := add_comm'
  add_zero     := add_zero'
  add_left_neg := add_left_neg'
  mul_assoc    := mul_assoc'
  add_mul      := add_mul'
  mul_add      := mul_add'

open E213.Meta.Algebra213.CDDouble in
instance instStarRing213CDDouble [CommStarRing213 α] :
    StarRing213 (CDDouble α) where
  conj      := conj
  conj_conj := conj_conj'
  conj_add  := conj_add'
  conj_mul  := conj_mul'

/-! ## §6 — Non-associative parametric instances on `CDDouble α`

`CDDouble α` is non-associative when α is non-commutative (Cayley
layer onward).  This section provides `NonAssocRing213` and
`NonAssocStarRing213` instances on `CDDouble α` requiring only
`[StarRing213 α]` (no commutativity, no mul_assoc).

These instances unlock the Cayley-layer algebraic structure for
concrete CD layers built on non-commutative associative bases —
specifically `CDDouble ZOmegaDouble` (Type C L4 = ZOmegaQuad),
`CDDouble L3T` (Type B L4 = L4T), and `CDDouble Lipschitz`
(Type A L3 = Cayley).  Each concrete type then bridges through
the abstract instance via `toCDDouble`.
-/

open E213.Meta.Algebra213.CDDouble in
/-- `NonAssocRing213 (CDDouble α)` from `[StarRing213 α]`.  Drops the
    `mul_assoc` field present in `Ring213`.  All other axioms reduce
    to base-ring projections componentwise. -/
instance instNonAssocRing213CDDoubleStar [StarRing213 α] :
    NonAssocRing213 (CDDouble α) where
  add_assoc    := add_assoc'
  add_comm     := add_comm'
  add_zero     := add_zero'
  add_left_neg := add_left_neg'
  add_mul      := add_mul'
  mul_add      := mul_add'

open E213.Meta.Algebra213.CDDouble in
/-- `NonAssocStarRing213 (CDDouble α)` from `[StarRing213 α]`.  Extends
    the parametric `NonAssocRing213` with the anti-distributive
    `conj_mul` proved at `[StarRing213 α]` level (no commutativity). -/
instance instNonAssocStarRing213CDDoubleStar [StarRing213 α] :
    NonAssocStarRing213 (CDDouble α) where
  conj      := conj
  conj_conj := conj_conj'
  conj_add  := conj_add'
  conj_mul  := conj_mul'

/-! ## §7 — Abstract `IntegerNormed213 (CDDouble α)` for comm base

Cayley-Dickson Hurwitz extension at the level of a CD doubling over
a commutative integer-normed *-ring base.  Provides the
`IntegerNormed213 (CDDouble α)` instance parametrically — once
registered, the generic `IntegerNormed213.normSq_mul` derives
`N(uv) = N(u)·N(v)` at the CDDouble carrier for free.

Concrete L2/L3 quaternion-analog instances (Lipschitz=CDDouble ZI,
ZOmegaDouble=CDDouble ZOmega, L3T=CDDouble Z2) all satisfy
`[CommStarRing213 α]` and `[IntegerNormed213 α]` at base. -/

variable [IntegerNormed213 α]

/-- CDDouble lifted ofInt: real-axis embed. -/
def cd_ofInt (z : Int) : CDDouble α :=
  ⟨IntegerNormed213.ofInt z, 0⟩

/-- CDDouble lifted normSq: sum of base norms (CD recurrence). -/
def cd_normSq (u : CDDouble α) : Int :=
  IntegerNormed213.normSq u.re + IntegerNormed213.normSq u.im

/-- Abstract `self_mul_conj` at CDDouble α level.
    For u = ⟨a, b⟩, conj u = ⟨ā, -b⟩.  u · conj u expands to:
      .re: a·ā - (-b)̄·b = a·ā + b̄·b = ofInt(N a + N b)
      .im: (-b)·a + b·(ā)̄ = -(b·a) + b·a = 0 -/
private theorem cd_self_mul_conj' (u : CDDouble α) :
    u * CDDouble.conj u = cd_ofInt (cd_normSq u) := by
  apply ext
  · show u.re * StarRing213.conj u.re
         + -(StarRing213.conj (-u.im) * u.im)
       = IntegerNormed213.ofInt
           (IntegerNormed213.normSq u.re + IntegerNormed213.normSq u.im)
    rw [conj_neg u.im,
        Ring213.neg_mul (StarRing213.conj u.im) u.im, Ring213.neg_neg,
        IntegerNormed213.self_mul_conj u.re,
        IntegerNormed213.conj_mul_self u.im,
        ← IntegerNormed213.ofInt_add (IntegerNormed213.normSq u.re)
                                      (IntegerNormed213.normSq u.im)]
  · show (-u.im) * u.re + u.im * StarRing213.conj (StarRing213.conj u.re)
       = (0 : α)
    rw [StarRing213.conj_conj,
        Ring213.neg_mul u.im u.re,
        Ring213.add_left_neg (u.im * u.re)]

/-- Helper: `-(0 : α) = 0` in any `Ring213 α`. -/
private theorem ring_neg_zero {α : Type} [Ring213 α] : -(0 : α) = 0 := by
  have h1 : -(0 : α) + 0 = 0 := Ring213.add_left_neg 0
  have h2 : -(0 : α) + 0 = -0 := Ring213.add_zero (-0)
  exact h2.symm.trans h1

/-- Abstract `ofInt_mul` at CDDouble α level.  ⟨ofInt a, 0⟩ · ⟨ofInt b, 0⟩
    = ⟨ofInt a · ofInt b - 0̄·0, 0·ofInt a + 0·0̄⟩
    = ⟨ofInt(a*b), 0⟩. -/
private theorem cd_ofInt_mul' (a b : Int) :
    cd_ofInt a * (cd_ofInt b : CDDouble α) = cd_ofInt (a * b) := by
  apply ext
  · show IntegerNormed213.ofInt a * IntegerNormed213.ofInt b
         + -(StarRing213.conj 0 * 0)
       = IntegerNormed213.ofInt (a * b)
    rw [conj_zero_base, Ring213.zero_mul, ring_neg_zero,
        Ring213.add_zero, IntegerNormed213.ofInt_mul]
  · show (0 : α) * IntegerNormed213.ofInt a + 0 * StarRing213.conj (IntegerNormed213.ofInt b)
       = 0
    rw [Ring213.zero_mul, Ring213.zero_mul, Ring213.add_zero]

/-- Abstract `ofInt_add` at CDDouble α level. -/
private theorem cd_ofInt_add' (a b : Int) :
    cd_ofInt a + (cd_ofInt b : CDDouble α) = cd_ofInt (a + b) := by
  apply ext
  · show IntegerNormed213.ofInt a + IntegerNormed213.ofInt b
       = IntegerNormed213.ofInt (a + b)
    exact IntegerNormed213.ofInt_add a b
  · show (0 : α) + 0 = 0
    exact Ring213.add_zero 0

/-- Abstract `ofInt_inj` at CDDouble α level.  Follows from base
    `ofInt_inj` applied to the `re` component. -/
private theorem cd_ofInt_inj' {a b : Int}
    (h : (cd_ofInt a : CDDouble α) = cd_ofInt b) : a = b := by
  have h_re : (cd_ofInt a : CDDouble α).re = (cd_ofInt b : CDDouble α).re :=
    congrArg CDDouble.re h
  exact IntegerNormed213.ofInt_inj h_re

/-- Abstract `ofInt_central` at CDDouble α level.  ⟨ofInt z, 0⟩ · ⟨a, b⟩
    = ⟨a, b⟩ · ⟨ofInt z, 0⟩.  Uses base `ofInt_central` +
    `ofInt_conj` (`conj (ofInt z) = ofInt z`). -/
private theorem cd_ofInt_central' (z : Int) (u : CDDouble α) :
    cd_ofInt z * u = u * cd_ofInt z := by
  apply ext
  · show IntegerNormed213.ofInt z * u.re + -(StarRing213.conj u.im * 0)
       = u.re * IntegerNormed213.ofInt z + -(StarRing213.conj 0 * u.im)
    rw [conj_zero_base, Ring213.zero_mul, Ring213.mul_zero,
        ring_neg_zero, IntegerNormed213.ofInt_central]
  · show u.im * IntegerNormed213.ofInt z + 0 * StarRing213.conj u.re
       = 0 * u.re + u.im * StarRing213.conj (IntegerNormed213.ofInt z)
    rw [Ring213.zero_mul, Ring213.zero_mul, Ring213.add_zero,
        Ring213.zero_add, IntegerNormed213.ofInt_conj]

/-- Abstract `normSq_conj` at CDDouble α level.  cd_normSq (conj u)
    = N(conj u.re) + N(-u.im) = N u.re + N u.im = cd_normSq u.  Uses
    base `normSq_conj` and a helper for `N(-a) = N a` derived via
    `self_mul_conj` + `neg_mul` + `mul_neg` + `neg_neg` + `ofInt_inj`. -/
private theorem cd_normSq_conj' (u : CDDouble α) :
    cd_normSq (CDDouble.conj u) = cd_normSq u := by
  show IntegerNormed213.normSq (StarRing213.conj u.re)
       + IntegerNormed213.normSq (-u.im)
     = IntegerNormed213.normSq u.re + IntegerNormed213.normSq u.im
  rw [IntegerNormed213.normSq_conj u.re]
  have h_neg : IntegerNormed213.normSq (-u.im) = IntegerNormed213.normSq u.im := by
    apply @IntegerNormed213.ofInt_inj α _
    rw [← IntegerNormed213.self_mul_conj (-u.im),
        ← IntegerNormed213.self_mul_conj u.im,
        conj_neg u.im,
        Ring213.neg_mul u.im (-StarRing213.conj u.im),
        Ring213.mul_neg u.im (StarRing213.conj u.im),
        Ring213.neg_neg]
  rw [h_neg]

/-! ## Abstract Cayley-Dickson Hurwitz extension — public theorems

The `cd_*` private theorems above provide all 8 IntegerNormed213 fields
abstractly over `[CommStarRing213 α] [IntegerNormed213 α]` base.  The
parametric instance `IntegerNormed213 (CDDouble α)` would unlock the
generic `IntegerNormed213.normSq_mul` for the CDDouble carrier directly,
but registration is blocked by a typeclass diamond between
`CommStarRing213.toStarRing213` and `IntegerNormed213.toStarRing213`
when both are inferred for α — Lean treats these as distinct StarRing213
α records even though they share the same `conj` field.  Resolution
requires a structural reorganization (e.g., a `CommIntegerNormed213`
typeclass that combines both, avoiding the diamond at instance time).

In the meantime, the abstract `cd_*` lemmas can be invoked manually
per concrete bridge (Lipschitz/ZOmegaDouble/L3T) to replace their
hand-written self_mul_conj'/ofInt_*/normSq_conj proofs. -/

end E213.Meta.Algebra213.CDDouble
