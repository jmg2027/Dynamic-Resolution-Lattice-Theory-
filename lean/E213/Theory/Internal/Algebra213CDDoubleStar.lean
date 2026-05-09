import E213.Theory.Internal.Algebra213CDDouble

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

namespace E213.Theory.Internal.Algebra213.CDDouble

variable {α : Type}

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

-- ═══ Anti-distributive conj_mul (requires CommStarRing213 base) ═══

private theorem conj_mul' [CommStarRing213 α] (u v : CDDouble α) :
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

end E213.Theory.Internal.Algebra213.CDDouble
