import E213.Meta.Algebra213.CDDoubleStar

/-!
# `MoufangIntegerNormed213 (CDDouble α)` over a non-commutative base

The associative Cayley-Dickson layers (Lipschitz, ZOmegaDouble, L3T)
register `MoufangIntegerNormed213` trivially: `mul_assoc` collapses the
Moufang norm identity in one re-association.  The *next* layer
(Cayley = CDDouble Lipschitz, ZOmegaQuad = CDDouble ZOmegaDouble,
L4T = CDDouble L3T) doubles a **non-commutative** associative base and
loses associativity, so the Moufang identity becomes the genuine
degree-4 Hurwitz norm-composition identity.

This file proves that identity once, abstractly, for `CDDouble α` over
any `[TraceNormed213 α]`.  The proof isolates the non-commutative
residue into exactly four cross-terms and cancels them with the single
**polarization condition** `a + conj a = ofInt (trace a)` (central):

  * four *diagonal* terms collapse to central `ofInt` scalars via
    `self_mul_conj` (`diag_collapse`);
  * four *cross* terms cancel pairwise via `cross_zero`, which is the
    trace-form companion of `self_mul_conj`.

This replaces the 32-Int-variable `hurwitz_ring` brute force at the
Cayley layer with one structural lemma reused across Types A/B/C.
-/

namespace E213.Meta.Algebra213

open Ring213 StarRing213 IntegerNormed213 TraceNormed213

variable {α : Type} [TraceNormed213 α]

/-- Pure additive-group reshuffle (commutative monoid permutation)
    used to finish `cross_zero`.  Both sides are the 5-element sum
    `{S,X,Y,P,M}`. -/
private theorem add_shuffle (S X Y P M : α) :
    M + (S + X + (Y + P)) = P + (S + Y + (X + M)) := by
  have hL : M + (S + X + (Y + P)) = S + (Y + (X + (M + P))) := by
    rw [Ring213.add_comm M (S + X + (Y + P)),
        Ring213.add_assoc (S + X) (Y + P) M,
        Ring213.add_assoc S X (Y + P + M),
        Ring213.add_assoc Y P M,
        Ring213.add_comm P M,
        Ring213.add_left_comm X Y (M + P)]
  have hR : P + (S + Y + (X + M)) = S + (Y + (X + (M + P))) := by
    rw [Ring213.add_comm P (S + Y + (X + M)),
        Ring213.add_assoc (S + Y) (X + M) P,
        Ring213.add_assoc S Y (X + M + P),
        Ring213.add_assoc X M P]
  rw [hL, hR]

/-- `(A+B)+(C+D) = (A+D)+(B+C)` — swap the inner pair. -/
private theorem swap_inner4 (A B C D : α) :
    A + B + (C + D) = A + D + (B + C) := by
  rw [Ring213.add_assoc A B (C + D), Ring213.add_comm C D,
      ← Ring213.add_assoc B D C, Ring213.add_comm B D,
      Ring213.add_assoc D B C, ← Ring213.add_assoc A D (B + C)]

/-- `(A+B)+(C+D) = (A+C)+(B+D)` — swap the two middle terms. -/
private theorem swap_mid4 (A B C D : α) :
    A + B + (C + D) = A + C + (B + D) := by
  rw [Ring213.add_assoc A B (C + D), ← Ring213.add_assoc B C D,
      Ring213.add_comm B C, Ring213.add_assoc C B D,
      ← Ring213.add_assoc A C (B + D)]

/-! ## §1 — Base-α polarization lemmas -/

/-- Solve `self_add_conj` for `conj`: `conj a = ofInt (trace a) + -a`. -/
theorem conj_eq (a : α) : conj a = ofInt (trace a) + -a := by
  calc conj a
      = 0 + conj a := (Ring213.zero_add _).symm
    _ = (-a + a) + conj a := by rw [Ring213.add_left_neg]
    _ = -a + (a + conj a) := Ring213.add_assoc _ _ _
    _ = -a + ofInt (trace a) := by rw [self_add_conj]
    _ = ofInt (trace a) + -a := Ring213.add_comm _ _

/-- Diagonal collapse: in the associative base, the Hurwitz "sandwich"
    `(x·y)·(conj y·conj x)` is the central scalar `ofInt (|y|²·|x|²)`. -/
theorem diag_collapse (x y : α) :
    (x * y) * (conj y * conj x) = ofInt (normSq y * normSq x) := by
  rw [← Ring213.mul_assoc (x * y) (conj y) (conj x),
      Ring213.mul_assoc x y (conj y),
      self_mul_conj y,
      ← ofInt_central (normSq y) x,
      Ring213.mul_assoc (ofInt (normSq y)) x (conj x),
      self_mul_conj x,
      ofInt_mul]

/-- **Polarization cross-cancellation.**  The non-commutative residue
    of the Hurwitz identity.  Using `conj a = ofInt(trace a) - a` and
    centrality of `ofInt`, the difference `conj a·conj w − conj w·conj a`
    equals `a·w − w·a`, which is exactly what the cross-terms need. -/
theorem cross_zero (a w : α) :
    w * a + conj a * conj w = a * w + conj w * conj a := by
  rw [conj_eq a, conj_eq w]
  rw [Ring213.add_mul (ofInt (trace a)) (-a) (ofInt (trace w) + -w),
      Ring213.add_mul (ofInt (trace w)) (-w) (ofInt (trace a) + -a),
      Ring213.mul_add (ofInt (trace a)) (ofInt (trace w)) (-w),
      Ring213.mul_add (-a) (ofInt (trace w)) (-w),
      Ring213.mul_add (ofInt (trace w)) (ofInt (trace a)) (-a),
      Ring213.mul_add (-w) (ofInt (trace a)) (-a)]
  rw [Ring213.mul_neg (ofInt (trace a)) w,
      Ring213.neg_mul a (ofInt (trace w)),
      Ring213.neg_mul a (-w), Ring213.mul_neg a w, Ring213.neg_neg,
      Ring213.mul_neg (ofInt (trace w)) a,
      Ring213.neg_mul w (ofInt (trace a)),
      Ring213.neg_mul w (-a), Ring213.mul_neg w a, Ring213.neg_neg,
      ofInt_central (trace w) a, ofInt_central (trace a) w,
      ofInt_mul (trace a) (trace w), ofInt_mul (trace w) (trace a),
      E213.Meta.Int213.mul_comm (trace w) (trace a)]
  exact add_shuffle _ _ _ _ _

/-- The four Hurwitz cross-terms, assembled in the form
    `T7 + T6 = (positive T2) + (positive T3)`, which is exactly
    `cross_zero` for the witness `w = (c·conj b)·d`.  All four terms
    are re-associated to `w·a`, `conj a·conj w`, `a·w`, `conj w·conj a`
    using base associativity. -/
theorem hurwitz_cross (a b c d : α) :
    (c * conj b) * (d * a) + (conj a * conj d) * (b * conj c)
      = (a * c) * (conj b * d) + (conj d * b) * (conj c * conj a) := by
  have hw : conj d * (b * conj c) = conj ((c * conj b) * d) := by
    rw [StarRing213.conj_mul (c * conj b) d, StarRing213.conj_mul c (conj b),
        StarRing213.conj_conj b]
  have e7 : (c * conj b) * (d * a) = ((c * conj b) * d) * a :=
    (Ring213.mul_assoc (c * conj b) d a).symm
  have e6 : (conj a * conj d) * (b * conj c)
          = conj a * conj ((c * conj b) * d) := by
    rw [Ring213.mul_assoc (conj a) (conj d) (b * conj c), hw]
  have e2 : (a * c) * (conj b * d) = a * ((c * conj b) * d) := by
    rw [Ring213.mul_assoc a c (conj b * d), Ring213.mul_assoc c (conj b) d]
  have e3 : (conj d * b) * (conj c * conj a)
          = conj ((c * conj b) * d) * conj a := by
    rw [← hw, Ring213.mul_assoc (conj d) b (conj c * conj a),
        ← Ring213.mul_assoc b (conj c) (conj a),
        ← Ring213.mul_assoc (conj d) (b * conj c) (conj a)]
  rw [e7, e6, e2, e3]
  exact cross_zero a ((c * conj b) * d)

/-- **The Cayley-Dickson Hurwitz norm identity over a non-commutative
    base.**  This is the `re`-component content of the Moufang
    norm-collapse for `CDDouble α`.  `a,b,c,d` play the role of
    `u.re, u.im, v.re, v.im`.  Four diagonal terms collapse to central
    `ofInt` scalars (`diag_collapse`); the four cross-terms cancel via
    the polarization lemma `hurwitz_cross`. -/
theorem hurwitz_norm_re (a b c d : α) :
    (a * c + -(conj d * b)) * (conj c * conj a + -(conj b * d))
      + (conj a * conj d + c * conj b) * (d * a + b * conj c)
    = (a * conj a + conj b * b) * (c * conj c + conj d * d) := by
  -- Diagonal collapses (with `conj_conj` / `normSq_conj` massaging).
  have hT1 : (a * c) * (conj c * conj a) = ofInt (normSq c * normSq a) :=
    diag_collapse a c
  have hT4 : (conj d * b) * (conj b * d) = ofInt (normSq b * normSq d) := by
    have h := diag_collapse (conj d) b
    rw [StarRing213.conj_conj d, normSq_conj d] at h; exact h
  have hT5 : (conj a * conj d) * (d * a) = ofInt (normSq d * normSq a) := by
    have h := diag_collapse (conj a) (conj d)
    rw [StarRing213.conj_conj d, StarRing213.conj_conj a, normSq_conj d,
        normSq_conj a] at h; exact h
  have hT8 : (c * conj b) * (b * conj c) = ofInt (normSq b * normSq c) := by
    have h := diag_collapse c (conj b)
    rw [StarRing213.conj_conj b, normSq_conj b] at h; exact h
  -- Cross-term cancellation, packaged in the post-distribution shape.
  have cross_sum_zero :
      -((a * c) * (conj b * d)) + -((conj d * b) * (conj c * conj a))
        + ((conj a * conj d) * (b * conj c) + (c * conj b) * (d * a)) = 0 := by
    rw [Ring213.add_comm ((conj a * conj d) * (b * conj c))
          ((c * conj b) * (d * a)),
        hurwitz_cross a b c d,
        Ring213.add_assoc (-((a * c) * (conj b * d)))
          (-((conj d * b) * (conj c * conj a)))
          ((a * c) * (conj b * d) + (conj d * b) * (conj c * conj a)),
        ← Ring213.add_assoc (-((conj d * b) * (conj c * conj a)))
          ((a * c) * (conj b * d)) ((conj d * b) * (conj c * conj a)),
        Ring213.add_comm (-((conj d * b) * (conj c * conj a)))
          ((a * c) * (conj b * d)),
        Ring213.add_assoc ((a * c) * (conj b * d))
          (-((conj d * b) * (conj c * conj a)))
          ((conj d * b) * (conj c * conj a)),
        Ring213.add_left_neg ((conj d * b) * (conj c * conj a)),
        Ring213.add_zero ((a * c) * (conj b * d)),
        Ring213.add_left_neg ((a * c) * (conj b * d))]
  -- RHS expansion to four central scalars.
  have hRHS : (a * conj a + conj b * b) * (c * conj c + conj d * d)
            = ofInt (normSq a * normSq c) + ofInt (normSq a * normSq d)
              + (ofInt (normSq b * normSq c) + ofInt (normSq b * normSq d)) := by
    rw [Ring213.add_mul (a * conj a) (conj b * b) (c * conj c + conj d * d),
        Ring213.mul_add (a * conj a) (c * conj c) (conj d * d),
        Ring213.mul_add (conj b * b) (c * conj c) (conj d * d),
        self_mul_conj a, self_mul_conj c,
        conj_mul_self b, conj_mul_self d,
        ofInt_mul (normSq a) (normSq c), ofInt_mul (normSq a) (normSq d),
        ofInt_mul (normSq b) (normSq c), ofInt_mul (normSq b) (normSq d)]
  -- Distribute the LHS.
  rw [Ring213.add_mul (a * c) (-(conj d * b)) (conj c * conj a + -(conj b * d)),
      Ring213.add_mul (conj a * conj d) (c * conj b) (d * a + b * conj c),
      Ring213.mul_add (a * c) (conj c * conj a) (-(conj b * d)),
      Ring213.mul_add (-(conj d * b)) (conj c * conj a) (-(conj b * d)),
      Ring213.mul_add (conj a * conj d) (d * a) (b * conj c),
      Ring213.mul_add (c * conj b) (d * a) (b * conj c)]
  -- Normalise the negated summands.
  rw [Ring213.mul_neg (a * c) (conj b * d),
      Ring213.neg_mul (conj d * b) (conj c * conj a),
      Ring213.neg_mul (conj d * b) (-(conj b * d)),
      Ring213.mul_neg (conj d * b) (conj b * d), Ring213.neg_neg]
  -- Regroup diagonals together and cross-terms together.
  rw [swap_inner4 ((a * c) * (conj c * conj a)) (-((a * c) * (conj b * d)))
        (-((conj d * b) * (conj c * conj a))) ((conj d * b) * (conj b * d)),
      swap_inner4 ((conj a * conj d) * (d * a)) ((conj a * conj d) * (b * conj c))
        ((c * conj b) * (d * a)) ((c * conj b) * (b * conj c)),
      hT1, hT4, hT5, hT8,
      swap_mid4 (ofInt (normSq c * normSq a) + ofInt (normSq b * normSq d))
        (-((a * c) * (conj b * d)) + -((conj d * b) * (conj c * conj a)))
        (ofInt (normSq d * normSq a) + ofInt (normSq b * normSq c))
        ((conj a * conj d) * (b * conj c) + (c * conj b) * (d * a)),
      cross_sum_zero, Ring213.add_zero, hRHS]
  -- Reconcile the four central scalars (Int commutativity + reorder).
  rw [E213.Meta.Int213.mul_comm (normSq c) (normSq a),
      E213.Meta.Int213.mul_comm (normSq d) (normSq a),
      swap_mid4 (ofInt (normSq a * normSq c)) (ofInt (normSq b * normSq d))
        (ofInt (normSq a * normSq d)) (ofInt (normSq b * normSq c)),
      Ring213.add_comm (ofInt (normSq b * normSq d)) (ofInt (normSq b * normSq c))]

/-! ## §2 — Base `StarRing213` helpers (conj of `0` / `-`) -/

private theorem base_neg_zero : -(0 : α) = 0 :=
  ((Ring213.add_left_neg (0 : α)).symm.trans (Ring213.add_zero _)).symm

private theorem base_conj_zero : conj (0 : α) = 0 := by
  have h : conj (0 : α) = conj 0 + conj 0 := by
    rw [← StarRing213.conj_add, Ring213.add_zero]
  have h2 : -conj (0 : α) + conj 0 = 0 := Ring213.add_left_neg _
  calc conj (0 : α)
      = 0 + conj 0 := (Ring213.zero_add _).symm
    _ = (-conj 0 + conj 0) + conj 0 := by rw [h2]
    _ = -conj 0 + (conj 0 + conj 0) := Ring213.add_assoc _ _ _
    _ = -conj 0 + conj 0 := by rw [← h]
    _ = 0 := h2

private theorem base_conj_neg (a : α) : conj (-a) = -(conj a) := by
  have h0 : conj (-a) + conj a = 0 := by
    rw [← StarRing213.conj_add, Ring213.add_left_neg, base_conj_zero]
  calc conj (-a)
      = conj (-a) + 0 := (Ring213.add_zero _).symm
    _ = conj (-a) + (conj a + -conj a) := by
          rw [Ring213.add_comm (conj a) (-conj a), Ring213.add_left_neg]
    _ = (conj (-a) + conj a) + -conj a := (Ring213.add_assoc _ _ _).symm
    _ = 0 + -conj a := by rw [h0]
    _ = -conj a := Ring213.zero_add _

/-! ## §3 — `CDDouble α` integer-normed data (non-comm base) -/

/-- Real-axis integer embed. -/
def cdm_ofInt (z : Int) : CDDouble α := ⟨ofInt z, 0⟩

/-- Cayley-Dickson norm: sum of component norms. -/
def cdm_normSq (u : CDDouble α) : Int := normSq u.re + normSq u.im

/-- Anti-distributive conj on `CDDouble α` (re-exported from the
    parametric `NonAssocStarRing213 (CDDouble α)` instance). -/
theorem cd_conj_mul (u v : CDDouble α) :
    CDDouble.conj (u * v) = CDDouble.conj v * CDDouble.conj u :=
  NonAssocStarRing213.conj_mul u v

/-- `self_mul_conj` for `CDDouble α`: `u · conj u = ofInt (|u|²)`. -/
theorem cd_self_mul_conj (u : CDDouble α) :
    u * CDDouble.conj u = cdm_ofInt (cdm_normSq u) := by
  apply CDDouble.ext
  · show u.re * conj u.re + -(conj (-u.im) * u.im)
       = ofInt (normSq u.re + normSq u.im)
    rw [base_conj_neg u.im, Ring213.neg_mul (conj u.im) u.im, Ring213.neg_neg,
        self_mul_conj u.re, conj_mul_self u.im, ofInt_add]
  · show (-u.im) * u.re + u.im * conj (conj u.re) = (0 : α)
    rw [StarRing213.conj_conj, Ring213.neg_mul u.im u.re, Ring213.add_left_neg]

/-- `ofInt` is multiplicative on `CDDouble α`. -/
theorem cd_ofInt_mul (a b : Int) :
    cdm_ofInt a * (cdm_ofInt b : CDDouble α) = cdm_ofInt (a * b) := by
  apply CDDouble.ext
  · show ofInt a * ofInt b + -(conj 0 * 0) = ofInt (a * b)
    rw [base_conj_zero, Ring213.zero_mul, base_neg_zero, Ring213.add_zero,
        ofInt_mul]
  · show (0 : α) * ofInt a + 0 * conj (ofInt b) = 0
    rw [Ring213.zero_mul, Ring213.zero_mul, Ring213.add_zero]

/-- `ofInt` is central on `CDDouble α`. -/
theorem cd_ofInt_central (z : Int) (w : CDDouble α) :
    cdm_ofInt z * w = w * cdm_ofInt z := by
  apply CDDouble.ext
  · show ofInt z * w.re + -(conj w.im * 0) = w.re * ofInt z + -(conj 0 * w.im)
    rw [Ring213.mul_zero, base_conj_zero, Ring213.zero_mul, ofInt_central z w.re]
  · show w.im * ofInt z + 0 * conj w.re = 0 * w.re + w.im * conj (ofInt z)
    rw [Ring213.zero_mul, Ring213.zero_mul, Ring213.add_zero, Ring213.zero_add,
        ofInt_conj]

/-- `ofInt` is injective on `CDDouble α`. -/
theorem cd_ofInt_inj {a b : Int}
    (h : (cdm_ofInt a : CDDouble α) = cdm_ofInt b) : a = b :=
  ofInt_inj (congrArg CDDouble.re h)

/-- **Hurwitz norm composition for `CDDouble α` over a non-commutative
    base.**  `|u·v|² = |u|²·|v|²`, derived directly from the polarization
    identity `hurwitz_norm_re` — no Moufang assumption (so the later
    `cd_moufang_norm` derivation is not circular). -/
theorem cd_normSq_mul (u v : CDDouble α) :
    cdm_normSq (u * v) = cdm_normSq u * cdm_normSq v := by
  apply @IntegerNormed213.ofInt_inj α _
  show ofInt (normSq (u * v).re + normSq (u * v).im)
     = ofInt (cdm_normSq u * cdm_normSq v)
  rw [← ofInt_add, ← self_mul_conj (u * v).re, ← conj_mul_self (u * v).im]
  show (u.re * v.re + -(conj v.im * u.im))
         * conj (u.re * v.re + -(conj v.im * u.im))
        + conj (v.im * u.re + u.im * conj v.re)
         * (v.im * u.re + u.im * conj v.re)
     = ofInt ((normSq u.re + normSq u.im) * (normSq v.re + normSq v.im))
  rw [StarRing213.conj_add (u.re * v.re) (-(conj v.im * u.im)),
      StarRing213.conj_mul u.re v.re,
      base_conj_neg (conj v.im * u.im),
      StarRing213.conj_mul (conj v.im) u.im,
      StarRing213.conj_conj v.im,
      StarRing213.conj_add (v.im * u.re) (u.im * conj v.re),
      StarRing213.conj_mul v.im u.re,
      StarRing213.conj_mul u.im (conj v.re),
      StarRing213.conj_conj v.re,
      hurwitz_norm_re u.re u.im v.re v.im,
      self_mul_conj u.re, conj_mul_self u.im,
      self_mul_conj v.re, conj_mul_self v.im,
      ofInt_add, ofInt_add, ofInt_mul]

end E213.Meta.Algebra213
