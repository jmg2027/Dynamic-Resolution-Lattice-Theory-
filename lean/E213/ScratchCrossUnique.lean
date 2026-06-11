import E213.Meta.Nat.PairOp

/-! Scratch verification for the interaction-law rung (open programme item 1).
    NOT for commit — compile check only. -/

namespace E213.Meta.Nat.PairOp

/-! ## Generic infrastructure (any f, priced) -/

/-- Pair-cancellation: the slotwise lift is cancellable on the right —
    `pairEq (u ⊕ w) (v ⊕ w) → pairEq u v` — bought with commutativity +
    associativity + cancellation. -/
theorem pairLift_cancel_right (f : Nat → Nat → Nat)
    (hcomm : ∀ x y, f x y = f y x)
    (hassoc : ∀ x y z, f (f x y) z = f x (f y z))
    (hcancel : ∀ a x y, f a x = f a y → x = y)
    {u v : Nat × Nat} (w : Nat × Nat)
    (h : pairEq f (pairLift f u w) (pairLift f v w)) :
    pairEq f u v := by
  have h0 : f (f u.1 w.1) (f v.2 w.2) = f (f v.1 w.1) (f u.2 w.2) := h
  have h1 : f (f w.1 w.2) (f u.1 v.2) = f (f w.1 w.2) (f v.1 u.2) := by
    calc f (f w.1 w.2) (f u.1 v.2)
        = f (f u.1 v.2) (f w.1 w.2) := hcomm _ _
      _ = f (f u.1 w.1) (f v.2 w.2) := exchange f hcomm hassoc u.1 v.2 w.1 w.2
      _ = f (f v.1 w.1) (f u.2 w.2) := h0
      _ = f (f v.1 u.2) (f w.1 w.2) := exchange f hcomm hassoc v.1 w.1 u.2 w.2
      _ = f (f w.1 w.2) (f v.1 u.2) := hcomm _ _
  exact hcancel _ _ _ h1

/-- Two-sided lift congruence — commutativity + associativity only. -/
theorem pairLift_congr (f : Nat → Nat → Nat)
    (hcomm : ∀ x y, f x y = f y x)
    (hassoc : ∀ x y z, f (f x y) z = f x (f y z))
    {p p' q q' : Nat × Nat}
    (hp : pairEq f p p') (hq : pairEq f q q') :
    pairEq f (pairLift f p q) (pairLift f p' q') := by
  show f (f p.1 q.1) (f p'.2 q'.2) = f (f p'.1 q'.1) (f p.2 q.2)
  calc f (f p.1 q.1) (f p'.2 q'.2)
      = f (f p.1 p'.2) (f q.1 q'.2) := exchange f hcomm hassoc _ _ _ _
    _ = f (f p'.1 p.2) (f q'.1 q.2) := by
        rw [show f p.1 p'.2 = f p'.1 p.2 from hp,
            show f q.1 q'.2 = f q'.1 q.2 from hq]
    _ = f (f p'.1 q'.1) (f p.2 q.2) := exchange f hcomm hassoc _ _ _ _

/-- Embedded pairs: `(f x t, t)` is the pair-layer copy of `x` (anchor
    `t` arbitrary).  ⊕-shifting any pair by the embedded copy of its
    second slot lands on the embedded copy of its first slot. -/
theorem oplus_embed (f : Nat → Nat → Nat)
    (hcomm : ∀ x y, f x y = f y x)
    (hassoc : ∀ x y z, f (f x y) z = f x (f y z))
    (p : Nat × Nat) (t s : Nat) :
    pairEq f (pairLift f p (f p.2 t, t)) (f p.1 s, s) := by
  show f (f p.1 (f p.2 t)) s = f (f p.1 s) (f p.2 t)
  calc f (f p.1 (f p.2 t)) s
      = f p.1 (f (f p.2 t) s) := hassoc _ _ _
    _ = f p.1 (f s (f p.2 t)) := by rw [hcomm (f p.2 t) s]
    _ = f (f p.1 s) (f p.2 t) := (hassoc _ _ _).symm

/-! ## + specialization helpers -/

private theorem addTrans {p q r : Nat × Nat}
    (h1 : pairEq Nat.add p q) (h2 : pairEq Nat.add q r) :
    pairEq Nat.add p r :=
  pairEq_trans Nat.add Nat.add_comm Nat.add_assoc
    (fun _ _ h => Nat.add_left_cancel h) h1 h2

private theorem addCongr {p p' q q' : Nat × Nat}
    (hp : pairEq Nat.add p p') (hq : pairEq Nat.add q q') :
    pairEq Nat.add (pairLift Nat.add p q) (pairLift Nat.add p' q') :=
  pairLift_congr Nat.add Nat.add_comm Nat.add_assoc hp hq

private theorem addCancel {u v : Nat × Nat} (w : Nat × Nat)
    (h : pairEq Nat.add (pairLift Nat.add u w) (pairLift Nat.add v w)) :
    pairEq Nat.add u v :=
  pairLift_cancel_right Nat.add Nat.add_comm Nat.add_assoc
    (fun _ _ _ h => Nat.add_left_cancel h) w h

private theorem zero_oplus (z : Nat × Nat) :
    pairLift Nat.add (0, 0) z = z := by
  show (0 + z.1, 0 + z.2) = z
  rw [Nat.zero_add, Nat.zero_add]

private theorem split_pair (a b : Nat) :
    (a, b) = pairLift Nat.add (a, 0) (0, b) := by
  show (a, b) = (a + 0, 0 + b)
  rw [Nat.add_zero, Nat.zero_add]

/-- `(0,d) ⊕ (d,0) ≈ (0,0)` — the inverse pairing on +-pairs. -/
private theorem diag_negpair (d : Nat) :
    pairEq Nat.add (pairLift Nat.add (0, d) (d, 0)) (0, 0) := by
  show (0 + d) + 0 = 0 + (d + 0)
  rw [Nat.zero_add, Nat.add_zero, Nat.zero_add]

/-- Inverse readout: `u ⊕ (m,0) ≈ (0,0)` pins `u ≈ (0,m)`. -/
private theorem eq_neg_of {u : Nat × Nat} {m : Nat}
    (h : pairEq Nat.add (pairLift Nat.add u (m, 0)) (0, 0)) :
    pairEq Nat.add u (0, m) := by
  have h' : (u.1 + m) + 0 = 0 + (u.2 + 0) := h
  show u.1 + m = 0 + u.2
  calc u.1 + m
      = (u.1 + m) + 0 := (Nat.add_zero _).symm
    _ = 0 + (u.2 + 0) := h'
    _ = 0 + u.2 := congrArg (fun t => 0 + t) (Nat.add_zero u.2)

/-- Inverse readout, mirrored: `u ⊕ (0,m) ≈ (0,0)` pins `u ≈ (m,0)`. -/
private theorem eq_pos_of {u : Nat × Nat} {m : Nat}
    (h : pairEq Nat.add (pairLift Nat.add u (0, m)) (0, 0)) :
    pairEq Nat.add u (m, 0) := by
  have h' : (u.1 + 0) + 0 = 0 + (u.2 + m) := h
  show u.1 + 0 = m + u.2
  calc u.1 + 0
      = (u.1 + 0) + 0 := (Nat.add_zero _).symm
    _ = 0 + (u.2 + m) := h'
    _ = u.2 + m := Nat.zero_add _
    _ = m + u.2 := Nat.add_comm _ _

/-! ## The M-chain -/

/-- Right annihilation `M p (0,0) ≈ (0,0)` — right distributivity +
    pair-cancellation alone (no congruence, no extension). -/
theorem M_zero_right (M : Nat × Nat → Nat × Nat → Nat × Nat)
    (distR : ∀ p q r, pairEq Nat.add (M p (pairLift Nat.add q r))
      (pairLift Nat.add (M p q) (M p r)))
    (p : Nat × Nat) :
    pairEq Nat.add (M p (0, 0)) (0, 0) := by
  have h : pairEq Nat.add (M p (0, 0))
      (pairLift Nat.add (M p (0, 0)) (M p (0, 0))) := distR p (0, 0) (0, 0)
  have h' : pairEq Nat.add (pairLift Nat.add (0, 0) (M p (0, 0)))
      (pairLift Nat.add (M p (0, 0)) (M p (0, 0))) := by
    rw [zero_oplus]; exact h
  exact pairEq_symm Nat.add (addCancel (M p (0, 0)) h')

/-- Left annihilation `M (0,0) q ≈ (0,0)` — left distributivity +
    pair-cancellation alone. -/
theorem M_zero_left (M : Nat × Nat → Nat × Nat → Nat × Nat)
    (distL : ∀ p q r, pairEq Nat.add (M (pairLift Nat.add p q) r)
      (pairLift Nat.add (M p r) (M q r)))
    (q : Nat × Nat) :
    pairEq Nat.add (M (0, 0) q) (0, 0) := by
  have h : pairEq Nat.add (M (0, 0) q)
      (pairLift Nat.add (M (0, 0) q) (M (0, 0) q)) := distL (0, 0) (0, 0) q
  have h' : pairEq Nat.add (pairLift Nat.add (0, 0) (M (0, 0) q))
      (pairLift Nat.add (M (0, 0) q) (M (0, 0) q)) := by
    rw [zero_oplus]; exact h
  exact pairEq_symm Nat.add (addCancel (M (0, 0) q) h')

/-- The inverse rung on the right: `M p (0,d) ⊕ M p (d,0) ≈ (0,0)` —
    right congruence + right distributivity. -/
theorem M_negpair_right (M : Nat × Nat → Nat × Nat → Nat × Nat)
    (congrR : ∀ (p : Nat × Nat) {q q' : Nat × Nat}, pairEq Nat.add q q' →
      pairEq Nat.add (M p q) (M p q'))
    (distR : ∀ p q r, pairEq Nat.add (M p (pairLift Nat.add q r))
      (pairLift Nat.add (M p q) (M p r)))
    (p : Nat × Nat) (d : Nat) :
    pairEq Nat.add (pairLift Nat.add (M p (0, d)) (M p (d, 0))) (0, 0) := by
  have h1 := distR p (0, d) (d, 0)
  have h2 : pairEq Nat.add (M p (pairLift Nat.add (0, d) (d, 0)))
      (M p (0, 0)) := congrR p (diag_negpair d)
  exact addTrans (addTrans (pairEq_symm Nat.add h1) h2) (M_zero_right M distR p)

/-- Mixed atom `M (a,0) (0,d) ≈ (0, a·d)` — the first sign rule. -/
theorem M_atom_pn (M : Nat × Nat → Nat × Nat → Nat × Nat)
    (congrR : ∀ (p : Nat × Nat) {q q' : Nat × Nat}, pairEq Nat.add q q' →
      pairEq Nat.add (M p q) (M p q'))
    (distR : ∀ p q r, pairEq Nat.add (M p (pairLift Nat.add q r))
      (pairLift Nat.add (M p q) (M p r)))
    (ext : ∀ x y : Nat, pairEq Nat.add (M (x, 0) (y, 0)) (x * y, 0))
    (a d : Nat) :
    pairEq Nat.add (M (a, 0) (0, d)) (0, a * d) := by
  have hneg := M_negpair_right M congrR distR (a, 0) d
  have hcg : pairEq Nat.add
      (pairLift Nat.add (M (a, 0) (0, d)) (a * d, 0))
      (pairLift Nat.add (M (a, 0) (0, d)) (M (a, 0) (d, 0))) :=
    addCongr (pairEq_refl Nat.add _) (pairEq_symm Nat.add (ext a d))
  exact eq_neg_of (addTrans hcg hneg)

/-- Mixed atom `M (0,b) (c,0) ≈ (0, b·c)` — left-side mirror. -/
theorem M_atom_np (M : Nat × Nat → Nat × Nat → Nat × Nat)
    (congrL : ∀ {p p' : Nat × Nat} (q : Nat × Nat), pairEq Nat.add p p' →
      pairEq Nat.add (M p q) (M p' q))
    (distL : ∀ p q r, pairEq Nat.add (M (pairLift Nat.add p q) r)
      (pairLift Nat.add (M p r) (M q r)))
    (ext : ∀ x y : Nat, pairEq Nat.add (M (x, 0) (y, 0)) (x * y, 0))
    (b c : Nat) :
    pairEq Nat.add (M (0, b) (c, 0)) (0, b * c) := by
  have h1 := distL (0, b) (b, 0) (c, 0)
  have h2 : pairEq Nat.add (M (pairLift Nat.add (0, b) (b, 0)) (c, 0))
      (M (0, 0) (c, 0)) := congrL (c, 0) (diag_negpair b)
  have hsum : pairEq Nat.add
      (pairLift Nat.add (M (0, b) (c, 0)) (M (b, 0) (c, 0))) (0, 0) :=
    addTrans (addTrans (pairEq_symm Nat.add h1) h2) (M_zero_left M distL (c, 0))
  have hcg : pairEq Nat.add
      (pairLift Nat.add (M (0, b) (c, 0)) (b * c, 0))
      (pairLift Nat.add (M (0, b) (c, 0)) (M (b, 0) (c, 0))) :=
    addCongr (pairEq_refl Nat.add _) (pairEq_symm Nat.add (ext b c))
  exact eq_neg_of (addTrans hcg hsum)

/-- Sign atom `M (0,b) (0,d) ≈ (b·d, 0)` — the (−1)(−1) = 1 rung. -/
theorem M_atom_nn (M : Nat × Nat → Nat × Nat → Nat × Nat)
    (congrL : ∀ {p p' : Nat × Nat} (q : Nat × Nat), pairEq Nat.add p p' →
      pairEq Nat.add (M p q) (M p' q))
    (congrR : ∀ (p : Nat × Nat) {q q' : Nat × Nat}, pairEq Nat.add q q' →
      pairEq Nat.add (M p q) (M p q'))
    (distL : ∀ p q r, pairEq Nat.add (M (pairLift Nat.add p q) r)
      (pairLift Nat.add (M p r) (M q r)))
    (distR : ∀ p q r, pairEq Nat.add (M p (pairLift Nat.add q r))
      (pairLift Nat.add (M p q) (M p r)))
    (ext : ∀ x y : Nat, pairEq Nat.add (M (x, 0) (y, 0)) (x * y, 0))
    (b d : Nat) :
    pairEq Nat.add (M (0, b) (0, d)) (b * d, 0) := by
  have hneg := M_negpair_right M congrR distR (0, b) d
  have hnp := M_atom_np M congrL distL ext b d
  have hcg : pairEq Nat.add
      (pairLift Nat.add (M (0, b) (0, d)) (0, b * d))
      (pairLift Nat.add (M (0, b) (0, d)) (M (0, b) (d, 0))) :=
    addCongr (pairEq_refl Nat.add _) (pairEq_symm Nat.add hnp)
  exact eq_pos_of (addTrans hcg hneg)

/-- ★★★★ **The interaction-law rung**: the cross rule
    `(a,b) ⊗ (c,d) ≈ (a·c + b·d, a·d + b·c)` is the unique
    relation-respecting, ⊕-bidistributive extension of × to +-pairs. -/
theorem cross_lift_unique (M : Nat × Nat → Nat × Nat → Nat × Nat)
    (congrL : ∀ {p p' : Nat × Nat} (q : Nat × Nat), pairEq Nat.add p p' →
      pairEq Nat.add (M p q) (M p' q))
    (congrR : ∀ (p : Nat × Nat) {q q' : Nat × Nat}, pairEq Nat.add q q' →
      pairEq Nat.add (M p q) (M p q'))
    (distL : ∀ p q r, pairEq Nat.add (M (pairLift Nat.add p q) r)
      (pairLift Nat.add (M p r) (M q r)))
    (distR : ∀ p q r, pairEq Nat.add (M p (pairLift Nat.add q r))
      (pairLift Nat.add (M p q) (M p r)))
    (ext : ∀ x y : Nat, pairEq Nat.add (M (x, 0) (y, 0)) (x * y, 0))
    (a b c d : Nat) :
    pairEq Nat.add (M (a, b) (c, d)) (a * c + b * d, a * d + b * c) := by
  rw [split_pair a b, split_pair c d]
  have h1 := distL (a, 0) (0, b) (pairLift Nat.add (c, 0) (0, d))
  have h2 := distR (a, 0) (c, 0) (0, d)
  have h3 := distR (0, b) (c, 0) (0, d)
  have h4 := addCongr h2 h3
  have h5 := addCongr (addCongr (ext a c) (M_atom_pn M congrR distR ext a d))
    (addCongr (M_atom_np M congrL distL ext b c) (M_atom_nn M congrL congrR distL distR ext b d))
  have h6 : pairLift Nat.add (pairLift Nat.add (a * c, 0) (0, a * d))
      (pairLift Nat.add (0, b * c) (b * d, 0))
      = (a * c + b * d, a * d + b * c) := by
    show ((a * c + 0) + (0 + b * d), (0 + a * d) + (b * c + 0))
       = (a * c + b * d, a * d + b * c)
    rw [Nat.add_zero (a * c), Nat.zero_add (b * d),
        Nat.zero_add (a * d), Nat.add_zero (b * c)]
  rw [← h6]
  exact addTrans h1 (addTrans h4 h5)

/-- Optional weakening: the full extension hypothesis is generated by the
    unit extension `M (1,0)(1,0) ≈ (1,0)` plus the two distributivities. -/
theorem ext_of_unit (M : Nat × Nat → Nat × Nat → Nat × Nat)
    (distL : ∀ p q r, pairEq Nat.add (M (pairLift Nat.add p q) r)
      (pairLift Nat.add (M p r) (M q r)))
    (distR : ∀ p q r, pairEq Nat.add (M p (pairLift Nat.add q r))
      (pairLift Nat.add (M p q) (M p r)))
    (unit : pairEq Nat.add (M (1, 0) (1, 0)) (1, 0)) :
    ∀ x y : Nat, pairEq Nat.add (M (x, 0) (y, 0)) (x * y, 0) := by
  have hrow : ∀ y : Nat, pairEq Nat.add (M (1, 0) (y, 0)) (y, 0) := by
    intro y
    induction y with
    | zero => exact M_zero_right M distR (1, 0)
    | succ n ih =>
      have hstep := distR (1, 0) (n, 0) (1, 0)
      have hcg : pairEq Nat.add
          (pairLift Nat.add (M (1, 0) (n, 0)) (M (1, 0) (1, 0)))
          (pairLift Nat.add (n, 0) (1, 0)) := addCongr ih unit
      exact addTrans hstep hcg
  intro x y
  induction x with
  | zero =>
    rw [Nat.zero_mul]
    exact M_zero_left M distL (y, 0)
  | succ n ih =>
    have hstep := distL (n, 0) (1, 0) (y, 0)
    have hcg : pairEq Nat.add
        (pairLift Nat.add (M (n, 0) (y, 0)) (M (1, 0) (y, 0)))
        (pairLift Nat.add (n * y, 0) (y, 0)) := addCongr ih (hrow y)
    rw [Nat.succ_mul]
    exact addTrans hstep hcg

/-! ## Generic uniqueness (deliverable 3) -/

/-- ★★★★ **Generic lift uniqueness**: over any commutative, associative,
    cancellative `f`, two congruent, ⊕-bidistributive binary operations on
    `f`-pairs that agree on embedded pairs agree everywhere.  No inverse
    trick: `oplus_embed` (every pair is embedded after one embedded shift)
    + pair-cancellation replace `(0,d) ⊕ (d,0) ≈ (0,0)`. -/
theorem lift_unique (f : Nat → Nat → Nat)
    (hcomm : ∀ x y, f x y = f y x)
    (hassoc : ∀ x y z, f (f x y) z = f x (f y z))
    (hcancel : ∀ a x y, f a x = f a y → x = y)
    (M M' : Nat × Nat → Nat × Nat → Nat × Nat)
    (congrL : ∀ {p p' : Nat × Nat} (q : Nat × Nat),
      pairEq f p p' → pairEq f (M p q) (M p' q))
    (congrR : ∀ (p : Nat × Nat) {q q' : Nat × Nat},
      pairEq f q q' → pairEq f (M p q) (M p q'))
    (congrL' : ∀ {p p' : Nat × Nat} (q : Nat × Nat),
      pairEq f p p' → pairEq f (M' p q) (M' p' q))
    (congrR' : ∀ (p : Nat × Nat) {q q' : Nat × Nat},
      pairEq f q q' → pairEq f (M' p q) (M' p q'))
    (distL : ∀ p q r, pairEq f (M (pairLift f p q) r)
      (pairLift f (M p r) (M q r)))
    (distR : ∀ p q r, pairEq f (M p (pairLift f q r))
      (pairLift f (M p q) (M p r)))
    (distL' : ∀ p q r, pairEq f (M' (pairLift f p q) r)
      (pairLift f (M' p r) (M' q r)))
    (distR' : ∀ p q r, pairEq f (M' p (pairLift f q r))
      (pairLift f (M' p q) (M' p r)))
    (base : ∀ x t y s, pairEq f (M (f x t, t) (f y s, s))
      (M' (f x t, t) (f y s, s)))
    (p q : Nat × Nat) : pairEq f (M p q) (M' p q) := by
  have ftr : ∀ {u v w : Nat × Nat},
      pairEq f u v → pairEq f v w → pairEq f u w :=
    fun h1 h2 => pairEq_trans f hcomm hassoc (fun x y h => hcancel _ x y h) h1 h2
  have fcancel : ∀ {u v : Nat × Nat} (w : Nat × Nat),
      pairEq f (pairLift f u w) (pairLift f v w) → pairEq f u v :=
    fun w h => pairLift_cancel_right f hcomm hassoc hcancel w h
  have claimA : ∀ (p₀ : Nat × Nat) (y s : Nat),
      pairEq f (M p₀ (f y s, s)) (M' p₀ (f y s, s)) := by
    intro p₀ y s
    have hshift : pairEq f (pairLift f p₀ (f p₀.2 p₀.2, p₀.2))
        (f p₀.1 p₀.1, p₀.1) := oplus_embed f hcomm hassoc p₀ p₀.2 p₀.1
    have h1 : pairEq f (M (f p₀.1 p₀.1, p₀.1) (f y s, s))
        (M (pairLift f p₀ (f p₀.2 p₀.2, p₀.2)) (f y s, s)) :=
      congrL _ (pairEq_symm f hshift)
    have h2 := distL p₀ (f p₀.2 p₀.2, p₀.2) (f y s, s)
    have h1' : pairEq f (M' (f p₀.1 p₀.1, p₀.1) (f y s, s))
        (M' (pairLift f p₀ (f p₀.2 p₀.2, p₀.2)) (f y s, s)) :=
      congrL' _ (pairEq_symm f hshift)
    have h2' := distL' p₀ (f p₀.2 p₀.2, p₀.2) (f y s, s)
    have hbA := base p₀.1 p₀.1 y s
    have hbB := base p₀.2 p₀.2 y s
    apply fcancel (M (f p₀.2 p₀.2, p₀.2) (f y s, s))
    have c1 : pairEq f
        (pairLift f (M p₀ (f y s, s)) (M (f p₀.2 p₀.2, p₀.2) (f y s, s)))
        (M' (f p₀.1 p₀.1, p₀.1) (f y s, s)) :=
      ftr (ftr (pairEq_symm f h2) (pairEq_symm f h1)) hbA
    have c2 : pairEq f (M' (f p₀.1 p₀.1, p₀.1) (f y s, s))
        (pairLift f (M' p₀ (f y s, s)) (M' (f p₀.2 p₀.2, p₀.2) (f y s, s))) :=
      ftr h1' h2'
    have c3 : pairEq f
        (pairLift f (M' p₀ (f y s, s)) (M' (f p₀.2 p₀.2, p₀.2) (f y s, s)))
        (pairLift f (M' p₀ (f y s, s)) (M (f p₀.2 p₀.2, p₀.2) (f y s, s))) :=
      pairLift_congr f hcomm hassoc (pairEq_refl f _) (pairEq_symm f hbB)
    exact ftr (ftr c1 c2) c3
  have hshift : pairEq f (pairLift f q (f q.2 q.2, q.2)) (f q.1 q.1, q.1) :=
    oplus_embed f hcomm hassoc q q.2 q.1
  have h1 : pairEq f (M p (f q.1 q.1, q.1))
      (M p (pairLift f q (f q.2 q.2, q.2))) := congrR p (pairEq_symm f hshift)
  have h2 := distR p q (f q.2 q.2, q.2)
  have h1' : pairEq f (M' p (f q.1 q.1, q.1))
      (M' p (pairLift f q (f q.2 q.2, q.2))) := congrR' p (pairEq_symm f hshift)
  have h2' := distR' p q (f q.2 q.2, q.2)
  have hAc := claimA p q.1 q.1
  have hAd := claimA p q.2 q.2
  apply fcancel (M p (f q.2 q.2, q.2))
  have c1 : pairEq f (pairLift f (M p q) (M p (f q.2 q.2, q.2)))
      (M p (f q.1 q.1, q.1)) :=
    ftr (pairEq_symm f h2) (pairEq_symm f h1)
  have c2 : pairEq f (M p (f q.1 q.1, q.1))
      (pairLift f (M' p q) (M' p (f q.2 q.2, q.2))) :=
    ftr hAc (ftr h1' h2')
  have c3 : pairEq f (pairLift f (M' p q) (M' p (f q.2 q.2, q.2)))
      (pairLift f (M' p q) (M p (f q.2 q.2, q.2))) :=
    pairLift_congr f hcomm hassoc (pairEq_refl f _) (pairEq_symm f hAd)
  exact ftr (ftr c1 c2) c3

/-! ## Counterexamples (minimality of the hypothesis set) -/

namespace CE

/-- Drop right congruence: `M p q = (p.1·q.1, p.2·q.1)` keeps left
    congruence, the extension, and BOTH distributivities (exactly). -/
def Mr (p q : Nat × Nat) : Nat × Nat := (p.1 * q.1, p.2 * q.1)

theorem Mr_congrL {p p' : Nat × Nat} (q : Nat × Nat)
    (h : pairEq Nat.add p p') : pairEq Nat.add (Mr p q) (Mr p' q) := by
  show p.1 * q.1 + p'.2 * q.1 = p'.1 * q.1 + p.2 * q.1
  rw [← Nat.add_mul, ← Nat.add_mul, show p.1 + p'.2 = p'.1 + p.2 from h]

theorem Mr_ext (x y : Nat) :
    pairEq Nat.add (Mr (x, 0) (y, 0)) (x * y, 0) := by
  show x * y + 0 = x * y + 0 * y
  rw [Nat.zero_mul]

theorem Mr_distL (p q r : Nat × Nat) :
    pairEq Nat.add (Mr (pairLift Nat.add p q) r)
      (pairLift Nat.add (Mr p r) (Mr q r)) := by
  show (p.1 + q.1) * r.1 + (p.2 * r.1 + q.2 * r.1)
     = (p.1 * r.1 + q.1 * r.1) + (p.2 + q.2) * r.1
  rw [Nat.add_mul, Nat.add_mul]

theorem Mr_distR (p q r : Nat × Nat) :
    pairEq Nat.add (Mr p (pairLift Nat.add q r))
      (pairLift Nat.add (Mr p q) (Mr p r)) := by
  show p.1 * (q.1 + r.1) + (p.2 * q.1 + p.2 * r.1)
     = (p.1 * q.1 + p.1 * r.1) + p.2 * (q.1 + r.1)
  rw [Nat.mul_add, Nat.mul_add]

theorem Mr_conclusion_fails :
    ¬ pairEq Nat.add (Mr (1, 0) (0, 1)) (1 * 0 + 0 * 1, 1 * 1 + 0 * 0) := by
  intro h
  have h' : (0 : Nat) + 1 = 0 + 0 := h
  rw [Nat.zero_add, Nat.zero_add] at h'
  exact Nat.noConfusion h'

theorem Mr_congrR_fails :
    ¬ (∀ (p : Nat × Nat) {q q' : Nat × Nat}, pairEq Nat.add q q' →
      pairEq Nat.add (Mr p q) (Mr p q')) := by
  intro hc
  have hdiag : pairEq Nat.add ((1, 1) : Nat × Nat) (0, 0) := by
    show 1 + 0 = 0 + 1
    rw [Nat.zero_add]
  have h := hc (1, 0) hdiag
  have h' : (1 : Nat) + 0 = 0 + 0 := h
  rw [Nat.add_zero, Nat.zero_add] at h'
  exact Nat.noConfusion h'

/-- Drop left distributivity: `M p q = (|p| · q.1, |p| · q.2)` with
    `|p| = natAbs (subNatNat p.1 p.2)` keeps both congruences, the
    extension, and right distributivity. -/
def Ml (p q : Nat × Nat) : Nat × Nat :=
  ((Int.subNatNat p.1 p.2).natAbs * q.1, (Int.subNatNat p.1 p.2).natAbs * q.2)

theorem Ml_congrL {p p' : Nat × Nat} (q : Nat × Nat)
    (h : pairEq Nat.add p p') : pairEq Nat.add (Ml p q) (Ml p' q) := by
  have hs : Int.subNatNat p.1 p.2 = Int.subNatNat p'.1 p'.2 :=
    (E213.Meta.Int213.subNatNat_eq_iff p.1 p.2 p'.1 p'.2).mpr h
  show (Int.subNatNat p.1 p.2).natAbs * q.1 + (Int.subNatNat p'.1 p'.2).natAbs * q.2
     = (Int.subNatNat p'.1 p'.2).natAbs * q.1 + (Int.subNatNat p.1 p.2).natAbs * q.2
  rw [hs]

theorem Ml_congrR (p : Nat × Nat) {q q' : Nat × Nat}
    (h : pairEq Nat.add q q') : pairEq Nat.add (Ml p q) (Ml p q') := by
  show (Int.subNatNat p.1 p.2).natAbs * q.1 + (Int.subNatNat p.1 p.2).natAbs * q'.2
     = (Int.subNatNat p.1 p.2).natAbs * q'.1 + (Int.subNatNat p.1 p.2).natAbs * q.2
  rw [← Nat.mul_add, ← Nat.mul_add, show q.1 + q'.2 = q'.1 + q.2 from h]

theorem Ml_ext (x y : Nat) :
    pairEq Nat.add (Ml (x, 0) (y, 0)) (x * y, 0) := by
  show (Int.subNatNat x 0).natAbs * y + 0 = x * y + (Int.subNatNat x 0).natAbs * 0
  rw [Int.subNatNat, Nat.zero_sub]
  show (Int.ofNat (x - 0)).natAbs * y + 0 = x * y + (Int.ofNat (x - 0)).natAbs * 0
  rw [Nat.sub_zero]
  show x * y + 0 = x * y + x * 0
  rw [Nat.mul_zero]

theorem Ml_distR (p q r : Nat × Nat) :
    pairEq Nat.add (Ml p (pairLift Nat.add q r))
      (pairLift Nat.add (Ml p q) (Ml p r)) := by
  show (Int.subNatNat p.1 p.2).natAbs * (q.1 + r.1)
        + ((Int.subNatNat p.1 p.2).natAbs * q.2 + (Int.subNatNat p.1 p.2).natAbs * r.2)
     = ((Int.subNatNat p.1 p.2).natAbs * q.1 + (Int.subNatNat p.1 p.2).natAbs * r.1)
        + (Int.subNatNat p.1 p.2).natAbs * (q.2 + r.2)
  rw [Nat.mul_add, Nat.mul_add]

theorem Ml_conclusion_fails :
    ¬ pairEq Nat.add (Ml (0, 1) (1, 0)) (0 * 1 + 1 * 0, 0 * 0 + 1 * 1) := by
  intro h
  have h' : (1 : Nat) * 1 + (0 * 0 + 1 * 1) = (0 * 1 + 1 * 0) + 1 * 0 := h
  rw [Nat.one_mul, Nat.one_mul, Nat.zero_mul, Nat.zero_mul,
      Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.add_zero] at h'
  exact Nat.noConfusion h'

theorem Ml_distL_fails :
    ¬ (∀ p q r, pairEq Nat.add (Ml (pairLift Nat.add p q) r)
      (pairLift Nat.add (Ml p r) (Ml q r))) := by
  intro hd
  have h := hd (1, 0) (0, 1) (1, 0)
  -- Ml ((1,1)) (1,0) = (0,0); Ml (1,0)(1,0) ⊕ Ml (0,1)(1,0) = (2,0)
  have h' : (Int.subNatNat 1 1).natAbs * 1 +
      ((Int.subNatNat 1 0).natAbs * 0 + (Int.subNatNat 0 1).natAbs * 0)
      = ((Int.subNatNat 1 0).natAbs * 1 + (Int.subNatNat 0 1).natAbs * 1)
        + (Int.subNatNat 1 1).natAbs * 0 := h
  have e1 : Int.subNatNat 1 1 = Int.ofNat 0 := rfl
  have e2 : Int.subNatNat 1 0 = Int.ofNat 1 := rfl
  have e3 : Int.subNatNat 0 1 = Int.negSucc 0 := rfl
  rw [e1, e2, e3] at h'
  have h'' : (0 : Nat) = 2 := by
    have := h'
    rw [Nat.zero_mul, Nat.mul_zero, Nat.mul_zero, Nat.zero_add,
        Nat.add_zero, Nat.one_mul, Nat.one_mul, Nat.mul_zero, Nat.add_zero] at this
    exact this
  exact Nat.noConfusion h''

end CE

end E213.Meta.Nat.PairOp

#print axioms E213.Meta.Nat.PairOp.cross_lift_unique
#print axioms E213.Meta.Nat.PairOp.lift_unique
#print axioms E213.Meta.Nat.PairOp.ext_of_unit
#print axioms E213.Meta.Nat.PairOp.pairLift_cancel_right
