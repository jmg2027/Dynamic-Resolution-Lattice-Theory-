# _pure-named decls (76 total) — Phase E++ explicit PURE parallels

## File: E213/Math/Cauchy/EulerCombinatorialPure.lean  (2 decls)

### \`euler_upper_pure\` (kind: theorem)
```lean
theorem euler_upper_pure (n : Nat) : 3 * eulerDen n ≥ eulerNum n + 1 := by
  induction n with
  | zero => decide
  | succ k ih =>
      match k with
      | 0 => decide  -- n = 1
      | k_pred + 1 =>
          -- k = k_pred + 1 ≥ 1, so (k+1) = k_pred + 2 ≥ 2.
          show 3 * eulerDen (k_pred + 1 + 1) ≥ eulerNum (k_pred + 1 + 1) + 1
          show 3 * ((k_pred + 1 + 1) * eulerDen (k_pred + 1)) ≥
               (k_pred + 1 + 1) * eulerNum (k_pred + 1) + 1 + 1
          have h_assoc : 3 * ((k_p
... [trunc]
```

### \`euler_lower_pure\` (kind: theorem)
```lean
theorem euler_lower_pure (n : Nat) (hn : n ≥ 2) :
    eulerNum n ≥ 2 * eulerDen n + 1 := by
  induction n with
  | zero =>
      exfalso; exact Nat.not_succ_le_zero 1 hn
  | succ k ih =>
      match k with
      | 0 =>
          exfalso
          have : 1 ≤ 0 := Nat.le_of_succ_le_succ hn
          exact Nat.not_succ_le_zero 0 this
      | 1 =>
          decide
      | k_pred + 2 =>
          have hk2 : k_pred + 2 ≥ 2 :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
          ha
... [trunc]
```

## File: E213/Math/Cauchy/EulerSharperPure.lean  (2 decls)

### \`euler_sharper_8_3_pure\` (kind: theorem)
```lean
theorem euler_sharper_8_3_pure (n : Nat) (hn : n ≥ 4) :
    3 * eulerNum n ≥ 8 * eulerDen n + 1 := by
  induction n with
  | zero => exact absurd hn (by decide)
  | succ k ih =>
      match k with
      | 0 => exact absurd hn (by decide)
      | 1 => exact absurd hn (by decide)
      | 2 => exact absurd hn (by decide)
      | 3 => decide  -- n = 4
      | k_pred + 4 =>
          have hk4 : k_pred + 4 ≥ 4 := Nat.le_add_left 4 k_pred
          have h_inv := ih hk4
          show 3 * ((k_pred + 4 +
... [trunc]
```

### \`eulerDen_pos_pure\` (kind: theorem)
```lean
theorem eulerDen_pos_pure (N : Nat) : eulerDen N ≥ 1 := by
  induction N with
  | zero => exact Nat.le_refl 1
  | succ k ih =>
      show eulerDen (k + 1) ≥ 1
      show (k + 1) * eulerDen k ≥ 1
      have h_kp : k + 1 ≥ 1 := Nat.succ_le_succ (Nat.zero_le k)
      have h_mul : (k + 1) * eulerDen k ≥ (k + 1) * 1 :=
        Nat.mul_le_mul_left (k+1) ih
      rw [Nat.mul_one] at h_mul
      exact Nat.le_trans h_kp h_mul

/-- **e ≠ a/3 (partial sum form, axiom-free)**: for every N ≥ 4
    and positi
... [trunc]
```

## File: E213/Math/Cohomology/HodgeConjecture/Bridge/G7Vacuity.lean  (1 decls)

### \`g7_phase_1_pure_capstone\` (kind: theorem)
```lean
theorem g7_phase_1_pure_capstone :
    witness_213 = 3
    ∧ isExoticPattern witness_213 = true
    ∧ witness_213 < 32
    ∧ (∃ n : Nat, isExoticPattern n = true ∧ n < 32) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · decide
  · decide
  · exact ⟨3, by decide, by decide⟩
```

## File: E213/Math/Cohomology/HodgeConjecture/Bridge/G9ReductioVoid.lean  (1 decls)

### \`g9_capstone_pure\` (kind: theorem)
```lean
theorem g9_capstone_pure :
    P_demo 3 = true
    ∧ (∃ n : Nat, P_demo n = true)
    ∧ (3 : Nat) = 3
    ∧ ¬((3 : Nat) < 3) := by
  refine ⟨rfl, ⟨3, rfl⟩, rfl, ?_⟩
  decide
```

## File: E213/Math/Real213/ClassicCalc.lean  (3 decls)

### \`mvt_pure\` (kind: theorem)
```lean
theorem mvt_pure {f} (cc : ClassicCalc_at f) :
    fluxCutEq (localDivergence f unitBracket) (ofCut (constCut 1 1)) :=
  Passthrough_at.mvt_pure cc.pass

/-- Extract FTC bridge (one-liner, fluxCutEq, PURE). -/
```

### \`ftc_pure\` (kind: theorem)
```lean
theorem ftc_pure {f} (cc : ClassicCalc_at f) :
    fluxCutEq (localDivergence f unitBracket) (fluxAlong f unitBracket) :=
  Passthrough_at.ftc_pure cc.pass

/-- ★ Phase BL capstone (PURE): ClassicCalc_at gives MVT + FTC at unit. -/
```

## File: E213/Math/Real213/ClassicCalcCombinators.lean  (1 decls)

### \`combinators_capstone_pure\` (kind: theorem)
```lean
theorem combinators_capstone_pure :
    fluxCutEq (localDivergence (fun x => cutMul x (cutMul x x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  x_mul_square_calc.mvt_pure
```

## File: E213/Math/Real213/ClassicCalcExtreme.lean  (1 decls)

### \`extreme_capstone_pure\` (kind: theorem)
```lean
theorem extreme_capstone_pure :
    fluxCutEq (localDivergence (fun x =>
        cutMul (cutMul (cutMul x x) (cutMul x x))
               (cutMul (cutMul x x) (cutMul x (cutMul x x))))
        unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x =>
        cutMul (cutMul (cutMul x x) (cutMul x (cutMul x x)))
               (cutMul (cutMul x x) (cutMul x (cutMul x x))))
        unitBracket) (ofCut (constCut 1 1)) :=
  ⟨nonic_calc.mvt_pure, decic_calc.mvt_pure⟩
```

## File: E213/Math/Real213/ClassicCalcGeneric.lean  (3 decls)

### \`cutPow_calc_mvt_pure\` (kind: theorem)
```lean
theorem cutPow_calc_mvt_pure (n : Nat) :
    E213.Math.Real213.FluxMVT.FluxCut.fluxCutEq
      (localDivergence (fun x => cutPow x (n+1)) unitBracket)
      (ofCut (constCut 1 1)) :=
  (cutPow_calc_at n).mvt_pure

/-- ★ Generic FTC bridge for x^(n+1) (fluxCutEq, PURE). -/
```

### \`cutPow_calc_ftc_pure\` (kind: theorem)
```lean
theorem cutPow_calc_ftc_pure (n : Nat) :
    E213.Math.Real213.FluxMVT.FluxCut.fluxCutEq
      (localDivergence (fun x => cutPow x (n+1)) unitBracket)
      (fluxAlong (fun x => cutPow x (n+1)) unitBracket) :=
  (cutPow_calc_at n).ftc_pure

/-- Phase BP capstone (PURE): cutPow_calc gives MVT + FTC for any n
    (fluxCutEq + pointwise endpoints). -/
```

## File: E213/Math/Real213/ClassicCalcHigher.lean  (1 decls)

### \`classic_calc_higher_capstone_pure\` (kind: theorem)
```lean
theorem classic_calc_higher_capstone_pure :
    fluxCutEq (localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
                               unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence
        (fun x => cutMul (cutMul x x) (cutMul x (cutMul x x)))
        unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence
        (fun x => cutMul (cutMul x (cutMul x x))
                         (cutMul x (cutMul x x))) unitBracket)
        (ofCut (constCut 1 1)
... [trunc]
```

## File: E213/Math/Real213/ClassicCalcMid.lean  (3 decls)

### \`mid_id_square_mvt_pure\` (kind: theorem)
```lean
theorem mid_id_square_mvt_pure :
    fluxCutEq (localDivergence (fun x => cutMid x (cutMul x x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  mid_id_square_calc.mvt_pure

/-- mid(x², x³) MVT (fluxCutEq, PURE). -/
```

### \`mid_square_cube_mvt_pure\` (kind: theorem)
```lean
theorem mid_square_cube_mvt_pure :
    fluxCutEq (localDivergence (fun x => cutMid (cutMul x x)
                                          (cutMul x (cutMul x x)))
                              unitBracket)
              (ofCut (constCut 1 1)) :=
  mid_square_cube_calc.mvt_pure

/-- Phase BS capstone (fluxCutEq, PURE). -/
```

## File: E213/Math/Real213/FTCRiemannMid.lean  (1 decls)

### \`ftc_riemann_mid_capstone_pure\` (kind: theorem)
```lean
theorem ftc_riemann_mid_capstone_pure :
    ∀ m k, riemannSampleSum (midIsDifferentiable idIsDifferentiable
                              squareIsDifferentiable).derivative
             unitBracket 0 m k = constCut 1 1 m k :=
  riemann_mid_id_square_derivative_zero_at
```

## File: E213/Math/Real213/FTCRiemannSquare.lean  (1 decls)

### \`ftc_riemann_square_capstone_pure\` (kind: theorem)
```lean
theorem ftc_riemann_square_capstone_pure :
    (∀ m k, riemannSampleSum squareIsDifferentiable.derivative unitBracket 0
              m k = constCut 1 1 m k)
    ∧ (∀ m k, riemannSampleSum squareIsDifferentiable.derivative unitBracket 0
                m k
              = (fluxAlong (fun x => cutMul x x) unitBracket).forward m k)
    ∧ fluxCutEq (fluxAlong (fun x => cutMul x x) unitBracket)
                (ofCut (constCut 1 1)) :=
  ⟨riemann_square_derivative_unit_zero_at,
   ftc_riemann_square
... [trunc]
```

## File: E213/Math/Real213/FluxFTC.lean  (2 decls)

### \`ftc_bridge_id_unitBracket_pure\` (kind: theorem)
```lean
theorem ftc_bridge_id_unitBracket_pure :
    fluxCutEq (localDivergence id unitBracket) (fluxAlong id unitBracket) :=
  E213.Math.Real213.FluxMVT.FluxCut.fluxBalance_trans
    mvt_id_unitBracket_pure
    (E213.Math.Real213.FluxMVT.FluxCut.fluxBalance_symm _ _
      (fluxCutEq_of_pointwise (fun _ _ => rfl) (fun _ _ => rfl)))

/-- ★ Phase AZ-1 capstone (fluxCutEq, PURE). -/
```

### \`ftc_concrete_capstone_pure\` (kind: theorem)
```lean
theorem ftc_concrete_capstone_pure (c : Nat → Nat → Bool)
    (db : DyadicBracket) :
    fluxCutEq (fluxAlong id unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence id unitBracket) (fluxAlong id unitBracket)
    ∧ isBalanced (fluxAlong (constCutFn c) db)
    ∧ isBalanced (localDivergence (constCutFn c) db) :=
  ⟨fluxCutEq_of_pointwise (fun _ _ => rfl) (fun _ _ => rfl),
   ftc_bridge_id_unitBracket_pure,
   fluxAlong_const_isBalanced c db, localDivergence_const_balanced c db⟩
```

## File: E213/Math/Real213/FluxFTCPolynomial.lean  (5 decls)

### \`fluxAlong_square_unitBracket_pure\` (kind: theorem)
```lean
theorem fluxAlong_square_unitBracket_pure :
    fluxCutEq (fluxAlong (fun x => cutMul x x) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    fluxAlong_square_unitBracket_forward_at
    fluxAlong_square_unitBracket_backward_at

/-- fluxAlong x³ at unit (fluxCutEq, PURE). -/
```

### \`fluxAlong_cube_unitBracket_pure\` (kind: theorem)
```lean
theorem fluxAlong_cube_unitBracket_pure :
    fluxCutEq (fluxAlong (fun x => cutMul x (cutMul x x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    fluxAlong_cube_unitBracket_forward_at
    fluxAlong_cube_unitBracket_backward_at

/-- ★ FTC bridge for x² at unit (fluxCutEq, PURE).  Chains
    `mvt_square_pure` with `fluxAlong_square_pure` via fluxBalance_trans. -/
```

## File: E213/Math/Real213/FluxMVTApplications.lean  (5 decls)

### \`mvt_id_via_passthrough_pure\` (kind: theorem)
```lean
theorem mvt_id_via_passthrough_pure :
    fluxCutEq (localDivergence id unitBracket) (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure id (fun _ _ => rfl) (fun _ _ => rfl)

/-- ★ x^(n+1) MVT via passthrough (fluxCutEq, PURE). -/
```

### \`mvt_cutPow_via_passthrough_pure\` (kind: theorem)
```lean
theorem mvt_cutPow_via_passthrough_pure (n : Nat) :
    fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
              (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure (fun x => cutPow x (n+1))
    (cutPow_zero_succ_at n) (cutPow_one_n_at (n+1))

/-- x² MVT via passthrough (fluxCutEq, PURE). -/
```

## File: E213/Math/Real213/FluxMVTClosure.lean  (1 decls)

### \`mvt_mul_passthrough_pure\` (kind: theorem)
```lean
theorem mvt_mul_passthrough_pure
    (f g : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (hf_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (hf_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k)
    (hg_left : ∀ m k, g (constCut 0 1) m k = constCut 0 1 m k)
    (hg_right : ∀ m k, g (constCut 1 1) m k = constCut 1 1 m k) :
    fluxCutEq (localDivergence (fun x => cutMul (f x) (g x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure (fun x => cutMul 
... [trunc]
```

## File: E213/Math/Real213/FluxMVTConcrete.lean  (2 decls)

### \`mvt_id_unitBracket_pure\` (kind: theorem)
```lean
theorem mvt_id_unitBracket_pure :
    E213.Math.Real213.FluxMVT.FluxCut.fluxCutEq
      (localDivergence id unitBracket) (ofCut (constCut 1 1)) :=
  E213.Math.Real213.FluxMVT.FluxCut.fluxCutEq_of_pointwise
    mvt_id_unitBracket_forward_at mvt_id_unitBracket_backward_at

/-- ★ MVT corollary for id (fluxCutEq, PURE) — derivative form pointwise. -/
```

### \`mvt_id_unitBracket_cohomEquiv_pure\` (kind: theorem)
```lean
theorem mvt_id_unitBracket_cohomEquiv_pure :
    E213.Math.Real213.FluxMVT.FluxCut.fluxCutEq
      (localDivergence id unitBracket)
      (ofCut (idIsDifferentiable.derivative (constCut 0 1))) :=
  mvt_id_unitBracket_pure
```

## File: E213/Math/Real213/FluxMVTGeneric.lean  (4 decls)

### \`mvt_cutPow_unitBracket_pure\` (kind: theorem)
```lean
theorem mvt_cutPow_unitBracket_pure (n : Nat) :
    fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    (mvt_cutPow_unitBracket_forward_at n)
    (mvt_cutPow_unitBracket_backward_at n)

/-- ★ Generic fluxAlong for x^(n+1) at unit (fluxCutEq, PURE). -/
```

### \`fluxAlong_cutPow_unitBracket_pure\` (kind: theorem)
```lean
theorem fluxAlong_cutPow_unitBracket_pure (n : Nat) :
    fluxCutEq (fluxAlong (fun x => cutPow x (n+1)) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    (fluxAlong_cutPow_unitBracket_forward_at n)
    (fluxAlong_cutPow_unitBracket_backward_at n)

/-- ★ Generic FTC bridge for x^(n+1) at unit (fluxCutEq, PURE). -/
```

## File: E213/Math/Real213/FluxMVTHigh.lean  (4 decls)

### \`fluxAlong_quartic_unitBracket_pure\` (kind: theorem)
```lean
theorem fluxAlong_quartic_unitBracket_pure :
    fluxCutEq (fluxAlong (fun x => cutMul (cutMul x x) (cutMul x x))
                         unitBracket) (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    fluxAlong_quartic_unitBracket_forward_at
    fluxAlong_quartic_unitBracket_backward_at

/-- LD x⁴ at unit forward, pointwise (∅-axiom). -/
```

### \`mvt_quartic_unitBracket_pure\` (kind: theorem)
```lean
theorem mvt_quartic_unitBracket_pure :
    fluxCutEq (localDivergence (fun x => cutMul (cutMul x x) (cutMul x x))
                                unitBracket) (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    mvt_quartic_unitBracket_forward_at
    mvt_quartic_unitBracket_backward_at

/-- ★ FTC bridge for x⁴ at unit (fluxCutEq, PURE).  Chains
    `mvt_quartic_pure` with `fluxAlong_quartic_pure` via fluxBalance. -/
```

## File: E213/Math/Real213/FluxMVTPassthrough.lean  (6 decls)

### \`mvt_passthrough_unit_forward_at_pure\` (kind: theorem)
```lean
theorem mvt_passthrough_unit_forward_at_pure
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k) (m k : Nat) :
    (localDivergence f unitBracket).forward m k
      = (ofCut (constCut 1 1) : FluxCut).forward m k := by
  show cutMul (constCut 1 1) (f (constCut 1 1)) m k = constCut 1 1 m k
  show cutMulOuter (constCut 1 1) (f (constCut 1 1)) k m
         ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 1 1 m k
  have step : cutMulOuter (constCut 1
... [trunc]
```

### \`mvt_passthrough_unit_backward_at_pure\` (kind: theorem)
```lean
theorem mvt_passthrough_unit_backward_at_pure
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k) (m k : Nat) :
    (localDivergence f unitBracket).backward m k
      = (ofCut (constCut 1 1) : FluxCut).backward m k := by
  show cutMul (constCut 1 1) (f (constCut 0 1)) m k = constCut 0 1 m k
  show cutMulOuter (constCut 1 1) (f (constCut 0 1)) k m
         ((m+1)*(k+1)) ((m+1)*(k+1)) = constCut 0 1 m k
  have step : cutMulOuter (constCut
... [trunc]
```

## File: E213/Math/Real213/FluxMVTPolynomial.lean  (3 decls)

### \`mvt_square_unitBracket_pure\` (kind: theorem)
```lean
theorem mvt_square_unitBracket_pure :
    fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    mvt_square_unitBracket_forward_at
    mvt_square_unitBracket_backward_at

/-- Helper: fluxAlong x³ at unit forward at point. -/
```

### \`mvt_cube_unitBracket_pure\` (kind: theorem)
```lean
theorem mvt_cube_unitBracket_pure :
    fluxCutEq (localDivergence (fun x => cutMul x (cutMul x x)) unitBracket)
              (ofCut (constCut 1 1)) :=
  fluxCutEq_of_pointwise
    mvt_cube_unitBracket_forward_at
    mvt_cube_unitBracket_backward_at

/-- ★ Phase BB capstone (fluxCutEq, PURE): polynomial MVT at unit bracket. -/
```

## File: E213/Math/Real213/FluxMVTPropagate.lean  (1 decls)

### \`propagation_capstone_pure\` (kind: theorem)
```lean
theorem propagation_capstone_pure :
    (∀ m k, (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
              ).derivative (constCut 1 2) m k = constCut 1 1 m k)
    ∧ (∀ m k, (midIsDifferentiable
                (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
                squareIsDifferentiable).derivative (constCut 1 2) m k
              = constCut 1 1 m k) :=
  ⟨mid_witness_propagates_at idIsDifferentiable squareIsDifferentiable
     (fun _ _ => rfl) squareDe
... [trunc]
```

## File: E213/Math/Real213/FluxMVTPropagateCompose.lean  (1 decls)

### \`id_compose_propagation_capstone_pure\` (kind: theorem)
```lean
theorem id_compose_propagation_capstone_pure :
    (∀ m k, (composeIsDifferentiable squareIsDifferentiable
              idIsDifferentiable).derivative (constCut 1 2) m k
            = constCut 1 1 m k)
    ∧ (∀ m k, (composeIsDifferentiable
                (midIsDifferentiable idIsDifferentiable squareIsDifferentiable)
                idIsDifferentiable).derivative (constCut 1 2) m k
              = constCut 1 1 m k) :=
  ⟨id_compose_witness_propagates_at squareIsDifferentiable
     squareDeriv
... [trunc]
```

## File: E213/Math/Real213/FluxMVTWitness.lean  (2 decls)

### \`mvt_square_explicit_pure\` (kind: theorem)
```lean
theorem mvt_square_explicit_pure :
    fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
              (ofCut (constCut 1 1))
    ∧ (∀ m k, squareIsDifferentiable.derivative (constCut 1 2) m k
                = constCut 1 1 m k) :=
  ⟨mvt_square_unitBracket_pure, squareDerivative_at_half_at⟩

/-- ★ MVT existence (pointwise) with explicit witness for x² (PURE). -/
```

### \`mvt_square_with_witness_capstone_pure\` (kind: theorem)
```lean
theorem mvt_square_with_witness_capstone_pure :
    fluxCutEq (localDivergence (fun x => cutMul x x) unitBracket)
              (ofCut (constCut 1 1))
    ∧ (∀ m k, squareIsDifferentiable.derivative (constCut 1 2) m k
                = constCut 1 1 m k)
    ∧ ∃ c, ∀ m k, squareIsDifferentiable.derivative c m k = constCut 1 1 m k :=
  ⟨mvt_square_unitBracket_pure, squareDerivative_at_half_at,
   ⟨constCut 1 2, squareDerivative_at_half_at⟩⟩
```

## File: E213/Math/Real213/FluxPassthroughClass.lean  (2 decls)

### \`mvt_pure\` (kind: theorem)
```lean
theorem mvt_pure {f} (pf : Passthrough_at f) :
    fluxCutEq (localDivergence f unitBracket) (ofCut (constCut 1 1)) :=
  mvt_passthrough_unit_pure f pf.left pf.right

/-- One-liner FTC bridge (fluxCutEq, PURE) for any Passthrough_at. -/
```

### \`ftc_pure\` (kind: theorem)
```lean
theorem ftc_pure {f} (pf : Passthrough_at f) :
    fluxCutEq (localDivergence f unitBracket) (fluxAlong f unitBracket) :=
  ftc_bridge_passthrough_unit_pure f pf.left pf.right
```

## File: E213/Math/Real213/MVTWitnessChain.lean  (1 decls)

### \`chain_rule_witness_capstone_pure\` (kind: theorem)
```lean
theorem chain_rule_witness_capstone_pure :
    (∀ m k, (composeIsDifferentiable squareIsDifferentiable
              idIsDifferentiable).derivative (constCut 1 2) m k
            = constCut 1 1 m k)
    ∧ (∃ c, ∀ m k, (composeIsDifferentiable squareIsDifferentiable
                     idIsDifferentiable).derivative c m k = constCut 1 1 m k) :=
  ⟨id_compose_square_derivative_at_half_at,
   id_compose_square_has_dyadic_witness_at⟩
```

## File: E213/Math/Real213/NewtonFirst.lean  (1 decls)

### \`newton_first_law_capstone_pure\` (kind: theorem)
```lean
theorem newton_first_law_capstone_pure (v0 x0 : Nat) :
    (∀ t m k, (linearWithIntercept_isDifferentiable v0 x0).derivative t m k
              = constCutFn (constCut v0 1) t m k)
    ∧ (∀ t m k, (linearWithIntercept_isDifferentiable v0 x0).derivative t m k
                = constCut v0 1 m k)
    ∧ (linearWithIntercept_secondDerivable v0).derivative
        = constCutFn (constCut 0 1) :=
  ⟨linearWithIntercept_derivative_at v0 x0,
   velocity_is_v0_at v0 x0,
   rfl⟩
```

## File: E213/Math/Real213/ODECatalog.lean  (1 decls)

### \`ode_catalog_capstone_pure\` (kind: theorem)
```lean
theorem ode_catalog_capstone_pure (a b : Nat) (c : Nat → Nat → Bool) :
    (∀ t m k, (constIsDifferentiable c).derivative t m k
              = constCutFn (constCut 0 1) t m k)
    ∧ (∀ t m k, idIsDifferentiable.derivative t m k
                = constCutFn (constCut 1 1) t m k)
    ∧ (∀ t m k, (linearWithIntercept_isDifferentiable a b).derivative t m k
                = constCutFn (constCut a 1) t m k)
    ∧ (∀ t m k, (cutScaleIsDifferentiable a b).derivative t m k
                = constCutFn 
... [trunc]
```

## File: E213/Math/Real213/PhaseBACapstone.lean  (1 decls)

### \`phaseBA_capstone_pure\` (kind: theorem)
```lean
theorem phaseBA_capstone_pure (a b c d : FluxCut) (hab : cohomEquiv a b)
    (hcd : cohomEquiv c d)
    (cf : Nat → Nat → Bool) (db : DyadicBracket) :
    cohomEquiv a a
    ∧ cohomEquiv b a
    ∧ cohomEquiv a.neg b.neg
    ∧ cohomEquiv (add a c) (add b d)
    ∧ cohomEquiv (sub a c) (sub b d)
    ∧ fluxCutEq (localDivergence id unitBracket) (ofCut (constCut 1 1))
    ∧ isBalanced (localDivergence (constCutFn cf) db) :=
  ⟨cohomEquiv_refl a,
   cohomEquiv_symm a b hab,
   neg_cohomEquiv a b hab,

... [trunc]
```

## File: E213/Math/Real213/PhaseBHCapstone.lean  (1 decls)

### \`phaseBH_grand_capstone_pure\` (kind: theorem)
```lean
theorem phaseBH_grand_capstone_pure (a : FluxCut)
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (h_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k) :
    cohomEquiv a a
    ∧ fluxCutEq (localDivergence id unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence f unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (fluxAlong f unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence f unitBracket
... [trunc]
```

## File: E213/Math/Real213/PhaseBQOmegaCapstone.lean  (1 decls)

### \`phaseBQ_omega_capstone_pure\` (kind: theorem)
```lean
theorem phaseBQ_omega_capstone_pure (n : Nat) (a : FluxCut)
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (h_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k) :
    cohomEquiv a a
    ∧ fluxCutEq (localDivergence id unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
                (ofCut (constCut 1 1))
    ∧ fluxCutEq (fluxAlong (fun x => cutPow x (n+1)) unitBrac
... [trunc]
```

## File: E213/Math/Real213/PhaseBZMegaOmega.lean  (1 decls)

### \`phaseBZ_megaOmega_capstone_pure\` (kind: theorem)
```lean
theorem phaseBZ_megaOmega_capstone_pure (n : Nat) (a : FluxCut) :
    cohomEquiv a a
    ∧ fluxCutEq (localDivergence id unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
                (ofCut (constCut 1 1))
    ∧ (∀ m k, squareIsDifferentiable.derivative (constCut 1 2) m k
              = constCut 1 1 m k)
    ∧ (∀ m k, (midIsDifferentiable idIsDifferentiable squareIsDifferentiable
        ).derivative (constCut 1 2) m k = constCut 1 1
... [trunc]
```

## File: E213/Math/Real213/PhaseCMFinalCapstone.lean  (1 decls)

### \`phaseCM_final_capstone_pure\` (kind: theorem)
```lean
theorem phaseCM_final_capstone_pure (n : Nat)
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool))
    (h_left : ∀ m k, f (constCut 0 1) m k = constCut 0 1 m k)
    (h_right : ∀ m k, f (constCut 1 1) m k = constCut 1 1 m k) :
    fluxCutEq (localDivergence id unitBracket) (ofCut (constCut 1 1))
    ∧ fluxCutEq (localDivergence (fun x => cutPow x (n+1)) unitBracket)
                (ofCut (constCut 1 1))
    ∧ fluxCutEq (fluxAlong (fun x => cutPow x (n+1)) unitBracket)
                (ofCut (constC
... [trunc]
```

## File: E213/Physics/AlphaEM/Tight.lean  (1 decls)

### \`alpha_em_bare_pure_drlt\` (kind: theorem)
```lean
theorem alpha_em_bare_pure_drlt :
    let lo := inv_alpha_em_bare_lower 20
    let hi := inv_alpha_em_bare_upper 20
    -- 128 inside bare bracket
    (lo.1 < 128 * lo.2 ∧ 128 * hi.2 < hi.1)
    -- 137 outside (needs running)
    ∧ (hi.1 < 137 * hi.2)
    -- gap is 9
    ∧ (137 - 128 = 9) := by decide
```

## File: E213/Physics/Cosmology/NeffDerivation.lean  (1 decls)

### \`alpha_3_pure_sector_exhaustion\` (kind: theorem)
```lean
theorem alpha_3_pure_sector_exhaustion :
    -- Choosing all NS vertices from NS-dim sector: C(NS, NS) = 1
    binom NS NS = 1 ∧ binom NS (NS + 1) = 0 := by decide

/-- **Sharper alpha_2 statement**: temporal sector rank constraint.
    Choosing 2 out of 2 temporal directions: only 1 way. -/
```

## File: E213/Physics/Couplings/RunningGap.lean  (1 decls)

### \`running_gap_pure_DRLT\` (kind: theorem)
```lean
theorem running_gap_pure_DRLT :
    running_gap = (25, 3)
    ∧ d * d = NS * NS + NT * NT + 2 * NS * NT
    ∧ d = NS + NT := by decide
```
