import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyLattice

/-!
# HolonomyFreeness — the Stern–Brocot monoid ⟨L,R⟩ is free (∅-axiom)

Item (1) of the holonomy-lattice frontier: full **freeness** of `⟨L,R⟩` —
`holonomy` is *injective* on positive words.  `positive_loop_trivial`
(`HolonomyLattice`) already gives non-return-to-`I`; here the stronger unique-word
property: distinct positive words have distinct holonomies.

The crux is **first-letter determinacy** `L_head_ne_R_head`: an `L`-headed
positive matrix can never equal an `R`-headed one — equating
`L·M = ⟨a, b, a+c, b+d⟩` with `R·M' = ⟨a'+c', b'+d', c', d'⟩` forces `a' + c = 0`,
impossible for `Pos M'` (`a' ≥ 1`).  With left-cancellation of `L` and `R`
(`mul_L_inj` / `mul_R_inj`), injectivity follows by induction on the word.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyFreeness

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace.Mat2 (mul)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyLattice
  (holonomy L R Pos mul_L_eq mul_R_eq positive_loop_trivial PositiveWord holonomy_pos)
open E213.Meta.Int213.Order
  (le_of_sub_nonneg nonneg_of_le_zero le_zero_of_nonneg sub_nonneg_of_le)

/-- Pure `1 ≤ x + y` from `1 ≤ x`, `0 ≤ y` (`Int.add_le_add` is propext-tainted). -/
private theorem one_le_add_of {x y : Int} (hx : 1 ≤ x) (hy : 0 ≤ y) : 1 ≤ x + y := by
  apply le_of_sub_nonneg
  rw [show x + y - 1 = (x - 1) + y from by ring_intZ]
  exact nonneg_of_le_zero
    (E213.Meta.Int213.add_nonneg (le_zero_of_nonneg (sub_nonneg_of_le hx)) hy)

/-- Pure left-cancellation on `Int` (`Int.add_left_cancel` is propext-tainted). -/
private theorem add_cancel_l {a b c : Int} (h : a + b = a + c) : b = c :=
  (show b = (a + b) - a from by ring_intZ).trans
    ((congrArg (· - a) h).trans (show (a + c) - a = c from by ring_intZ))

/-- Pure right-cancellation on `Int`. -/
private theorem add_cancel_r {a b c : Int} (h : a + c = b + c) : a = b :=
  (show a = (a + c) - c from by ring_intZ).trans
    ((congrArg (· - c) h).trans (show (b + c) - c = b from by ring_intZ))

/-- Left-multiplication by `L` is injective: `L·M = L·M' ⟹ M = M'`. -/
theorem mul_L_inj {M M' : Mat2} (h : mul L M = mul L M') : M = M' := by
  rcases M with ⟨a, b, c, d⟩; rcases M' with ⟨a', b', c', d'⟩
  rw [mul_L_eq, mul_L_eq] at h
  dsimp only at h
  injection h with h1 h2 h3 h4   -- h1:a=a', h2:b=b', h3:a+c=a'+c', h4:b+d=b'+d'
  subst h1; subst h2
  rw [add_cancel_l h3, add_cancel_l h4]

/-- Left-multiplication by `R` is injective. -/
theorem mul_R_inj {M M' : Mat2} (h : mul R M = mul R M') : M = M' := by
  rcases M with ⟨a, b, c, d⟩; rcases M' with ⟨a', b', c', d'⟩
  rw [mul_R_eq, mul_R_eq] at h
  dsimp only at h
  injection h with h1 h2 h3 h4   -- h1:a+c=a'+c', h2:b+d=b'+d', h3:c=c', h4:d=d'
  subst h3; subst h4
  rw [add_cancel_r h1, add_cancel_r h2]

/-- ★★★★ **First-letter determinacy.**  An `L`-headed positive matrix is never an
    `R`-headed one: `Pos M → Pos M' → L·M ≠ R·M'`.  Equating the two forces
    `a' + c = 0`, impossible since `Pos M'` gives `a' ≥ 1` and `Pos M` gives `c ≥ 0`. -/
theorem L_head_ne_R_head {M M' : Mat2} (hM : Pos M) (hM' : Pos M') :
    mul L M ≠ mul R M' := by
  rcases M with ⟨a, b, c, d⟩; rcases M' with ⟨a', b', c', d'⟩
  rw [mul_L_eq, mul_R_eq]
  intro h
  dsimp only at h
  injection h with h1 _ h3 _   -- h1 : a = a' + c',  h3 : a + c = c'
  obtain ⟨ha', _, _, _⟩ := hM'
  obtain ⟨_, _, hc, _⟩ := hM
  have heq : a = a' + (a + c) := h1.trans (congrArg (a' + ·) h3.symm)
  have key : a + (a' + c) = a + 0 := by
    rw [Int.add_zero, show a + (a' + c) = a' + (a + c) from by ring_intZ]
    exact heq.symm
  have hzero : a' + c = 0 := add_cancel_l key
  exact absurd (hzero ▸ one_le_add_of ha' hc) (by decide)

/-- ★★★★★ **The Stern–Brocot monoid ⟨L,R⟩ is free**: `holonomy` is injective on
    positive words — distinct words in `{L,R}*` have distinct holonomies.  The
    unique-word property, the strengthening of `positive_loop_trivial`. -/
theorem holonomy_injective_positive :
    ∀ (w₁ w₂ : List Mat2), PositiveWord w₁ → PositiveWord w₂ →
      holonomy w₁ = holonomy w₂ → w₁ = w₂
  | [], [], _, _, _ => rfl
  | [], (_ :: _), _, hw₂, h =>
      absurd h.symm (positive_loop_trivial hw₂ (fun hc => List.noConfusion hc))
  | (_ :: _), [], hw₁, _, h =>
      absurd h (positive_loop_trivial hw₁ (fun hc => List.noConfusion hc))
  | (g₁ :: gs₁), (g₂ :: gs₂), hw₁, hw₂, h => by
      have hp₁ : Pos (holonomy gs₁) :=
        holonomy_pos gs₁ (fun x hx => hw₁ x (List.Mem.tail g₁ hx))
      have hp₂ : Pos (holonomy gs₂) :=
        holonomy_pos gs₂ (fun x hx => hw₂ x (List.Mem.tail g₂ hx))
      have hw₁' : PositiveWord gs₁ := fun x hx => hw₁ x (List.Mem.tail g₁ hx)
      have hw₂' : PositiveWord gs₂ := fun x hx => hw₂ x (List.Mem.tail g₂ hx)
      rcases hw₁ g₁ (List.Mem.head gs₁) with e1 | e1 <;>
        rcases hw₂ g₂ (List.Mem.head gs₂) with e2 | e2 <;> subst e1 <;> subst e2
      · exact congrArg (L :: ·)
          (holonomy_injective_positive gs₁ gs₂ hw₁' hw₂' (mul_L_inj h))
      · exact absurd h (L_head_ne_R_head hp₁ hp₂)
      · exact absurd h (fun he => L_head_ne_R_head hp₂ hp₁ he.symm)
      · exact congrArg (R :: ·)
          (holonomy_injective_positive gs₁ gs₂ hw₁' hw₂' (mul_R_inj h))

end E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HolonomyFreeness
