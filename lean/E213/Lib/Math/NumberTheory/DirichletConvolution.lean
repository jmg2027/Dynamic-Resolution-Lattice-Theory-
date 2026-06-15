import E213.Lib.Math.NumberTheory.MobiusInversion

/-!
# Dirichlet convolution of arithmetic functions (∅-axiom)

`dconv f g n = Σ_{d∣n} f(d)·g(n/d)`, built on `divisorSumZ` and the proven
`divisor_pair_swap` core in `MobiusInversion.lean`.  Establishes that arithmetic
functions `Nat → Int` form a **commutative monoid** under `dconv` (the multiplicative
structure of the Dirichlet ring) on the positive-`n` support — the algebraic capstone
of the φ/μ/σ/τ/σ_k/λ + Möbius-inversion framework built this session.

  ★★★ `dirichlet_comm`  : `dconv f g n = dconv g f n`.
  ★★★ `dirichlet_assoc` : `dconv (dconv f g) h n = dconv f (dconv g h) n`.
  `divisorSumZ_reflect` : `Σ_{d∣n} F(d) = Σ_{d∣n} F(n/d)` (divisor reflection, free from comm).

Commutativity via a flat symmetric bridge `dconv_flat` (gating exact factorizations
`[a·b=n]`) + `sumZ_fubini`; associativity reduces both sides to the canonical
`Σ_{d∣n}Σ_{e∣(n/d)} f(d)·g(e)·h(n/(d·e))` via `divisor_pair_swap` + `comm` + `div_div_pure`.
(Note: `Nat.mul_assoc` carries propext here — uses the PURE twin `NatHelper.mul_assoc`.)
All ∅-axiom.  Genuinely absent (the corpus `*Convolution` are binomial, not Dirichlet).
-/

namespace E213.Lib.Math.NumberTheory.DirichletConvolution

open E213.Lib.Math.NumberTheory.MobiusFunction (sumZ divisorSumZ)
open E213.Lib.Math.NumberTheory.MobiusPrimeCase
  (sumZ_succ sumZ_const_zero sumZ_congr sumZ_split_first)
open E213.Lib.Math.NumberTheory.EulerTotient (dvdInd)
open E213.Lib.Math.NumberTheory.GaussTotient
  (eqInd eqInd_self eqInd_ne mul_div_of_dvd dvd_mod_zero)
open E213.Lib.Math.NumberTheory.DivisorMultiplicative
  (dvdInd_eq_one_iff dvdInd_eq_zero_iff dvdInd_zero_or_one le_of_dvd_pos')
open E213.Lib.Math.NumberTheory.MobiusDivisorSum
  (sumZ_add_func sumZ_mul_left sumZ_fubini sum_eqIndZ_weight_eq
   sumZ_mul_right castOne_mul castZero_mul)
open E213.Lib.Math.NumberTheory.MobiusInversion
  (divisor_pair_swap pair_dvd_iff divisorSumZ_const_mul div_eq_one_iff_eq
   sumZ_eq_of_tail_zero)
open E213.Meta.Nat.NatDiv213 (mul_div_cancel_left_pure mul_witness_iff_mod_eq_zero
  div_le_self_pos div_sandwich div_eq_of_sandwich)
open E213.Meta.Nat.Beq213 (nat_beq_op_eq_false_of_ne)

/-! ## §1 — Definition -/

/-- Dirichlet convolution: `(f ⋆ g)(n) = Σ_{d∣n} f(d)·g(n/d)`. -/
def dconv (f g : Nat → Int) (n : Nat) : Int :=
  divisorSumZ n (fun d => f d * g (n / d))

/-! ## §2 — Positivity helpers -/

/-- A divisor of a positive number is positive. -/
theorem pos_of_dvd_pos {n d : Nat} (hn : 0 < n) (hd : d ∣ n) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · exfalso; obtain ⟨c, hc⟩ := hd; rw [h0, Nat.zero_mul] at hc
    exact Nat.lt_irrefl 0 (hc ▸ hn)
  · exact hpos

/-- For `d ∣ n` (`0 < n`), the cofactor `n/d` is positive. -/
theorem cofactor_pos {n d : Nat} (hn : 0 < n) (hd : d ∣ n) : 0 < n / d := by
  have hcof : d * (n / d) = n := mul_div_of_dvd hd
  rcases Nat.eq_zero_or_pos (n / d) with h0 | hpos
  · exfalso; rw [h0, Nat.mul_zero] at hcof; exact Nat.lt_irrefl 0 (hcof ▸ hn)
  · exact hpos

/-! ## §3 — The exact-factorization gate -/

/-- `prodInd a b n = [a·b = n]` as an Int. -/
def prodInd (a b n : Nat) : Int := (eqInd (a * b) n : Int)

theorem prodInd_comm (a b n : Nat) : prodInd a b n = prodInd b a n := by
  show (eqInd (a * b) n : Int) = (eqInd (b * a) n : Int)
  rw [Nat.mul_comm a b]

/-- `prodInd a b n = 1 ↔ a·b = n`. -/
theorem prodInd_eq_one_iff (a b n : Nat) : prodInd a b n = 1 ↔ a * b = n := by
  show ((eqInd (a * b) n : Nat) : Int) = 1 ↔ a * b = n
  constructor
  · intro h
    by_cases hc : a * b = n
    · exact hc
    · exfalso
      have hz : ((eqInd (a * b) n : Nat) : Int) = 0 := by rw [eqInd_ne hc]; rfl
      rw [hz] at h; exact absurd h (by decide)
  · intro h; rw [h, eqInd_self]; rfl

/-- `prodInd a b n = 0 ↔ a·b ≠ n`. -/
theorem prodInd_eq_zero_iff (a b n : Nat) : prodInd a b n = 0 ↔ a * b ≠ n := by
  constructor
  · intro h heq
    have : prodInd a b n = 1 := (prodInd_eq_one_iff a b n).mpr heq
    rw [this] at h; exact absurd h (by decide)
  · intro h; show ((eqInd (a * b) n : Nat) : Int) = 0; rw [eqInd_ne h]; rfl

/-! ## §4 — Cofactor bridge: replace `g(n/d)` by a gated sum over `e` -/

/-- For a divisor `d = jd+1` of `n`, the single value `g(n/d)` equals the gated
    sum `Σ_{je<n} [(jd+1)·(je+1) = n] · g(je+1)` (the unique survivor `je+1 = n/d`). -/
theorem cofactor_collapse {n : Nat} (hn : 0 < n) (g : Nat → Int) {jd : Nat}
    (hdvd : (jd + 1) ∣ n) :
    g (n / (jd + 1))
      = sumZ n (fun je => prodInd (jd + 1) (je + 1) n * g (je + 1)) := by
  have hd0 : 0 < jd + 1 := Nat.succ_pos jd
  have hcof : (jd + 1) * (n / (jd + 1)) = n := mul_div_of_dvd hdvd
  have hndpos : 0 < n / (jd + 1) := cofactor_pos hn hdvd
  -- the survivor index is je = n/(jd+1) - 1
  have hsurv1 : n / (jd + 1) - 1 + 1 = n / (jd + 1) :=
    E213.Tactic.NatHelper.sub_one_add_one (Nat.ne_of_gt hndpos)
  have hsurv_lt : n / (jd + 1) - 1 < n := by
    have hle : n / (jd + 1) ≤ n := div_le_self_pos n (jd + 1) hd0
    exact Nat.lt_of_lt_of_le (Nat.sub_lt hndpos Nat.one_pos) hle
  -- each term equals [je = survivor] · g(n/(jd+1))
  have hpt : ∀ je, je < n →
      prodInd (jd + 1) (je + 1) n * g (je + 1)
        = (eqInd (n / (jd + 1) - 1) je : Int) * g (n / (jd + 1)) := by
    intro je _
    cases Nat.decEq je (n / (jd + 1) - 1) with
    | isTrue hjeq =>
      subst hjeq
      rw [eqInd_self, hsurv1,
          (prodInd_eq_one_iff (jd + 1) (n / (jd + 1)) n).mpr hcof, castOne_mul]
      show (1 : Int) * g (n / (jd + 1)) = g (n / (jd + 1))
      rw [E213.Meta.Int213.PolyIntM.one_mulZ]
    | isFalse hjne =>
      rw [eqInd_ne (fun he : n / (jd + 1) - 1 = je => hjne he.symm), castZero_mul]
      -- prodInd = 0 since (jd+1)·(je+1) = n would force je+1 = n/(jd+1)
      have hne : (jd + 1) * (je + 1) ≠ n := by
        intro heq
        apply hjne
        -- from (jd+1)(je+1) = n = (jd+1)(n/(jd+1)) cancel ⟹ je+1 = n/(jd+1)
        have hc2 : (jd + 1) * (je + 1) = (jd + 1) * (n / (jd + 1)) := by rw [heq, hcof]
        have hcancel : je + 1 = n / (jd + 1) :=
          E213.Tactic.NatHelper.mul_left_cancel_pos hd0 hc2
        rw [← hcancel]; exact (E213.Tactic.NatHelper.add_sub_cancel_right je 1).symm
      rw [(prodInd_eq_zero_iff (jd + 1) (je + 1) n).mpr hne, E213.Meta.Int213.zero_mul]
  rw [sumZ_congr n _ _ hpt]
  exact (sum_eqIndZ_weight_eq n (n / (jd + 1) - 1) (g (n / (jd + 1))) hsurv_lt).symm

/-! ## §5 — Flat bridge: `dconv` as a symmetric double sum -/

/-- If `(jd+1)·(je+1) = n` then `(jd+1) ∣ n`. -/
theorem dvd_of_prod_eq {n jd je : Nat} (heq : (jd + 1) * (je + 1) = n) :
    (jd + 1) ∣ n := ⟨je + 1, heq.symm⟩

/-- **Per-row bridge**: for each `jd`,
    `dvdInd jd n · (f(jd+1)·g(n/(jd+1))) = Σ_{je<n} prodInd(jd+1)(je+1)n · (f(jd+1)·g(je+1))`. -/
theorem row_bridge {n : Nat} (hn : 0 < n) (f g : Nat → Int) (jd : Nat) :
    (dvdInd jd n : Int) * (f (jd + 1) * g (n / (jd + 1)))
      = sumZ n (fun je => prodInd (jd + 1) (je + 1) n * (f (jd + 1) * g (je + 1))) := by
  cases Nat.decEq (n % (jd + 1)) 0 with
  | isTrue hmod =>
    have hdvd : (jd + 1) ∣ n := by
      obtain ⟨x, hx⟩ := (mul_witness_iff_mod_eq_zero (jd + 1) n).mpr hmod
      exact ⟨x, hx.symm⟩
    have hd1 : dvdInd jd n = 1 := (dvdInd_eq_one_iff jd n).mpr hdvd
    rw [hd1, castOne_mul, cofactor_collapse hn g hdvd]
    -- pull f(jd+1) inside the sum
    rw [sumZ_mul_left (f (jd + 1)) n
        (fun je => prodInd (jd + 1) (je + 1) n * g (je + 1))]
    exact sumZ_congr n _ _ (fun je _ => by
      generalize prodInd (jd + 1) (je + 1) n = P
      generalize f (jd + 1) = F
      generalize g (je + 1) = G
      ring_intZ)
  | isFalse hmod =>
    have hnd : ¬ (jd + 1) ∣ n := fun hd => hmod (dvd_mod_zero hd)
    have hd0 : dvdInd jd n = 0 := (dvdInd_eq_zero_iff jd n).mpr hnd
    rw [hd0, castZero_mul]
    -- RHS all zero
    have hz : sumZ n (fun je => prodInd (jd + 1) (je + 1) n * (f (jd + 1) * g (je + 1)))
        = sumZ n (fun _ => (0 : Int)) :=
      sumZ_congr n _ _ (fun je _ => by
        have hne : (jd + 1) * (je + 1) ≠ n := fun heq => hnd (dvd_of_prod_eq heq)
        rw [(prodInd_eq_zero_iff (jd + 1) (je + 1) n).mpr hne, E213.Meta.Int213.zero_mul])
    rw [hz, sumZ_const_zero n]

/-- ★★ **Flat bridge**: `dconv f g n = Σ_{jd<n}Σ_{je<n} prodInd(jd+1)(je+1)n · (f(jd+1)·g(je+1))`. -/
theorem dconv_flat {n : Nat} (hn : 0 < n) (f g : Nat → Int) :
    dconv f g n
      = sumZ n (fun jd => sumZ n (fun je =>
          prodInd (jd + 1) (je + 1) n * (f (jd + 1) * g (je + 1)))) := by
  show sumZ n (fun jd => (dvdInd jd n : Int) * (f (jd + 1) * g (n / (jd + 1))))
      = sumZ n (fun jd => sumZ n (fun je =>
          prodInd (jd + 1) (je + 1) n * (f (jd + 1) * g (je + 1))))
  exact sumZ_congr n _ _ (fun jd _ => row_bridge hn f g jd)

/-! ## §6 — ★★★ Commutativity -/

/-- ★★★ **Dirichlet convolution is commutative**: `dconv f g n = dconv g f n` (`0 < n`). -/
theorem dirichlet_comm (f g : Nat → Int) (n : Nat) (hn : 0 < n) :
    dconv f g n = dconv g f n := by
  rw [dconv_flat hn f g, dconv_flat hn g f]
  -- swap the two summation variables, then use prodInd symmetry + mul comm
  rw [sumZ_fubini (fun jd je =>
        prodInd (jd + 1) (je + 1) n * (f (jd + 1) * g (je + 1))) n n]
  exact sumZ_congr n _ _ (fun je _ =>
    sumZ_congr n _ _ (fun jd _ => by
      -- prodInd(jd+1)(je+1)·(f(jd+1)·g(je+1)) = prodInd(je+1)(jd+1)·(g(je+1)·f(jd+1))
      rw [prodInd_comm (jd + 1) (je + 1) n]
      generalize prodInd (je + 1) (jd + 1) n = P
      generalize f (jd + 1) = F
      generalize g (je + 1) = G
      ring_intZ))

/-! ## §7 — Divisor reflection (corollary of commutativity) -/

/-- `dconv (fun _ => 1) F n = divisorSumZ n (fun d => F (n/d))`. -/
theorem dconv_one_left (F : Nat → Int) (n : Nat) :
    dconv (fun _ => (1 : Int)) F n = divisorSumZ n (fun d => F (n / d)) := by
  show divisorSumZ n (fun d => (1 : Int) * F (n / d))
      = divisorSumZ n (fun d => F (n / d))
  show sumZ n (fun j => (dvdInd j n : Int) * ((1 : Int) * F (n / (j + 1))))
      = sumZ n (fun j => (dvdInd j n : Int) * F (n / (j + 1)))
  exact sumZ_congr n _ _ (fun j _ => by
    rw [E213.Meta.Int213.PolyIntM.one_mulZ])

/-- `dconv F (fun _ => 1) n = divisorSumZ n F`. -/
theorem dconv_one_right (F : Nat → Int) (n : Nat) :
    dconv F (fun _ => (1 : Int)) n = divisorSumZ n F := by
  show divisorSumZ n (fun d => F d * (1 : Int)) = divisorSumZ n F
  show sumZ n (fun j => (dvdInd j n : Int) * (F (j + 1) * (1 : Int)))
      = sumZ n (fun j => (dvdInd j n : Int) * F (j + 1))
  exact sumZ_congr n _ _ (fun j _ => by
    rw [E213.Meta.Int213.mul_one])

/-- ★★ **Divisor reflection**: `Σ_{d∣n} F(d) = Σ_{d∣n} F(n/d)` (`0 < n`). -/
theorem divisorSumZ_reflect (F : Nat → Int) (n : Nat) (hn : 0 < n) :
    divisorSumZ n F = divisorSumZ n (fun d => F (n / d)) := by
  rw [← dconv_one_right F n, dirichlet_comm F (fun _ => (1 : Int)) n hn, dconv_one_left F n]

/-! ## §8 — Nested floor + inner dconv expansion -/

/-- Pure nested floor `n / (a·b) = n / a / b` (`a,b > 0`). -/
theorem div_div_pure (n a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    n / (a * b) = n / a / b := by
  have hab : 0 < a * b := Nat.mul_pos ha hb
  have sy := div_sandwich a n ha
  have sx := div_sandwich b (n / a) hb
  refine (div_eq_of_sandwich hab ?_ ?_).symm
  · calc a * b * (n / a / b) = a * (b * (n / a / b)) := E213.Tactic.NatHelper.mul_assoc a b (n / a / b)
      _ ≤ a * (n / a) := Nat.mul_le_mul_left a sx.1
      _ ≤ n := sy.1
  · calc n < a * (n / a + 1) := sy.2
      _ ≤ a * (b * (n / a / b + 1)) := Nat.mul_le_mul_left a (Nat.succ_le_of_lt sx.2)
      _ = a * b * (n / a / b + 1) := (E213.Tactic.NatHelper.mul_assoc a b (n / a / b + 1)).symm

/-- **Inner-dconv expansion**: for `0 < n`,
    `dconv F (dconv G H) n = Σ_{d∣n} Σ_{e∣(n/d)} F(d)·(G(e)·H(n/(d·e)))`. -/
theorem dconv_inner_right (F G H : Nat → Int) (n : Nat) (_hn : 0 < n) :
    dconv F (dconv G H) n
      = divisorSumZ n (fun d => divisorSumZ (n / d)
          (fun e => F d * (G e * H (n / (d * e))))) := by
  show sumZ n (fun jd => (dvdInd jd n : Int)
        * (F (jd + 1) * dconv G H (n / (jd + 1))))
      = sumZ n (fun jd => (dvdInd jd n : Int)
        * divisorSumZ (n / (jd + 1))
            (fun e => F (jd + 1) * (G e * H (n / ((jd + 1) * e)))))
  refine sumZ_congr n _ _ (fun jd _ => ?_)
  cases Nat.decEq (n % (jd + 1)) 0 with
  | isFalse hmod =>
    have hnd : ¬ (jd + 1) ∣ n := fun hd => hmod (dvd_mod_zero hd)
    have hd0 : dvdInd jd n = 0 := (dvdInd_eq_zero_iff jd n).mpr hnd
    rw [hd0, castZero_mul, castZero_mul]
  | isTrue hmod =>
    have hdvd : (jd + 1) ∣ n := by
      obtain ⟨x, hx⟩ := (mul_witness_iff_mod_eq_zero (jd + 1) n).mpr hmod
      exact ⟨x, hx.symm⟩
    have hd0 : 0 < jd + 1 := Nat.succ_pos jd
    -- expand dconv G H (n/(jd+1)) and pull F(jd+1) in, rewrite floor
    show (dvdInd jd n : Int) * (F (jd + 1)
          * divisorSumZ (n / (jd + 1)) (fun e => G e * H ((n / (jd + 1)) / e)))
      = (dvdInd jd n : Int) * divisorSumZ (n / (jd + 1))
            (fun e => F (jd + 1) * (G e * H (n / ((jd + 1) * e))))
    rw [← divisorSumZ_const_mul (F (jd + 1)) (n / (jd + 1))
          (fun e => G e * H ((n / (jd + 1)) / e))]
    -- now match the integrands: ((n/(jd+1))/e) vs n/((jd+1)*e)
    refine congrArg (fun s => (dvdInd jd n : Int) * s) ?_
    show divisorSumZ (n / (jd + 1)) (fun e => F (jd + 1) * (G e * H ((n / (jd + 1)) / e)))
        = divisorSumZ (n / (jd + 1)) (fun e => F (jd + 1) * (G e * H (n / ((jd + 1) * e))))
    refine sumZ_congr (n / (jd + 1)) _ _ (fun je _ => ?_)
    show (dvdInd je (n / (jd + 1)) : Int)
          * (F (jd + 1) * (G (je + 1) * H ((n / (jd + 1)) / (je + 1))))
        = (dvdInd je (n / (jd + 1)) : Int)
          * (F (jd + 1) * (G (je + 1) * H (n / ((jd + 1) * (je + 1)))))
    rw [div_div_pure n (jd + 1) (je + 1) hd0 (Nat.succ_pos je)]

/-! ## §9 — ★★★ Associativity -/

/-- ★★★ **Dirichlet convolution is associative**:
    `dconv (dconv f g) h n = dconv f (dconv g h) n` (`0 < n`). -/
theorem dirichlet_assoc (f g h : Nat → Int) (n : Nat) (hn : 0 < n) :
    dconv (dconv f g) h n = dconv f (dconv g h) n := by
  -- LHS: commute to h ⋆ (f ⋆ g), then expand
  rw [dirichlet_comm (dconv f g) h n hn,
      dconv_inner_right h f g n hn]
  -- RHS: expand directly
  rw [dconv_inner_right f g h n hn]
  -- LHS-form:  Σ_{d∣n}Σ_{e∣(n/d)} h(d)·(f(e)·g(n/(d·e)))
  -- swap (d,e):  Σ_{e∣n}Σ_{d∣(n/e)} h(d)·(f(e)·g(n/(d·e)))
  rw [divisor_pair_swap hn (fun d e => h d * (f e * g (n / (d * e))))]
  -- now rename: outer is the e-variable.  Match against RHS pointwise per outer d.
  refine sumZ_congr n _ _ (fun jd _ => ?_)
  -- per outer divisor d = jd+1: show the two inner sums agree.
  cases Nat.decEq (n % (jd + 1)) 0 with
  | isFalse hmod =>
    have hnd : ¬ (jd + 1) ∣ n := fun hd => hmod (dvd_mod_zero hd)
    have hd0 : dvdInd jd n = 0 := (dvdInd_eq_zero_iff jd n).mpr hnd
    show (dvdInd jd n : Int) * divisorSumZ (n / (jd + 1))
            (fun d => h d * (f (jd + 1) * g (n / (d * (jd + 1)))))
        = (dvdInd jd n : Int) * divisorSumZ (n / (jd + 1))
            (fun e => f (jd + 1) * (g e * h (n / ((jd + 1) * e))))
    rw [hd0, castZero_mul, castZero_mul]
  | isTrue hmod =>
    have hdvd : (jd + 1) ∣ n := by
      obtain ⟨x, hx⟩ := (mul_witness_iff_mod_eq_zero (jd + 1) n).mpr hmod
      exact ⟨x, hx.symm⟩
    have hd0 : 0 < jd + 1 := Nat.succ_pos jd
    have hndpos : 0 < n / (jd + 1) := cofactor_pos hn hdvd
    have hcof : (jd + 1) * (n / (jd + 1)) = n := mul_div_of_dvd hdvd
    show (dvdInd jd n : Int) * divisorSumZ (n / (jd + 1))
            (fun d => h d * (f (jd + 1) * g (n / (d * (jd + 1)))))
        = (dvdInd jd n : Int) * divisorSumZ (n / (jd + 1))
            (fun e => f (jd + 1) * (g e * h (n / ((jd + 1) * e))))
    refine congrArg (fun s => (dvdInd jd n : Int) * s) ?_
    -- inner-LHS = dconv h g (n/(jd+1))  (after rewriting floors),
    -- inner-RHS = dconv g h (n/(jd+1));  equal by comm.
    -- First rewrite both integrands' floors to (n/(jd+1))/_.
    have hL : divisorSumZ (n / (jd + 1))
            (fun d => h d * (f (jd + 1) * g (n / (d * (jd + 1)))))
          = divisorSumZ (n / (jd + 1))
            (fun e => f (jd + 1) * (h e * g ((n / (jd + 1)) / e))) := by
      refine sumZ_congr (n / (jd + 1)) _ _ (fun je _ => ?_)
      show (dvdInd je (n / (jd + 1)) : Int)
            * (h (je + 1) * (f (jd + 1) * g (n / ((je + 1) * (jd + 1)))))
          = (dvdInd je (n / (jd + 1)) : Int)
            * (f (jd + 1) * (h (je + 1) * g ((n / (jd + 1)) / (je + 1))))
      -- n/((je+1)*(jd+1)) = n/((jd+1)*(je+1)) = (n/(jd+1))/(je+1)
      rw [Nat.mul_comm (je + 1) (jd + 1),
          div_div_pure n (jd + 1) (je + 1) hd0 (Nat.succ_pos je)]
      generalize (dvdInd je (n / (jd + 1)) : Int) = D
      generalize h (je + 1) = HH
      generalize f (jd + 1) = FF
      generalize g ((n / (jd + 1)) / (je + 1)) = GG
      ring_intZ
    have hR : divisorSumZ (n / (jd + 1))
            (fun e => f (jd + 1) * (g e * h (n / ((jd + 1) * e))))
          = divisorSumZ (n / (jd + 1))
            (fun e => f (jd + 1) * (g e * h ((n / (jd + 1)) / e))) := by
      refine sumZ_congr (n / (jd + 1)) _ _ (fun je _ => ?_)
      show (dvdInd je (n / (jd + 1)) : Int)
            * (f (jd + 1) * (g (je + 1) * h (n / ((jd + 1) * (je + 1)))))
          = (dvdInd je (n / (jd + 1)) : Int)
            * (f (jd + 1) * (g (je + 1) * h ((n / (jd + 1)) / (je + 1))))
      rw [div_div_pure n (jd + 1) (je + 1) hd0 (Nat.succ_pos je)]
    rw [hL, hR]
    -- both equal f(jd+1) · (inner dconv); the two inner dconvs are comm-related
    rw [divisorSumZ_const_mul (f (jd + 1)) (n / (jd + 1))
          (fun e => h e * g ((n / (jd + 1)) / e)),
        divisorSumZ_const_mul (f (jd + 1)) (n / (jd + 1))
          (fun e => g e * h ((n / (jd + 1)) / e))]
    refine congrArg (fun s => f (jd + 1) * s) ?_
    -- divisorSumZ (n/d) (fun e => h e * g((n/d)/e)) = dconv h g (n/d)
    -- divisorSumZ (n/d) (fun e => g e * h((n/d)/e)) = dconv g h (n/d)
    show dconv h g (n / (jd + 1)) = dconv g h (n / (jd + 1))
    exact dirichlet_comm h g (n / (jd + 1)) hndpos

end E213.Lib.Math.NumberTheory.DirichletConvolution
