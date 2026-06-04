import E213.Meta.Nat.PureNat

/-!
# EisensteinClassNumber — disc `−3` has class number one (the Eisenstein form is the only one)

The Eisenstein period factors so cleanly (`Σ' 1/(a²+ab+b²)^s = 6 ζ L(·,χ₋₃)`, a single
form, no genus/class ambiguity) for a structural reason: the discriminant `−3` has **class
number one** — every reduced positive-definite binary quadratic form of discriminant `−3`
is the single principal form `x² + xy + y²` (`= a² + ab + b²`).  This is the form-class
counterpart of `ℤ[ω]` being a PID (`h(−3) = 1`), and it is what makes "*the* Eisenstein
form" well defined.

The proof is finite.  A *reduced* form `(a, b, c)` — `|b| ≤ a ≤ c`, positive-definite
`a, c > 0` — of discriminant `b² − 4ac = −3` is forced to be `(1, ±1, 1)`.  Writing
`4ac = b² + 3` (with `B = |b|`) and using `B ≤ a ≤ c`:

  `4a² ≤ 4ac = B² + 3 ≤ a² + 3`  ⟹  `3a² ≤ 3`  ⟹  `a = 1`,

and then `4c = B² + 3` with `B ≤ 1` forces `B = 1`, `c = 1`.  No reciprocity, no descent —
only the reduction inequalities, all `∅`-axiom over `ℕ`.

  * ★★★★ `reduced_disc_neg3_unique` — `B ≤ a ≤ c` and `4ac = B² + 3` force
    `a = 1 ∧ B = 1 ∧ c = 1`: the unique reduced datum of discriminant `−3`.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinClassNumber

/-- Pure left-cancellation of `≤` over `+` (the core lemma is `propext`-dirty): by
    induction on the cancelled summand `k`, stripping a `succ` each step. -/
private theorem le_cancel_add_left : ∀ (k m n : Nat), k + m ≤ k + n → m ≤ n
  | 0, _, _, h => by rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | k + 1, m, n, h => by
      rw [Nat.add_right_comm k 1 m, Nat.add_right_comm k 1 n] at h
      exact le_cancel_add_left k m n (Nat.le_of_succ_le_succ h)

/-- `a*a ≤ 1` with `1 ≤ a` forces `a = 1` (since `a ≤ a*a` for `a ≥ 1`). -/
private theorem a_eq_one (a : Nat) (ha : 1 ≤ a) (h : a * a ≤ 1) : a = 1 := by
  have hle : a ≤ a * a := by
    have hx : a * 1 ≤ a * a := Nat.mul_le_mul (Nat.le_refl a) ha
    rwa [Nat.mul_one] at hx
  exact Nat.le_antisymm (Nat.le_trans hle h) ha

/-- ★★★★ **The reduced disc-`−3` datum is unique.**  With `B ≤ a ≤ c` and `4ac = B² + 3`,
    necessarily `a = 1`, `B = 1`, `c = 1` — the principal Eisenstein form `x² + xy + y²` is
    the only reduced form of discriminant `−3`.  The finite heart of class number one
    (`h(−3) = 1`), `B = |b|`. -/
theorem reduced_disc_neg3_unique (a B c : Nat)
    (hBa : B ≤ a) (hac : a ≤ c) (hdisc : 4 * a * c = B * B + 3) :
    a = 1 ∧ B = 1 ∧ c = 1 := by
  -- `4a² ≤ 4ac`  from `a ≤ c`
  have h4ac : 4 * a * a ≤ 4 * a * c := Nat.mul_le_mul (Nat.le_refl (4 * a)) hac
  -- `B² ≤ a²`  from `B ≤ a`
  have hBB : B * B ≤ a * a := Nat.mul_le_mul hBa hBa
  -- `4a² ≤ B² + 3 ≤ a² + 3`
  have hchain : 4 * a * a ≤ a * a + 3 := by
    rw [hdisc] at h4ac
    exact Nat.le_trans h4ac (Nat.add_le_add_right hBB 3)
  -- `4a² = a² + 3a²`, so `3a² ≤ 3`
  have he : 4 * a * a = a * a + 3 * (a * a) := by
    rw [E213.Meta.Nat.PureNat.mul_assoc 4 a a, show (4 : Nat) = 1 + 3 from rfl,
        E213.Meta.Nat.PureNat.add_mul, Nat.one_mul]
  have h3 : 3 * (a * a) ≤ 3 := by
    rw [he] at hchain
    exact le_cancel_add_left (a * a) (3 * (a * a)) 3 hchain
  -- `a² ≤ 1`  (divide by 3)
  have haa : a * a ≤ 1 :=
    Nat.le_of_mul_le_mul_left (show 3 * (a * a) ≤ 3 * 1 from by rw [Nat.mul_one]; exact h3)
      (by decide)
  -- `1 ≤ a`  (else `4ac = 0 ≠ B² + 3 ≥ 3`)
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · exfalso
      rw [h0, Nat.mul_zero, Nat.zero_mul] at hdisc
      have hpos3 : 0 < B * B + 3 := Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 3 (B * B))
      exact absurd hdisc (Nat.ne_of_lt hpos3)
    · exact hpos
  have ha : a = 1 := a_eq_one a ha1 haa
  subst ha
  -- now `4c = B² + 3`, `B ≤ 1`
  rw [Nat.mul_one] at hdisc
  rcases B with _ | _ | B''
  · -- B = 0: `4c = 3` impossible
    exfalso
    rcases c with _ | c'
    · exact absurd hdisc (by decide)
    · rw [Nat.mul_succ] at hdisc
      have h4 : (4 : Nat) ≤ 0 * 0 + 3 := hdisc ▸ Nat.le_add_left 4 (4 * c')
      exact absurd h4 (by decide)
  · -- B = 1: `4c = 4` ⟹ `c = 1`
    refine ⟨rfl, rfl, ?_⟩
    have h4 : 4 * c = 4 * 1 := by rw [Nat.mul_one]; exact hdisc
    exact Nat.eq_of_mul_eq_mul_left (by decide) h4
  · -- B = B''+2: contradicts `B ≤ 1`
    have h2 : 2 ≤ 1 :=
      Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le B''))) hBa
    exact absurd h2 (by decide)

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinClassNumber
