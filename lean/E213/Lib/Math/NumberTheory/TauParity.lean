import E213.Lib.Math.NumberTheory.SumOfDivisors
import E213.Lib.Math.NumberTheory.DivisorMultiplicative
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.NatRing213
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.PolyNatMTactic

/-!
# τ(n) odd ⟺ n is a perfect square  (∅-axiom, Route A: involution/pairing)

`tau n = Σ_{d∣n} 1` (corpus def, `SumOfDivisors.tau`).  The classical pairing
`d ↦ n/d` on divisors pairs them up; the unique fixed point is `d = √n`, which
exists iff `n` is a perfect square.  Hence `tau n` is odd ⟺ `n` is a square.

Formalized via a **symmetric double-sum parity** core: for a symmetric weight
`g a b = g b a`, the full `N×N` double sum is congruent mod 2 to its diagonal
`Σ_a g a a`.  We then identify `tau n` with the ordered-factorization double sum
`Σ_{a<n}Σ_{b<n} [ (a+1)(b+1) = n ]` and read the diagonal as the square indicator.
-/

namespace E213.Lib.Math.NumberTheory.TauParity

open E213.Lib.Math.NumberTheory.SumOfDivisors (tau)
open E213.Lib.Math.NumberTheory.EulerTotient (divisorSum dvdInd)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_zero sumTo_succ)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
  (sumTo_congr sumTo_add_func)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod)

/-! ## §1 — mod-2 helpers -/

/-- `(x + x) % 2 = 0`. -/
theorem two_mul_mod_two (x : Nat) : (x + x) % 2 = 0 := by
  have : x + x = 2 * x := by rw [Nat.two_mul]
  rw [this]
  exact E213.Meta.Nat.NatDiv213.mul_mod_self_pure 2 x

/-- `(a + (x + x)) % 2 = a % 2`: an even addend drops out mod 2. -/
theorem add_two_mul_mod_two (a x : Nat) : (a + (x + x)) % 2 = a % 2 := by
  rw [add_mod_gen a (x + x) 2, two_mul_mod_two x, Nat.add_zero, mod_mod a 2]

/-! ## §2 — symmetric double-sum parity (the involution core) -/

/-- The full `N×N` double sum `Σ_{a<N} Σ_{b<N} g a b`. -/
def doubleSum (N : Nat) (g : Nat → Nat → Nat) : Nat :=
  sumTo N (fun a => sumTo N (fun b => g a b))

/-- The diagonal `Σ_{a<N} g a a`. -/
def diagSum (N : Nat) (g : Nat → Nat → Nat) : Nat :=
  sumTo N (fun a => g a a)

/-- Expanding the last row+column: `doubleSum (N+1) g` is the smaller block plus
    the `N`-th column (over old rows), plus the `N`-th row (over all columns). -/
theorem doubleSum_succ (N : Nat) (g : Nat → Nat → Nat) :
    doubleSum (N + 1) g
      = doubleSum N g
        + sumTo N (fun a => g a N)
        + (sumTo N (fun b => g N b) + g N N) := by
  show sumTo (N + 1) (fun a => sumTo (N + 1) (fun b => g a b))
      = sumTo N (fun a => sumTo N (fun b => g a b))
        + sumTo N (fun a => g a N)
        + (sumTo N (fun b => g N b) + g N N)
  rw [sumTo_succ N (fun a => sumTo (N + 1) (fun b => g a b))]
  -- last row: sumTo (N+1) (fun b => g N b) = sumTo N (..) + g N N
  rw [show sumTo (N + 1) (fun b => g N b) = sumTo N (fun b => g N b) + g N N from
        sumTo_succ N (fun b => g N b)]
  -- each old row a: sumTo (N+1) (fun b => g a b) = sumTo N (fun b => g a b) + g a N
  rw [sumTo_congr N (fun a => sumTo (N + 1) (fun b => g a b))
        (fun a => sumTo N (fun b => g a b) + g a N)
        (fun a _ => sumTo_succ N (fun b => g a b))]
  -- now split the outer sum of (rowblock a + g a N) into two sums
  rw [← sumTo_add_func N (fun a => sumTo N (fun b => g a b)) (fun a => g a N)]

/-- ★★ **Symmetric double-sum parity**: for a symmetric weight,
    `doubleSum N g ≡ diagSum N g (mod 2)`.  The off-diagonal pairs `(a,b)`/`(b,a)`
    cancel in pairs (each contributes `g a b` twice). -/
theorem doubleSum_parity (g : Nat → Nat → Nat) (hsymm : ∀ a b, g a b = g b a) :
    ∀ N, doubleSum N g % 2 = diagSum N g % 2
  | 0 => rfl
  | N + 1 => by
    rw [doubleSum_succ N g]
    -- the two cross terms are equal by symmetry
    have hcross : sumTo N (fun a => g a N) = sumTo N (fun b => g N b) :=
      sumTo_congr N _ _ (fun a _ => hsymm a N)
    rw [hcross]
    -- goal: (doubleSum N g + C + (C + g N N)) % 2 = diagSum (N+1) g % 2
    --       where C = sumTo N (fun b => g N b)
    -- rearrange:  doubleSum N g + g N N + (C + C)
    have hrearr :
        doubleSum N g + sumTo N (fun b => g N b)
          + (sumTo N (fun b => g N b) + g N N)
        = (doubleSum N g + g N N)
          + (sumTo N (fun b => g N b) + sumTo N (fun b => g N b)) := by
      ring_nat
    rw [hrearr, add_two_mul_mod_two (doubleSum N g + g N N) (sumTo N (fun b => g N b))]
    -- now: (doubleSum N g + g N N) % 2 = diagSum (N+1) g % 2
    rw [add_mod_gen (doubleSum N g) (g N N) 2,
        doubleSum_parity g hsymm N]
    rw [← add_mod_gen (diagSum N g) (g N N) 2]
    show (diagSum N g + g N N) % 2 = (sumTo N (fun a => g a a) + g N N) % 2
    rfl

/-! ## §3 — τ(n) as the ordered-factorization double sum -/

open E213.Lib.Math.NumberTheory.GaussTotient (eqInd eqInd_self eqInd_ne mul_div_of_dvd)
open E213.Lib.Math.NumberTheory.DivisorProductReindex (sum_eqInd_weight_eq)
open E213.Lib.Math.NumberTheory.DivisorMultiplicative
  (dvdInd_eq_one_iff dvdInd_eq_zero_iff dvdInd_zero_or_one)

/-- The ordered-factorization weight: `1` iff `(a+1)·(b+1) = n`. -/
def factInd (n a b : Nat) : Nat := eqInd ((a + 1) * (b + 1)) n

/-- `factInd` is symmetric in its two index arguments (commutativity of `×`). -/
theorem factInd_symm (n a b : Nat) : factInd n a b = factInd n b a := by
  show eqInd ((a + 1) * (b + 1)) n = eqInd ((b + 1) * (a + 1)) n
  rw [Nat.mul_comm (a + 1) (b + 1)]

/-- **Inner-row collapse**: for `a < n` with `(a+1) ∣ n`, exactly one `b < n` gives
    a factorization, namely the cofactor `b + 1 = n/(a+1)`.  So the row sums to `1`. -/
theorem inner_dvd {a n : Nat} (hn : 0 < n) (hdvd : (a + 1) ∣ n) :
    sumTo n (fun b => factInd n a b) = 1 := by
  have hcof : (a + 1) * (n / (a + 1)) = n := mul_div_of_dvd hdvd
  -- abbreviate the cofactor as q
  let q := n / (a + 1)
  have hcofq : (a + 1) * q = n := hcof
  -- q ≥ 1 (else n = 0)
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · exfalso; rw [h0, Nat.mul_zero] at hcofq; exact absurd hcofq.symm (Nat.ne_of_gt hn)
    · exact hpos
  -- witness W := q - 1, so W + 1 = q
  let W := q - 1
  have hW1 : W + 1 = q := E213.Meta.Nat.NatRing213.nat_sub_add_cancel hq1
  -- W < n
  have hWn : W < n := by
    rw [← hcofq]
    have hWlt : W < W + 1 := Nat.lt_succ_self W
    have h1le : 1 ≤ a + 1 := Nat.succ_le_succ (Nat.zero_le a)
    calc W < W + 1 := hWlt
      _ = q := hW1
      _ = 1 * q := (Nat.one_mul q).symm
      _ ≤ (a + 1) * q := Nat.mul_le_mul h1le (Nat.le_refl q)
  -- pointwise: factInd n a b = eqInd W b
  have hpt : ∀ b, b < n → factInd n a b = eqInd W b := by
    intro b _
    show eqInd ((a + 1) * (b + 1)) n = eqInd W b
    by_cases hb : b = W
    · subst hb
      rw [hW1, hcofq, eqInd_self, eqInd_self]
    · have hne1 : (a + 1) * (b + 1) ≠ n := by
        intro he
        -- from (a+1)*(b+1) = n = (a+1)*q  get  b+1 = q  hence b = W
        have heq : (a + 1) * (b + 1) = (a + 1) * q := by rw [he, hcofq]
        have hb1q : b + 1 = q := E213.Tactic.NatHelper.mul_left_cancel_pos (Nat.succ_pos a) heq
        have hbW : b + 1 = W + 1 := by rw [hb1q, hW1]
        exact hb (Nat.succ.inj hbW)
      rw [eqInd_ne hne1, eqInd_ne (fun he => hb he.symm)]
  rw [sumTo_congr n (fun b => factInd n a b) (fun b => eqInd W b * 1)
        (fun b hb => (hpt b hb).trans (Nat.mul_one (eqInd W b)).symm)]
  exact sum_eqInd_weight_eq n W 1 hWn

open E213.Lib.Math.NumberTheory.FactorialLcmIdentity (sumTo_const_zero)

/-- **Non-divisor row vanishes**: if `(a+1) ∤ n` no `b` factorizes `n`, so the row is `0`. -/
theorem inner_nondvd {a n : Nat} (hdvd : ¬ (a + 1) ∣ n) :
    sumTo n (fun b => factInd n a b) = 0 := by
  rw [sumTo_congr n (fun b => factInd n a b) (fun _ => 0) (fun b _ => ?_)]
  · exact sumTo_const_zero n
  · show eqInd ((a + 1) * (b + 1)) n = 0
    refine eqInd_ne (fun he => hdvd ?_)
    exact ⟨b + 1, he.symm⟩

/-- **Row = divisor indicator**: each `a`-row of the factorization grid is `dvdInd a n`.
    Cases on the *value* of `dvdInd a n` (decidable on Nat, propext-free), avoiding a
    `by_cases` on the `Dvd` proposition (which leaks propext). -/
theorem inner_eq_dvdInd {a n : Nat} (hn : 0 < n) :
    sumTo n (fun b => factInd n a b) = dvdInd a n := by
  cases dvdInd_zero_or_one a n with
  | inr h1 =>
    rw [inner_dvd hn ((dvdInd_eq_one_iff a n).mp h1), h1]
  | inl h0 =>
    rw [inner_nondvd ((dvdInd_eq_zero_iff a n).mp h0), h0]

/-- ★ **τ as the ordered-factorization double sum**:
    `tau n = doubleSum n (factInd n)` for `0 < n`. -/
theorem tau_eq_doubleSum {n : Nat} (hn : 0 < n) :
    tau n = doubleSum n (factInd n) := by
  show divisorSum n (fun _ => 1) = sumTo n (fun a => sumTo n (fun b => factInd n a b))
  show sumTo n (fun j => dvdInd j n * 1) = sumTo n (fun a => sumTo n (fun b => factInd n a b))
  refine sumTo_congr n _ _ (fun a _ => ?_)
  rw [Nat.mul_one, inner_eq_dvdInd hn]

/-! ## §4 — the diagonal is the perfect-square indicator -/

/-- Strict monotonicity of squaring: `x < y → x*x < y*y`.  PURE via the corpus
    `nat_mul_lt_mul_right` / `Nat.mul_le_mul`. -/
theorem sq_lt_sq {x y : Nat} (h : x < y) : x * x < y * y := by
  have hy : 0 < y := Nat.lt_of_le_of_lt (Nat.zero_le x) h
  have h1 : x * x ≤ y * x := Nat.mul_le_mul (Nat.le_of_lt h) (Nat.le_refl x)
  have h2 : y * x < y * y := E213.Meta.Nat.NatRing213.nat_mul_lt_mul_left hy h
  exact Nat.lt_of_le_of_lt h1 h2

/-- A perfect square `r*r = n` with `0 < n` has a positive root, and the
    witness `a = r - 1` satisfies `(a+1)*(a+1) = n` with `a < n`. -/
theorem diag_square {n : Nat} (hn : 0 < n) (h : ∃ r, r * r = n) :
    diagSum n (factInd n) = 1 := by
  obtain ⟨r, hr⟩ := h
  -- r ≥ 1
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · exfalso; rw [h0, Nat.mul_zero] at hr; exact absurd hr.symm (Nat.ne_of_gt hn)
    · exact hpos
  let a := r - 1
  have ha1 : a + 1 = r := E213.Meta.Nat.NatRing213.nat_sub_add_cancel hr1
  have hsq : (a + 1) * (a + 1) = n := by rw [ha1]; exact hr
  -- a < n : a < a+1 = r ≤ r*r = n
  have han : a < n := by
    have h1 : a < a + 1 := Nat.lt_succ_self a
    have h2 : r ≤ r * r := by
      calc r = r * 1 := (Nat.mul_one r).symm
        _ ≤ r * r := Nat.mul_le_mul (Nat.le_refl r) hr1
    exact Nat.lt_of_lt_of_le (ha1 ▸ h1) (hr ▸ h2)
  -- pointwise: factInd n c c = eqInd a c  over c < n
  show sumTo n (fun c => factInd n c c) = 1
  have hpt : ∀ c, c < n → factInd n c c = eqInd a c := by
    intro c _
    show eqInd ((c + 1) * (c + 1)) n = eqInd a c
    by_cases hc : c = a
    · subst hc; rw [hsq, eqInd_self, eqInd_self]
    · have hne : (c + 1) * (c + 1) ≠ n := by
        intro he
        -- (c+1)² = n = (a+1)² ⇒ c+1 = a+1 ⇒ c = a
        have heq : (c + 1) * (c + 1) = (a + 1) * (a + 1) := by rw [he, hsq]
        -- c+1 = a+1 by antisymmetry, each ≤ from sq_le_imp on the equal squares
        have hcia : c + 1 = a + 1 :=
          Nat.le_antisymm
            (E213.Meta.Nat.NatRing213.sq_le_imp (c + 1) (a + 1) (Nat.le_of_eq heq))
            (E213.Meta.Nat.NatRing213.sq_le_imp (a + 1) (c + 1) (Nat.le_of_eq heq.symm))
        exact hc (Nat.succ.inj hcia)
      rw [eqInd_ne hne, eqInd_ne (fun he => hc he.symm)]
  rw [sumTo_congr n (fun c => factInd n c c) (fun c => eqInd a c * 1)
        (fun c hc => (hpt c hc).trans (Nat.mul_one (eqInd a c)).symm)]
  exact sum_eqInd_weight_eq n a 1 han

/-- If `n` is **not** a perfect square, the diagonal vanishes. -/
theorem diag_nonsquare {n : Nat} (h : ¬ ∃ r, r * r = n) :
    diagSum n (factInd n) = 0 := by
  show sumTo n (fun c => factInd n c c) = 0
  rw [sumTo_congr n (fun c => factInd n c c) (fun _ => 0) (fun c _ => ?_)]
  · exact sumTo_const_zero n
  · show eqInd ((c + 1) * (c + 1)) n = 0
    refine eqInd_ne (fun he => h ⟨c + 1, he⟩)

/-! ## §4b — constructive square decision (propext/Classical-free) -/

/-- Bounded existence scan: either some `r < B` is a square root of `n`, or none is.
    Constructive recursion on the bound `B` — no `Decidable`/`Classical`. -/
theorem square_scan (n : Nat) : ∀ B, (∃ r, r < B ∧ r * r = n) ∨ (∀ r, r < B → r * r ≠ n)
  | 0 => Or.inr (fun r hr => absurd hr (Nat.not_lt_zero r))
  | B + 1 => by
    cases square_scan n B with
    | inl h => obtain ⟨r, hrB, hr⟩ := h; exact Or.inl ⟨r, Nat.lt_succ_of_lt hrB, hr⟩
    | inr h =>
      cases Nat.decEq (B * B) n with
      | isTrue heq => exact Or.inl ⟨B, Nat.lt_succ_self B, heq⟩
      | isFalse hne =>
        refine Or.inr (fun r hr => ?_)
        cases Nat.lt_or_ge r B with
        | inl hlt => exact h r hlt
        | inr hge =>
          have hrB : r = B := Nat.le_antisymm (Nat.le_of_lt_succ hr) hge
          rw [hrB]; exact hne

/-- A square root, if it exists, is `≤ n` (so the scan to `n+1` is exhaustive). -/
theorem root_le {r n : Nat} (hr : r * r = n) : r < n + 1 := by
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0; rw [Nat.zero_mul] at hr; subst hr; exact Nat.zero_lt_one
  · have : r ≤ r * r := by
      calc r = r * 1 := (Nat.mul_one r).symm
        _ ≤ r * r := Nat.mul_le_mul (Nat.le_refl r) hpos
    exact Nat.lt_succ_of_le (hr ▸ this)

/-- ★ **Constructive square dichotomy**: every `n` either is a perfect square (with an
    explicit root) or provably is not — built by exhaustive scan, no `Classical`. -/
theorem square_dichotomy (n : Nat) : (∃ r, r * r = n) ∨ (¬ ∃ r, r * r = n) := by
  cases square_scan n (n + 1) with
  | inl h => obtain ⟨r, _, hr⟩ := h; exact Or.inl ⟨r, hr⟩
  | inr h =>
    refine Or.inr (fun hex => ?_)
    obtain ⟨r, hr⟩ := hex
    exact h r (root_le hr) hr

/-! ## §5 — ★★★ the divisor-count parity theorem -/

/-- `tau n % 2 = diagSum n (factInd n) % 2`: τ's parity is the diagonal's parity. -/
theorem tau_mod_two_eq_diag {n : Nat} (hn : 0 < n) :
    tau n % 2 = diagSum n (factInd n) % 2 := by
  rw [tau_eq_doubleSum hn]
  exact doubleSum_parity (factInd n) (factInd_symm n) n

/-- ★★★ **Divisor-count parity**: `τ(n)` is **odd** exactly when `n` is a
    **perfect square** (`0 < n`).

    Proof (Route A, involution/pairing — no factorization): `tau n` equals the
    ordered-factorization double sum `Σ_{a,b<n} [(a+1)(b+1)=n]` (`tau_eq_doubleSum`);
    the weight is symmetric in `a,b` (commutativity of `×`), so by the symmetric
    double-sum parity (`doubleSum_parity`) `τ(n)` is congruent mod 2 to the diagonal
    `Σ_{a<n} [(a+1)² = n]`.  Squaring is strictly monotone, so the diagonal is `1`
    when `n` is a square (unique root `√n`) and `0` otherwise. -/
theorem tau_odd_iff_square {n : Nat} (hn : 0 < n) :
    (tau n % 2 = 1) ↔ ∃ r, r * r = n := by
  rw [tau_mod_two_eq_diag hn]
  constructor
  · intro h
    cases square_dichotomy n with
    | inl hsq => exact hsq
    | inr hsq => exfalso; rw [diag_nonsquare hsq] at h; exact Nat.noConfusion h
  · intro h
    rw [diag_square hn h]

/-! ## §6 — smokes -/

/-- The squares in `1..16` are exactly `1, 4, 9, 16`, read off via `tau_odd_iff_square`
    composed with the corpus `tau` table.  (`decide` on closed numerics, axiom-clean.) -/
theorem tau_parity_smoke :
    tau 1 % 2 = 1 ∧ tau 4 % 2 = 1 ∧ tau 9 % 2 = 1 ∧ tau 16 % 2 = 1
    ∧ tau 2 % 2 = 0 ∧ tau 3 % 2 = 0 ∧ tau 6 % 2 = 0 ∧ tau 12 % 2 = 0 := by
  decide

/-- The square witnesses, via the theorem: `τ(r*r)` is odd for every `r ≥ 1`. -/
theorem tau_square_odd (r : Nat) (hr : 0 < r) : tau (r * r) % 2 = 1 :=
  (tau_odd_iff_square (Nat.mul_pos hr hr)).mpr ⟨r, rfl⟩

end E213.Lib.Math.NumberTheory.TauParity
