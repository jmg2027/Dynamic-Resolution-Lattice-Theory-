import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Lib.Math.NumberTheory.PolyRoot.ResidueList
import E213.Lib.Math.Combinatorics.Pigeonhole
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.PolyNatMTactic

/-!
# FourSquareSeed — the additive pigeonhole `∃ x y, p ∣ x²+y²+1` (Pillar I of four-square)

The seed of Lagrange's four-square theorem, and the repo's first use of an **additive**
pigeonhole (vs the multiplicative Lagrange-root bound of `PolyRoot.RootBound`).  For an odd
prime `p = 2m+1`, the `m+1` squares `{x² mod p : 0 ≤ x ≤ m}` are pairwise distinct
(`sq_distinct`), and so are the `m+1` values `{(p−1−y²) mod p}`; together `p+1 > p` values in
`Fin p`, so two coincide — necessarily across the two families, giving `x² ≡ −1−y²`, i.e.
`p ∣ x²+y²+1`.  The witness is produced **constructively** by a bounded 2-D search whose
`none`-branch is refuted by `Combinatorics.Pigeonhole.no_inj_lt`.

  * `nat_prime_dvd_mul` — `p` prime, `p ∣ a·b` ⟹ `p ∣ a ∨ p ∣ b` (∅-axiom).
  * `sq_distinct` — squares are injective on `[0,m]` mod `p` (`2m < p`).
  * `gval` / `gval_inj_or_seed` — the `Fin (p+1) → Fin p` pigeonhole map; a collision is either
    a forced index-equality or the seed.
  * ★★★★ `four_square_seed` — `p` prime, `p = 2m+1` ⟹ `∃ x y, x ≤ m ∧ y ≤ m ∧ p ∣ x²+y²+1`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.FourSquareSeed

open E213.Lib.Math.NumberTheory.PolyRoot (mod_eq_imp_dvd_sub int_dvd_to_nat)
open E213.Lib.Math.NumberTheory.ModArith.MarkovPrimeFactor (prime_coprime euclid_of_coprime)
open E213.Meta.Nat.Gcd213 (gcd213_comm)
open E213.Tactic.NatHelper
  (gcd213 sub_add_cancel add_sub_cancel_right mul_mod_right sub_sub_self le_sub_of_add_le)
open E213.Tactic.Pow213 (le_of_dvd_pos)
open E213.Meta.Nat.AddMod213 (div_add_mod)
open E213.Lib.Math.Combinatorics.Pigeonhole (no_inj_lt)

/-- `(↑(m+n) : ℤ) = ↑m + ↑n`. -/
private theorem ncast_add (m n : Nat) : ((m + n : Nat) : Int) = (m : Int) + (n : Int) := rfl

/-- `b ≤ a` ⟹ `(↑(a−b) : ℤ) = ↑a − ↑b`. -/
theorem natCast_sub {a b : Nat} (h : b ≤ a) : ((a - b : Nat) : Int) = (a : Int) - (b : Int) := by
  have hab : a - b + b = a := sub_add_cancel h
  have hc : ((a - b : Nat) : Int) + (b : Int) = (a : Int) := by rw [← ncast_add, hab]
  rw [← hc]; ring_intZ

/-- `a % p = 0 ⟹ p ∣ a`. -/
theorem dvd_of_mod_zero (a p : Nat) (h : a % p = 0) : p ∣ a := by
  have hdm := div_add_mod a p
  rw [h, Nat.add_zero] at hdm
  exact ⟨a / p, hdm.symm⟩

/-- `p ∣ a ⟹ a % p = 0`. -/
theorem mod_zero_of_dvd (a p : Nat) (h : p ∣ a) : a % p = 0 := by
  obtain ⟨k, hk⟩ := h
  rw [hk]; exact mul_mod_right p k

/-- `p` prime, `p ∣ a·b` ⟹ `p ∣ a ∨ p ∣ b` (∅-axiom Euclid). -/
theorem nat_prime_dvd_mul (p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (a b : Nat) (hab : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  rcases Nat.eq_zero_or_pos (a % p) with ha | ha
  · exact Or.inl (dvd_of_mod_zero a p ha)
  · right
    have hnp : ¬ p ∣ a := by
      intro hd; rw [mod_zero_of_dvd a p hd] at ha; exact Nat.lt_irrefl 0 ha
    have hco : gcd213 a p = 1 := by rw [gcd213_comm]; exact prime_coprime p a hpr hnp
    exact euclid_of_coprime a b p hp hco hab

/-- ★★★ **Squares are injective on `[0, m]` modulo `p`** (for `2m < p`).  `x²≡x'²` ⟹
    `p ∣ (x−x')(x+x')`; both factors are `< p`, so (Euclid) one is `0`, forcing `x = x'`. -/
theorem sq_distinct (p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (h2m : 2 * m < p) :
    ∀ x x', x ≤ m → x' ≤ m → x * x % p = x' * x' % p → x = x' := by
  have hmp : m < p := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left m (by decide)) h2m
  have key : ∀ x x', x' ≤ x → x ≤ m → x * x % p = x' * x' % p → x = x' := by
    intro x x' hle hxm heq
    have hxx : x' * x' ≤ x * x := Nat.mul_le_mul hle hle
    have hdvdI : (p : Int) ∣ ((x * x : Nat) : Int) - ((x' * x' : Nat) : Int) :=
      mod_eq_imp_dvd_sub _ _ p heq
    rw [← natCast_sub hxx] at hdvdI
    have hdvdN : p ∣ (x * x - x' * x') := by
      have := int_dvd_to_nat p _ hdvdI
      rwa [Int.natAbs_ofNat] at this
    obtain ⟨d, hd⟩ : ∃ d, x = d + x' := ⟨x - x', (sub_add_cancel hle).symm⟩
    have hfact : x * x - x' * x' = (x - x') * (x + x') := by
      rw [hd, add_sub_cancel_right]
      have hk : (d + x') * (d + x') = d * ((d + x') + x') + x' * x' := by ring_nat
      rw [hk, add_sub_cancel_right]
    rw [hfact] at hdvdN
    rcases nat_prime_dvd_mul p hp hpr _ _ hdvdN with hd1 | hd2
    · rcases Nat.eq_zero_or_pos (x - x') with hz | hpos
      · exact Nat.le_antisymm (Nat.le_of_sub_eq_zero hz) hle
      · exfalso
        have hlt : x - x' < p := Nat.lt_of_le_of_lt (Nat.le_trans (Nat.sub_le x x') hxm) hmp
        exact absurd (le_of_dvd_pos p (x - x') hpos hd1) (Nat.not_le.mpr hlt)
    · rcases Nat.eq_zero_or_pos (x + x') with hz | hpos
      · have hx0 : x = 0 :=
          Nat.le_zero.mp (Nat.le_trans (Nat.le_add_right x x') (Nat.le_of_eq hz))
        have hx'0 : x' = 0 :=
          Nat.le_zero.mp (Nat.le_trans (Nat.le_add_left x' x) (Nat.le_of_eq hz))
        rw [hx0, hx'0]
      · exfalso
        have h2m' : m + m < p := by rw [← Nat.two_mul]; exact h2m
        have hlt : x + x' < p :=
          Nat.lt_of_le_of_lt (Nat.add_le_add hxm (Nat.le_trans hle hxm)) h2m'
        exact absurd (le_of_dvd_pos p (x + x') hpos hd2) (Nat.not_le.mpr hlt)
  intro x x' hxm hx'm heq
  rcases Nat.le_total x' x with h | h
  · exact key x x' h hxm heq
  · exact (key x' x h hx'm heq.symm).symm

/-- `c − a = c − b`, `a, b ≤ c` ⟹ `a = b`. -/
theorem sub_left_cancel_le (c a b : Nat) (ha : a ≤ c) (hb : b ≤ c) (h : c - a = c - b) : a = b := by
  rw [← sub_sub_self ha, ← sub_sub_self hb, h]

/-- `x²%p + y²%p = p−1` ⟹ `p ∣ (x²+y²+1)`. -/
theorem seed_dvd (p x y : Nat) (hp : 1 < p)
    (hsum : x * x % p + y * y % p = p - 1) : p ∣ (x * x + y * y + 1) := by
  have hA : x * x = p * (x * x / p) + (x * x % p) := (div_add_mod (x * x) p).symm
  have hB : y * y = p * (y * y / p) + (y * y % p) := (div_add_mod (y * y) p).symm
  generalize x * x / p = A at hA
  generalize y * y / p = B at hB
  generalize x * x % p = r1 at hA hsum
  generalize y * y % p = r2 at hB hsum
  refine ⟨A + B + 1, ?_⟩
  have hp1 : (p - 1) + 1 = p := sub_add_cancel (Nat.le_of_lt hp)
  rw [hA, hB]
  have hrw : p * A + r1 + (p * B + r2) + 1 = p * A + p * B + (r1 + r2 + 1) := by ring_nat
  rw [hrw, hsum, hp1]; ring_nat

/-! ## §2 — the pigeonhole map and the constructive search -/

/-- The pigeonhole value map: `x²%p` on `[0,m]`, `p−1−y²%p` on `(m, 2m+1]`. -/
def gval (p m i : Nat) : Nat :=
  if i ≤ m then (i * i) % p else p - 1 - ((i - (m + 1)) * (i - (m + 1)) % p)

/-- A `gval`-collision is either an index-equality or the seed. -/
theorem gval_inj_or_seed (p m a b : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hpm : 2 * m + 1 = p) (hab : a < 2 * m + 2) (hbb : b < 2 * m + 2)
    (heq : gval p m a = gval p m b) :
    a = b ∨ ∃ x y, x ≤ m ∧ y ≤ m ∧ p ∣ (x * x + y * y + 1) := by
  have hp0 : 0 < p := Nat.lt_trans (by decide) hp
  have h2m : 2 * m < p := by rw [← hpm]; exact Nat.lt_succ_self _
  have hsub : 2 * m + 1 - (m + 1) = m := by
    have e : 2 * m + 1 = m + (m + 1) := by ring_nat
    rw [e, add_sub_cancel_right]
  have ha1 : a ≤ 2 * m + 1 := Nat.le_of_lt_succ hab
  have hb1 : b ≤ 2 * m + 1 := Nat.le_of_lt_succ hbb
  have yle : ∀ z, z ≤ 2 * m + 1 → z - (m + 1) ≤ m := fun z hz => by
    have := Nat.sub_le_sub_right hz (m + 1); rwa [hsub] at this
  have modle : ∀ z, z * z % p ≤ p - 1 := fun z => le_sub_of_add_le (Nat.mod_lt _ hp0)
  by_cases ha : a ≤ m <;> by_cases hb : b ≤ m
  · left
    rw [gval, gval, if_pos ha, if_pos hb] at heq
    exact sq_distinct p m hp hpr h2m a b ha hb heq
  · right
    rw [gval, gval, if_pos ha, if_neg hb] at heq
    have hsum : a * a % p + (b - (m + 1)) * (b - (m + 1)) % p = p - 1 := by
      rw [heq]; exact sub_add_cancel (modle (b - (m + 1)))
    exact ⟨a, b - (m + 1), ha, yle b hb1, seed_dvd p a (b - (m + 1)) hp hsum⟩
  · right
    rw [gval, gval, if_neg ha, if_pos hb] at heq
    have hsum : b * b % p + (a - (m + 1)) * (a - (m + 1)) % p = p - 1 := by
      rw [← heq]; exact sub_add_cancel (modle (a - (m + 1)))
    exact ⟨b, a - (m + 1), hb, yle a ha1, seed_dvd p b (a - (m + 1)) hp hsum⟩
  · left
    rw [gval, gval, if_neg ha, if_neg hb] at heq
    have hya : a - (m + 1) = b - (m + 1) :=
      sq_distinct p m hp hpr h2m _ _ (yle a ha1) (yle b hb1)
        (sub_left_cancel_le (p - 1) _ _ (modle _) (modle _) heq)
    have ea : a - (m + 1) + (m + 1) = a := sub_add_cancel (Nat.lt_of_not_le ha)
    have eb : b - (m + 1) + (m + 1) = b := sub_add_cancel (Nat.lt_of_not_le hb)
    rw [← ea, ← eb, hya]

/-- Search `y ∈ [0, bound]` for `(x²+y²+1) % p = 0`. -/
def findY (p x : Nat) : Nat → Option Nat
  | 0 => if (x * x + 0 * 0 + 1) % p = 0 then some 0 else none
  | y + 1 => if (x * x + (y + 1) * (y + 1) + 1) % p = 0 then some (y + 1) else findY p x y

theorem findY_some (p x : Nat) : ∀ bound y, findY p x bound = some y →
    y ≤ bound ∧ (x * x + y * y + 1) % p = 0 := by
  intro bound
  induction bound with
  | zero =>
    intro y h; rw [findY] at h
    rcases Nat.eq_zero_or_pos ((x * x + 0 * 0 + 1) % p) with hc | hc
    · rw [if_pos hc] at h; injection h with h; subst h; exact ⟨Nat.le_refl 0, hc⟩
    · rw [if_neg (Nat.pos_iff_ne_zero.mp hc)] at h; exact Option.noConfusion h
  | succ b ih =>
    intro y h; rw [findY] at h
    rcases Nat.eq_zero_or_pos ((x * x + (b + 1) * (b + 1) + 1) % p) with hc | hc
    · rw [if_pos hc] at h; injection h with h; subst h; exact ⟨Nat.le_refl _, hc⟩
    · rw [if_neg (Nat.pos_iff_ne_zero.mp hc)] at h
      obtain ⟨hy, hm⟩ := ih y h; exact ⟨Nat.le_succ_of_le hy, hm⟩

theorem findY_none (p x : Nat) : ∀ bound, findY p x bound = none →
    ∀ y, y ≤ bound → (x * x + y * y + 1) % p ≠ 0 := by
  intro bound
  induction bound with
  | zero =>
    intro h y hy; rw [findY] at h
    rcases Nat.eq_zero_or_pos ((x * x + 0 * 0 + 1) % p) with hc | hc
    · rw [if_pos hc] at h; exact Option.noConfusion h
    · rw [Nat.le_zero.mp hy]; exact Nat.pos_iff_ne_zero.mp hc
  | succ b ih =>
    intro h y hy; rw [findY] at h
    rcases Nat.eq_zero_or_pos ((x * x + (b + 1) * (b + 1) + 1) % p) with hc | hc
    · rw [if_pos hc] at h; exact Option.noConfusion h
    · rw [if_neg (Nat.pos_iff_ne_zero.mp hc)] at h
      rcases Nat.lt_or_eq_of_le hy with hlt | heq
      · exact ih h y (Nat.le_of_lt_succ hlt)
      · subst heq; exact Nat.pos_iff_ne_zero.mp hc

/-- Search `x ∈ [0, bound]`, each with a `y ∈ [0, m]` search. -/
def findXY (p m : Nat) : Nat → Option (Nat × Nat)
  | 0 => match findY p 0 m with | some y => some (0, y) | none => none
  | x + 1 => match findY p (x + 1) m with | some y => some (x + 1, y) | none => findXY p m x

theorem findXY_some (p m : Nat) : ∀ bound x y, findXY p m bound = some (x, y) →
    x ≤ bound ∧ y ≤ m ∧ (x * x + y * y + 1) % p = 0 := by
  intro bound
  induction bound with
  | zero =>
    intro x y h; rw [findXY] at h
    cases hfy : findY p 0 m with
    | some yy =>
      rw [hfy] at h; injection h with h; injection h with hx hy; subst hx; subst hy
      exact ⟨Nat.le_refl 0, (findY_some p 0 m yy hfy).1, (findY_some p 0 m yy hfy).2⟩
    | none => rw [hfy] at h; exact Option.noConfusion h
  | succ b ih =>
    intro x y h; rw [findXY] at h
    cases hfy : findY p (b + 1) m with
    | some yy =>
      rw [hfy] at h; injection h with h; injection h with hx hy; subst hx; subst hy
      exact ⟨Nat.le_refl _, (findY_some p (b + 1) m yy hfy).1, (findY_some p (b + 1) m yy hfy).2⟩
    | none =>
      rw [hfy] at h; obtain ⟨hx, hy, hm⟩ := ih x y h
      exact ⟨Nat.le_succ_of_le hx, hy, hm⟩

theorem findXY_none (p m : Nat) : ∀ bound, findXY p m bound = none →
    ∀ x, x ≤ bound → ∀ y, y ≤ m → (x * x + y * y + 1) % p ≠ 0 := by
  intro bound
  induction bound with
  | zero =>
    intro h x hx y hy; rw [findXY] at h
    cases hfy : findY p 0 m with
    | some yy => rw [hfy] at h; exact Option.noConfusion h
    | none => rw [Nat.le_zero.mp hx]; exact findY_none p 0 m hfy y hy
  | succ b ih =>
    intro h x hx y hy; rw [findXY] at h
    cases hfy : findY p (b + 1) m with
    | some yy => rw [hfy] at h; exact Option.noConfusion h
    | none =>
      rw [hfy] at h
      rcases Nat.lt_or_eq_of_le hx with hlt | heq
      · exact ih h x (Nat.le_of_lt_succ hlt) y hy
      · subst heq; exact findY_none p (b + 1) m hfy y hy

/-- ★★★★ **The four-square seed.**  For an odd prime `p = 2m+1`,
    `∃ x y, x ≤ m ∧ y ≤ m ∧ p ∣ (x²+y²+1)` — produced constructively by `findXY`, its
    `none`-branch refuted by the additive pigeonhole (`no_inj_lt` on `gval`). -/
theorem four_square_seed (p m : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (hpm : 2 * m + 1 = p) : ∃ x y, x ≤ m ∧ y ≤ m ∧ p ∣ (x * x + y * y + 1) := by
  cases hf : findXY p m m with
  | some w =>
    obtain ⟨x, y⟩ := w
    obtain ⟨hx, hy, hmod⟩ := findXY_some p m m x y hf
    exact ⟨x, y, hx, hy, dvd_of_mod_zero _ p hmod⟩
  | none =>
    exfalso
    have hall := findXY_none p m m hf
    have hlt : p < 2 * m + 2 := by rw [← hpm]; exact Nat.lt_succ_self _
    have hp0 : 0 < p := Nat.lt_trans (by decide) hp
    have gbound : ∀ i : Fin (2 * m + 2), gval p m i.val < p := by
      intro i; unfold gval
      by_cases h : i.val ≤ m
      · rw [if_pos h]; exact Nat.mod_lt _ hp0
      · rw [if_neg h]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.sub_lt hp0 (by decide))
    refine no_inj_lt hlt (fun i => ⟨gval p m i.val, gbound i⟩) ?_
    intro i j hij heq
    have hgeq : gval p m i.val = gval p m j.val := congrArg Fin.val heq
    rcases gval_inj_or_seed p m i.val j.val hp hpr hpm i.isLt j.isLt hgeq with hval | ⟨x, y, hx, hy, hdvd⟩
    · exact hij (Fin.ext hval)
    · exact hall x hx y hy (mod_zero_of_dvd _ p hdvd)

end E213.Lib.Math.NumberTheory.FourSquareSeed
