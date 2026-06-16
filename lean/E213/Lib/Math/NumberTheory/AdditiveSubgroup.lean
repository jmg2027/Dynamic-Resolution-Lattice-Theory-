import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.NatDiv213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.Valuation
import E213.Meta.Tactic.NatHelper
import E213.Meta.Tactic.Pow213
import E213.Lib.Math.NumberTheory.Lcm213

/-!
# The additive subgroup structure of `ℤ/n` on representatives (∅-axiom)

**Forcing (vein A).**  Classically the subgroups of the additive group `ℤ/n` are
subgroups of a *quotient group*, and the lattice isomorphism "subgroups ↔
divisors of `n`" is an abstract order-iso.  With **no quotient / no abstract
group**, a subgroup is an explicit set of residues `{ (k·d) % n : k }`, its
generator is `gcd(d,n)` (computed), and its order is `n / gcd(d,n)` (computed).
The subgroup-divisor correspondence is literally `d ↦ gcd(d,n)` (generator) and
`e ↦ n/e` (order).  **The subgroup lattice of `ℤ/n` IS the divisor lattice of
`n`, realized by gcd; the quotient group was packaging.**

The load-bearing step is `n ∣ t·d ⟺ (n/g) ∣ t` (with `g = gcd(d,n)`): cancel
`g` from `g·(n/g) ∣ t·g·(d/g)` to get `(n/g) ∣ t·(d/g)`, then strip the coprime
`(d/g)` (`gcd(n/g, d/g) = 1`) to land at `(n/g) ∣ t`.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.AdditiveSubgroup

open E213.Tactic.NatHelper (gcd213)
open E213.Meta.Nat.Gcd213
  (gcd213_dvd_left gcd213_dvd_right gcd213_greatest gcd213_comm
   coprime_dvd_of_dvd_mul mul_assoc_213)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Meta.Nat.Valuation (mod_zero_of_dvd)
open E213.Lib.Math.NumberTheory.Lcm213 (gcd_div_coprime mul_div_cancel_of_dvd gcd_pos)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-! ## §1 — the additive orbit, generator, and order -/

/-- The additive cyclic subgroup `⟨d⟩` in `ℤ/n` as the **concrete orbit**:
    `addOrbit n d k = (k·d) % n`. -/
def addOrbit (n d k : Nat) : Nat := (k * d) % n

/-- The additive order of `d` mod `n`: `add_order n d = n / gcd(d,n)`.  The least
    `t ≥ 1` with `(t·d) % n = 0` (proven below). -/
def add_order (n d : Nat) : Nat := n / gcd213 d n

/-- `g·a ∣ g·b ⟹ a ∣ b` for `0 < g` (cancel the common factor). -/
theorem dvd_of_mul_dvd_mul_left {g a b : Nat} (hg : 0 < g) (h : g * a ∣ g * b) :
    a ∣ b := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w, Nat.eq_of_mul_eq_mul_left hg (by rw [hw]; exact mul_assoc_213 g a w)⟩

/-! ## §2 — `(t·d) % n = 0 ⟺ (n/g) ∣ t`, the load-bearing equivalence -/

/-- The reduced parts are coprime: `gcd(n/g, d/g) = 1` where `g = gcd(d,n)`. -/
theorem coprime_reduced (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    gcd213 (n / gcd213 d n) (d / gcd213 d n) = 1 := by
  -- gcd_div_coprime n d : gcd213 (n / gcd213 n d) (d / gcd213 n d) = 1
  have hc : gcd213 (n / gcd213 n d) (d / gcd213 n d) = 1 := gcd_div_coprime n d hn hd
  rw [gcd213_comm n d] at hc
  exact hc

/-- `g ∣ d` and `g ∣ n` for `g = gcd(d,n)`, and `0 < g`. -/
theorem gcd_facts (n d : Nat) (hn : 0 < n) :
    gcd213 d n ∣ d ∧ gcd213 d n ∣ n ∧ 0 < gcd213 d n := by
  refine ⟨gcd213_dvd_left d n, gcd213_dvd_right d n, ?_⟩
  rw [gcd213_comm d n]; exact gcd_pos n d hn

/-- ★★★ **`n ∣ t·d ⟺ (n/g) ∣ t`** (`g = gcd(d,n)`, `n,d > 0`).
    The combinatorial heart: divisibility of the orbit step by `n` is exactly
    `(n/g)`-divisibility of the step count. -/
theorem n_dvd_mul_iff (n d t : Nat) (hn : 0 < n) (hd : 0 < d) :
    n ∣ t * d ↔ (n / gcd213 d n) ∣ t := by
  obtain ⟨hgd, hgn, hgpos⟩ := gcd_facts n d hn
  have hcop : gcd213 (n / gcd213 d n) (d / gcd213 d n) = 1 := coprime_reduced n d hn hd
  -- generalize the reduced parts and the gcd to opaque atoms so `ring_nat` applies
  have hng : gcd213 d n * (n / gcd213 d n) = n := mul_div_cancel_of_dvd _ n hgpos hgn
  have hdg : gcd213 d n * (d / gcd213 d n) = d := mul_div_cancel_of_dvd _ d hgpos hgd
  -- abstract:  g·N = n, g·D = d, gcd N D = 1, 0 < g
  revert hcop hng hdg hgpos
  generalize hN : n / gcd213 d n = N
  generalize hD : d / gcd213 d n = D
  generalize hg : gcd213 d n = g
  intro hgpos hcopN hngN hdgD
  constructor
  · intro h
    -- g·N ∣ g·(t·D)   (since t·d = t·(g·D) = g·(t·D), and n = g·N ∣ t·d)
    have h1 : g * N ∣ g * (t * D) := by
      rw [hngN]
      have hrw : g * (t * D) = t * d := by rw [← hdgD]; ring_nat
      rw [hrw]; exact h
    have h2 : N ∣ t * D := dvd_of_mul_dvd_mul_left hgpos h1
    have h3 : N ∣ D * t := by rw [Nat.mul_comm]; exact h2
    exact coprime_dvd_of_dvd_mul hcopN h3
  · intro h
    obtain ⟨c, hc⟩ := h
    refine ⟨c * D, ?_⟩
    -- t·d = (N·c)·(g·D) = (g·N)·(c·D) = n·(c·D)
    calc t * d = (N * c) * d := by rw [← hc]
      _ = (N * c) * (g * D) := by rw [hdgD]
      _ = (g * N) * (c * D) := by ring_nat
      _ = n * (c * D) := by rw [hngN]

/-! ## §3 — ★★★ additive order = `n/gcd`: the step returns to 0, and minimally -/

/-- ★★★ **The order-many step returns to 0**: `((n/g)·d) % n = 0`.
    (`add_order n d = n/g` is a valid additive period.) -/
theorem add_order_smul_zero (n d : Nat) (hn : 0 < n) (hd : 0 < d) :
    (add_order n d * d) % n = 0 := by
  show ((n / gcd213 d n) * d) % n = 0
  apply mod_zero_of_dvd hn
  -- n ∣ (n/g)·d  ⟺  (n/g) ∣ (n/g)  (true)
  exact (n_dvd_mul_iff n d (n / gcd213 d n) hn hd).mpr ⟨1, (Nat.mul_one _).symm⟩

/-- ★★★ **Minimality**: any positive `t` with `(t·d) % n = 0` has `add_order n d ≤ t`.
    Together with `add_order_smul_zero`, the additive order of `d` is `n/gcd(d,n)`. -/
theorem add_order_min (n d : Nat) (hn : 0 < n) (hd : 0 < d)
    {t : Nat} (ht : 0 < t) (h : (t * d) % n = 0) : add_order n d ≤ t := by
  show n / gcd213 d n ≤ t
  have hdvd : n ∣ t * d := dvd_of_mod_eq_zero h
  have hnt : (n / gcd213 d n) ∣ t := (n_dvd_mul_iff n d t hn hd).mp hdvd
  exact le_of_dvd_pos _ _ ht hnt

/-! ## §4 — ★★ the subgroup `⟨d⟩` lies in the multiples of `gcd(d,n)` -/

/-- ★★ **`⟨d⟩ ⊆ ⟨gcd(d,n)⟩`**: every orbit element `(k·d)%n` is `(j·g)%n` for
    `g = gcd(d,n)` (taking `j = k·(d/g)`).  Forward via `d = g·(d/g)`.

    The reverse inclusion `⟨g⟩ ⊆ ⟨d⟩` (so `⟨d⟩ = ⟨g⟩`, "the generator is the
    gcd") requires writing `g` itself as a combination `(k·d)%n` — a Bézout
    identity, a *signed* combination, which is not ∅-axiom over `Nat`.  So the
    set-level "generator is the gcd" is recorded here as the inclusion; the
    load-bearing **order** equality `|⟨d⟩| = n/g = |⟨g⟩|` is §3/§5, where the gcd
    *is* the computed generator at the order level. -/
theorem addOrbit_mem_gcd_multiples (n d k : Nat) (hn : 0 < n) :
    ∃ j, addOrbit n d k = (j * gcd213 d n) % n := by
  refine ⟨k * (d / gcd213 d n), ?_⟩
  show (k * d) % n = (k * (d / gcd213 d n) * gcd213 d n) % n
  obtain ⟨hgd, _, hgpos⟩ := gcd_facts n d hn
  have hdg : gcd213 d n * (d / gcd213 d n) = d := mul_div_cancel_of_dvd _ d hgpos hgd
  have hrw : k * (d / gcd213 d n) * gcd213 d n = k * (gcd213 d n * (d / gcd213 d n)) := by
    ring_nat
  rw [hrw, hdg]

/-! ## §5 — ★★★ subgroup ↔ divisor correspondence -/

/-- For a divisor `e ∣ n`, `gcd(e, n) = e` (since `e ∣ e` and `e ∣ n`, and any
    common divisor of `e, n` divides `e`). -/
theorem gcd_of_dvd (e n : Nat) (he : e ∣ n) : gcd213 e n = e := by
  apply E213.Meta.Nat.Gcd213.dvd_antisymm_213
  · exact gcd213_dvd_left e n
  · exact gcd213_greatest e n e ⟨1, (Nat.mul_one e).symm⟩ he

/-- ★★★ **Subgroup order = `n/e` for a divisor `e ∣ n`**: the cyclic subgroup
    `⟨e⟩` of `ℤ/n` has additive order `n/e`. -/
theorem subgroup_order (n e : Nat) (he : e ∣ n) (hn : 0 < n) :
    add_order n e = n / e := by
  show n / gcd213 e n = n / e
  rw [gcd_of_dvd e n he]

/-- ★★★ **Distinct divisors give distinct subgroups**: for `e₁,e₂ ∣ n` with the
    same additive order (= same subgroup), `e₁ = e₂`.  `n/e₁ = n/e₂ ⟹ e₁ = e₂`
    via `e·(n/e) = n` (cancellation in the positive `n`). -/
theorem divisor_subgroup_inj (n e1 e2 : Nat) (hn : 0 < n)
    (he1 : e1 ∣ n) (he2 : e2 ∣ n) (he1p : 0 < e1) (he2p : 0 < e2)
    (h : add_order n e1 = add_order n e2) : e1 = e2 := by
  rw [subgroup_order n e1 he1 hn, subgroup_order n e2 he2 hn] at h
  -- n/e1 = n/e2, with e1·(n/e1) = n = e2·(n/e2)
  have hc1 : e1 * (n / e1) = n := mul_div_cancel_of_dvd e1 n he1p he1
  have hc2 : e2 * (n / e2) = n := mul_div_cancel_of_dvd e2 n he2p he2
  -- e1·(n/e1) = e2·(n/e2) = e2·(n/e1)  ⟹  e1 = e2
  have heq : e1 * (n / e1) = e2 * (n / e1) := by
    have h2 : e2 * (n / e1) = n := by rw [h]; exact hc2
    rw [hc1, h2]
  have hnpos : 0 < n / e1 := by
    rcases Nat.eq_zero_or_pos (n / e1) with h0 | hp
    · rw [h0, Nat.mul_zero] at hc1; exact absurd hc1 (Nat.ne_of_lt hn)
    · exact hp
  exact Nat.eq_of_mul_eq_mul_right hnpos heq

/-! ## §6 — concrete smokes (n = 12) -/

/-- `⟨3⟩` in `ℤ/12` has additive order `12/3 = 4` and orbit `{0,3,6,9}`. -/
theorem smoke_order_3_12 : add_order 12 3 = 4 := by decide

theorem smoke_orbit_3_12 :
    addOrbit 12 3 0 = 0 ∧ addOrbit 12 3 1 = 3 ∧ addOrbit 12 3 2 = 6 ∧
    addOrbit 12 3 3 = 9 ∧ addOrbit 12 3 4 = 0 := by decide

/-- `⟨4⟩` in `ℤ/12` has additive order `12/4 = 3`. -/
theorem smoke_order_4_12 : add_order 12 4 = 3 := by decide

/-- The generator of `⟨8⟩` is `gcd(8,12) = 4`, so `⟨8⟩ = ⟨4⟩` and both have
    order `3`. -/
theorem smoke_gen_8_12 : gcd213 8 12 = 4 ∧ add_order 12 8 = add_order 12 4 := by decide

/-- The order-many step returns to 0 at `n=12, d=3`: `(4·3) % 12 = 0`. -/
theorem smoke_smul_zero_3_12 : (add_order 12 3 * 3) % 12 = 0 := by decide

end E213.Lib.Math.NumberTheory.AdditiveSubgroup
