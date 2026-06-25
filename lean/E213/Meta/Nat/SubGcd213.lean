import E213.Meta.Nat.SubMod213

/-!
# Structural gcd (Euclidean algorithm on `subMod`) — the FTA-uniqueness seed (∅-axiom)

FTA *uniqueness* needs Euclid's lemma (`p` prime, `p ∣ a·b → p∣a ∨ p∣b`), which the repo proves via
`Gcd213` — but `Gcd213.gcd213` uses `Nat.mod` (verified: `lt_wfRel=true`).  To ground uniqueness the
whole gcd → coprime/Bézout → `prime_dvd_mul` chain must be regrounded onto `SubMod213.subMod` (the
`Nat.mod`-free remainder).  This file is the **first brick**: the structural gcd itself.

`gcdSub fuel a b = gcd(a, b)` by the Euclidean recursion `gcd(a,b) = gcd(b, a mod b)` with the
remainder from `subMod` (repeated subtraction), so it carries no `Nat.mod`.  The divisibility
properties (`gcdSub ∣ a`, `gcdSub ∣ b`, greatest), coprime/Bézout, and Euclid's lemma on top are the
remaining (substantial) work.

∅-axiom; `subMod`-based, no `Nat.mod`/`Nat.div`/`Nat.lt_wfRel`.
-/

namespace E213.Meta.Nat.SubGcd213

open E213.Meta.Nat.SubMod213 (subMod subMod_lt subMod_eq subMod_zero_iff_dvd)

/-- `gcd(a, b)` via the Euclidean recursion `gcd(a,b) = gcd(b, a mod b)`, the remainder by `subMod`
    (repeated subtraction).  Fuel-bounded, structural `Nat.rec` on fuel. -/
def gcdSub : Nat → Nat → Nat → Nat
  | 0,     a, _ => a
  | f + 1, a, b =>
    match b with
    | 0     => a
    | _ + 1 => gcdSub f b (subMod a a b)

/-- `gcd(a, 0) = a` (the search bottoms out). -/
theorem gcdSub_zero_right (fuel a : Nat) : gcdSub (fuel + 1) a 0 = a := rfl

/-- The Euclidean recursion step, `subMod` form: for `b ≥ 1`, `gcd(a, b) = gcd(b, a mod b)`. -/
theorem gcdSub_succ (fuel a b : Nat) :
    gcdSub (fuel + 1) a (b + 1) = gcdSub fuel (b + 1) (subMod a a (b + 1)) := rfl

/-- With ample fuel, `gcdSub` divides its second argument when that is `0` — the base case of the
    divisibility invariant (`gcd(a,0) = a ∣ 0`). -/
theorem gcdSub_dvd_zero (fuel a : Nat) : gcdSub (fuel + 1) a 0 ∣ 0 := ⟨0, rfl⟩

/-! ## §2 — the divisibility property (brick 2) -/

/-- **Lift step**: if `g` divides the modulus `a` and the remainder `subMod b b a` (= `b mod a`), it
    divides `b`.  Immediate from `subMod_eq` (`b = a*q + subMod b b a`) — much shorter than the
    `Nat.mod` version (`Gcd213.g_dvd_b_via_mod`), which needs the mod-subtraction recursion. -/
theorem g_dvd_of_dvd_subMod {g a b : Nat} (hga : g ∣ a) (hgr : g ∣ subMod b b a) : g ∣ b := by
  obtain ⟨q, hq⟩ := subMod_eq b b a          -- b = a * q + subMod b b a
  obtain ⟨s, hs⟩ := hga                       -- a = g * s
  obtain ⟨t, ht⟩ := hgr                       -- subMod b b a = g * t
  refine ⟨s * q + t, ?_⟩
  have e1 : a * q = g * (s * q) := by
    rw [hs]; exact E213.Tactic.NatHelper.mul_assoc g s q
  calc b = a * q + subMod b b a := hq
    _ = g * (s * q) + g * t := by rw [e1, ht]
    _ = g * (s * q + t) := (Nat.mul_add g (s * q) t).symm

/-- ★★★ **`gcdSub n a b` divides both `a` and `b`** (fuel `n ≥ b`, the second argument — the
    Euclidean monovariant).  Mirrors `Gcd213.gcdFuel_dvd_both`, but on `subMod`: the inductive step
    reduces `(a, b'+1)` to `(b'+1, a mod (b'+1))`, applies the IH (`a mod (b'+1) < b'+1 ≤ n`), and
    lifts via `g_dvd_of_dvd_subMod`.  `Nat.mod`-free, ∅-axiom. -/
theorem gcdSub_dvd_both : ∀ (n a b : Nat), b ≤ n → gcdSub n a b ∣ a ∧ gcdSub n a b ∣ b
  | 0,     a, b, hb => by
    have hb0 : b = 0 := Nat.le_antisymm hb (Nat.zero_le b)
    subst hb0
    exact ⟨⟨1, (Nat.mul_one a).symm⟩, ⟨0, rfl⟩⟩
  | f + 1, a, b, hb => by
    match b, hb with
    | 0,      _  => exact ⟨⟨1, (Nat.mul_one a).symm⟩, ⟨0, rfl⟩⟩
    | b' + 1, hb =>
      show gcdSub f (b' + 1) (subMod a a (b' + 1)) ∣ a
            ∧ gcdSub f (b' + 1) (subMod a a (b' + 1)) ∣ (b' + 1)
      have hr_lt : subMod a a (b' + 1) < b' + 1 :=
        subMod_lt a a (b' + 1) (Nat.zero_lt_succ b') (Nat.le_refl a)
      have hr_le_f : subMod a a (b' + 1) ≤ f :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hr_lt hb)
      obtain ⟨hg_b, hg_r⟩ := gcdSub_dvd_both f (b' + 1) (subMod a a (b' + 1)) hr_le_f
      exact ⟨g_dvd_of_dvd_subMod hg_b hg_r, hg_b⟩

/-- **Forward lift**: if `d` divides `a` and `b`, it divides the remainder `subMod a a b` (= `a mod
    b`).  From `subMod_eq` (`a = b*q + subMod a a b`): `subMod a a b = a − b*q`, and `d ∣ a`,
    `d ∣ b*q` give `d ∣ a − b*q` (`Nat.dvd_sub'`).  The companion to `g_dvd_of_dvd_subMod`. -/
theorem dvd_subMod_of_dvd {d a b : Nat} (hda : d ∣ a) (hdb : d ∣ b) : d ∣ subMod a a b := by
  obtain ⟨q, hq⟩ := subMod_eq a a b              -- a = b * q + subMod a a b
  obtain ⟨x, hx⟩ := hda                          -- a = d * x
  obtain ⟨y, hy⟩ := hdb                          -- b = d * y
  have hr : a - b * q = subMod a a b :=
    (congrArg (· - b * q) hq).trans
      ((congrArg (· - b * q) (Nat.add_comm (b * q) (subMod a a b))).trans
        (E213.Tactic.NatHelper.add_sub_cancel_right (subMod a a b) (b * q)))
  -- subMod a a b = a − b*q = d*x − (d*y)*q = d*(x − y*q)
  refine ⟨x - y * q, ?_⟩
  rw [← hr, hx, hy, E213.Tactic.NatHelper.mul_assoc, ← E213.Tactic.NatHelper.mul_sub]

/-- ★★★ **`gcdSub n a b` is divisible by every common divisor** (the *greatest* half of gcd; fuel
    `n ≥ b`).  Mirrors `gcdSub_dvd_both`: the step `(a, b'+1) → (b'+1, a mod (b'+1))` keeps `d ∣
    (b'+1)` and gains `d ∣ a mod (b'+1)` (`dvd_subMod_of_dvd`), then recurses.  `Nat.mod`-free,
    ∅-axiom. -/
theorem gcdSub_greatest : ∀ (n a b d : Nat), b ≤ n → d ∣ a → d ∣ b → d ∣ gcdSub n a b
  | 0,     a, b, d, _,  hda, _   => hda
  | f + 1, a, b, d, hb, hda, hdb => by
    match b, hb, hdb with
    | 0,      _,  _   => exact hda
    | b' + 1, hb, hdb =>
      show d ∣ gcdSub f (b' + 1) (subMod a a (b' + 1))
      have hr_lt : subMod a a (b' + 1) < b' + 1 :=
        subMod_lt a a (b' + 1) (Nat.zero_lt_succ b') (Nat.le_refl a)
      have hr_le_f : subMod a a (b' + 1) ≤ f :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hr_lt hb)
      exact gcdSub_greatest f (b' + 1) (subMod a a (b' + 1)) d hr_le_f hdb
        (dvd_subMod_of_dvd hda hdb)

/-! ## §3 — the gcd wrapper + coprimality (brick 3) -/

/-- **The gcd, fuel discharged.**  `gcdW a b = gcd(a, b)` with fuel `a + b`, ample for the divisibility
    invariant (`b ≤ a + b`).  The user-facing structural gcd — no fuel parameter. -/
def gcdW (a b : Nat) : Nat := gcdSub (a + b) a b

/-- `gcdW a b ∣ a`. -/
theorem gcdW_dvd_left (a b : Nat) : gcdW a b ∣ a :=
  (gcdSub_dvd_both (a + b) a b (Nat.le_add_left b a)).1

/-- `gcdW a b ∣ b`. -/
theorem gcdW_dvd_right (a b : Nat) : gcdW a b ∣ b :=
  (gcdSub_dvd_both (a + b) a b (Nat.le_add_left b a)).2

/-- `d ∣ a → d ∣ b → d ∣ gcdW a b` — the greatest property, fuel discharged. -/
theorem gcdW_greatest {a b d : Nat} (hda : d ∣ a) (hdb : d ∣ b) : d ∣ gcdW a b :=
  gcdSub_greatest (a + b) a b d (Nat.le_add_left b a) hda hdb

/-- ★★★ **Coprimality of a prime with a non-multiple.**  For `p` prime (`2 ≤ p`, only divisors `1`
    and `p`) with `p ∤ a`, `gcd(p, a) = 1`.  The half of Euclid's lemma that needs *no* Bézout: the
    only candidate divisors of `gcdW p a` are `1` and `p`, and `p` is excluded because `gcdW p a ∣ a`
    would force `p ∣ a`.  Stated with explicit prime hypotheses (no coupling to a concrete prime
    predicate).  `Nat.mod`/`Nat.div`/`lt_wfRel`-free, ∅-axiom. -/
theorem gcd_eq_one_of_prime_not_dvd {p a : Nat} (_hp2 : 2 ≤ p)
    (hpdiv : ∀ d, d ∣ p → d = 1 ∨ d = p) (hna : ¬ p ∣ a) : gcdW p a = 1 := by
  rcases hpdiv (gcdW p a) (gcdW_dvd_left p a) with h1 | hp
  · exact h1
  · exact absurd (hp ▸ gcdW_dvd_right p a) hna

end E213.Meta.Nat.SubGcd213
