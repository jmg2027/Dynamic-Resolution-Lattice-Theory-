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
remaining (substantial) work — scoped in `research-notes/frontiers/the_descent_leg.md`.

∅-axiom; `subMod`-based, no `Nat.mod`/`Nat.div`/`Nat.lt_wfRel`.
-/

namespace E213.Meta.Nat.SubGcd213

open E213.Meta.Nat.SubMod213 (subMod subMod_lt subMod_zero_iff_dvd)

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

end E213.Meta.Nat.SubGcd213
