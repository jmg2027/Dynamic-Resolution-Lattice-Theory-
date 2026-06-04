import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSignature
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmegaDomain
import E213.Lib.Math.NumberTheory.ModArith.EisensteinFormCharacter
import E213.Meta.Int213.PolyIntMTactic

/-!
# EisensteinSplitting — the local splitting of the Eisenstein period's L-function

The Eisenstein period's Epstein zeta `Σ' 1/(a²+ab+b²)^s = 6 ζ(s) L(s, χ₋₃)` has an Euler
product whose local factor at each prime `p` is governed by how `p` splits in `ℤ[ω]` — the
disc-`−3` analog of the Gaussian `ℤ[i]` splitting behind `Σ 1/(a²+b²)^s`.  The three local
behaviours, by the value of `χ₋₃(p)` (i.e. `p mod 3`):

  * **split** (`p ≡ 1 mod 3`, `χ₋₃(p) = +1`) — `p = N(π)` for a prime `π ∈ ℤ[ω]`; `p` *is*
    a value of the Eisenstein form (`7 = 3²−3·1+1²`, `13 = 4²−4+1`);
  * **ramified** (`p = 3`, the conductor of `χ₋₃`) — `3 = N(1−ω)` and `(1−ω)² = −3ω`, so
    `(3) = (1−ω)²` up to a unit: the unique ramified prime;
  * **inert** (`p ≡ 2 mod 3`, `χ₋₃(p) = −1`) — `p` stays prime, *not* a value of the form
    (`2, 5, 8, …`; the character fingerprint `EisensteinFormCharacter.eisCyc_mod3_ne_two`).

This file pins the `∅`-axiom-reachable arithmetic of that splitting.

  * ★★★ `eisForm_composition` — the **Brahmagupta–Fibonacci identity for disc `−3`**:
    `(a²−ab+b²)(c²−cd+d²) = E²−EF+F²` with `E = ac−bd`, `F = ad+bc−bd` (the `ℤ[ω]`
    multiplication law).  The Loeschian numbers (values of the form) are a **multiplicative
    monoid** — the norm-growth multiplicativity that governs the period's convergence.
  * ★★★ `eisenstein_ramified_three` — `N(1−ω) = 3` and `(1−ω)² = −3ω`: `3` ramifies, the
    conductor of `χ₋₃`.
  * ★★ `eisForm_split_witnesses` — `7` and `13` (the first split primes `≡ 1 mod 3`) are
    values of the form.
  * ★★ `eisenstein_inert_two` — `2` (the first inert prime `≡ 2 mod 3`) is not a value
    (`EisensteinFormCharacter`).

**The wall (honest scope).**  Only the directions provable without quadratic reciprocity
are `∅`-axiom here.  The **split converse** — *every* `p ≡ 1 (mod 3)` is a value (not just
`7, 13, …`) — needs `−3` to be a quadratic residue mod `p` (reciprocity) plus Euclidean
descent in `ℤ[ω]`; that is the disc-`−3` Fermat two-square theorem, not reached from inside
the reflection provers.  The multiplicativity, the ramification, and the inert obstruction
(the character) are pinned; the split-direction existence stays open, as does the period
*value* itself (`EisensteinFormCharacter` wall).

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitting

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSignature (eisForm)
open E213.Lib.Math.NumberTheory.ModArith.EisensteinFormCharacter (mod3_two_not_eisenstein)

/-! ## §1 — the Brahmagupta composition law (multiplicativity of the disc-`−3` form) -/

/-- ★★★ **The disc-`−3` Brahmagupta–Fibonacci identity.**  The Eisenstein form is
    multiplicative: `(a²−ab+b²)(c²−cd+d²) = E²−EF+F²` with `E = ac−bd`, `F = ad+bc−bd` —
    the `ℤ[ω]` multiplication law `(a+bω)(c+dω) = E + Fω`.  So the Loeschian numbers form a
    multiplicative monoid; the norm-growth that governs the period's convergence is
    multiplicative, the disc-`−3` analog of the two-square `(a²+b²)(c²+d²) = …`. -/
theorem eisForm_composition (a b c d : Int) :
    eisForm a b * eisForm c d
      = eisForm (a * c - b * d) (a * d + b * c - b * d) := by
  show (a * a - a * b + b * b) * (c * c - c * d + d * d)
      = (a * c - b * d) * (a * c - b * d)
        - (a * c - b * d) * (a * d + b * c - b * d)
        + (a * d + b * c - b * d) * (a * d + b * c - b * d)
  ring_intZ

/-! ## §2 — ramification at 3 (the conductor of χ₋₃) -/

/-- ★★★ **`3` ramifies in `ℤ[ω]`.**  `N(1−ω) = 3` and `(1−ω)² = −3ω = ⟨0,−3⟩`, so the ideal
    `(3) = (1−ω)²` up to the unit `−ω`: the unique ramified prime, the conductor of the
    quadratic character `χ₋₃`. -/
theorem eisenstein_ramified_three :
    (⟨1, -1⟩ : ZOmega).normSq = 3 ∧ (⟨1, -1⟩ : ZOmega) * ⟨1, -1⟩ = ⟨0, -3⟩ := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §3 — split primes `≡ 1 (mod 3)` are values; inert primes `≡ 2 (mod 3)` are not -/

/-- ★★ **The first split primes are values of the form.**  `7 = 3²−3·1+1² = N(3+ω)` and
    `13 = 4²−4·1+1² = N(4+ω)` — `7 ≡ 13 ≡ 1 (mod 3)` split, so each is `N(π)` for a prime
    `π ∈ ℤ[ω]`. -/
theorem eisForm_split_witnesses :
    eisForm 3 1 = 7 ∧ eisForm 4 1 = 13 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ★★ **The first inert prime is not a value.**  `2 ≡ 2 (mod 3)` is inert in `ℤ[ω]`, so it
    is not represented by `a²+ab+b²` for any `a, b` — the character obstruction
    (`EisensteinFormCharacter.eisCyc_mod3_ne_two`, `mod3 2 = 2`). -/
theorem eisenstein_inert_two (a b : Nat) : a * a + a * b + b * b ≠ 2 :=
  mod3_two_not_eisenstein 2 (by decide) a b

/-! ## §4 — the bundled local-splitting trichotomy -/

/-- ★★★★ **The local splitting of the Eisenstein form (the period's L-function locally).**
    Split (`7 = N(3+ω)`), ramified (`3 = N(1−ω)`, `(1−ω)² = −3ω`), inert (`2` not a value)
    — the three Euler-factor behaviours of `Σ' 1/(a²+ab+b²)^s = 6 ζ L(·,χ₋₃)`, indexed by
    `χ₋₃(p) = p mod 3 ∈ {+1, 0, −1}`.  Bundled with the multiplicativity
    (`eisForm_composition`) that ties the local factors into the global product. -/
theorem eisenstein_local_splitting :
    -- split: a prime ≡ 1 mod 3 is a value
    eisForm 3 1 = 7
    -- ramified: 3 = N(1−ω), (1−ω)² = −3ω
    ∧ ((⟨1, -1⟩ : ZOmega).normSq = 3 ∧ (⟨1, -1⟩ : ZOmega) * ⟨1, -1⟩ = ⟨0, -3⟩)
    -- inert: a prime ≡ 2 mod 3 is not a value
    ∧ (∀ a b : Nat, a * a + a * b + b * b ≠ 2)
    -- multiplicativity: the values form a monoid
    ∧ (∀ a b c d : Int,
        eisForm a b * eisForm c d
          = eisForm (a * c - b * d) (a * d + b * c - b * d)) :=
  ⟨(eisForm_split_witnesses).1, eisenstein_ramified_three,
   eisenstein_inert_two, eisForm_composition⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplitting
