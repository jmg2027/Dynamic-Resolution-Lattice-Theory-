import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial
import E213.Meta.Nat.PolyNatMTactic

/-!
# LambertWeld — the series side of the Lambert ladder (weld, stage 1)

The weld frontier (`modulus_degree_ladder.md`): prove the Lambert CF real
`[q; 3q, 5q, …]` (`cothUnitCFCauchySeq`) equals series `coth(1/q)`.  The classical
content is the Bessel/Padé three-term ladder

  `F_{n-1} = (2n+1)·F_n + u·F_{n+1}`,   `F_n(u) = Σ_j u^j / ((2j)!!·(2n+2j+1)!!)`,

whose coefficient identity is just `(2n+1) + 2j = 2n+2j+1`, and whose bottom rungs
**collapse to cosh and sinh**: `(2j)!!(2j−1)!! = (2j)!` gives `F_{−1}(1/q²) = cosh(1/q)`
and `(2j)!!(2j+1)!! = (2j+1)!` gives `F_0(1/q²) = q·sinh(1/q)` — so
`coth(1/q) = q·F_{−1}/F_0`, and unrolling the ladder is exactly the Lambert continued
fraction.

This file delivers the ladder **division-free**: the truncated series
`F_n|_J (1/q²)`, cleared over its own denominator `(2J)!!(2n+2J+1)!!·q^{2J}`, is the
`Nat` sequence `FNum q n J` with the Horner recursion

  `FNum q n (J+1) = (2J+2)(2n+2J+3)·q²·FNum q n J + 1`,

and the exact truncated ladder identities hold as `Nat` theorems:

  * `weld_ladder` — `(2n+2J+3)·FNum q n J = (2n+3)·FNum q (n+1) J + 2J·FNum q (n+2) (J−1)`
    (the three-term recurrence, exact at every truncation level);
  * `weld_base`   — `(2J+1)·coshNum q J = FNum q 0 J + 2J·FNum q 1 (J−1)`
    (the `n = −1` rung: cosh enters the ladder);
  * `sinhNum_eq_FNum_zero` — the `n = 0` rung *is* the sinh-partial numerator.

**What remains for stage 2** (the finite weld identity): pair the ladder with the CF
convergent polynomials — `F_{−1}·B_n − F_0·A_n = ±u^{n+1}·F_{n+1}` at truncated level
(induction on `n` along `weld_ladder`), where `A_n/B_n` are the `u`-polynomial
convergents with `cfPn (cothCF q) n = q^{n+1}·A_n(1/q²)` (the equivalence-transform
bridge).  Then order-transfer pins `cothUnitCFCauchySeq q` between the
cosh/sinh-partial brackets — the weld.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld

/-! ## §1 — the cleared truncated ladder series -/

/-- The cleared truncation of `F_n(1/q²) = Σ_j (1/q²)^j/((2j)!!(2n+2j+1)!!)` over its
    own denominator `(2J)!!(2n+2J+1)!!·q^{2J}`:
    `FNum q n J = Σ_{j≤J} [(2J)!!/(2j)!!]·[(2n+2J+1)!!/(2n+2j+1)!!]·q^{2(J−j)}`,
    by the Horner recursion (each new level scales the old sum by the two new
    denominator factors and `q²`, and contributes `1` for the new deepest term). -/
def FNum (q n : Nat) : Nat → Nat
  | 0 => 1
  | J + 1 => (2 * J + 2) * (2 * n + 2 * J + 3) * q ^ 2 * FNum q n J + 1

/-- The cleared cosh partial numerator: `coshNum q J = Σ_{j≤J} (2J)!/(2j)!·q^{2(J−j)}`
    (`cosh(1/q)` truncated, over `(2J)!·q^{2J}`) — the `n = −1` member of the ladder,
    since `(2j)!!·(2j−1)!! = (2j)!`. -/
def coshNum (q : Nat) : Nat → Nat
  | 0 => 1
  | J + 1 => (2 * J + 1) * (2 * J + 2) * q ^ 2 * coshNum q J + 1

/-- The cleared sinh partial numerator: `sinhNum q J = Σ_{j≤J} (2J+1)!/(2j+1)!·q^{2(J−j)}`
    (`q·sinh(1/q)` truncated, over `(2J+1)!·q^{2J}`) — the `n = 0` member, since
    `(2j)!!·(2j+1)!! = (2j+1)!`. -/
def sinhNum (q : Nat) : Nat → Nat
  | 0 => 1
  | J + 1 => (2 * J + 2) * (2 * J + 3) * q ^ 2 * sinhNum q J + 1

/-- The `n = 0` rung of the ladder **is** the sinh numerator (the denominators
    `(2j)!!(2j+1)!!` interleave to `(2j+1)!`). -/
theorem sinhNum_eq_FNum_zero (q : Nat) : ∀ J, sinhNum q J = FNum q 0 J
  | 0 => rfl
  | J + 1 => by
    show (2 * J + 2) * (2 * J + 3) * q ^ 2 * sinhNum q J + 1
        = (2 * J + 2) * (2 * 0 + 2 * J + 3) * q ^ 2 * FNum q 0 J + 1
    rw [sinhNum_eq_FNum_zero q J]
    ring_nat

/-! ## §2 — the exact truncated three-term ladder -/

/-- ★★★★★ **The Lambert three-term ladder, exact at every truncation** (division-free):

      `(2n+2J+3)·F_n|_J = (2n+3)·F_{n+1}|_J + 2J·F_{n+2}|_{J−1}`.

    This is `F_{n} = (2n+3)F_{n+1} + u·F_{n+2}` (the Bessel `I_{ν−1} − I_{ν+1} =
    (2ν/y)I_ν` contiguity at `ν = n+3/2`) cleared over the common denominator — the
    coefficient identity is `(2n+3) + 2j = 2n+2j+3`.  Unrolled, this ladder **is**
    the Lambert continued fraction `[q; 3q, 5q, …]` of `coth(1/q)`. -/
theorem weld_ladder (q n : Nat) : ∀ J,
    (2 * n + 2 * J + 3) * FNum q n J
      = (2 * n + 3) * FNum q (n + 1) J + 2 * J * FNum q (n + 2) (J - 1)
  | 0 => rfl
  | 1 => by
    have h1 : FNum q n 1 = 2 * (2 * n + 3) * q ^ 2 + 1 := by
      show 2 * (2 * n + 3) * q ^ 2 * 1 + 1 = 2 * (2 * n + 3) * q ^ 2 + 1
      rw [Nat.mul_one]
    have h2 : FNum q (n + 1) 1 = 2 * (2 * n + 5) * q ^ 2 + 1 := by
      show 2 * (2 * n + 5) * q ^ 2 * 1 + 1 = 2 * (2 * n + 5) * q ^ 2 + 1
      rw [Nat.mul_one]
    show (2 * n + 5) * FNum q n 1 = (2 * n + 3) * FNum q (n + 1) 1 + 2
    rw [h1, h2]
    ring_nat
  | J + 2 => by
    have ih : (2 * n + 2 * (J + 1) + 3) * FNum q n (J + 1)
        = (2 * n + 3) * FNum q (n + 1) (J + 1) + 2 * (J + 1) * FNum q (n + 2) J :=
      weld_ladder q n (J + 1)
    show (2 * n + 2 * (J + 2) + 3)
          * ((2 * (J + 1) + 2) * (2 * n + 2 * (J + 1) + 3) * q ^ 2 * FNum q n (J + 1) + 1)
        = (2 * n + 3)
          * ((2 * (J + 1) + 2) * (2 * (n + 1) + 2 * (J + 1) + 3) * q ^ 2
              * FNum q (n + 1) (J + 1) + 1)
          + 2 * (J + 2)
            * ((2 * J + 2) * (2 * (n + 2) + 2 * J + 3) * q ^ 2 * FNum q (n + 2) J + 1)
    rw [show (2 * n + 2 * (J + 2) + 3)
          * ((2 * (J + 1) + 2) * (2 * n + 2 * (J + 1) + 3) * q ^ 2 * FNum q n (J + 1) + 1)
        = (2 * J + 4) * (2 * n + 2 * J + 7) * q ^ 2
            * ((2 * n + 2 * (J + 1) + 3) * FNum q n (J + 1))
          + (2 * n + 2 * J + 7) from by ring_nat,
       ih]
    ring_nat

/-- ★★★★ **The cosh rung** (`n = −1` instance of the ladder):

      `(2J+1)·coshNum q J = FNum q 0 J + 2J·FNum q 1 (J−1)`,

    i.e. `F_{−1} = 1·F_0 + u·F_1` truncated — cosh enters the ladder whose `n = 0`
    rung is sinh (`sinhNum_eq_FNum_zero`), so `coth(1/q) = q·F_{−1}/F_0` unrolls into
    the Lambert continued fraction.  Same induction as `weld_ladder`. -/
theorem weld_base (q : Nat) : ∀ J,
    (2 * J + 1) * coshNum q J = FNum q 0 J + 2 * J * FNum q 1 (J - 1)
  | 0 => rfl
  | 1 => by
    have hc : coshNum q 1 = 2 * q ^ 2 + 1 := by
      show 2 * q ^ 2 * 1 + 1 = 2 * q ^ 2 + 1
      rw [Nat.mul_one]
    have hf : FNum q 0 1 = 6 * q ^ 2 + 1 := by
      show 6 * q ^ 2 * 1 + 1 = 6 * q ^ 2 + 1
      rw [Nat.mul_one]
    show 3 * coshNum q 1 = FNum q 0 1 + 2
    rw [hc, hf]
    ring_nat
  | J + 2 => by
    have ih : (2 * (J + 1) + 1) * coshNum q (J + 1)
        = FNum q 0 (J + 1) + 2 * (J + 1) * FNum q 1 J :=
      weld_base q (J + 1)
    show (2 * (J + 2) + 1)
          * ((2 * (J + 1) + 1) * (2 * (J + 1) + 2) * q ^ 2 * coshNum q (J + 1) + 1)
        = ((2 * (J + 1) + 2) * (2 * 0 + 2 * (J + 1) + 3) * q ^ 2 * FNum q 0 (J + 1) + 1)
          + 2 * (J + 2)
            * ((2 * J + 2) * (2 * 1 + 2 * J + 3) * q ^ 2 * FNum q 1 J + 1)
    rw [show (2 * (J + 2) + 1)
          * ((2 * (J + 1) + 1) * (2 * (J + 1) + 2) * q ^ 2 * coshNum q (J + 1) + 1)
        = (2 * J + 4) * (2 * J + 5) * q ^ 2 * ((2 * (J + 1) + 1) * coshNum q (J + 1))
          + (2 * J + 5) from by ring_nat,
       ih]
    ring_nat

/-! ## §3 — anchors -/

/-- Numeric anchors (`q = 1`, `J = 2`): `coshNum = 37` (`37/24 ≈ 1.5417`, `cosh 1 ≈
    1.5431`) and `sinhNum = 141` (`141/120 = 1.175`, `sinh 1 ≈ 1.1752`); ladder and
    base instances check arithmetically. -/
theorem weld_anchors :
    coshNum 1 2 = 37 ∧ sinhNum 1 2 = 141
    ∧ (2 * 2 + 1) * coshNum 1 2 = FNum 1 0 2 + 2 * 2 * FNum 1 1 1
    ∧ (2 * 0 + 2 * 2 + 3) * FNum 1 0 2 = (2 * 0 + 3) * FNum 1 1 2 + 2 * 2 * FNum 1 2 1 :=
  ⟨by decide, by decide, by decide, by decide⟩

end E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld
