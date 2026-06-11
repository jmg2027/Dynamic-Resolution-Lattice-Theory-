import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial
import E213.Lib.Math.NumberSystems.Real213.ContinuedFractionModulus
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

/-! ## §4 — pairing a `u`-polynomial against the ladder: the `PF` functional

A `u`-polynomial with `Nat` coefficients (a `List Nat`, constant term first) pairs
with the truncated ladder member `F_m|_J`, cleared over `F_m`'s own denominator:
`[P·F_m]|_J = c₀·F_m|_J + [u·P'·F_m]|_J`, and the `u`-shift costs exactly the two
fresh denominator factors `2J·(2m+2J+1)` while dropping the truncation to `J−1`. -/

/-- Cleared truncated pairing `[P(u)·F_m]|_J` over `(2J)!!(2m+2J+1)!!·q^{2J}`. -/
def PF (q : Nat) : List Nat → Nat → Nat → Nat
  | [], _, _ => 0
  | c :: cs, m, J => c * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q cs m (J - 1)

theorem PF_one (q m J : Nat) : PF q [1] m J = FNum q m J := by
  show 1 * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q [] m (J - 1) = FNum q m J
  rw [Nat.one_mul]
  exact Nat.add_zero (FNum q m J)

theorem PF_shift (q : Nat) (c : List Nat) (m J : Nat) :
    PF q (0 :: c) m J = 2 * J * (2 * m + 2 * J + 1) * PF q c m (J - 1) := by
  show 0 * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q c m (J - 1) = _
  rw [Nat.zero_mul]
  exact Nat.zero_add _

/-- Scalar action on coefficient lists. -/
def lsmul (k : Nat) : List Nat → List Nat
  | [] => []
  | c :: cs => k * c :: lsmul k cs

/-- Coefficient-wise sum (padding with the longer tail). -/
def ladd : List Nat → List Nat → List Nat
  | [], l => l
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: ladd as bs

theorem PF_lsmul (q k : Nat) : ∀ (c : List Nat) (m J : Nat),
    PF q (lsmul k c) m J = k * PF q c m J
  | [], m, J => by
    show (0 : Nat) = k * 0
    exact (Nat.mul_zero k).symm
  | c :: cs, m, J => by
    show k * c * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q (lsmul k cs) m (J - 1)
        = k * (c * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q cs m (J - 1))
    rw [PF_lsmul q k cs m (J - 1)]
    ring_nat

theorem PF_ladd (q : Nat) : ∀ (c d : List Nat) (m J : Nat),
    PF q (ladd c d) m J = PF q c m J + PF q d m J
  | [], d, m, J => by
    show PF q d m J = 0 + PF q d m J
    exact (Nat.zero_add _).symm
  | a :: as, [], m, J => rfl
  | a :: as, b :: bs, m, J => by
    show (a + b) * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q (ladd as bs) m (J - 1)
        = (a * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q as m (J - 1))
          + (b * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q bs m (J - 1))
    rw [PF_ladd q as bs m (J - 1)]
    ring_nat

/-- ★★★★ **The ladder lifts through the pairing, uniformly in the polynomial**:

      `(2n+2J+3)·[P·F_n]|_J = (2n+3)·[P·F_{n+1}]|_J + 2J·[P·F_{n+2}]|_{J−1}`,

    same shape as `weld_ladder` (the `c`-head is `weld_ladder` itself; the tail
    reduces to the same statement one level down — the diagonal weights match
    exactly). -/
theorem pf_ladder (q : Nat) : ∀ (c : List Nat) (n J : Nat),
    (2 * n + 2 * J + 3) * PF q c n J
      = (2 * n + 3) * PF q c (n + 1) J + 2 * J * PF q c (n + 2) (J - 1)
  | [], n, J => rfl
  | c :: cs, n, 0 => by
    have h0 : ∀ m, PF q (c :: cs) m 0 = c := by
      intro m
      show c * FNum q m 0 + 2 * 0 * (2 * m + 2 * 0 + 1) * PF q cs m (0 - 1) = c
      rw [show (2 * 0 : Nat) = 0 from rfl, Nat.zero_mul, Nat.zero_mul]
      show c * 1 + 0 = c
      rw [Nat.mul_one]
      exact Nat.add_zero c
    rw [h0 n, h0 (n + 1), show (2 * 0 : Nat) = 0 from rfl, Nat.zero_mul]
    show (2 * n + 3) * c = (2 * n + 3) * c + 0
    exact (Nat.add_zero _).symm
  | c :: cs, n, J + 1 => by
    have ihc : (2 * n + 2 * J + 3) * PF q cs n J
        = (2 * n + 3) * PF q cs (n + 1) J + 2 * J * PF q cs (n + 2) (J - 1) :=
      pf_ladder q cs n J
    have hw : (2 * n + 2 * J + 5) * FNum q n (J + 1)
        = (2 * n + 3) * FNum q (n + 1) (J + 1) + (2 * J + 2) * FNum q (n + 2) J :=
      weld_ladder q n (J + 1)
    show (2 * n + 2 * (J + 1) + 3)
          * (c * FNum q n (J + 1)
             + 2 * (J + 1) * (2 * n + 2 * (J + 1) + 1) * PF q cs n J)
        = (2 * n + 3)
          * (c * FNum q (n + 1) (J + 1)
             + 2 * (J + 1) * (2 * (n + 1) + 2 * (J + 1) + 1) * PF q cs (n + 1) J)
          + 2 * (J + 1)
            * (c * FNum q (n + 2) J
               + 2 * J * (2 * (n + 2) + 2 * J + 1) * PF q cs (n + 2) (J - 1))
    rw [show (2 * n + 2 * (J + 1) + 3)
          * (c * FNum q n (J + 1)
             + 2 * (J + 1) * (2 * n + 2 * (J + 1) + 1) * PF q cs n J)
        = c * ((2 * n + 2 * J + 5) * FNum q n (J + 1))
          + (2 * J + 2) * (2 * n + 2 * J + 5)
            * ((2 * n + 2 * J + 3) * PF q cs n J) from by ring_nat,
       hw, ihc]
    ring_nat

/-! ## §5 — the convergent polynomials and the finite weld identity

The `u`-polynomial convergents of the ladder CF `F_{−1}/F_0 = 1 + u/(3 + u/(5 + …))`
(`Ã_{k−1} =: AP k`, `B̃_{k−1} =: BP k`, shifted so the seeds are total):

  `AP 0 = AP 1 = [1]`, `AP (n+2) = (2n+3)·AP (n+1) + u·AP n`,
  `BP 0 = []`,  `BP 1 = [1]`,  `BP (n+2) = (2n+3)·BP (n+1) + u·BP n`.

The matrix unrolling `(F_{−1}, F_0) = M₀⋯Mₙ·(Fₙ, F_{n+1})` gives the **exact, finite,
division-free weld identities** below: the cosh row pairs `AP` against the ladder, the
sinh row pairs `BP` — at every truncation `J`, with the conversion weights
`vFac`/`v0Fac` (the odd-double-factorial ratios `D(n,J)/D(−1,J)`, `D(n,J)/D(0,J)`). -/

def AP : Nat → List Nat
  | 0 => [1]
  | 1 => [1]
  | n + 2 => ladd (lsmul (2 * n + 3) (AP (n + 1))) (0 :: AP n)

def BP : Nat → List Nat
  | 0 => []
  | 1 => [1]
  | n + 2 => ladd (lsmul (2 * n + 3) (BP (n + 1))) (0 :: BP n)

/-- `vFac J n = (2J+1)(2J+3)⋯(2J+2n+1)` — the cosh-row conversion weight. -/
def vFac (J : Nat) : Nat → Nat
  | 0 => 2 * J + 1
  | n + 1 => (2 * J + 2 * n + 3) * vFac J n

/-- `v0Fac J n = (2J+3)(2J+5)⋯(2J+2n+1)` — the sinh-row conversion weight. -/
def v0Fac (J : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => (2 * J + 2 * n + 3) * v0Fac J n

/-- Generic pairing-row induction: if a row `G` satisfies the weld-base shape against
    `(P₁, P₀) = (row n+1, row n)` seeds, the ladder + linearity push it down every
    rung.  Stated and proven separately for the two rows below. -/
private theorem pair_step (q n J : Nat) (X : List Nat) (Y : List Nat) (T : Nat)
    (ih : T = PF q X n J + 2 * J * PF q Y (n + 1) (J - 1)) :
    (2 * J + 2 * n + 3) * T
      = PF q (ladd (lsmul (2 * n + 3) X) (0 :: Y)) (n + 1) J
        + 2 * J * PF q X (n + 2) (J - 1) := by
  rw [ih, PF_ladd, PF_lsmul, PF_shift]
  rw [show (2 * J + 2 * n + 3) * (PF q X n J + 2 * J * PF q Y (n + 1) (J - 1))
        = (2 * n + 2 * J + 3) * PF q X n J
          + (2 * J + 2 * n + 3) * (2 * J) * PF q Y (n + 1) (J - 1) from by ring_nat,
      pf_ladder q X n J]
  ring_nat

/-- ★★★★★ **The finite weld identity, cosh row**: for every `n` and every truncation
    `J`,

      `vFac J n · coshNum q J = [Ã_{n−1}·F_n]|_J + 2J·[Ã_{n−2}·F_{n+1}]|_{J−1}`

    (cleared form of `F_{−1} = Ã_{n−1}Fₙ + u·Ã_{n−2}F_{n+1}`).  The `n = 0` rung is
    `weld_base`; each step is `pair_step` (ladder + linearity), matching the `AP`
    recursion exactly.  This is the CF-correctness identity of the Lambert fold,
    finite and division-free. -/
theorem weld_pair_cosh (q : Nat) : ∀ (n J : Nat),
    vFac J n * coshNum q J
      = PF q (AP (n + 1)) n J + 2 * J * PF q (AP n) (n + 1) (J - 1)
  | 0, J => by
    show (2 * J + 1) * coshNum q J = PF q [1] 0 J + 2 * J * PF q [1] 1 (J - 1)
    rw [PF_one, PF_one]
    exact weld_base q J
  | n + 1, J => by
    show (2 * J + 2 * n + 3) * vFac J n * coshNum q J
        = PF q (ladd (lsmul (2 * n + 3) (AP (n + 1))) (0 :: AP n)) (n + 1) J
          + 2 * J * PF q (AP (n + 1)) (n + 2) (J - 1)
    rw [show (2 * J + 2 * n + 3) * vFac J n * coshNum q J
          = (2 * J + 2 * n + 3) * (vFac J n * coshNum q J) from by ring_nat]
    exact pair_step q n J (AP (n + 1)) (AP n) (vFac J n * coshNum q J)
      (weld_pair_cosh q n J)

/-- ★★★★★ **The finite weld identity, sinh row**: `v0Fac J n · sinhNum q J =
    [B̃_{n−1}·F_n]|_J + 2J·[B̃_{n−2}·F_{n+1}]|_{J−1}` — the cleared
    `F_0 = B̃_{n−1}Fₙ + u·B̃_{n−2}F_{n+1}`.  Together with the cosh row this is the
    full matrix unrolling `(F_{−1}, F_0) = M₀⋯M_{n−1}·(Fₙ, F_{n+1})`: the two rows of
    the weld. -/
theorem weld_pair_sinh (q : Nat) : ∀ (n J : Nat),
    v0Fac J n * sinhNum q J
      = PF q (BP (n + 1)) n J + 2 * J * PF q (BP n) (n + 1) (J - 1)
  | 0, J => by
    show 1 * sinhNum q J = PF q [1] 0 J + 2 * J * PF q [] 1 (J - 1)
    rw [PF_one, Nat.one_mul, sinhNum_eq_FNum_zero q J]
    show FNum q 0 J = FNum q 0 J + 2 * J * 0
    rw [Nat.mul_zero]
    exact (Nat.add_zero _).symm
  | n + 1, J => by
    show (2 * J + 2 * n + 3) * v0Fac J n * sinhNum q J
        = PF q (ladd (lsmul (2 * n + 3) (BP (n + 1))) (0 :: BP n)) (n + 1) J
          + 2 * J * PF q (BP (n + 1)) (n + 2) (J - 1)
    rw [show (2 * J + 2 * n + 3) * v0Fac J n * sinhNum q J
          = (2 * J + 2 * n + 3) * (v0Fac J n * sinhNum q J) from by ring_nat]
    exact pair_step q n J (BP (n + 1)) (BP n) (v0Fac J n * sinhNum q J)
      (weld_pair_sinh q n J)

/-! ## §6 — anchors for the pairing -/

/-- Pairing anchors (`q = 1`): the convergent polynomials produce `AP 2 = [3, 1]`
    (`Ã_1 = 3 + u`) and `BP 2 = [3]` (`B̃_1 = 3`), and both weld rows check
    arithmetically at `n = 2`, `J = 2`. -/
theorem weld_pair_anchors :
    AP 2 = [3, 1] ∧ BP 2 = [3]
    ∧ vFac 2 2 * coshNum 1 2 = PF 1 (AP 3) 2 2 + 2 * 2 * PF 1 (AP 2) 3 1
    ∧ v0Fac 2 2 * sinhNum 1 2 = PF 1 (BP 3) 2 2 + 2 * 2 * PF 1 (BP 2) 3 1 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## §7 — the evaluation bridge: the weld polynomials ARE the CF convergents

The Lambert fold (`ContinuedFractionModulus.cfPn/cfQn` at `cothCF q`) and the weld
rows (§5, in `AP`/`BP`-polynomial language) speak the same coordinates: evaluating
the `u`-polynomials at `u = 1/q²` and clearing (descending Horner `dev`, head =
highest power of `q²`) recovers the regular-CF convergents exactly, up to the
parity-alternating factor `q`:

  `cfPn (cothCF q) (2k)   = q · dev (AP (2k+1))`,   `cfPn (2k+1) = dev (AP (2k+2))`,
  `cfQn (cothCF q) (2k)   =     dev (BP (2k+1))`,   `cfQn (2k+1) = q · dev (BP (2k+2))`

(the equivalence transform `[q; 3q, 5q, …] ↔ 1 + u/(3 + u/(5 + …))` made explicit).
With §5's weld rows this puts `cothUnitCFCauchySeq`'s convergents and the cosh/sinh
partial numerators in one identity system — stage 3's remaining step is pure order
transfer. -/

/-- Pure `q^{n+2} = qⁿ·(q·q)` (core `Nat.pow_add` carries `propext`; `pow_succ` is
    definitional). -/
private theorem pow_add_two (q n : Nat) : q ^ (n + 2) = q ^ n * (q * q) := by
  show q ^ n * q * q = q ^ n * (q * q)
  ring_nat

private theorem pow_two (q : Nat) : q ^ 2 = q * q := by
  rw [Nat.pow_succ, Nat.pow_one]

/-- Descending Horner evaluation at `q²` (head coefficient gets the highest power):
    `hornEv q a [c₀,…,c_D] = a·q^{2(D+1)} + Σᵢ cᵢ·q^{2(D−i)}`. -/
def hornEv (q : Nat) : Nat → List Nat → Nat
  | acc, [] => acc
  | acc, c :: cs => hornEv q (c + q ^ 2 * acc) cs

/-- The cleared descending evaluation `dev q c = Σᵢ cᵢ·q^{2(D−i)}`. -/
def dev (q : Nat) (c : List Nat) : Nat := hornEv q 0 c

theorem hornEv_acc (q : Nat) : ∀ (c : List Nat) (a : Nat),
    hornEv q a c = a * q ^ (2 * c.length) + hornEv q 0 c
  | [], a => by
    show a = a * 1 + 0
    rw [Nat.mul_one]
    exact (Nat.add_zero a).symm
  | c :: cs, a => by
    show hornEv q (c + q ^ 2 * a) cs
        = a * q ^ (2 * cs.length + 2) + hornEv q c cs
    rw [hornEv_acc q cs (c + q ^ 2 * a), hornEv_acc q cs c,
        pow_add_two q (2 * cs.length), pow_two q]
    ring_nat

theorem dev_cons (q c : Nat) (cs : List Nat) :
    dev q (c :: cs) = c * q ^ (2 * cs.length) + dev q cs := by
  show hornEv q c cs = c * q ^ (2 * cs.length) + hornEv q 0 cs
  exact hornEv_acc q cs c

/-- A leading zero is free: `dev (0 :: c) = dev c`. -/
theorem dev_zero_cons (q : Nat) (c : List Nat) : dev q (0 :: c) = dev q c := rfl

theorem lsmul_length (k : Nat) : ∀ c : List Nat, (lsmul k c).length = c.length
  | [] => rfl
  | c :: cs => by
    show (lsmul k cs).length + 1 = cs.length + 1
    rw [lsmul_length k cs]

theorem dev_lsmul (q k : Nat) : ∀ c : List Nat, dev q (lsmul k c) = k * dev q c
  | [] => (Nat.mul_zero k).symm
  | c :: cs => by
    rw [show lsmul k (c :: cs) = k * c :: lsmul k cs from rfl,
        dev_cons, dev_cons, dev_lsmul q k cs, lsmul_length k cs]
    ring_nat

theorem ladd_length_eq : ∀ (c d : List Nat), c.length = d.length →
    (ladd c d).length = d.length
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | _ :: cs, _ :: ds, h => by
    show (ladd cs ds).length + 1 = ds.length + 1
    rw [ladd_length_eq cs ds (Nat.succ.inj h)]

theorem ladd_length_succ : ∀ (c d : List Nat), c.length + 1 = d.length →
    (ladd c d).length = d.length
  | [], [], h => Nat.noConfusion h
  | [], _ :: ds, _ => rfl
  | _ :: _, [], h => Nat.noConfusion h
  | _ :: cs, _ :: ds, h => by
    show (ladd cs ds).length + 1 = ds.length + 1
    rw [ladd_length_succ cs ds (Nat.succ.inj h)]

theorem dev_ladd_eq (q : Nat) : ∀ (c d : List Nat), c.length = d.length →
    dev q (ladd c d) = dev q c + dev q d
  | [], [], _ => rfl
  | [], _ :: _, h => Nat.noConfusion h
  | _ :: _, [], h => Nat.noConfusion h
  | c :: cs, d :: ds, h => by
    have hl : cs.length = ds.length := Nat.succ.inj h
    rw [show ladd (c :: cs) (d :: ds) = (c + d) :: ladd cs ds from rfl,
        dev_cons, dev_cons, dev_cons, dev_ladd_eq q cs ds hl,
        ladd_length_eq cs ds hl, hl]
    ring_nat

theorem dev_ladd_succ (q : Nat) : ∀ (c d : List Nat), c.length + 1 = d.length →
    dev q (ladd c d) = q ^ 2 * dev q c + dev q d
  | [], [], h => Nat.noConfusion h
  | [], d :: ds, h => by
    show dev q (d :: ds) = q ^ 2 * 0 + dev q (d :: ds)
    rw [Nat.mul_zero]
    exact (Nat.zero_add _).symm
  | _ :: _, [], h => Nat.noConfusion h
  | c :: cs, d :: ds, h => by
    have hl : cs.length + 1 = ds.length := Nat.succ.inj h
    rw [show ladd (c :: cs) (d :: ds) = (c + d) :: ladd cs ds from rfl,
        dev_cons, dev_cons, dev_cons, dev_ladd_succ q cs ds hl,
        ladd_length_succ cs ds hl, ← hl,
        show q ^ (2 * (cs.length + 1)) = q ^ (2 * cs.length) * (q * q) from
          pow_add_two q (2 * cs.length),
        pow_two q]
    ring_nat

/-- Lengths of the weld polynomials, by parity: `|AP (2k+1)| = k+1`,
    `|AP (2k+2)| = k+2`, `|BP (2k+1)| = k+1`, `|BP (2k+2)| = k+1`. -/
theorem AP_BP_length : ∀ k : Nat,
    (AP (2 * k + 1)).length = k + 1 ∧ (AP (2 * k + 2)).length = k + 2
    ∧ (BP (2 * k + 1)).length = k + 1 ∧ (BP (2 * k + 2)).length = k + 1
  | 0 => ⟨rfl, rfl, rfl, rfl⟩
  | k + 1 => by
    obtain ⟨h1, h2, h3, h4⟩ := AP_BP_length k
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (ladd (lsmul (2 * (2 * k + 1) + 3) (AP (2 * k + 2))) (0 :: AP (2 * k + 1))).length
          = k + 2
      rw [ladd_length_eq _ _ (by
            rw [lsmul_length, h2]
            show k + 2 = (AP (2 * k + 1)).length + 1
            rw [h1])]
      show (AP (2 * k + 1)).length + 1 = k + 2
      rw [h1]
    · show (ladd (lsmul (2 * (2 * k + 2) + 3) (AP (2 * k + 3))) (0 :: AP (2 * k + 2))).length
          = k + 3
      have h1' : (AP (2 * k + 3)).length = k + 2 := by
        show (ladd (lsmul (2 * (2 * k + 1) + 3) (AP (2 * k + 2))) (0 :: AP (2 * k + 1))).length
            = k + 2
        rw [ladd_length_eq _ _ (by
              rw [lsmul_length, h2]
              show k + 2 = (AP (2 * k + 1)).length + 1
              rw [h1])]
        show (AP (2 * k + 1)).length + 1 = k + 2
        rw [h1]
      rw [ladd_length_succ _ _ (by
            rw [lsmul_length, h1']
            show k + 3 = (AP (2 * k + 2)).length + 1
            rw [h2])]
      show (AP (2 * k + 2)).length + 1 = k + 3
      rw [h2]
    · show (ladd (lsmul (2 * (2 * k + 1) + 3) (BP (2 * k + 2))) (0 :: BP (2 * k + 1))).length
          = k + 2
      rw [ladd_length_succ _ _ (by
            rw [lsmul_length, h4]
            show k + 2 = (BP (2 * k + 1)).length + 1
            rw [h3])]
      show (BP (2 * k + 1)).length + 1 = k + 2
      rw [h3]
    · show (ladd (lsmul (2 * (2 * k + 2) + 3) (BP (2 * k + 3))) (0 :: BP (2 * k + 2))).length
          = k + 2
      have h3' : (BP (2 * k + 3)).length = k + 2 := by
        show (ladd (lsmul (2 * (2 * k + 1) + 3) (BP (2 * k + 2))) (0 :: BP (2 * k + 1))).length
            = k + 2
        rw [ladd_length_succ _ _ (by
              rw [lsmul_length, h4]
              show k + 2 = (BP (2 * k + 1)).length + 1
              rw [h3])]
        show (BP (2 * k + 1)).length + 1 = k + 2
        rw [h3]
      rw [ladd_length_eq _ _ (by
            rw [lsmul_length, h3']
            show k + 2 = (BP (2 * k + 2)).length + 1
            rw [h4])]
      show (BP (2 * k + 2)).length + 1 = k + 2
      rw [h4]

open E213.Lib.Math.NumberSystems.Real213.ContinuedFractionModulus (cfPn cothCF)
open E213.Lib.Math.NumberSystems.Real213.ContinuedFractionFloor (cfQn)

/-- ★★★★★ **The evaluation bridge**: the regular-CF convergents of the Lambert fold
    (`cothUnitCFCauchySeq`'s carrier, partial quotients `(2n+1)q`) are **exactly** the
    cleared evaluations of the weld polynomials, with the parity-alternating factor
    `q` — the equivalence transform `[q; 3q, 5q, …] ↔ 1 + u/(3 + u/(5 + …))` as four
    `Nat` identities.  Together with the weld rows (§5) the CF fold and the cosh/sinh
    partial numerators now live in one identity system. -/
theorem cf_bridge (q : Nat) : ∀ k : Nat,
    cfPn (cothCF q) (2 * k) = q * dev q (AP (2 * k + 1))
    ∧ cfPn (cothCF q) (2 * k + 1) = dev q (AP (2 * k + 2))
    ∧ cfQn (cothCF q) (2 * k) = dev q (BP (2 * k + 1))
    ∧ cfQn (cothCF q) (2 * k + 1) = q * dev q (BP (2 * k + 2))
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 1 * q = q * 1
      rw [Nat.one_mul, Nat.mul_one]
    · show 3 * q * (1 * q) + 1 = 1 + q ^ 2 * 3
      rw [Nat.one_mul, pow_two]
      ring_nat
    · rfl
    · show 3 * q = q * 3
      ring_nat
  | k + 1 => by
    obtain ⟨ih1, ih2, ih3, ih4⟩ := cf_bridge q k
    obtain ⟨l1, l2, l3, l4⟩ := AP_BP_length k
    obtain ⟨m1, m2, m3, m4⟩ := AP_BP_length (k + 1)
    have m1' : (AP (2 * k + 3)).length = k + 2 := m1
    have m3' : (BP (2 * k + 3)).length = k + 2 := m3
    have hA3 : dev q (AP (2 * k + 3))
        = (2 * (2 * k + 1) + 3) * dev q (AP (2 * k + 2)) + dev q (AP (2 * k + 1)) := by
      show dev q (ladd (lsmul (2 * (2 * k + 1) + 3) (AP (2 * k + 2))) (0 :: AP (2 * k + 1)))
          = _
      rw [dev_ladd_eq q _ _ (by
            rw [lsmul_length, l2]
            show k + 2 = (AP (2 * k + 1)).length + 1
            rw [l1]),
          dev_lsmul, dev_zero_cons]
    have hA4 : dev q (AP (2 * k + 4))
        = q ^ 2 * ((2 * (2 * k + 2) + 3) * dev q (AP (2 * k + 3))) + dev q (AP (2 * k + 2)) := by
      show dev q (ladd (lsmul (2 * (2 * k + 2) + 3) (AP (2 * k + 3))) (0 :: AP (2 * k + 2)))
          = _
      rw [dev_ladd_succ q _ _ (by
            rw [lsmul_length, m1']
            show k + 3 = (AP (2 * k + 2)).length + 1
            rw [l2]),
          dev_lsmul, dev_zero_cons]
    have hB3 : dev q (BP (2 * k + 3))
        = q ^ 2 * ((2 * (2 * k + 1) + 3) * dev q (BP (2 * k + 2))) + dev q (BP (2 * k + 1)) := by
      show dev q (ladd (lsmul (2 * (2 * k + 1) + 3) (BP (2 * k + 2))) (0 :: BP (2 * k + 1)))
          = _
      rw [dev_ladd_succ q _ _ (by
            rw [lsmul_length, l4]
            show k + 2 = (BP (2 * k + 1)).length + 1
            rw [l3]),
          dev_lsmul, dev_zero_cons]
    have hB4 : dev q (BP (2 * k + 4))
        = (2 * (2 * k + 2) + 3) * dev q (BP (2 * k + 3)) + dev q (BP (2 * k + 2)) := by
      show dev q (ladd (lsmul (2 * (2 * k + 2) + 3) (BP (2 * k + 3))) (0 :: BP (2 * k + 2)))
          = _
      rw [dev_ladd_eq q _ _ (by
            rw [lsmul_length, m3']
            show k + 2 = (BP (2 * k + 2)).length + 1
            rw [l4]),
          dev_lsmul, dev_zero_cons]
    have g1 : cfPn (cothCF q) (2 * k + 2) = q * dev q (AP (2 * k + 3)) := by
      show (2 * (2 * k + 2) + 1) * q * cfPn (cothCF q) (2 * k + 1) + cfPn (cothCF q) (2 * k)
          = q * dev q (AP (2 * k + 3))
      rw [ih2, ih1, hA3]
      ring_nat
    have g2 : cfPn (cothCF q) (2 * k + 3) = dev q (AP (2 * k + 4)) := by
      show (2 * (2 * k + 3) + 1) * q * cfPn (cothCF q) (2 * k + 2) + cfPn (cothCF q) (2 * k + 1)
          = dev q (AP (2 * k + 4))
      rw [g1, ih2, hA4, pow_two]
      ring_nat
    have g3 : cfQn (cothCF q) (2 * k + 2) = dev q (BP (2 * k + 3)) := by
      show (2 * (2 * k + 2) + 1) * q * cfQn (cothCF q) (2 * k + 1) + cfQn (cothCF q) (2 * k)
          = dev q (BP (2 * k + 3))
      rw [ih4, ih3, hB3, pow_two]
      ring_nat
    have g4 : cfQn (cothCF q) (2 * k + 3) = q * dev q (BP (2 * k + 4)) := by
      show (2 * (2 * k + 3) + 1) * q * cfQn (cothCF q) (2 * k + 2) + cfQn (cothCF q) (2 * k + 1)
          = q * dev q (BP (2 * k + 4))
      rw [g3, ih4, hB4]
      ring_nat
    exact ⟨g1, g2, g3, g4⟩

/-- Bridge anchors (`q = 2`, so the `q`-powers are visible): `p₂ = 2·dev(AP 3)`,
    `q₂ = dev(BP 3)`, etc., `decide`-checked. -/
theorem cf_bridge_anchors :
    cfPn (cothCF 2) 2 = 2 * dev 2 (AP 3)
    ∧ cfPn (cothCF 2) 3 = dev 2 (AP 4)
    ∧ cfQn (cothCF 2) 2 = dev 2 (BP 3)
    ∧ cfQn (cothCF 2) 3 = 2 * dev 2 (BP 4) :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## §8 — toward the order transfer: the row determinant collapses (weld 3c prep)

Comparing the truncated coth ratio with a CF convergent means comparing the two weld
rows cross-multiplied against the pairings.  The head products `X_A·X_B` cancel
**exactly**: the row determinant collapses to the `2J`-tail cross — the truncated form
of the classical `F₋₁B̃ − F₀Ã = ±u·(det)·F`-telescope.  Stage 3c reduces to the sign
of the tail cross `Y_A·X_B − Y_B·X_A` (and the `vFac = (2J+1)·v0Fac` scaling link,
which is what makes the rows comparable to `T_J = (2J+1)q·coshNum/sinhNum` at all). -/

theorem FNum_pos (q n : Nat) : ∀ J, 1 ≤ FNum q n J
  | 0 => Nat.le_refl 1
  | _ + 1 => Nat.le_add_left 1 _

/-- The pairing dominates its head term. -/
theorem PF_head_le (q c : Nat) (cs : List Nat) (m J : Nat) :
    c * FNum q m J ≤ PF q (c :: cs) m J :=
  Nat.le_add_right _ _

/-- The two conversion weights differ by exactly the `T`-scaling factor:
    `vFac J n = (2J+1)·v0Fac J n` — the cosh row is `(2J+1)`-heavier, which is
    precisely the truncated coth numerator's `(2J+1)` (the ratio `(2J+1)!/(2J)!`). -/
theorem vFac_eq (J : Nat) : ∀ n, vFac J n = (2 * J + 1) * v0Fac J n
  | 0 => by
    show 2 * J + 1 = (2 * J + 1) * 1
    exact (Nat.mul_one _).symm
  | n + 1 => by
    show (2 * J + 2 * n + 3) * vFac J n = (2 * J + 1) * ((2 * J + 2 * n + 3) * v0Fac J n)
    rw [vFac_eq J n]
    ring_nat

/-- ★★★★★ **The row determinant collapses to the tail cross**:

      `vFac·cosh·[B̃F]-pairing + 2J·(Y_B·X_A) = v0Fac·sinh·[ÃF]-pairing + 2J·(Y_A·X_B)`

    (additive form of `(vFac·cosh)·X_B − (v0Fac·sinh)·X_A = 2J·(Y_AX_B − Y_BX_A)`):
    multiplying the cosh row by the sinh pairing and vice versa, the head products
    cancel exactly — the order comparison between the truncated coth and a CF
    convergent is governed **entirely by the `2J`-tail cross**, whose parity sign is
    stage 3c's remaining content. -/
theorem row_det (q n J : Nat) :
    vFac J n * coshNum q J * PF q (BP (n + 1)) n J
      + 2 * J * (PF q (BP n) (n + 1) (J - 1) * PF q (AP (n + 1)) n J)
    = v0Fac J n * sinhNum q J * PF q (AP (n + 1)) n J
      + 2 * J * (PF q (AP n) (n + 1) (J - 1) * PF q (BP (n + 1)) n J) := by
  rw [weld_pair_cosh q n J, weld_pair_sinh q n J]
  ring_nat

/-! ## §9 — the Chebyshev engine: pairing-vs-evaluation cross, conditional on minors

The order transfer's analytic core.  `PF` and `dev` are two positive-weight readings
of the same coefficient list; their cross over a pair `(a, b)` is controlled by two
facts: (i) **weight dominance** — the `PF`-weight system, transported one `u`-shift,
is dominated by the `dev`-weight system (`weight_dom`: per step it is the `FNum`
recursion minus its `+1`); (ii) the **coefficient minors** of `(a, b)`
(`MinorLE`, the hypothesis the convergent-polynomial pair supplies).  The engine
(`cross_le`) reduces the mixed-head terms to weight dominance **of the gap list**
(`b₀·as = a₀·bs + g` pointwise), so no double-sum infrastructure is needed: two
list inductions close it. -/

/-- Pointwise (truncated) list difference, keeping the first list's length. -/
def lsub : List Nat → List Nat → List Nat
  | a :: as, b :: bs => (a - b) :: lsub as bs
  | a, _ => a

theorem lsub_length : ∀ (a b : List Nat), (lsub a b).length = a.length
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | _ :: as, _ :: bs => by
    show (lsub as bs).length + 1 = as.length + 1
    rw [lsub_length as bs]

/-- Pointwise scaled comparison: `x·vⱼ ≤ y·uⱼ` along the zip of `(us, vs)`. -/
def scaledLE (x y : Nat) : List Nat → List Nat → Prop
  | u :: us, v :: vs => x * v ≤ y * u ∧ scaledLE x y us vs
  | _, _ => True

/-- The full minor condition: every head scales below every later entry —
    `aᵢ·bⱼ ≤ bᵢ·aⱼ` for all `i < j` (`a/b` increasing along positions). -/
def MinorLE : List Nat → List Nat → Prop
  | a :: as, b :: bs => scaledLE a b as bs ∧ MinorLE as bs
  | _, _ => True

private theorem add_sub_recover {x y : Nat} (h : x ≤ y) : x + (y - x) = y := by
  obtain ⟨k, hk⟩ := Nat.le.dest h
  rw [← hk, Nat.add_comm x k, E213.Tactic.NatHelper.add_sub_cancel_right k x]
  exact Nat.add_comm x k

/-- Gap recovery: under `scaledLE x y us vs`, the pointwise gap
    `g = lsub (lsmul y us) (lsmul x vs)` satisfies `lsmul x vs + g = lsmul y us`. -/
theorem ladd_lsub_recover (x y : Nat) : ∀ (us vs : List Nat),
    us.length = vs.length → scaledLE x y us vs →
    ladd (lsmul x vs) (lsub (lsmul y us) (lsmul x vs)) = lsmul y us
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | u :: us, v :: vs, h, hsc => by
    show (x * v + (y * u - x * v)) :: ladd (lsmul x vs) (lsub (lsmul y us) (lsmul x vs))
        = y * u :: lsmul y us
    rw [add_sub_recover hsc.1,
        ladd_lsub_recover x y us vs (Nat.succ.inj h) hsc.2]

/-- ★★★★ **Weight dominance**: the `PF`-weight system, transported one `u`-shift
    (`2J(2m+2J+1)·q^{2·len}·PF(·, J−1)`), is dominated by the `dev`-weight system
    scaled by `FNum(m,J)` — per step it is exactly the `FNum` recursion minus its
    `+1`.  Holds for **every** coefficient list, no hypotheses. -/
theorem weight_dom (q m : Nat) : ∀ (c : List Nat) (J : Nat),
    2 * J * (2 * m + 2 * J + 1) * q ^ (2 * c.length) * PF q c m (J - 1)
      ≤ FNum q m J * dev q c
  | [], J => by
    show 2 * J * (2 * m + 2 * J + 1) * q ^ (2 * 0) * 0 ≤ FNum q m J * 0
    exact Nat.le_refl _
  | c :: cs, 0 => by
    rw [show (2 * 0 : Nat) = 0 from rfl, Nat.zero_mul, Nat.zero_mul, Nat.zero_mul]
    exact Nat.zero_le _
  | c :: cs, J + 1 => by
    have ih := weight_dom q m cs J
    have hF : FNum q m (J + 1)
        = (2 * J + 2) * (2 * m + 2 * J + 3) * q ^ 2 * FNum q m J + 1 := rfl
    rw [dev_cons q c cs]
    show 2 * (J + 1) * (2 * m + 2 * (J + 1) + 1) * q ^ (2 * (cs.length + 1))
          * (c * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q cs m (J - 1))
        ≤ FNum q m (J + 1) * (c * q ^ (2 * cs.length) + dev q cs)
    rw [show q ^ (2 * (cs.length + 1)) = q ^ (2 * cs.length) * (q * q) from
          pow_add_two q (2 * cs.length),
        hF, pow_two q]
    have hhead : 2 * (J + 1) * (2 * m + 2 * (J + 1) + 1) * (q ^ (2 * cs.length) * (q * q))
          * (c * FNum q m J)
        ≤ ((2 * J + 2) * (2 * m + 2 * J + 3) * (q * q) * FNum q m J + 1)
          * (c * q ^ (2 * cs.length)) := by
      rw [show 2 * (J + 1) * (2 * m + 2 * (J + 1) + 1) * (q ^ (2 * cs.length) * (q * q))
            * (c * FNum q m J)
          = ((2 * J + 2) * (2 * m + 2 * J + 3) * (q * q) * FNum q m J)
            * (c * q ^ (2 * cs.length)) from by ring_nat]
      exact Nat.mul_le_mul (Nat.le_add_right _ 1) (Nat.le_refl _)
    have htail : 2 * (J + 1) * (2 * m + 2 * (J + 1) + 1) * (q ^ (2 * cs.length) * (q * q))
          * (2 * J * (2 * m + 2 * J + 1) * PF q cs m (J - 1))
        ≤ ((2 * J + 2) * (2 * m + 2 * J + 3) * (q * q) * FNum q m J + 1) * dev q cs := by
      have h1 : (2 * J + 2) * (2 * m + 2 * J + 3) * (q * q)
            * (2 * J * (2 * m + 2 * J + 1) * q ^ (2 * cs.length) * PF q cs m (J - 1))
          ≤ (2 * J + 2) * (2 * m + 2 * J + 3) * (q * q) * (FNum q m J * dev q cs) :=
        Nat.mul_le_mul_left _ ih
      calc 2 * (J + 1) * (2 * m + 2 * (J + 1) + 1) * (q ^ (2 * cs.length) * (q * q))
            * (2 * J * (2 * m + 2 * J + 1) * PF q cs m (J - 1))
          = (2 * J + 2) * (2 * m + 2 * J + 3) * (q * q)
            * (2 * J * (2 * m + 2 * J + 1) * q ^ (2 * cs.length) * PF q cs m (J - 1)) := by
            ring_nat
        _ ≤ (2 * J + 2) * (2 * m + 2 * J + 3) * (q * q) * (FNum q m J * dev q cs) := h1
        _ = ((2 * J + 2) * (2 * m + 2 * J + 3) * (q * q) * FNum q m J) * dev q cs := by
            ring_nat
        _ ≤ ((2 * J + 2) * (2 * m + 2 * J + 3) * (q * q) * FNum q m J + 1) * dev q cs :=
            Nat.mul_le_mul (Nat.le_add_right _ 1) (Nat.le_refl _)
    calc 2 * (J + 1) * (2 * m + 2 * (J + 1) + 1) * (q ^ (2 * cs.length) * (q * q))
          * (c * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q cs m (J - 1))
        = 2 * (J + 1) * (2 * m + 2 * (J + 1) + 1) * (q ^ (2 * cs.length) * (q * q))
            * (c * FNum q m J)
          + 2 * (J + 1) * (2 * m + 2 * (J + 1) + 1) * (q ^ (2 * cs.length) * (q * q))
            * (2 * J * (2 * m + 2 * J + 1) * PF q cs m (J - 1)) := by ring_nat
      _ ≤ ((2 * J + 2) * (2 * m + 2 * J + 3) * (q * q) * FNum q m J + 1)
            * (c * q ^ (2 * cs.length))
          + ((2 * J + 2) * (2 * m + 2 * J + 3) * (q * q) * FNum q m J + 1) * dev q cs :=
          Nat.add_le_add hhead htail
      _ = ((2 * J + 2) * (2 * m + 2 * J + 3) * (q * q) * FNum q m J + 1)
            * (c * q ^ (2 * cs.length) + dev q cs) := by ring_nat

/-- ★★★★★ **The Chebyshev cross engine**: for equal-length lists with the minor
    condition (`a/b` increasing along positions),

      `[a·F_m]|_J · dev b ≤ dev a · [b·F_m]|_J`.

    The `PF`-weights shift mass to early positions relative to the `dev`-weights
    (weight dominance), and `a/b` increases — so the `PF`-average of `a/b` is the
    smaller.  Induction: tails by IH; the mixed-head terms reduce **exactly** to
    `weight_dom` on the pointwise gap list `g` (`b₀·as = a₀·bs + g`).  This is the
    order-transfer engine; instantiating `(a,b) = (AP, BP)` per parity (the minor
    sign of the convergent polynomials) is what remains of the weld. -/
theorem cross_le (q m : Nat) : ∀ (a b : List Nat) (J : Nat),
    a.length = b.length → MinorLE a b →
    PF q a m J * dev q b ≤ dev q a * PF q b m J
  | [], [], _, _, _ => Nat.le_refl _
  | [], _ :: _, _, h, _ => Nat.noConfusion h
  | _ :: _, [], _, h, _ => Nat.noConfusion h
  | a₀ :: as, b₀ :: bs, J, hlen, hminor => by
    obtain ⟨hsc, hm⟩ := hminor
    have hl : as.length = bs.length := Nat.succ.inj hlen
    have ih := cross_le q m as bs (J - 1) hl hm
    have hgadd : ladd (lsmul a₀ bs) (lsub (lsmul b₀ as) (lsmul a₀ bs)) = lsmul b₀ as :=
      ladd_lsub_recover a₀ b₀ as bs hl hsc
    have hglen : (lsub (lsmul b₀ as) (lsmul a₀ bs)).length = bs.length := by
      rw [lsub_length, lsmul_length, hl]
    have hdev : b₀ * dev q as
        = a₀ * dev q bs + dev q (lsub (lsmul b₀ as) (lsmul a₀ bs)) := by
      have h1 : dev q (lsmul b₀ as)
          = dev q (ladd (lsmul a₀ bs) (lsub (lsmul b₀ as) (lsmul a₀ bs))) :=
        congrArg (dev q) hgadd.symm
      rw [dev_lsmul,
          dev_ladd_eq q _ _ (by rw [lsmul_length, hglen]),
          dev_lsmul] at h1
      exact h1
    have hpf : b₀ * PF q as m (J - 1)
        = a₀ * PF q bs m (J - 1) + PF q (lsub (lsmul b₀ as) (lsmul a₀ bs)) m (J - 1) := by
      have h1 : PF q (lsmul b₀ as) m (J - 1)
          = PF q (ladd (lsmul a₀ bs) (lsub (lsmul b₀ as) (lsmul a₀ bs))) m (J - 1) :=
        congrArg (fun l => PF q l m (J - 1)) hgadd.symm
      rw [PF_lsmul, PF_ladd, PF_lsmul] at h1
      exact h1
    have hwd : 2 * J * (2 * m + 2 * J + 1) * q ^ (2 * bs.length)
          * PF q (lsub (lsmul b₀ as) (lsmul a₀ bs)) m (J - 1)
        ≤ FNum q m J * dev q (lsub (lsmul b₀ as) (lsmul a₀ bs)) := by
      have h := weight_dom q m (lsub (lsmul b₀ as) (lsmul a₀ bs)) J
      rwa [hglen] at h
    have e1 : PF q (a₀ :: as) m J * dev q (b₀ :: bs)
        = (a₀ * b₀ * (q ^ (2 * bs.length) * FNum q m J)
            + a₀ * FNum q m J * dev q bs
            + a₀ * (q ^ (2 * bs.length)
              * (2 * J * (2 * m + 2 * J + 1) * PF q bs m (J - 1))))
          + (q ^ (2 * bs.length) * (2 * J * (2 * m + 2 * J + 1)
              * PF q (lsub (lsmul b₀ as) (lsmul a₀ bs)) m (J - 1))
            + 2 * J * (2 * m + 2 * J + 1) * (PF q as m (J - 1) * dev q bs)) := by
      rw [show PF q (a₀ :: as) m J
            = a₀ * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q as m (J - 1) from rfl,
          dev_cons q b₀ bs,
          show (a₀ * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q as m (J - 1))
              * (b₀ * q ^ (2 * bs.length) + dev q bs)
            = q ^ (2 * bs.length) * (2 * J * (2 * m + 2 * J + 1)
                * (b₀ * PF q as m (J - 1)))
              + (a₀ * b₀ * (q ^ (2 * bs.length) * FNum q m J)
                + a₀ * FNum q m J * dev q bs
                + 2 * J * (2 * m + 2 * J + 1) * (PF q as m (J - 1) * dev q bs)) from by
            ring_nat,
          hpf]
      ring_nat
    have e2 : dev q (a₀ :: as) * PF q (b₀ :: bs) m J
        = (a₀ * b₀ * (q ^ (2 * bs.length) * FNum q m J)
            + a₀ * FNum q m J * dev q bs
            + a₀ * (q ^ (2 * bs.length)
              * (2 * J * (2 * m + 2 * J + 1) * PF q bs m (J - 1))))
          + (FNum q m J * dev q (lsub (lsmul b₀ as) (lsmul a₀ bs))
            + 2 * J * (2 * m + 2 * J + 1) * (dev q as * PF q bs m (J - 1))) := by
      rw [dev_cons q a₀ as, hl,
          show PF q (b₀ :: bs) m J
            = b₀ * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q bs m (J - 1) from rfl,
          show (a₀ * q ^ (2 * bs.length) + dev q as)
              * (b₀ * FNum q m J + 2 * J * (2 * m + 2 * J + 1) * PF q bs m (J - 1))
            = FNum q m J * (b₀ * dev q as)
              + (a₀ * b₀ * (q ^ (2 * bs.length) * FNum q m J)
                + a₀ * (q ^ (2 * bs.length)
                  * (2 * J * (2 * m + 2 * J + 1) * PF q bs m (J - 1)))
                + 2 * J * (2 * m + 2 * J + 1) * (dev q as * PF q bs m (J - 1))) from by
            ring_nat,
          hdev]
      ring_nat
    rw [e1, e2]
    refine Nat.add_le_add_left (Nat.add_le_add ?_ ?_) _
    · calc q ^ (2 * bs.length) * (2 * J * (2 * m + 2 * J + 1)
            * PF q (lsub (lsmul b₀ as) (lsmul a₀ bs)) m (J - 1))
          = 2 * J * (2 * m + 2 * J + 1) * q ^ (2 * bs.length)
            * PF q (lsub (lsmul b₀ as) (lsmul a₀ bs)) m (J - 1) := by ring_nat
        _ ≤ FNum q m J * dev q (lsub (lsmul b₀ as) (lsmul a₀ bs)) := hwd
    · exact Nat.mul_le_mul_left _ ih

end E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld
