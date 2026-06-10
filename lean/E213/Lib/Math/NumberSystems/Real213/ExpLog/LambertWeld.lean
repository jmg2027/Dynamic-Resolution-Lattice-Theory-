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

end E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld
