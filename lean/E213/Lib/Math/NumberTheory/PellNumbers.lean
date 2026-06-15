import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Nat.PolyNatMTactic

/-!
# Elementary Pell-number identities (∅-axiom)

The Pell numbers `P` (`P 0=0, P 1=1, P(n+2)=2P(n+1)+P n`) and their half-companion
`H` (`H 0=1, H 1=1, H(n+2)=2H(n+1)+H n`), with:

  * ★ **`cassini`** — `Pₙ·P_{n+2} − P_{n+1}² = (−1)^{n+1}` (Pell Cassini).
  * ★★ **`norm`** — `Hₙ² − 2·Pₙ² = (−1)ⁿ`: `(Hₙ, Pₙ)` solve the Pell equation
    `x²−2y²=±1`, i.e. `(1+√2)ⁿ = Hₙ + Pₙ√2`.  Connects the Pell numbers to the
    `x²−2y²` norm form (`PellNorm.isPell`).

Genuinely absent — the corpus had Pell FSM/matrix work and the `x²−2y²` *form*
closures, but not the elementary Pell-number sequence, its Cassini, or the
half-companion norm identity.  `norm` needs a **triple invariant** (norm@n,
norm@(n+1), and the cross term `Hₙ·H_{n+1} − 2·Pₙ·P_{n+1} = (−1)ⁿ`) since the
recurrence expansion mixes both diagonal norms and the cross term.  All ∅-axiom
(two-step paired/triple induction over Int with `powInt (-1)` sign-flips).
-/

namespace E213.Lib.Math.NumberTheory.PellNumbers

open E213.Meta.Int213.PolyIntM (powInt)

/-- Pell numbers: `P 0 = 0`, `P 1 = 1`, `P (n+2) = 2·P(n+1) + P n`. -/
def P : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => 2 * P (n + 1) + P n

/-- Half-companion Pell: `H 0 = 1`, `H 1 = 1`, `H (n+2) = 2·H(n+1) + H n`. -/
def H : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * H (n + 1) + H n

theorem P_rec (n : Nat) : P (n + 2) = 2 * P (n + 1) + P n := rfl
theorem H_rec (n : Nat) : H (n + 2) = 2 * H (n + 1) + H n := rfl

theorem P_6 : P 6 = 70 := by decide
theorem H_4 : H 4 = 17 := by decide
/-- `H_3² − 2·P_3² = 49 − 50 = −1`. -/
theorem norm_smoke_3 :
    (H 3 : Int) * (H 3 : Int) - 2 * ((P 3 : Int) * (P 3 : Int)) = -1 := by decide

theorem P_rec_cast (n : Nat) :
    ((P (n + 2) : Nat) : Int) = 2 * (P (n + 1) : Int) + (P n : Int) := by
  rw [P_rec n, Int.ofNat_add (2 * P (n + 1)) (P n), Int.ofNat_mul 2 (P (n + 1))]; rfl

theorem H_rec_cast (n : Nat) :
    ((H (n + 2) : Nat) : Int) = 2 * (H (n + 1) : Int) + (H n : Int) := by
  rw [H_rec n, Int.ofNat_add (2 * H (n + 1)) (H n), Int.ofNat_mul 2 (H (n + 1))]; rfl

/-! ## Pell Cassini -/

/-- Paired two-step form: Cassini at `n` AND `n+1`. -/
theorem cassini_pair : ∀ n : Nat,
    ((P n : Int) * (P (n + 2) : Int) - (P (n + 1) : Int) * (P (n + 1) : Int)
        = powInt (-1) (n + 1))
    ∧ ((P (n + 1) : Int) * (P (n + 1 + 2) : Int)
          - (P (n + 1 + 1) : Int) * (P (n + 1 + 1) : Int)
        = powInt (-1) (n + 1 + 1)) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show (P 0 : Int) * (P 2 : Int) - (P 1 : Int) * (P 1 : Int) = powInt (-1) 1
      rw [show (P 0 : Int) = 0 from rfl, show (P 1 : Int) = 1 from rfl,
          show (P 2 : Int) = 2 from rfl]
      decide
    · show (P 1 : Int) * (P 3 : Int) - (P 2 : Int) * (P 2 : Int) = powInt (-1) 2
      rw [show (P 1 : Int) = 1 from rfl, show (P 2 : Int) = 2 from rfl,
          show (P 3 : Int) = 5 from rfl]
      decide
  | succ k ih =>
    obtain ⟨_, ih1⟩ := ih
    refine ⟨ih1, ?_⟩
    have ek4 : ((P (k + 1 + 1 + 2) : Nat) : Int)
        = 2 * (P (k + 1 + 1 + 1) : Int) + (P (k + 1 + 1) : Int) := P_rec_cast (k + 1 + 1)
    have ek3 : ((P (k + 1 + 1 + 1) : Nat) : Int)
        = 2 * (P (k + 1 + 1) : Int) + (P (k + 1) : Int) := P_rec_cast (k + 1)
    show (P (k + 1 + 1) : Int) * (P (k + 1 + 1 + 2) : Int)
          - (P (k + 1 + 1 + 1) : Int) * (P (k + 1 + 1 + 1) : Int)
        = powInt (-1) (k + 1 + 1 + 1)
    rw [ek4, ek3]
    have ihaligned :
        (P (k + 1) : Int) * (2 * (P (k + 1 + 1) : Int) + (P (k + 1) : Int))
          - (P (k + 1 + 1) : Int) * (P (k + 1 + 1) : Int)
        = powInt (-1) (k + 1 + 1) := by
      have e : ((P (k + 1 + 2) : Nat) : Int)
          = 2 * (P (k + 1 + 1) : Int) + (P (k + 1) : Int) := P_rec_cast (k + 1)
      rw [← e]; exact ih1
    rw [show powInt (-1 : Int) (k + 1 + 1 + 1) = powInt (-1) (k + 1 + 1) * (-1) from rfl,
        ← ihaligned]
    ring_intZ

/-- ★ **Pell Cassini**: `Pₙ·P_{n+2} − P_{n+1}² = (−1)^{n+1}`. -/
theorem cassini (n : Nat) :
    (P n : Int) * (P (n + 2) : Int) - (P (n + 1) : Int) * (P (n + 1) : Int)
      = powInt (-1) (n + 1) :=
  (cassini_pair n).1

/-! ## Half-companion ↔ Pell norm -/

/-- Triple invariant: norm@n, norm@(n+1), cross@n, each a power of `−1`. -/
theorem norm_triple : ∀ n : Nat,
    ((H n : Int) * (H n : Int) - 2 * ((P n : Int) * (P n : Int)) = powInt (-1) n)
    ∧ ((H (n + 1) : Int) * (H (n + 1) : Int)
          - 2 * ((P (n + 1) : Int) * (P (n + 1) : Int)) = powInt (-1) (n + 1))
    ∧ ((H n : Int) * (H (n + 1) : Int) - 2 * ((P n : Int) * (P (n + 1) : Int))
          = powInt (-1) n) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · show (H 0 : Int) * (H 0 : Int) - 2 * ((P 0 : Int) * (P 0 : Int)) = powInt (-1) 0
      rw [show (H 0 : Int) = 1 from rfl, show (P 0 : Int) = 0 from rfl]; decide
    · show (H 1 : Int) * (H 1 : Int) - 2 * ((P 1 : Int) * (P 1 : Int)) = powInt (-1) 1
      rw [show (H 1 : Int) = 1 from rfl, show (P 1 : Int) = 1 from rfl]; decide
    · show (H 0 : Int) * (H 1 : Int) - 2 * ((P 0 : Int) * (P 1 : Int)) = powInt (-1) 0
      rw [show (H 0 : Int) = 1 from rfl, show (H 1 : Int) = 1 from rfl,
          show (P 0 : Int) = 0 from rfl, show (P 1 : Int) = 1 from rfl]; decide
  | succ k ih =>
    obtain ⟨ih0, ih1, ihC⟩ := ih
    have eH : ((H (k + 1 + 1) : Nat) : Int)
        = 2 * (H (k + 1) : Int) + (H k : Int) := H_rec_cast k
    have eP : ((P (k + 1 + 1) : Nat) : Int)
        = 2 * (P (k + 1) : Int) + (P k : Int) := P_rec_cast k
    refine ⟨ih1, ?_, ?_⟩
    · show (H (k + 1 + 1) : Int) * (H (k + 1 + 1) : Int)
            - 2 * ((P (k + 1 + 1) : Int) * (P (k + 1 + 1) : Int))
          = powInt (-1) (k + 1 + 1)
      rw [eH, eP]
      have key :
          (2 * (H (k + 1) : Int) + (H k : Int)) * (2 * (H (k + 1) : Int) + (H k : Int))
            - 2 * ((2 * (P (k + 1) : Int) + (P k : Int))
                    * (2 * (P (k + 1) : Int) + (P k : Int)))
          = 4 * ((H (k + 1) : Int) * (H (k + 1) : Int)
                  - 2 * ((P (k + 1) : Int) * (P (k + 1) : Int)))
            + 4 * ((H k : Int) * (H (k + 1) : Int) - 2 * ((P k : Int) * (P (k + 1) : Int)))
            + ((H k : Int) * (H k : Int) - 2 * ((P k : Int) * (P k : Int))) := by
        ring_intZ
      rw [key, ih0, ih1, ihC]
      rw [show powInt (-1 : Int) (k + 1 + 1) = powInt (-1) k * (-1) * (-1) from rfl]
      rw [show powInt (-1 : Int) (k + 1) = powInt (-1) k * (-1) from rfl]
      ring_intZ
    · show (H (k + 1) : Int) * (H (k + 1 + 1) : Int)
            - 2 * ((P (k + 1) : Int) * (P (k + 1 + 1) : Int))
          = powInt (-1) (k + 1)
      rw [eH, eP]
      have key :
          (H (k + 1) : Int) * (2 * (H (k + 1) : Int) + (H k : Int))
            - 2 * ((P (k + 1) : Int) * (2 * (P (k + 1) : Int) + (P k : Int)))
          = 2 * ((H (k + 1) : Int) * (H (k + 1) : Int)
                  - 2 * ((P (k + 1) : Int) * (P (k + 1) : Int)))
            + ((H k : Int) * (H (k + 1) : Int) - 2 * ((P k : Int) * (P (k + 1) : Int))) := by
        ring_intZ
      rw [key, ih1, ihC]
      rw [show powInt (-1 : Int) (k + 1) = powInt (-1) k * (-1) from rfl]
      ring_intZ

/-- ★★ **Half-companion ↔ Pell norm**: `Hₙ² − 2·Pₙ² = (−1)ⁿ`.
    `(Hₙ, Pₙ)` solve `x² − 2y² = ±1`, i.e. `(1+√2)ⁿ = Hₙ + Pₙ√2`. -/
theorem norm (n : Nat) :
    (H n : Int) * (H n : Int) - 2 * ((P n : Int) * (P n : Int)) = powInt (-1) n :=
  (norm_triple n).1

/-! ## Addition and doubling formulas (over Nat)

The cross-step recurrences `P(m+1)=Pₘ+Hₘ`, `H(m+1)=2Pₘ+Hₘ` (from
`(1+√2)(Hₘ+Pₘ√2) = (Hₘ+2Pₘ)+(Hₘ+Pₘ)√2`) feed the addition formulas
`P(m+n)=Pₘ·Hₙ+Hₘ·Pₙ`, `H(m+n)=Hₘ·Hₙ+2PₘPₙ`, whence the doublings. -/

/-- Paired step invariant: `P(m+1)=Pₘ+Hₘ` AND `H(m+1)=2Pₘ+Hₘ`. -/
theorem step_pair : ∀ m : Nat,
    (P (m + 1) = P m + H m) ∧ (H (m + 1) = 2 * P m + H m) := by
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · show P 1 = P 0 + H 0
      rw [show P 1 = 1 from rfl, show P 0 = 0 from rfl, show H 0 = 1 from rfl]
    · show H 1 = 2 * P 0 + H 0
      rw [show H 1 = 1 from rfl, show P 0 = 0 from rfl, show H 0 = 1 from rfl]
  | succ k ih =>
    obtain ⟨ihP, ihH⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [P_rec k, ihP, ihH]; ring_nat
    · rw [H_rec k, ihP, ihH]; ring_nat

theorem P_step (m : Nat) : P (m + 1) = P m + H m := (step_pair m).1
theorem H_step (m : Nat) : H (m + 1) = 2 * P m + H m := (step_pair m).2

/-- Paired addition invariant: P-add and H-add at `n` AND at `n+1`. -/
theorem add_pair (m : Nat) : ∀ n : Nat,
    (P (m + n) = P m * H n + H m * P n)
    ∧ (H (m + n) = H m * H n + 2 * (P m * P n))
    ∧ (P (m + (n + 1)) = P m * H (n + 1) + H m * P (n + 1))
    ∧ (H (m + (n + 1)) = H m * H (n + 1) + 2 * (P m * P (n + 1))) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show P (m + 0) = P m * H 0 + H m * P 0
      rw [show H 0 = 1 from rfl, show P 0 = 0 from rfl, Nat.add_zero,
          Nat.mul_one, Nat.mul_zero, Nat.add_zero]
    · show H (m + 0) = H m * H 0 + 2 * (P m * P 0)
      rw [show H 0 = 1 from rfl, show P 0 = 0 from rfl, Nat.add_zero,
          Nat.mul_one, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
    · show P (m + (0 + 1)) = P m * H (0 + 1) + H m * P (0 + 1)
      rw [show (0 : Nat) + 1 = 1 from rfl, show H 1 = 1 from rfl,
          show P 1 = 1 from rfl, P_step m, Nat.mul_one, Nat.mul_one]
    · show H (m + (0 + 1)) = H m * H (0 + 1) + 2 * (P m * P (0 + 1))
      rw [show (0 : Nat) + 1 = 1 from rfl, show H 1 = 1 from rfl,
          show P 1 = 1 from rfl, H_step m, Nat.mul_one, Nat.mul_one]
      ring_nat
  | succ k ih =>
    obtain ⟨ihP0, ihH0, ihP1, ihH1⟩ := ih
    refine ⟨ihP1, ihH1, ?_, ?_⟩
    · have ePidx : P (m + (k + 1 + 1)) = 2 * P (m + (k + 1)) + P (m + k) := by
        rw [show m + (k + 1 + 1) = (m + k) + 2 from by ring_nat,
            show m + (k + 1) = (m + k) + 1 from by ring_nat]
        exact P_rec (m + k)
      have eH : H (k + 1 + 1) = 2 * H (k + 1) + H k := H_rec k
      have eP : P (k + 1 + 1) = 2 * P (k + 1) + P k := P_rec k
      rw [ePidx, eH, eP, ihP1, ihP0]
      ring_nat
    · have eHidx : H (m + (k + 1 + 1)) = 2 * H (m + (k + 1)) + H (m + k) := by
        rw [show m + (k + 1 + 1) = (m + k) + 2 from by ring_nat,
            show m + (k + 1) = (m + k) + 1 from by ring_nat]
        exact H_rec (m + k)
      have eH : H (k + 1 + 1) = 2 * H (k + 1) + H k := H_rec k
      have eP : P (k + 1 + 1) = 2 * P (k + 1) + P k := P_rec k
      rw [eHidx, eH, eP, ihH1, ihH0]
      ring_nat

/-- ★ **Pell addition formula (P)**: `P (m+n) = Pₘ·Hₙ + Hₘ·Pₙ`. -/
theorem P_add (m n : Nat) : P (m + n) = P m * H n + H m * P n :=
  (add_pair m n).1

/-- ★ **Pell addition formula (H)**: `H (m+n) = Hₘ·Hₙ + 2·Pₘ·Pₙ`. -/
theorem H_add (m n : Nat) : H (m + n) = H m * H n + 2 * (P m * P n) :=
  (add_pair m n).2.1

/-- ★ **Pell doubling (P)**: `P (2n) = 2·Pₙ·Hₙ`. -/
theorem P_double (n : Nat) : P (2 * n) = 2 * (P n * H n) := by
  rw [show 2 * n = n + n from by ring_nat, P_add n n]
  ring_nat

/-- ★ **Pell doubling (H)**: `H (2n) = Hₙ² + 2·Pₙ²`. -/
theorem H_double (n : Nat) : H (2 * n) = H n * H n + 2 * (P n * P n) := by
  rw [show 2 * n = n + n from by ring_nat, H_add n n]

end E213.Lib.Math.NumberTheory.PellNumbers
