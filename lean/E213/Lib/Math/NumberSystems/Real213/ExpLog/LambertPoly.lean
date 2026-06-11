import E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CothSeriesCut
import E213.Meta.Nat.PolyNatMTactic

/-!
# LambertPoly — the constant-first polynomial layer (the weld's connection infra)

`LowerBase`'s last layer is per-`q²`-grade: the product `devA·s_J` must be
compared with `(2J+1)·devB·c_J` **coefficientwise** (every evaluated shortcut
fails at the margins — the per-grade cancellation is the content).  This file
provides the grading infrastructure:

  * `evc` — constant-first evaluation `evc q (c :: cs) = c + q²·evc q cs`
    (position = `q²`-power).  Unlike `dev` (head = highest power), **no length
    conditions appear anywhere**: `evc_ladd` is unconditional, and the polynomial
    product is the standard recursion `lmulC (a :: as) b = ladd (lsmul a b)
    (0 :: lmulC as b)` with `evc_lmulC : evc (lmulC a b) = evc a · evc b`.
  * `rev` + `dev_eq_evc_rev` — the bridge to the weld's `dev`-world:
    `dev q l = evc q (rev l)`, so `dev q (AP n)` enters the graded layer as
    `evc q (rev (AP n))`.
  * `cListC/sListC` — the coefficient lists of the cleared cosh/sinh partials
    (`evc_cListC : evc q (cListC J) = coshNum q J`, likewise sinh).
  * the **connection statements** (`conn_A`, `conn_B`): the two sides of the
    `LowerBase` cross are `evc`s of explicit convolutions —
    `devA·s_J = evc (lmulC (rev (AP (2i+1))) (sListC J))` and
    `(2J+1)·devB·c_J = evc (lmulC (rev (BP (2i+1))) (lsmul (2J+1) (cListC J)))`.

What remains after this file: the per-coefficient comparison of the two
convolutions through the master identity (`LambertMasterId`) + halving — the
coefficient recursion `nth (lmulC (a :: as) b) (p+1) = a·nth b (p+1) +
nth (lmulC as b) p` needs no closed convolution formula.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertPoly

open E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertWeld
  (ladd lsmul AP BP dev dev_cons coshNum sinhNum)

/-! ## §1 — constant-first evaluation -/

/-- Constant-first evaluation at `q²`: position = power.  The dual of `dev`. -/
def evc (q : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs => c + q ^ 2 * evc q cs

/-- `evc` is additive over `ladd` — **no length condition** (the tail padding is
    on the high-power side, which `evc` reads correctly). -/
theorem evc_ladd (q : Nat) : ∀ (a b : List Nat),
    evc q (ladd a b) = evc q a + evc q b
  | [], b => (Nat.zero_add (evc q b)).symm
  | _ :: _, [] => (Nat.add_zero _).symm
  | a :: as, b :: bs => by
    show (a + b) + q ^ 2 * evc q (ladd as bs) = (a + q ^ 2 * evc q as) + (b + q ^ 2 * evc q bs)
    rw [evc_ladd q as bs]
    ring_nat

theorem evc_lsmul (q k : Nat) : ∀ l : List Nat, evc q (lsmul k l) = k * evc q l
  | [] => (Nat.mul_zero k).symm
  | c :: cs => by
    show k * c + q ^ 2 * evc q (lsmul k cs) = k * (c + q ^ 2 * evc q cs)
    rw [evc_lsmul q k cs]
    ring_nat

theorem evc_shift (q : Nat) (l : List Nat) : evc q (0 :: l) = q ^ 2 * evc q l := by
  show 0 + q ^ 2 * evc q l = q ^ 2 * evc q l
  rw [Nat.zero_add]

/-! ## §2 — the polynomial product -/

/-- Constant-first polynomial product: the standard convolution recursion. -/
def lmulC : List Nat → List Nat → List Nat
  | [], _ => []
  | a :: as, b => ladd (lsmul a b) (0 :: lmulC as b)

/-- ★★★ **`evc` is multiplicative**: `evc (lmulC a b) = evc a · evc b` —
    two-line induction thanks to the unconditional `evc_ladd`. -/
theorem evc_lmulC (q : Nat) : ∀ (a b : List Nat),
    evc q (lmulC a b) = evc q a * evc q b
  | [], b => by
    show (0 : Nat) = 0 * evc q b
    rw [Nat.zero_mul]
  | a :: as, b => by
    show evc q (ladd (lsmul a b) (0 :: lmulC as b)) = (a + q ^ 2 * evc q as) * evc q b
    rw [evc_ladd, evc_lsmul, evc_shift, evc_lmulC q as b]
    ring_nat

/-! ## §3 — the reversal bridge to `dev` -/

/-- List reversal (own recursion, defeq-controlled). -/
def rev : List Nat → List Nat
  | [] => []
  | c :: cs => rev cs ++ [c]

theorem len_app_single : ∀ (l : List Nat) (c : Nat), (l ++ [c]).length = l.length + 1
  | [], _ => rfl
  | _ :: cs, c => congrArg (· + 1) (len_app_single cs c)

theorem len_rev : ∀ l : List Nat, (rev l).length = l.length
  | [] => rfl
  | c :: cs => by
    show (rev cs ++ [c]).length = cs.length + 1
    rw [len_app_single (rev cs) c, len_rev cs]

/-- Appending a constant adds it at the top power. -/
theorem evc_append_single (q : Nat) : ∀ (l : List Nat) (c : Nat),
    evc q (l ++ [c]) = evc q l + c * q ^ (2 * l.length)
  | [], c => by
    show c + q ^ 2 * 0 = 0 + c * q ^ (2 * 0)
    rw [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    show c = c * q ^ 0
    rw [Nat.pow_zero, Nat.mul_one]
  | x :: xs, c => by
    show x + q ^ 2 * evc q (xs ++ [c])
        = (x + q ^ 2 * evc q xs) + c * q ^ (2 * (xs.length + 1))
    rw [evc_append_single q xs c,
        show q ^ (2 * (xs.length + 1)) = q ^ (2 * xs.length) * (q * q) from by
          show q ^ (2 * xs.length + 2) = q ^ (2 * xs.length) * (q * q)
          rw [Nat.pow_succ, Nat.pow_succ]; ring_nat,
        show (q : Nat) ^ 2 = q * q from by rw [Nat.pow_succ, Nat.pow_one]]
    ring_nat

/-- ★★★ **The bridge**: `dev q l = evc q (rev l)` — the weld's head-first world
    enters the constant-first graded layer. -/
theorem dev_eq_evc_rev (q : Nat) : ∀ l : List Nat, dev q l = evc q (rev l)
  | [] => rfl
  | c :: cs => by
    rw [dev_cons q c cs,
        show rev (c :: cs) = rev cs ++ [c] from rfl,
        evc_append_single q (rev cs) c, len_rev cs, dev_eq_evc_rev q cs,
        Nat.add_comm (evc q (rev cs)) (c * q ^ (2 * cs.length))]

/-! ## §4 — the cosh/sinh coefficient lists -/

/-- Constant-first coefficient list of `coshNum q J` (`q`-free!):
    `cListC (J+1) = 1 :: (2J+1)(2J+2)·cListC J`. -/
def cListC : Nat → List Nat
  | 0 => [1]
  | J + 1 => 1 :: lsmul ((2 * J + 1) * (2 * J + 2)) (cListC J)

/-- Constant-first coefficient list of `sinhNum q J`. -/
def sListC : Nat → List Nat
  | 0 => [1]
  | J + 1 => 1 :: lsmul ((2 * J + 2) * (2 * J + 3)) (sListC J)

theorem evc_cListC (q : Nat) : ∀ J, evc q (cListC J) = coshNum q J
  | 0 => by
    show 1 + q ^ 2 * 0 = 1
    rw [Nat.mul_zero]
  | J + 1 => by
    show 1 + q ^ 2 * evc q (lsmul ((2 * J + 1) * (2 * J + 2)) (cListC J))
        = (2 * J + 1) * (2 * J + 2) * q ^ 2 * coshNum q J + 1
    rw [evc_lsmul, evc_cListC q J]
    ring_nat

theorem evc_sListC (q : Nat) : ∀ J, evc q (sListC J) = sinhNum q J
  | 0 => by
    show 1 + q ^ 2 * 0 = 1
    rw [Nat.mul_zero]
  | J + 1 => by
    show 1 + q ^ 2 * evc q (lsmul ((2 * J + 2) * (2 * J + 3)) (sListC J))
        = (2 * J + 2) * (2 * J + 3) * q ^ 2 * sinhNum q J + 1
    rw [evc_lsmul, evc_sListC q J]
    ring_nat

/-! ## §5 — the connection: both `LowerBase` sides are `evc`s of convolutions -/

/-- ★★★★ The `A`-side of the `LowerBase` cross as a graded object:
    `dev (AP (2i+1)) · sinhNum q J = evc (lmulC (rev (AP (2i+1))) (sListC J))`. -/
theorem conn_A (q n J : Nat) :
    dev q (AP n) * sinhNum q J = evc q (lmulC (rev (AP n)) (sListC J)) := by
  rw [evc_lmulC, ← dev_eq_evc_rev, evc_sListC]

/-- ★★★★ The `B`-side:
    `(2J+1) · dev (BP (2i+1)) · coshNum q J
       = evc (lmulC (rev (BP (2i+1))) (lsmul (2J+1) (cListC J)))`. -/
theorem conn_B (q n J : Nat) :
    (2 * J + 1) * dev q (BP n) * coshNum q J
      = evc q (lmulC (rev (BP n)) (lsmul (2 * J + 1) (cListC J))) := by
  rw [evc_lmulC, ← dev_eq_evc_rev, evc_lsmul, evc_cListC]
  ring_nat

/-- Anchors: the graded layer reproduces the evaluated world (`q = 2`, `i = 1`,
    `J = 3`), and the two `LowerBase` sides match their convolutions. -/
theorem anchors :
    evc 2 (lmulC (rev (AP 3)) (sListC 3)) = dev 2 (AP 3) * sinhNum 2 3
    ∧ evc 2 (lmulC (rev (BP 3)) (lsmul 7 (cListC 3))) = 7 * dev 2 (BP 3) * coshNum 2 3
    ∧ rev (AP 3) = [6, 15] ∧ cListC 2 = [1, 12, 24] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

end E213.Lib.Math.NumberSystems.Real213.ExpLog.LambertPoly
