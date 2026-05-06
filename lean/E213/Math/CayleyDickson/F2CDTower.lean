import E213.Firmware.Raw
import E213.Hypervisor.Lens

/-!
# F2CDTower: CD tower over 𝔽₂ — Bool/CD crossing point

Note 26 claim: CD construction applied to Bool (= 𝔽₂) gives
finite 2^(2^k)-dim 𝔽₂-algebras at each layer.  These sit at
the intersection of:

- **CD tower** (algebraic signature: multiplication + conj)
- **Bool tower** (bootstrap-free finite structure)

Layer 1 turns out to be **dual numbers** 𝔽₂[ε]/(ε²), NOT
complex numbers — char-2 collapses the CD doubling differently.

## §1. Layer 0: 𝔽₂ = Bool

Base is Lean's `Bool` with `xor` as addition and `and` as
multiplication.  Involution is identity.
-/

namespace E213.Math.CayleyDickson.F2CDTower

/-- Bool as 𝔽₂ — addition = xor. -/
abbrev F2 := Bool

/-- 𝔽₂ multiplication = and. -/
def F2.mul (a b : F2) : F2 := a && b

/-- 𝔽₂ addition = xor. -/
def F2.add (a b : F2) : F2 := xor a b

/-- 𝔽₂ involution = identity (char-2 self-dual). -/
def F2.conj (a : F2) : F2 := a

theorem F2.conj_involutive : ∀ a : F2, F2.conj (F2.conj a) = a := by
  intro a; rfl

theorem F2.add_self : ∀ a : F2, F2.add a a = false := by
  intro a; cases a <;> rfl

/-! ## §2. Layer 1: 𝔽₂[ε]/(ε²) — dual numbers

CD doubling: F2D := F2 × F2.  Multiplication (char-2 adjusted):
  (a, b) · (c, d) = (a·c + b·d, a·d + b·c)

In char 2 minus signs vanish.
-/

/-- CD Layer 1 over 𝔽₂.  Underlying set = Bool × Bool. -/
abbrev F2D := F2 × F2

/-- CD multiplication, char-2 version. -/
def F2D.mul (p q : F2D) : F2D :=
  (xor (p.1 && q.1) (p.2 && q.2),
   xor (p.1 && q.2) (p.2 && q.1))

def F2D.zero : F2D := (false, false)
def F2D.one  : F2D := (true,  false)

/-- The "imaginary-like" element.  Will turn out NOT to satisfy
    e² = -1 (since in char 2, -1 = 1).  Actually e² = 1 here. -/
def F2D.e : F2D := (false, true)

/-- The "nilpotent" element.  Satisfies ε² = 0. -/
def F2D.eps : F2D := (true, true)

/-- **Identity check**: 1 · x = x. -/
theorem F2D.one_mul : ∀ x : F2D, F2D.mul F2D.one x = x := by
  intro ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- **Zero check**: 0 · x = 0. -/
theorem F2D.zero_mul : ∀ x : F2D, F2D.mul F2D.zero x = F2D.zero := by
  intro ⟨a, b⟩
  cases a <;> cases b <;> rfl

/-- **e² = 1** (not -1, because char 2). -/
theorem F2D.e_sq_is_one : F2D.mul F2D.e F2D.e = F2D.one := by
  decide

/-- **ε² = 0** — the nilpotent relation.  This is the key
    char-2 CD collapse: instead of imaginary (e² = -1), we
    get a nilpotent (ε² = 0). -/
theorem F2D.eps_sq_is_zero : F2D.mul F2D.eps F2D.eps = F2D.zero := by
  decide

/-! ## §3. Structural properties of F2D

Layer 1 over 𝔽₂ is commutative (unlike quaternions!),
has zero divisors (ε · ε = 0), and is NOT a field.

These collectively identify F2D with `𝔽₂[ε]/(ε²)`, the dual
numbers over 𝔽₂.
-/

/-- **Commutativity**.  F2D is commutative because char 2
    collapses the CD "twist". -/
theorem F2D.mul_comm : ∀ p q : F2D, F2D.mul p q = F2D.mul q p := by
  intro ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

/-- **Zero divisor**: ε is a zero divisor (ε · ε = 0). -/
theorem F2D.has_zero_divisors :
    ∃ x : F2D, x ≠ F2D.zero ∧ F2D.mul x x = F2D.zero := by
  refine ⟨F2D.eps, ?_, F2D.eps_sq_is_zero⟩
  intro h
  have : (F2D.eps : F2 × F2) = (false, false) := h
  have h1 : F2D.eps.1 = false := by rw [this]
  exact absurd h1 (by decide)

/-- **Full multiplication table** as a sanity check. -/
example : F2D.mul F2D.one F2D.eps = F2D.eps := by decide
example : F2D.mul F2D.e F2D.eps = (true, true) := by decide
  -- e · ε = (F, T)(T, T) = (F·T + T·T, F·T + T·T) = (T, T) = ε

/-- **F2D is NOT a field** — ε has no multiplicative inverse.
    Any `F2D.mul eps y` has form `(y.1 xor y.2, y.1 xor y.2)`
    whose two components are equal — so it can never equal
    `(true, false) = one`. -/
theorem F2D.eps_has_no_inverse :
    ¬ ∃ y : F2D, F2D.mul F2D.eps y = F2D.one := by
  rintro ⟨⟨a, b⟩, hy⟩
  cases a <;> cases b <;> (revert hy; decide)

/-! ## §4. Summary: What CD-over-𝔽₂ Layer 1 is

Collecting the proofs above:

| Property | F2D (𝔽₂[ε]/ε²) | ℂ (CD-over-ℝ L1) |
|----------|-----------------|------------------|
| underlying | Bool × Bool (4 elem) | ℝ × ℝ (continuous) |
| commutative | ✓ `F2D.mul_comm` | ✓ |
| zero divisors | ✓ `F2D.has_zero_divisors` | ✗ |
| field | ✗ `F2D.eps_has_no_inverse` | ✓ |
| ε² = 0 | ✓ `F2D.eps_sq_is_zero` | N/A |
| i² = -1 | `e² = 1` (char 2 collapse) | ✓ |
| bootstrap | **none** | via Nat bootstrap |

Layer 1 over 𝔽₂ is the **dual-number ring** 𝔽₂[ε]/ε² — a
finite commutative ring with nilpotent ε.  It's NOT ℂ (which
requires i² = -1 ≠ 1, failing in char 2).

### Crossing point confirmed

This file provides **Lean-verified evidence** for note 26's
claim: the CD construction, when applied over 𝔽₂ (= Bool),
lives inside the Bool tower — finite, bootstrap-free — while
inheriting the CD algebraic structure (mult, conj, norm —
though here degenerate in specific ways due to char 2).

The CD-over-𝔽₂ tower is therefore a **parallel CD tower** to
CD-over-ℝ, sharing the construction but differing in algebraic
character due to char-2 collapse.

### Status: Layer 2 not yet

Layer 2 would be 16-element 𝔽₂-algebra.  Deferred to follow-up
session if productive.
-/

end E213.Math.CayleyDickson.F2CDTower
