import E213.Meta.Tactic.NatHelper

/-!
# Lens.Number.Nat213.Peano — proper 213-native ℕ_+ type (inductive)

A 213-native ℕ that excludes 0.  Following the Raw axiom:
- Raw has at least one atom (a or b)
- Atom count of any Raw is therefore ≥ 1
- The natural counting object is **positive naturals**

This is distinct from Lean's `Nat` (which has 0) and matches the
original Peano definition of natural numbers.

**Why no 0**: 0 is not derivable from Raw — it
emerges only at the level of structural extensions (orthogonal-
axis quotients, group completions, etc.).  Including 0 in the
"primitive counting" type imports a non-Raw element.

**Operations**:
- `add` : closed (m + n ≥ 1 ∧ ≥ both)
- `mul` : closed (1 acts as identity, no absorption)
- `sub` : NOT defined (would require ℤ extension)

All theorems satisfy ∅-axiom standard.

**Framing (per `seed/AXIOM/06_lens_readings.md`).**  This
inductive `Nat213` is an *ergonomic parallel* to the lens-derived
form; it is not itself lens-derived.  The `.Bridge` module witnesses
the iso to the Method A chain (`.Raw`); `Lens.leaves` then maps both
to `Nat`.  Long-form discussion + open question on the future of
this file 
and §6 question 5.
-/

namespace E213.Lens.Number.Nat213.Peano

/-- 213-native positive naturals.  Inductive Peano ℕ_+. -/
inductive Nat213 : Type
  | one  : Nat213
  | succ : Nat213 → Nat213
  deriving DecidableEq, Repr

namespace Nat213

/-- Literal `2` shortcut. -/
def two   : Nat213 := succ one
/-- Literal `3` shortcut. -/
def three : Nat213 := succ two
/-- Literal `4` shortcut. -/
def four  : Nat213 := succ three
/-- Literal `5` shortcut (= d, universe size). -/
def five  : Nat213 := succ four

/-- Embed Nat213 into Lean Nat. -/
def toNat : Nat213 → Nat
  | one    => 1
  | succ n => n.toNat + 1

/-- Addition: m + n.  Closed since result ≥ max(m, n) ≥ 1. -/
def add : Nat213 → Nat213 → Nat213
  | one,    n => succ n
  | succ m, n => succ (add m n)

instance : Add Nat213 := ⟨add⟩

/-- Multiplication: m · n.  Closed since 1 is identity. -/
def mul : Nat213 → Nat213 → Nat213
  | one,    n => n
  | succ m, n => add n (mul m n)

instance : Mul Nat213 := ⟨mul⟩

-- ═══ Properties: closure, identity ═══

/-- ★ `toNat n ≥ 1` — closure: Nat213 contains no element ≤ 0. -/
theorem toNat_ge_one : ∀ n : Nat213, n.toNat ≥ 1
  | one    => Nat.le_refl 1
  | succ m => by
      show m.toNat + 1 ≥ 1
      exact Nat.succ_pos m.toNat

/-- ★ `toNat (add m n) = m.toNat + n.toNat` — additive homomorphism. -/
theorem toNat_add (m n : Nat213) : (add m n).toNat = m.toNat + n.toNat := by
  induction m with
  | one =>
      show (succ n).toNat = 1 + n.toNat
      show n.toNat + 1 = 1 + n.toNat
      exact Nat.add_comm _ _
  | succ k ih =>
      show (add k n).toNat + 1 = (k.toNat + 1) + n.toNat
      rw [ih]
      exact (Nat.add_right_comm _ _ _).symm

/-- ★ `toNat (mul m n) = m.toNat * n.toNat` — multiplicative homomorphism. -/
theorem toNat_mul (m n : Nat213) : (mul m n).toNat = m.toNat * n.toNat := by
  induction m with
  | one =>
      show n.toNat = 1 * n.toNat
      rw [Nat.one_mul]
  | succ k ih =>
      show (add n (mul k n)).toNat = (k.toNat + 1) * n.toNat
      rw [toNat_add, ih, Nat.succ_mul, Nat.add_comm]

/-- ★ `1 · n = n` — multiplicative identity. -/
theorem one_mul (n : Nat213) : mul one n = n := rfl

/-- ★ `n · 1 = n` — right identity (induction since mul recurses left). -/
theorem mul_one : ∀ n : Nat213, mul n one = n
  | one    => rfl
  | succ m => by
      show add one (mul m one) = succ m
      show succ (mul m one) = succ m
      rw [mul_one m]

/-- ★ `add (succ m) n = succ (add m n)` — successor on left. -/
theorem add_succ_left (m n : Nat213) :
    add (succ m) n = succ (add m n) := rfl

/-- ★ `one + n = succ n` — adding 1 yields successor. -/
theorem one_add (n : Nat213) : add one n = succ n := rfl

/-- ★ `n + one = succ n` — right-identity-succ.  Induction on n. -/
theorem add_one_right : ∀ n : Nat213, add n one = succ n
  | one    => rfl
  | succ k => by
      show succ (add k one) = succ (succ k)
      rw [add_one_right k]

/-- ★ `m + (succ n) = succ (m + n)` — succ on right.  Induction. -/
theorem add_succ_right : ∀ m n : Nat213, add m (succ n) = succ (add m n)
  | one,    n => rfl
  | succ m, n => by
      show succ (add m (succ n)) = succ (succ (add m n))
      rw [add_succ_right m n]

/-- ★ Commutativity of `add`.  Standard induction. -/
theorem add_comm : ∀ m n : Nat213, add m n = add n m
  | one,    one    => rfl
  | one,    succ k => by
      show succ (succ k) = add (succ k) one
      rw [add_one_right (succ k)]
  | succ m, n      => by
      show succ (add m n) = add n (succ m)
      rw [add_succ_right n m, add_comm m n]

/-- ★ Associativity of `add`.  Structural induction on the first
    argument (`add` recurses left). -/
theorem add_assoc : ∀ a b c : Nat213, add (add a b) c = add a (add b c)
  | one,    b, c => rfl
  | succ k, b, c => by
      show succ (add (add k b) c) = succ (add k (add b c))
      rw [add_assoc k b c]

/-- ★ `m * succ n = m + m * n` — succ on the right factor.
    Symmetric to the definition `mul (succ k) n = add n (mul k n)`,
    which is `rfl`.  Proven by induction on `m` using `add_assoc`
    + `add_comm`. -/
theorem mul_succ_right : ∀ m n : Nat213, mul m (succ n) = add m (mul m n)
  | one,    n => rfl
  | succ k, n => by
      show add (succ n) (mul k (succ n)) = add (succ k) (add n (mul k n))
      rw [mul_succ_right k n]
      rw [← add_assoc (succ n) k (mul k n),
          ← add_assoc (succ k) n (mul k n)]
      show add (succ n) k + mul k n = add (succ k) n + mul k n
      rw [show add (succ n) k = succ (add n k) from rfl,
          show add (succ k) n = succ (add k n) from rfl,
          add_comm n k]

/-- ★ Commutativity of `mul`. -/
theorem mul_comm : ∀ m n : Nat213, mul m n = mul n m
  | one,    n => (mul_one n).symm
  | succ k, n => by
      show add n (mul k n) = mul n (succ k)
      rw [mul_succ_right n k, mul_comm k n]

/-- ★ Right distributivity: `(a + b) * c = a*c + b*c`. -/
theorem add_mul : ∀ a b c : Nat213, mul (add a b) c = add (mul a c) (mul b c)
  | one,    b, c => by
      show mul (succ b) c = add c (mul b c)
      rfl
  | succ k, b, c => by
      show mul (succ (add k b)) c = add (mul (succ k) c) (mul b c)
      show add c (mul (add k b) c) = add (add c (mul k c)) (mul b c)
      rw [add_mul k b c, add_assoc]

/-- ★ Associativity of `mul`.  Uses `add_mul` distributivity. -/
theorem mul_assoc : ∀ a b c : Nat213, mul (mul a b) c = mul a (mul b c)
  | one,    b, c => rfl
  | succ k, b, c => by
      rw [show mul (succ k) b = add b (mul k b) from rfl,
          add_mul b (mul k b) c, mul_assoc k b c]
      rfl

/-- ★ Left distributivity: `a * (b + c) = a*b + a*c`.  Derived from
    `add_mul` + `mul_comm`. -/
theorem mul_add (a b c : Nat213) : mul a (add b c) = add (mul a b) (mul a c) := by
  rw [mul_comm a (add b c), add_mul, mul_comm b a, mul_comm c a]

/-- ★ Left cancellation for `add`: `a + b = a + c → b = c`. -/
theorem add_left_cancel : ∀ {a b c : Nat213}, add a b = add a c → b = c
  | one,    _, _ => Nat213.succ.inj
  | succ _, _, _ => fun h => add_left_cancel (Nat213.succ.inj h)

/-- ★ Right cancellation for `add`: `a + c = b + c → a = b`. -/
theorem add_right_cancel {a b c : Nat213} (h : add a c = add b c) : a = b := by
  apply add_left_cancel (a := c)
  rw [add_comm c a, add_comm c b]
  exact h

/-- ★ Injectivity of `toNat` on `Nat213`.  Every `Nat213` element is
    determined by its `toNat` projection.  Proven by structural
    induction; the impossible cases (`one` ↔ `succ k`) use
    `toNat_ge_one` to derive a contradiction. -/
theorem toNat_injective : ∀ {a b : Nat213}, a.toNat = b.toNat → a = b
  | one,    one,    _ => rfl
  | one,    succ k, h => by
      have h0 : (0 : Nat) + 1 = k.toNat + 1 := h
      have heq : (0 : Nat) = k.toNat :=
        E213.Tactic.NatHelper.add_right_cancel h0
      have hge : k.toNat ≥ 1 := toNat_ge_one k
      rw [← heq] at hge
      exact absurd hge (by decide)
  | succ k, one,    h => by
      have h0 : k.toNat + 1 = (0 : Nat) + 1 := h
      have heq : k.toNat = (0 : Nat) :=
        E213.Tactic.NatHelper.add_right_cancel h0
      have hge : k.toNat ≥ 1 := toNat_ge_one k
      rw [heq] at hge
      exact absurd hge (by decide)
  | succ k, succ m, h => by
      have h' : k.toNat + 1 = m.toNat + 1 := h
      have h'' : k.toNat = m.toNat :=
        E213.Tactic.NatHelper.add_right_cancel h'
      have hkm : k = m := toNat_injective h''
      rw [hkm]

/-- ★ Left cancellation for `mul`: `a * b = a * c → b = c`.  Since
    every `Nat213` is positive, no zero-divisor issue. -/
theorem mul_left_cancel {a b c : Nat213} (h : mul a b = mul a c) : b = c := by
  have hnat : (mul a b).toNat = (mul a c).toNat := congrArg toNat h
  rw [toNat_mul, toNat_mul] at hnat
  have hpos : 0 < a.toNat := toNat_ge_one a
  have hbc : b.toNat = c.toNat :=
    E213.Tactic.NatHelper.mul_left_cancel_pos hpos hnat
  exact toNat_injective hbc

/-- ★ Right cancellation for `mul`: `a * c = b * c → a = b`. -/
theorem mul_right_cancel {a b c : Nat213} (h : mul a c = mul b c) : a = b := by
  apply mul_left_cancel (a := c)
  rw [mul_comm c a, mul_comm c b]
  exact h

/-- ★ `add` left-commute: `a + (b + c) = b + (a + c)`.  Normalisation
    helper. -/
theorem add_left_comm (a b c : Nat213) : add a (add b c) = add b (add a c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

/-- ★ `mul` left-commute: `a * (b * c) = b * (a * c)`. -/
theorem mul_left_comm (a b c : Nat213) : mul a (mul b c) = mul b (mul a c) := by
  rw [← mul_assoc, mul_comm a b, mul_assoc]

/-- ★ `n * 2 = n + n`.  The two definitions of doubling agree.
    (Here `2 = succ one`, since `Nat213` has no zero.) -/
theorem mul_two (n : Nat213) : mul n (succ one) = add n n := by
  rw [mul_succ_right, mul_one]

-- ═══ Exponentiation ═══

/-- Exponentiation `a^n`, recursion on the exponent.  No zero exponent (`Nat213` has no zero);
    the base is `a^1 = a` (`pow a one = a`), and `a^(n+1) = a · a^n`. -/
def pow : Nat213 → Nat213 → Nat213
  | a, one    => a
  | a, succ n => mul a (pow a n)

/-- `a^1 = a` (the base of the exponent recursion). -/
theorem pow_one (a : Nat213) : pow a one = a := rfl

/-- `a^(n+1) = a · a^n` (the recursion step). -/
theorem pow_succ (a n : Nat213) : pow a (succ n) = mul a (pow a n) := rfl

/-- ★ `1^n = 1` — the unit is fixed by exponentiation. -/
theorem one_pow : ∀ n : Nat213, pow one n = one
  | one    => rfl
  | succ n => by show mul one (pow one n) = one; rw [one_mul, one_pow n]

/-- ★★ **`a^(m+n) = a^m · a^n`** — exponents add over products.  Induction on `m`. -/
theorem pow_add (a : Nat213) : ∀ m n : Nat213, pow a (add m n) = mul (pow a m) (pow a n)
  | one,    n => rfl
  | succ m, n => by
      show mul a (pow a (add m n)) = mul (mul a (pow a m)) (pow a n)
      rw [pow_add a m n, ← mul_assoc]

/-- ★★ **`a^(m·n) = (a^m)^n`** — the power tower law.  Induction on `n`. -/
theorem pow_mul (a : Nat213) : ∀ m n : Nat213, pow a (mul m n) = pow (pow a m) n
  | m, one    => by show pow a (mul m one) = pow a m; rw [mul_one]
  | m, succ n => by
      show pow a (mul m (succ n)) = mul (pow a m) (pow (pow a m) n)
      rw [mul_succ_right, pow_add a m (mul m n), pow_mul a m n]

/-- ★★ **`(a·b)^n = a^n · b^n`** — exponentiation distributes over products (commutativity).
    Induction on `n`, rearranging the four factors with `mul_assoc`/`mul_comm`. -/
theorem mul_pow (a b : Nat213) : ∀ n : Nat213, pow (mul a b) n = mul (pow a n) (pow b n)
  | one    => rfl
  | succ n => by
      show mul (mul a b) (pow (mul a b) n) = mul (mul a (pow a n)) (mul b (pow b n))
      rw [mul_pow a b n, mul_assoc a b (mul (pow a n) (pow b n)),
          ← mul_assoc b (pow a n) (pow b n), mul_comm b (pow a n),
          mul_assoc (pow a n) b (pow b n),
          ← mul_assoc a (pow a n) (mul b (pow b n))]

-- ═══ Factorial ═══

/-- `n!` over `Nat213`, recursion on `n`.  No zero exponent (`Nat213` has no zero); the base is
    `1! = 1` (`factorial one = one`), and `(n+1)! = (n+1) · n!`.  Reads out as the native `n!`
    (`ModArithReadout.toNat_factorial`), so Wilson's theorem transports along the carrier. -/
def factorial : Nat213 → Nat213
  | one    => one
  | succ n => mul (succ n) (factorial n)

/-- `1! = 1` (the base of the recursion). -/
theorem factorial_one : factorial one = one := rfl

/-- `(n+1)! = (n+1) · n!` (the recursion step). -/
theorem factorial_succ (n : Nat213) : factorial (succ n) = mul (succ n) (factorial n) := rfl

-- ═══ Nat-exponent exponentiation (the count-Lens readout, with a zero exponent) ═══

/-- `a` to a **Lean-`Nat`** power.  The exponent reads *in* from ℕ, so `powNat a 0 = one`
    (the empty product / identity) is available — unlike `pow`, whose exponent is a `Nat213`
    and hence ≥ 1.  This is the power a **valuation** needs: a multiplicity can be zero
    (`Nat213` has no zero, so the count is read *out* into ℕ — the legitimate direction). -/
def powNat : Nat213 → Nat → Nat213
  | _, 0     => one
  | a, k + 1 => mul a (powNat a k)

/-- `a^0 = 1` (the empty product). -/
theorem powNat_zero (a : Nat213) : powNat a 0 = one := rfl

/-- `a^(k+1) = a · a^k`. -/
theorem powNat_succ (a : Nat213) (k : Nat) : powNat a (k + 1) = mul a (powNat a k) := rfl

/-- `a^1 = a`. -/
theorem powNat_one (a : Nat213) : powNat a 1 = a := by
  show mul a (powNat a 0) = a; rw [powNat_zero, mul_one]

/-- `1^k = 1`. -/
theorem one_powNat : ∀ k : Nat, powNat one k = one
  | 0     => rfl
  | k + 1 => by rw [powNat_succ, one_mul, one_powNat k]

/-- ★ **`a^(m+n) = a^m · a^n`** (Nat exponents).  Induction on `n` — `m+(n+1)` reduces to
    `(m+n)+1` definitionally, so no Lean-`Nat` lemma is needed; only `Nat213`'s `mul` laws. -/
theorem powNat_add (a : Nat213) (m : Nat) : ∀ n : Nat,
    powNat a (m + n) = mul (powNat a m) (powNat a n)
  | 0     => by show powNat a m = mul (powNat a m) one; rw [mul_one]
  | n + 1 => by
      show powNat a (m + (n + 1)) = mul (powNat a m) (mul a (powNat a n))
      rw [show powNat a (m + (n + 1)) = mul a (powNat a (m + n)) from rfl,
          powNat_add a m n, mul_left_comm]

/-- ★ **Bridge `pow` ↔ `powNat`** — `a^m = a^(toNat m)`: the `Nat213`-exponent power is the
    `Nat`-exponent power read at the count of the exponent.  So `powNat` *extends* `pow` to the
    zero exponent (`pow` is its restriction to `toNat ≥ 1`). -/
theorem pow_eq_powNat_toNat (a : Nat213) : ∀ m : Nat213, pow a m = powNat a m.toNat
  | one    => by show pow a one = powNat a 1; rw [pow_one, powNat_one]
  | succ n => by
      show mul a (pow a n) = mul a (powNat a n.toNat)
      rw [pow_eq_powNat_toNat a n]

/-- ★ `succ n ≠ one`: every successor is distinct from the base. -/
theorem succ_ne_one (n : Nat213) : succ n ≠ one := fun h => Nat213.noConfusion h

/-- ★ `add a c ≠ a` — adding any `Nat213` strictly grows (there is no additive
    `0`).  **Native** structural induction on `a`, no `toNat`: `add one c`
    reduces to `succ c ≠ one` (`succ_ne_one`); the `succ` step descends through
    `succ.inj`.  This is the no-additive-identity shape forced by "`Raw` has an
    atom", proven on the generated carrier all the way down. -/
theorem add_ne_self : ∀ (a c : Nat213), add a c ≠ a
  | one,    c => fun h => succ_ne_one c h
  | succ a, c => fun h => add_ne_self a c (Nat213.succ.inj h)

/-- ★ `(succ n).toNat = n.toNat + 1` — by definition. -/
theorem succ_toNat (n : Nat213) : (succ n).toNat = n.toNat + 1 := rfl

/-- ★★★ NO ADDITIVE IDENTITY: there is no `z : Nat213` such that
    `add z one = one`.  In standard ℕ-with-0, `0 + 1 = 1` (identity).
    In Nat213, no such `z` exists — proves ℕ-with-0's identity
    structure is foreign to Nat213. -/
theorem no_additive_identity_at_one :
    ¬ ∃ z : Nat213, add z one = one := by
  intro ⟨z, h⟩
  rw [add_one_right z] at h
  exact Nat213.noConfusion h

/-- ★★★ NO CLOSED SUBTRACTION: there is no function
    `sub : Nat213 → Nat213 → Nat213` such that `add (sub n n) n = n`
    for every `n`.  Proof: setting `n = one`, the equation forces
    `sub one one` to be an additive identity at one, which doesn't
    exist (`no_additive_identity_at_one`).

    Therefore subtraction MUST escape Nat213 (= go to ℤ via the
    orthogonal-axis-generator fold). -/
theorem no_closed_subtraction :
    ¬ ∃ sub : Nat213 → Nat213 → Nat213,
        ∀ n : Nat213, add (sub n n) n = n := by
  intro ⟨sub, h⟩
  have h1 : add (sub one one) one = one := h one
  exact no_additive_identity_at_one ⟨sub one one, h1⟩

-- ═══ NO ABSORPTION: there is no zero in Nat213 ═══

/-- ★★★ NO ABSORBING ELEMENT: there is no `z : Nat213` such that `z · n = z`
    for all `n`.  In Lean `Nat` (with 0): `0 · n = 0` for all `n` — the
    absorption pathology of 0.  In `Nat213`, NO such element exists.

    **Native** proof, no `toNat`: instantiate at `n = 2`; `mul z 2 = add z z`
    (`mul_two`), so the hypothesis forces `add z z = z`, impossible by
    `add_ne_self`.  The no-zero/no-absorption shape is thus forced by the
    primitive and witnessed on the generated carrier all the way down. -/
theorem no_absorbing_element :
    ¬ ∃ z : Nat213, ∀ n : Nat213, mul z n = z := by
  intro ⟨z, h⟩
  have h2 : mul z (succ one) = z := h (succ one)
  rw [mul_two] at h2
  exact add_ne_self z z h2

end Nat213

end E213.Lens.Number.Nat213.Peano
