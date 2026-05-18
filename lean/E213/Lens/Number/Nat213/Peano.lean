import E213.Meta.Tactic.NatHelper

/-!
# Lens.Number.Nat213.Peano — proper 213-native ℕ_+ type (inductive)

A 213-native ℕ that excludes 0.  Following the Raw axiom:
- Raw has at least one atom (a or b)
- Atom count of any Raw is therefore ≥ 1
- The natural counting object is **positive naturals**

This is distinct from Lean's `Nat` (which has 0) and matches the
original Peano definition of natural numbers.

**Why no 0**: per G64/G65, 0 is not derivable from Raw — it
emerges only at the level of structural extensions (orthogonal-
axis quotients, group completions, etc.).  Including 0 in the
"primitive counting" type imports a non-Raw element.

**Operations**:
- `add` : closed (m + n ≥ 1 ∧ ≥ both)
- `mul` : closed (1 acts as identity, no absorption)
- `sub` : NOT defined (would require ℤ extension)

All theorems satisfy ∅-axiom standard.

**Framing (per `seed/AXIOM/09_chart_relativity.md`).**  This
inductive `Nat213` is an *ergonomic parallel* to the lens-derived
form; it is not itself lens-derived.  The `.Bridge` module witnesses
the iso to the Method A chain (`.Raw`); `Lens.leaves` then maps both
to `Nat`.  Long-form discussion + open question on the future of
this file in `research-notes/2026-05-18_lens_emergence_path.md` §4.2
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

/-- Helper: `mul_succ_two_strictly_grows` — if z = succ z', then
    `mul (succ z') two = succ (succ (mul z' two))`, which has
    `toNat ≥ z.toNat + 1`, hence cannot equal z. -/
theorem mul_two_grows : ∀ z : Nat213,
    (mul z (succ one)).toNat = z.toNat + z.toNat
  | one    => rfl
  | succ m => by
      show (add (succ one) (mul m (succ one))).toNat
         = (succ m).toNat + (succ m).toNat
      show (succ (succ (mul m (succ one)))).toNat
         = (m.toNat + 1) + (m.toNat + 1)
      show (mul m (succ one)).toNat + 1 + 1
         = m.toNat + 1 + (m.toNat + 1)
      rw [mul_two_grows m]
      -- LHS: m.toNat + m.toNat + 1 + 1
      -- RHS: m.toNat + 1 + m.toNat + 1
      -- Both = 2*m.toNat + 2
      rw [Nat.add_assoc m.toNat 1 (m.toNat + 1),
          Nat.add_comm 1 (m.toNat + 1),
          ← Nat.add_assoc m.toNat (m.toNat + 1) 1,
          ← Nat.add_assoc m.toNat m.toNat 1]

/-- ★★★ NO ABSORBING ELEMENT: there is no `z : Nat213` such that
    `z · n = z` for all `n`.  In Lean Nat (with 0): `0 · n = 0` for
    all n — this is the absorption pathology of 0.  In Nat213, NO
    such element exists.  Proof: if `mul z 2 = z`, then `2 · z.toNat
    = z.toNat`, which forces `z.toNat = 0`, contradicting
    `toNat_ge_one`. -/
theorem no_absorbing_element :
    ¬ ∃ z : Nat213, ∀ n : Nat213, mul z n = z := by
  intro ⟨z, h⟩
  have h2 : mul z (succ one) = z := h (succ one)
  have eq_nat : (mul z (succ one)).toNat = z.toNat :=
    congrArg toNat h2
  rw [mul_two_grows z] at eq_nat
  -- eq_nat : z.toNat + z.toNat = z.toNat.  Since toNat z ≥ 1, want
  -- a contradiction.  Cancel: z.toNat + z.toNat = z.toNat = 0 + z.toNat
  -- (by rfl on Lean Nat.add: n + 0 = n, but here we have left-add).
  -- Using Nat213-helper add_right_cancel: a + c = b + c → a = b.
  -- Cast: z.toNat + z.toNat = 0 + z.toNat (need 0 + n = n)
  have hz : z.toNat ≥ 1 := toNat_ge_one z
  -- z.toNat = 0 + z.toNat (rfl for Nat.add only when 0 is on right, not left).
  -- Workaround: use Nat213.add_right_cancel with c = z.toNat:
  --   eq_nat : z.toNat + z.toNat = z.toNat.  Rewrite RHS as 0 + z.toNat.
  -- Lean Nat: rfl gives n + 0 = n, but 0 + n requires Nat.zero_add (propext).
  -- Alternative: induct on z.toNat directly to derive contradiction.
  cases z with
  | one => exact Nat213.noConfusion h2
  | succ z' =>
      -- h2 : mul (succ z') (succ one) = succ z'
      -- LHS = add (succ one) (mul z' (succ one)) = succ (succ (mul z' (succ one)))
      have h_form : succ (succ (mul z' (succ one))) = succ z' := h2
      have h_inj : succ (mul z' (succ one)) = z' := Nat213.succ.inj h_form
      -- toNat: (mul z' 2).toNat + 1 = z'.toNat, so (mul z' 2).toNat < z'.toNat
      have h_tn : (mul z' (succ one)).toNat + 1 = z'.toNat :=
        congrArg toNat h_inj
      rw [mul_two_grows z'] at h_tn
      -- h_tn : z'.toNat + z'.toNat + 1 = z'.toNat
      -- Equivalently: z'.toNat + (z'.toNat + 1) = z'.toNat (using add_assoc).
      -- For Nat: a + b = a forces b = 0, but here b = z'.toNat + 1 ≥ 1.
      have hz' : z'.toNat ≥ 1 := toNat_ge_one z'
      -- Rearrange h_tn: z'.toNat + (z'.toNat + 1) = z'.toNat
      have h_tn2 : z'.toNat + (z'.toNat + 1) = z'.toNat := by
        rw [← Nat.add_assoc]; exact h_tn
      -- z'.toNat = z'.toNat + 0 by Nat.add reduction (n+0 = n by rfl):
      have h_eq : z'.toNat + (z'.toNat + 1) = z'.toNat + 0 := by
        rw [h_tn2]; rfl
      have h_zero : z'.toNat + 1 = 0 :=
        E213.Tactic.NatHelper.add_left_cancel h_eq
      exact Nat.noConfusion h_zero

end Nat213

end E213.Lens.Number.Nat213.Peano
