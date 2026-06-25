import E213.Lens.Number.Nat213.Peano
import E213.Lens.Number.Nat213.ToNatReadout
import E213.Lens.Number.Nat213.Coprime

/-!
# Lens.Number.Nat213.Congruence — modular arithmetic over the Raw-generated ℕ₊ (∅-axiom)

The **descent leg**, leg-2 — congruences regrounded on `Nat213`.  The classical `a ≡ b (mod m)`
is `m ∣ a − b`, but `Nat213` has **no subtraction** (`Peano`: no zero, no closed subtraction).  The
no-subtraction-friendly definition keeps the difference symmetric:

`ModEq m a b := ∃ k l, a + m·k = b + m·l` — `a` and `b` reach a common value by adding multiples of
`m`.  This needs no subtraction, and over `Nat213` it is an **equivalence relation** compatible with
`+` and `·` (a congruence on the semiring) — modular arithmetic computed on the distinguishing's own
counting object.  ∅-axiom throughout.
-/

namespace E213.Lens.Number.Nat213.Congruence

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213
  (add mul one add_assoc add_comm add_left_comm mul_add add_mul mul_assoc mul_comm mul_one
   pow pow_one pow_succ toNat toNat_add toNat_mul toNat_injective
   add_right_cancel add_left_cancel add_ne_self)
open E213.Lens.Number.Nat213.ToNatReadout (toNat_surj)
open E213.Lens.Number.Nat213.Order (lt_trichotomy)
open E213.Lens.Number.Nat213.Divisibility (Dvd)
open E213.Lens.Number.Nat213.Coprime (Coprime coprime_dvd_mul coprime_comm)

/-- **Congruence over the Raw-generated ℕ₊**: `a ≡ b (mod m)` iff `a` and `b` reach a common value
    by adding multiples of `m` — `∃ k l, a + m·k = b + m·l`.  Subtraction-free (no zero needed). -/
def ModEq (m a b : Nat213) : Prop := ∃ k l : Nat213, add a (mul m k) = add b (mul m l)

/-- `add`-right-commute helper (`(a+b)+c = (a+c)+b`). -/
private theorem add_right_comm (a b c : Nat213) : add (add a b) c = add (add a c) b := by
  rw [add_assoc, add_comm b c, ← add_assoc]

/-- `(a+c)+(b+d) = (a+b)+(c+d)` — comm-monoid regroup. -/
private theorem add_add_add_comm (a b c d : Nat213) :
    add (add a c) (add b d) = add (add a b) (add c d) := by
  rw [add_assoc, add_assoc, add_left_comm c b d]

/-- Reflexivity. -/
theorem refl (m a : Nat213) : ModEq m a a := ⟨one, one, rfl⟩

/-- Symmetry. -/
theorem symm {m a b : Nat213} (h : ModEq m a b) : ModEq m b a :=
  let ⟨k, l, h⟩ := h; ⟨l, k, h.symm⟩

/-- ★ **Transitivity** — compose the two "reach a common value" certificates, shuffling the added
    multiples with `add_right_comm`/`add_assoc`. -/
theorem trans {m a b c : Nat213} (h1 : ModEq m a b) (h2 : ModEq m b c) : ModEq m a c := by
  obtain ⟨k1, l1, h1⟩ := h1
  obtain ⟨k2, l2, h2⟩ := h2
  refine ⟨add k1 k2, add l2 l1, ?_⟩
  calc add a (mul m (add k1 k2))
      = add (add a (mul m k1)) (mul m k2) := by rw [mul_add, ← add_assoc]
    _ = add (add b (mul m l1)) (mul m k2) := by rw [h1]
    _ = add (add b (mul m k2)) (mul m l1) := by rw [add_right_comm]
    _ = add (add c (mul m l2)) (mul m l1) := by rw [h2]
    _ = add c (mul m (add l2 l1))         := by rw [add_assoc, ← mul_add]

/-- ★ **Compatible with `+`** — `a ≡ b`, `c ≡ d ⟹ a+c ≡ b+d`. -/
theorem add_compat {m a b c d : Nat213} (h1 : ModEq m a b) (h2 : ModEq m c d) :
    ModEq m (add a c) (add b d) := by
  obtain ⟨k1, l1, h1⟩ := h1
  obtain ⟨k2, l2, h2⟩ := h2
  refine ⟨add k1 k2, add l1 l2, ?_⟩
  rw [mul_add, mul_add, add_add_add_comm, h1, h2, add_add_add_comm]

/-- ★ **Compatible with right `·`** — `a ≡ b ⟹ a·c ≡ b·c` (multiply the certificate through by `c`). -/
theorem mul_right {m a b : Nat213} (h : ModEq m a b) (c : Nat213) :
    ModEq m (mul a c) (mul b c) := by
  obtain ⟨k, l, h⟩ := h
  refine ⟨mul k c, mul l c, ?_⟩
  calc add (mul a c) (mul m (mul k c))
      = mul (add a (mul m k)) c := by rw [add_mul, mul_assoc]
    _ = mul (add b (mul m l)) c := by rw [h]
    _ = add (mul b c) (mul m (mul l c)) := by rw [add_mul, mul_assoc]

/-- Compatible with left `·` — `a ≡ b ⟹ c·a ≡ c·b` (via `mul_comm`). -/
theorem mul_left {m a b : Nat213} (h : ModEq m a b) (c : Nat213) :
    ModEq m (mul c a) (mul c b) := by
  rw [mul_comm c a, mul_comm c b]; exact mul_right h c

/-- ★ **Full multiplicative compatibility** — `a ≡ b`, `c ≡ d ⟹ a·c ≡ b·d`. -/
theorem mul_compat {m a b c d : Nat213} (h1 : ModEq m a b) (h2 : ModEq m c d) :
    ModEq m (mul a c) (mul b d) :=
  trans (mul_right h1 c) (mul_left h2 b)

/-- ★★ **Modular exponentiation** — `a ≡ b ⟹ a^n ≡ b^n` (induction on `n` via `mul_compat`). -/
theorem pow_compat {m a b : Nat213} (h : ModEq m a b) (n : Nat213) :
    ModEq m (pow a n) (pow b n) := by
  induction n with
  | one => rw [pow_one, pow_one]; exact h
  | succ n ih => rw [pow_succ, pow_succ]; exact mul_compat h ih

/-- ★ **The defining step** — `a ≡ a + m·k`: adding any multiple of `m` lands in the same class. -/
theorem modeq_add_mul (m a k : Nat213) : ModEq m a (add a (mul m k)) :=
  ⟨add k one, one, by rw [mul_add, ← add_assoc]⟩

/-- ★★ **Readout into ℕ** — `a ≡ b (mod m)` over `Nat213` pushes forward to the native ℕ congruence
    in the same subtraction-free form: `a.toNat + m.toNat·k = b.toNat + m.toNat·l`.  The
    carrier-readout for the congruence field (forward direction, via the `toNat` `+`/`·`
    homomorphism). -/
theorem modeq_toNat {m a b : Nat213} (h : ModEq m a b) :
    ∃ k l : Nat, a.toNat + m.toNat * k = b.toNat + m.toNat * l := by
  obtain ⟨k, l, h⟩ := h
  refine ⟨k.toNat, l.toNat, ?_⟩
  have := congrArg toNat h
  rwa [toNat_add, toNat_add, toNat_mul, toNat_mul] at this

/-- ★★ **Concrete form of congruence** — `a ≡ b (mod m)` iff `a = b`, or one is the other plus a
    multiple of `m`.  Trichotomy on the certificate's `(k,l)`: equal ⟹ `a = b` (cancel); else the
    larger side carries the extra `m·t`.  The handle that turns `ModEq` into a divisibility fact. -/
theorem modeq_cases {m a b : Nat213} (h : ModEq m a b) :
    a = b ∨ (∃ c, add a (mul m c) = b) ∨ (∃ c, add b (mul m c) = a) := by
  obtain ⟨k, l, h⟩ := h
  rcases lt_trichotomy k l with hlt | heq | hgt
  · obtain ⟨t, ht⟩ := hlt
    refine Or.inr (Or.inr ⟨t, ?_⟩)
    apply add_right_cancel (c := mul m k)
    rw [add_assoc, ← mul_add, add_comm t k, ht]; exact h.symm
  · subst heq; exact Or.inl (add_right_cancel h)
  · obtain ⟨t, ht⟩ := hgt
    refine Or.inr (Or.inl ⟨t, ?_⟩)
    apply add_right_cancel (c := mul m l)
    rw [add_assoc, ← mul_add, add_comm t l, ht]; exact h

/-- ★ **CRT, split direction** — `a ≡ b (mod m·n) ⟹ a ≡ b (mod m) ∧ a ≡ b (mod n)` (no
    coprimality needed; rescale the certificate's multiples). -/
theorem modeq_split {m n a b : Nat213} (h : ModEq (mul m n) a b) :
    ModEq m a b ∧ ModEq n a b := by
  obtain ⟨k, l, h⟩ := h
  refine ⟨⟨mul n k, mul n l, ?_⟩, ⟨mul m k, mul m l, ?_⟩⟩
  · rw [← mul_assoc, ← mul_assoc]; exact h
  · rw [← mul_assoc, ← mul_assoc, mul_comm n m]; exact h

/-- ★★★ **Readout iff** — `ModEq m a b ⟺ a.toNat + m.toNat·k = b.toNat + m.toNat·l` for some
    native `k,l`: the `Nat213` congruence is exactly the native ℕ congruence (subtraction-free
    form) of the readouts.  ⟹ is `modeq_toNat`; ⟸ lifts native `k,l` back through `toNat`'s
    surjectivity — shifted by `+1` so both are `≥ 1` (`Nat213` has no zero), which `Nat.mul_succ`
    absorbs back into the same equation.  ∅-axiom. -/
theorem modeq_toNat_iff {m a b : Nat213} :
    ModEq m a b ↔ ∃ k l : Nat, a.toNat + m.toNat * k = b.toNat + m.toNat * l := by
  refine ⟨modeq_toNat, ?_⟩
  rintro ⟨k, l, h⟩
  obtain ⟨k', hk'⟩ := toNat_surj (k + 1) (Nat.le_add_left 1 k)
  obtain ⟨l', hl'⟩ := toNat_surj (l + 1) (Nat.le_add_left 1 l)
  refine ⟨k', l', toNat_injective ?_⟩
  rw [toNat_add, toNat_add, toNat_mul, toNat_mul, hk', hl', Nat.mul_succ, Nat.mul_succ,
      ← Nat.add_assoc, ← Nat.add_assoc, h]

/-- The directed CRT step: with `b = a + m·c` and `a ≡ b (mod n)`, coprimality lifts to
    `a ≡ b (mod m·n)`.  `n` divides `m·c` (from `a ≡ b (mod n)` via `modeq_cases`, the two wrong
    directions impossible by `add_ne_self`), so `Coprime m n ⟹ n ∣ c`, giving `b = a + (m·n)·f`. -/
private theorem crt_dir {m n a b c : Nat213} (hco : Coprime m n)
    (hc : add a (mul m c) = b) (hn : ModEq n a b) : ModEq (mul m n) a b := by
  have hnmc : Dvd n (mul m c) := by
    rcases modeq_cases hn with rfl | ⟨d, hd⟩ | ⟨d, hd⟩
    · exact absurd hc (add_ne_self _ _)
    · exact ⟨d, (add_left_cancel (by rw [hd, hc] : add a (mul n d) = add a (mul m c))).symm⟩
    · exfalso; rw [← hc, add_assoc] at hd; exact add_ne_self a (add (mul m c) (mul n d)) hd
  obtain ⟨f, hf⟩ := coprime_dvd_mul (coprime_comm hco) hnmc
  have hb : add a (mul (mul m n) f) = b := by rw [← hc, hf, mul_assoc]
  rw [← hb]; exact modeq_add_mul (mul m n) a f

/-- ★★★ **Chinese Remainder Theorem (combine direction)** — for coprime moduli, congruence mod `m`
    and mod `n` give congruence mod `m·n`: `Coprime m n → a ≡ b (mod m) → a ≡ b (mod n) →
    a ≡ b (mod m·n)`.  The common difference is a multiple of both `m` and `n`, hence (coprime) of
    `m·n` (`coprime_mul_dvd`'s content, via `crt_dir`).  With `modeq_split`, congruence mod `m·n` ⟺
    mod `m` and mod `n`.  ∅-axiom. -/
theorem crt {m n a b : Nat213} (hco : Coprime m n)
    (hm : ModEq m a b) (hn : ModEq n a b) : ModEq (mul m n) a b := by
  rcases modeq_cases hm with rfl | ⟨c, hc⟩ | ⟨c, hc⟩
  · exact refl _ _
  · exact crt_dir hco hc hn
  · exact symm (crt_dir hco hc (symm hn))

/-- ★★★ **`ModEq m` is a congruence on the Raw-generated semiring** — an equivalence relation
    compatible with `+` and `·`.  Modular arithmetic generated over `Nat213`, subtraction-free. -/
theorem modeq_congruence (m : Nat213) :
    (∀ a, ModEq m a a)
    ∧ (∀ a b, ModEq m a b → ModEq m b a)
    ∧ (∀ a b c, ModEq m a b → ModEq m b c → ModEq m a c)
    ∧ (∀ a b c d, ModEq m a b → ModEq m c d → ModEq m (add a c) (add b d))
    ∧ (∀ a b c, ModEq m a b → ModEq m (mul a c) (mul b c)) :=
  ⟨refl m, fun _ _ => symm, fun _ _ _ => trans, fun _ _ _ _ => add_compat,
   fun _ _ c h => mul_right h c⟩

end E213.Lens.Number.Nat213.Congruence
