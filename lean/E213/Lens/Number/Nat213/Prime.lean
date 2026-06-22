import E213.Lens.Number.Nat213.EuclidUnique

/-!
# Lens.Number.Nat213.Prime — irreducible ⟺ prime over the Raw-generated ℕ₊ (∅-axiom)

The **descent leg**, applied (breadth, §7.1).  Over `Nat213` the two notions of "prime" coincide:
the *irreducible* (no nontrivial factorization) and the *prime* (`p ∣ a·b → p ∣ a ∨ p ∣ b`) are the
same predicate (`irreducible_iff_prime`).  The `→` is Euclid's lemma (`EuclidUnique.euclid`); the `←`
is the cancellation argument.  This is the UFD-defining coincidence, generated over the
distinguishing's own counting object — the structural reason the FTA's uniqueness holds.  ∅-axiom.
-/

namespace E213.Lens.Number.Nat213.Prime

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lens.Number.Nat213.Peano.Nat213 (mul one mul_one mul_assoc mul_comm)
open E213.Lens.Number.Nat213.Order (mul_left_cancel)
open E213.Lens.Number.Nat213.Divisibility (Dvd mul_eq_one)
open E213.Lens.Number.Nat213.Irreducible (Irreducible)
open E213.Lens.Number.Nat213.EuclidUnique (euclid)

/-- **Prime over the Raw-generated ℕ₊**: not a unit, and divides a factor of every product it
    divides (`Nat213`'s own `mul`/`Dvd`). -/
def Prime (p : Nat213) : Prop :=
  p ≠ one ∧ ∀ a b : Nat213, Dvd p (mul a b) → Dvd p a ∨ Dvd p b

/-- Irreducible ⟹ prime — exactly Euclid's lemma (`euclid`). -/
theorem irreducible_imp_prime {p : Nat213} (hp : Irreducible p) : Prime p :=
  ⟨hp.1, fun _ _ h => euclid hp h⟩

/-- Prime ⟹ irreducible — the cancellation direction: a factorization `p = a·b` makes `p ∣ a·b`, so
    `p ∣ a` (say `a = p·c`), then `p = p·(c·b)` cancels to `c·b = 1`, forcing `b = 1`. -/
theorem prime_imp_irreducible {p : Nat213} (hp : Prime p) : Irreducible p := by
  refine ⟨hp.1, fun a b hab => ?_⟩
  have hpab : Dvd p (mul a b) := ⟨one, by rw [mul_one]; exact hab.symm⟩
  rcases hp.2 a b hpab with ⟨c, hc⟩ | ⟨c, hc⟩
  · right
    have hp1 : mul p one = mul p (mul c b) := by rw [mul_one, ← mul_assoc, ← hc, ← hab]
    exact (mul_eq_one (mul_left_cancel hp1).symm).2
  · left
    have hp1 : mul p one = mul p (mul c a) := by
      rw [mul_one, ← mul_assoc, ← hc, mul_comm b a, ← hab]
    exact (mul_eq_one (mul_left_cancel hp1).symm).2

/-- ★★★ **Irreducible ⟺ prime over the Raw-generated ℕ₊** — the UFD-defining coincidence, the
    structural reason the generated FTA's uniqueness holds, computed entirely over `Nat213`. -/
theorem irreducible_iff_prime {p : Nat213} : Irreducible p ↔ Prime p :=
  ⟨irreducible_imp_prime, prime_imp_irreducible⟩

end E213.Lens.Number.Nat213.Prime
