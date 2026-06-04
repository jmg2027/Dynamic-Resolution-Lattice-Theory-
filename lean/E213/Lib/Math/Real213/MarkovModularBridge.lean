import E213.Lib.Math.Real213.MarkovUniqueness
import E213.Lib.Math.Real213.ModularElliptic
import E213.Meta.Int213.PolyIntMTactic

/-!
# MarkovModularBridge — the Markov pair is the modular generator `S`'s eigenvector mod `c`

Merged-`main` gives the order-4 elliptic generator `S = [[0,−1],[1,0]]` (`ModularElliptic`, with
`S² = −I`), and `CayleyDickson/.../UnitsToModular` proves `repI i = S`: `S` is the regular-rep
image of the **Gaussian unit `i`** (`i² = −1`).  This module makes the HANDOFF "213-native
conjecture" concrete: the Markov √(−1)-residue is `S`'s eigenvalue mod a Markov number, with the
Markov pair `(a,b)` as the eigenvector.

`S` acts on a column vector by `S·(x,y) = (−y, x)`.  So `S·(a,b) ≡ u·(a,b) (mod c)` says
`−b ≡ u·a` and `a ≡ u·b` — i.e. `c ∣ u·a + b` and `a ≡ u·b (mod c)`.  Both are genuine Markov
facts about the recovery residue `u = (a·b⁻¹) mod c`:

  * `a ≡ u·b (mod c)` is the **recovery map** (`markov_root_recovery`);
  * `c ∣ u·a + b` is the **neighbor congruence** `a² + b² ≡ 0` in disguise: `b·(u·a+b) = c·(a·q +
    (3ab−c))` (using `u·b = c·q + a` and `a²+b² = c·(3ab−c)`), then `gcd(b,c)=1` cancels `b`
    (`euclid_of_coprime`).

So **the √(−1)-residue `u` that indexes a Markov number is exactly the eigenvalue of the Gaussian
unit `i = S` acting on the Markov pair `(a,b)` mod `c`** — the Markov↦√(−1) map realises the
order-4 elliptic generator, as conjectured.  `markov_pair_eigen` proves the two congruences (∅-axiom
`ℕ`); `S_eigenvector_of_dvd` is the abstract `S`-eigenvector criterion over `ℤ` (via `ring_intZ`)
that consumes exactly those two divisibilities.  (The only formality between them is the Nat→Int
cast of the divisibilities; the content is identical.)
-/

namespace E213.Lib.Math.Real213.MarkovModularBridge

open E213.Lib.Math.Real213.MarkovTree (markovEq)
open E213.Tactic.NatHelper (gcd213)
open E213.Lib.Math.Real213.MarkovUniqueness
open E213.Lib.Math.ModArith.MarkovPrimeFactor (euclid_of_coprime)
open E213.Lib.Math.Real213.ModularElliptic (S)
open E213.Meta.Int213 (zero_mul zero_add)

/-- ★★★★ **The Markov pair `(a,b)` satisfies the `S`-eigenvector congruences mod `c`.**  For a
    Markov triple `(a,b,c)` with `1 < c`, `gcd(b,c)=1`, `a < c`, the recovery residue
    `u = (a·b⁻¹) mod c` is a `√(−1)` (`(u²+1)%c = 0`) and satisfies `(u·b) % c = a` (recovery) and
    `(u·a + b) % c = 0` (neighbor congruence + Euclid).  These are precisely `S·(a,b) ≡ u·(a,b)
    (mod c)` — the Markov pair is the `i`-eigenvector of `S = repI i` reduced mod the Markov
    number, with eigenvalue the √(−1)-residue. -/
theorem markov_pair_eigen (a b c : Nat) (h : markovEq a b c) (hc : 1 < c)
    (hco : gcd213 b c = 1) (ha : a < c) :
    ∃ u, u < c ∧ (u * u + 1) % c = 0 ∧ (u * b) % c = a ∧ (u * a + b) % c = 0 := by
  have hcpos : 0 < c := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hc)
  obtain ⟨u, hu_lt, hu_root, hu_rec⟩ := markov_root_recovery a b c hc ha hco h
  refine ⟨u, hu_lt, hu_root, hu_rec.symm, ?_⟩
  obtain ⟨q, hq⟩ : ∃ q, u * b = c * q + a := by
    have hd := E213.Meta.Nat.AddMod213.div_add_mod (u * b) c
    rw [← hu_rec] at hd; exact ⟨(u * b) / c, hd.symm⟩
  have hne := markov_neighbor_eq a b c hcpos h
  have hbdvd : c ∣ b * (u * a + b) := by
    refine ⟨a * q + (3 * a * b - c), ?_⟩
    calc b * (u * a + b)
        = a * (u * b) + b * b := by ring_nat
      _ = a * (c * q + a) + b * b := by rw [hq]
      _ = c * (a * q) + (a * a + b * b) := by ring_nat
      _ = c * (a * q) + c * (3 * a * b - c) := by rw [hne]
      _ = c * (a * q + (3 * a * b - c)) := (Nat.mul_add c _ _).symm
  obtain ⟨k, hk⟩ := euclid_of_coprime b (u * a + b) c hc hco hbdvd
  rw [hk]; exact E213.Tactic.NatHelper.mul_mod_right c k

/-- ★★★★ **The abstract `S`-eigenvector criterion (over `ℤ`, via `ring_intZ`).**  If `c ∣ u·a + b`
    and `c ∣ u·b − a`, then `S·(a,b) − u·(a,b) ≡ 0 (mod c)` componentwise — i.e. `(a,b)` is an
    eigenvector of `S = [[0,−1],[1,0]]` with eigenvalue `u` mod `c`.  (`S·(a,b) = (−b, a)`, so the
    two entries are `−(u·a+b)` and `−(u·b−a)`.)  Fed the divisibilities of `markov_pair_eigen`,
    this is the Markov pair's eigenvector property. -/
theorem S_eigenvector_of_dvd (a b u c : Int)
    (h1 : c ∣ (u * a + b)) (h2 : c ∣ (u * b - a)) :
    c ∣ (S.a * a + S.b * b - u * a) ∧ c ∣ (S.c * a + S.d * b - u * b) := by
  refine ⟨?_, ?_⟩
  · have heq : S.a * a + S.b * b - u * a = -(u * a + b) := by
      rw [show S.a = 0 from rfl, show S.b = (-1) from rfl, zero_mul, zero_add]; ring_intZ
    rw [heq]; obtain ⟨k, hk⟩ := h1; exact ⟨-k, by rw [hk]; ring_intZ⟩
  · have heq : S.c * a + S.d * b - u * b = -(u * b - a) := by
      rw [show S.c = 1 from rfl, show S.d = 0 from rfl, Int.one_mul, zero_mul, Int.add_zero]
      ring_intZ
    rw [heq]; obtain ⟨k, hk⟩ := h2; exact ⟨-k, by rw [hk]; ring_intZ⟩

end E213.Lib.Math.Real213.MarkovModularBridge
