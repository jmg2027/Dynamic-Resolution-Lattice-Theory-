import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNormLaw
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrimary

/-!
# The Jacobi sum has a unique primary associate — `J = π` normalisation

`N(J)=p` with `3 ∤ p` (since `p ≡ 1 mod 3`) puts the Jacobi sum in the scope of
`EisensteinPrimary.exists_unique_primary`: exactly one of its six unit associates is **primary**
(`≡ 2 mod 3`):

  `∃! u ∈ units6,  IsPrimary (u · jacobiSum p m x)`   (`jacobi_primary`).

That unique primary associate **is** the canonical prime `π = (π/π')₃`'s normalisation uses — so `J = π`
up to the (now determined) primary unit.  With `jacobi_prime` (`J` is prime) and `jacobi_splits_p`
(`p = J·J̄`), the Jacobi sum is pinned to the primary Eisenstein prime above `p`.  ∅-axiom (PURE) —
the `Int`-`∣` `decide` is reflected to the `ℕ`-side `beq` test (`EisensteinPrimary.dvd3_{true,false}`).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiPrimary

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega units6)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (jacobiSum)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNormLaw (jacobi_norm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinPrimary
  (IsPrimary exists_unique_primary dvd3_false)
open E213.Meta.Nat.NatRing213 (nat_sub_add_cancel)

/-- ★★★★★ **The Jacobi sum has a unique primary associate** — for a prime `p ≡ 1 mod 3` (`p>3`),
    exactly one unit `u ∈ units6` makes `u · jacobiSum p m x` primary (`≡ 2 mod 3`).  From `N(J)=p`
    (`jacobi_norm`) and `3 ∤ p` (`p ≡ 1 mod 3`) via `exists_unique_primary`.  This pins `J` to the
    canonical primary prime `π` above `p`.  ∅-axiom (PURE). -/
theorem jacobi_primary {d : ZOmega} {p m x : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) :
    ∃ u, units6.contains u = true ∧ IsPrimary (u * jacobiSum p m x) ∧
      (∀ u', units6.contains u' = true → IsPrimary (u' * jacobiSum p m x) → u' = u) := by
  apply exists_unique_primary
  rw [jacobi_norm hp hp3 hpr h3m hm1 hdn hω hx]
  -- ¬ 3 ∣ ↑p, since p = 3m+1
  have h1p : 1 ≤ p := Nat.le_of_lt hp
  have hp_eq : 3 * m + 1 = p := by rw [h3m]; exact nat_sub_add_cancel h1p
  intro hdvd
  rw [← hp_eq] at hdvd
  have hcast : ((3 * m + 1 : Nat) : Int) = 3 * (m : Int) + 1 := rfl
  rw [hcast] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  have h31 : (3 : Int) ∣ 1 := ⟨k - (m : Int), by
    calc (1 : Int) = (3 * (m : Int) + 1) - 3 * (m : Int) := by ring_intZ
      _ = 3 * k - 3 * (m : Int) := by rw [hk]
      _ = 3 * (k - (m : Int)) := by ring_intZ⟩
  exact absurd h31 (dvd3_false (by decide))

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiPrimary
