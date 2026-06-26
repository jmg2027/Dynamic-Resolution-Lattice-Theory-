import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussShift

/-!
# Basis-vector convolution and powers in `R[C_p]` — `e_a ⋆ e_b = e_{(a+b)%p}` (Phase B2e.5)

The group multiplication of the cyclic group `C_p` lifted to the group ring: the basis vector
`e_a = ζ^a` (the indicator `δ_{·,a}`) convolves by index addition mod `p`, and its `q`-th power is the
basis vector at `tq mod p`:

  `basis_conv`    : `(e_a ⋆ e_b)(k) = e_{(a+b)%p}(k)`   (`a,b,k < p`),
  `basisPow_eq`   : `e_t^{⋆q}(k) = e_{(t·q)%p}(k)`       (`t,k < p`).

The second is what turns the Gauss-sum Frobenius `g^{⋆q} ≡ Σ_t χ(t)^q·e_t^{⋆q}` into
`Σ_t χ(t)^q·e_{tq%p}` — the `ζ^t ↦ ζ^{tq}` reindex of the Frobenius congruence (Phase B2).  Note
`delta = e_0` is the unit.  ∅-axiom up to allowed `propext` (the `ite` of the basis indicator).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvBasis

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv conv_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvPow
  (delta convPow convPow_zero convPow_succ convPow_scalar)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (one one_mul mul_one pow)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinFiniteSum (sumRange sum_single)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussShift (add_shift_index)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGaussSum (gauss)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinRangeSum (add_p_mod)
open E213.Meta.Nat.AddMod213 (mod_add_mod)
open E213.Meta.Nat.NatRing213 (nat_sub_add_cancel)
open E213.Meta.Algebra213.Ring213 (zero_mul mul_zero)

/-- The basis vector `e_a = ζ^a ∈ R[C_p]` — the indicator `δ_{·,a}` (so `e_0 = delta`). -/
def basis (a : Nat) : Nat → ZOmega := fun i => if i = a then one else 0

/-- **The convolution index condition** — for `a,b,k < p`, `(k + p − a) % p = b ⟺ k = (a + b) % p`.
    The `C_p` group law: `e_a ⋆ e_b` is supported at `k ≡ a + b (mod p)`.  ∅-axiom. -/
theorem conv_basis_index {p a b k : Nat} (hp : 0 < p) (ha : a < p) (hb : b < p) (hk : k < p) :
    (k + p - a) % p = b ↔ k = (a + b) % p := by
  constructor
  · intro h
    rw [← h, Nat.add_comm a ((k + p - a) % p), mod_add_mod hp (k + p - a) a,
        show (k + p - a) + a = k + p from
          nat_sub_add_cancel (Nat.le_of_lt (Nat.lt_of_lt_of_le ha (Nat.le_add_left p k))),
        add_p_mod hp k, Nat.mod_eq_of_lt hk]
  · intro hc
    rw [hc, Nat.add_comm a b]
    exact add_shift_index hp (Nat.le_of_lt ha) hb

/-- ★★★★★ **Basis-vector convolution** — `(e_a ⋆ e_b)(k) = e_{(a+b)%p}(k)` for `a,b,k < p`.  Only the
    `i=a` term of the convolution survives (`e_a = δ_{·,a}`), leaving `e_b((k+p−a)%p)`, which equals
    `e_{(a+b)%p}(k)` by the index condition `conv_basis_index`.  The `C_p` group law in `R[C_p]`.
    ∅-axiom. -/
theorem basis_conv {p a b : Nat} (hp : 0 < p) (ha : a < p) (hb : b < p) {k : Nat} (hk : k < p) :
    conv p (basis a) (basis b) k = basis ((a + b) % p) k := by
  show sumRange (fun i => basis a i * basis b ((k + p - i) % p)) p = basis ((a + b) % p) k
  rw [sum_single p a ha (fun i => basis a i * basis b ((k + p - i) % p))
        (fun i _ hia => by
          show (if i = a then one else 0) * basis b ((k + p - i) % p) = 0
          rw [if_neg hia, zero_mul])]
  show (if a = a then one else 0) * basis b ((k + p - a) % p) = basis ((a + b) % p) k
  rw [if_pos rfl, one_mul]
  show (if (k + p - a) % p = b then one else 0) = (if k = (a + b) % p then one else 0)
  by_cases hc : k = (a + b) % p
  · rw [if_pos hc, if_pos ((conv_basis_index hp ha hb hk).mpr hc)]
  · rw [if_neg hc, if_neg (fun h => hc ((conv_basis_index hp ha hb hk).mp h))]

/-- ★★★★★ **Basis-vector convolution power** — `e_t^{⋆q}(k) = e_{(t·q)%p}(k)` for `t,k < p`.  By
    induction on `q`: `e_t^{⋆0} = e_0` (`t·0 = 0`), and `e_t^{⋆(q+1)} = e_t^{⋆q} ⋆ e_t =
    e_{tq%p} ⋆ e_t = e_{(tq%p + t)%p} = e_{t(q+1)%p}` (`basis_conv` + `mod_add_mod`).  The `ζ^t ↦ ζ^{tq}`
    Frobenius reindex.  ∅-axiom. -/
theorem basisPow_eq {p t : Nat} (hp : 0 < p) (ht : t < p) :
    ∀ (q : Nat) {k : Nat}, k < p → convPow p (basis t) q k = basis ((t * q) % p) k
  | 0, k, _ => by
      show delta k = basis ((t * 0) % p) k
      rw [Nat.mul_zero, Nat.zero_mod]; rfl
  | q + 1, k, hk => by
      rw [convPow_succ,
          conv_congr p k hp (fun i hi => basisPow_eq hp ht q hi) (fun _ _ => rfl),
          basis_conv hp (Nat.mod_lt (t * q) hp) ht hk]
      show basis ((t * q % p + t) % p) k = basis ((t * (q + 1)) % p) k
      rw [mod_add_mod hp (t * q) t, show t * q + t = t * (q + 1) from by rw [Nat.mul_add, Nat.mul_one]]

/-- ★★★★★ **The scaled-basis convolution power** — `(c · e_t)^{⋆q}(k) = c^q · e_{(t·q)%p}(k)` for
    `t,k < p`.  Combines `convPow_scalar` (`(c·h)^{⋆q} = c^q·h^{⋆q}`) with `basisPow_eq`
    (`e_t^{⋆q} = e_{tq%p}`).  This is the per-`t` term of the Gauss-sum Frobenius: with `c = χ(t)`,
    `(χ(t)·e_t)^{⋆q}(k) = χ(t)^q · e_{tq%p}(k)`.  ∅-axiom up to allowed `propext`. -/
theorem scaledBasisPow_eq {p t : Nat} (hp : 0 < p) (ht : t < p) (c : ZOmega) (q : Nat) {k : Nat}
    (hk : k < p) : convPow p (fun i => c * basis t i) q k = pow c q * basis ((t * q) % p) k := by
  rw [convPow_scalar p c (basis t) q hk, basisPow_eq hp ht q hk]

/-- ★★★★ **The Gauss sum as a sum of scaled basis vectors** — `g(χ)(i) = Σ_{t<p} χ(t)·e_t(i)` for
    `i < p`.  Only the `t=i` term survives (`e_t = δ_{·,t}`), giving `χ(i) = g(χ)(i)`.  This rewrites
    `gauss = Σ_t χ(t)·e_t`, the form the multinomial Frobenius `convPow_sum_modEq_prime` consumes.
    ∅-axiom up to allowed `propext`. -/
theorem gauss_eq_sum_basis {p m x i : Nat} (hi : i < p) :
    gauss p m x i = sumRange (fun t => chiOmega p m x t * basis t i) p := by
  show chiOmega p m x i = sumRange (fun t => chiOmega p m x t * basis t i) p
  rw [sum_single p i hi (fun t => chiOmega p m x t * basis t i)
        (fun t _ hti => by
          show chiOmega p m x t * (if i = t then one else 0) = 0
          rw [if_neg (fun h => hti h.symm), mul_zero])]
  show chiOmega p m x i = chiOmega p m x i * (if i = i then one else 0)
  rw [if_pos rfl, mul_one]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvBasis
