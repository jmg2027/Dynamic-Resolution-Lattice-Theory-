import E213.Lib.Math.Real213.MarkovInjectivity
import E213.Lib.Math.Real213.ModularElliptic
import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Int213.PolyIntMTactic

/-!
# SternBrocotMarkov — the proper det-1 Stern-Brocot tree (toward the Markov recovery)

The Markov uniqueness conjecture reduces (`MarkovInjectivity`) to `SamePairInjective` — the
Farey-monotone recovery (Zhang Lemma 2), that the residue `u` determines the ordered triple.  The
classical proof runs on the **Stern-Brocot tree**, where each node carries a Farey interval
`(p/q, r/s)` of *adjacent* fractions (`q·r − p·s = 1`), and the Markov number `m_t` / residue `u_t`
attach by a mediant recurrence with Frobenius's determinant identities.

The repo's `Mobius213SternBrocot.SternBrocotReachable` is the **all-pairs mediant closure**
(`reachable_of_pos` proves *every* `(m,k)` with `m+k ≥ 1` is reachable — no coprimality), so it is
**not** the injective tree and cannot carry the recovery.  This module builds the *proper* tree:
nodes indexed by Stern-Brocot paths (`List Bool`), each carrying a Farey interval with the
**adjacency invariant `q·r = p·s + 1`** preserved by every L/R mediant step.  On this:
`sbInterval_adj` (the det-1 invariant) and `sbInterval_mediant_coprime` (every mediant is a coprime
pair) are the Layer-1 foundation; the Markov/residue functions + Frobenius identities + monotonicity
(Zhang Lemma 2 = `SamePairInjective`) build on top.
-/

namespace E213.Lib.Math.Real213.SternBrocotMarkov

open E213.Lib.Math.Real213.MarkovInjectivity (farey_mediant_coprime)
open E213.Tactic.NatHelper (gcd213)

/-- A Farey interval `((p,q),(r,s))` is *adjacent* when `q·r = p·s + 1` — the Stern-Brocot det-1
    orientation (`p/q < r/s` are Farey neighbours).  The root `(0/1, 1/0)` satisfies it. -/
def adj (iv : (Nat × Nat) × (Nat × Nat)) : Prop := iv.1.2 * iv.2.1 = iv.1.1 * iv.2.2 + 1

/-- One Stern-Brocot step: `true` = left child (the mediant `(p+r,q+s)` becomes the new right
    bound), `false` = right child (the mediant becomes the new left bound). -/
def sbStep : Bool → (Nat × Nat) × (Nat × Nat) → (Nat × Nat) × (Nat × Nat)
  | true,  ((p, q), (r, s)) => ((p, q), (p + r, q + s))
  | false, ((p, q), (r, s)) => ((p + r, q + s), (r, s))

/-- The Farey interval at a Stern-Brocot path (root = `(0/1, 1/0)`; head of the list is the last
    step taken). -/
def sbInterval : List Bool → (Nat × Nat) × (Nat × Nat)
  | []     => ((0, 1), (1, 0))
  | b :: t => sbStep b (sbInterval t)

/-- Each L/R step preserves the adjacency (det-1) invariant — the mediant inserts between the
    bounds keeping both pairs Farey-adjacent. -/
theorem sbStep_preserves (b : Bool) (iv : (Nat × Nat) × (Nat × Nat)) (h : adj iv) :
    adj (sbStep b iv) := by
  obtain ⟨⟨p, q⟩, ⟨r, s⟩⟩ := iv
  have h' : q * r = p * s + 1 := h
  cases b
  · show (q + s) * r = (p + r) * s + 1
    rw [show (q + s) * r = q * r + s * r from by ring_nat, h']; ring_nat
  · show q * (p + r) = p * (q + s) + 1
    rw [show q * (p + r) = q * r + q * p from by ring_nat, h']; ring_nat

/-- ★★★★★ **The Stern-Brocot adjacency invariant.**  Every node's bounding fractions are det-1
    Farey neighbours (`q·r = p·s + 1`).  This is exactly the invariant the repo's all-pairs
    `SternBrocotReachable` lacks — `sbInterval` is the *proper* (injective) Stern-Brocot tree. -/
theorem sbInterval_adj (path : List Bool) : adj (sbInterval path) := by
  induction path with
  | nil => show (1 : Nat) * 1 = 0 * 0 + 1; decide
  | cons b t ih => exact sbStep_preserves b (sbInterval t) ih

/-- The mediant `(p+r, q+s)` of any adjacent interval is a coprime pair (`farey_mediant_coprime`
    on the det-1 invariant). -/
theorem adj_mediant_coprime (iv : (Nat × Nat) × (Nat × Nat)) (h : adj iv) :
    gcd213 (iv.1.1 + iv.2.1) (iv.1.2 + iv.2.2) = 1 := by
  obtain ⟨⟨p, q⟩, ⟨r, s⟩⟩ := iv
  have h' : q * r = p * s + 1 := h
  have hdet : r * q = s * p + 1 := by rw [Nat.mul_comm r q, Nat.mul_comm s p]; exact h'
  have hcop := farey_mediant_coprime r s p q hdet
  rw [Nat.add_comm r p, Nat.add_comm s q] at hcop
  exact hcop

/-- ★★★★★ **Every Stern-Brocot mediant is a coprime pair** — the proper tree enumerates the
    coprime pairs (the backbone the recovery needs; the repo's mediant-closure does not have this). -/
theorem sbInterval_mediant_coprime (path : List Bool) :
    gcd213 ((sbInterval path).1.1 + (sbInterval path).2.1)
           ((sbInterval path).1.2 + (sbInterval path).2.2) = 1 :=
  adj_mediant_coprime (sbInterval path) (sbInterval_adj path)

/-! ## §2 — the Markoff-matrix carrier (the recommended residue vehicle)

Per the classical proof (Zhang §5; Frobenius), the cleanest carrier of the Markov number `m_t` and
residue `u_t` along the tree is the **Markoff matrix** `M_t ∈ SL₂(ℤ)`, multiplicative under mediant
(`M_{r⊕s} = M_r·M_s`), with `m_t = (M_t)₂₁` (`.c`) and `u_t = (M_t)₂₂ − (M_t)₂₁`.  The Frobenius
determinant identities (the engine of monotonicity / `SamePairInjective`) then become a one-multiply
entry read-off using `det = 1`.  The backbone is **determinant multiplicativity**: -/

open E213.Lib.Math.Real213.ModularElliptic (Mat2 mul I2)

/-- The `2×2` determinant on `Mat2`. -/
def det2 (M : Mat2) : Int := M.a * M.d - M.b * M.c

/-- ★★★★★ **Determinant is multiplicative** — `det(MN) = det M · det N`.  Pure `ℤ` polynomial
    identity (`ring_intZ`); the backbone making the whole Markoff-matrix tree `det = 1`. -/
theorem det2_mul (M N : Mat2) : det2 (mul M N) = det2 M * det2 N := by
  show (M.a * N.a + M.b * N.c) * (M.c * N.b + M.d * N.d)
       - (M.a * N.b + M.b * N.d) * (M.c * N.a + M.d * N.c)
     = (M.a * M.d - M.b * M.c) * (N.a * N.d - N.b * N.c)
  ring_intZ

/-- Markoff matrix generators: `M_{0/1} = [[2,1],[1,1]]` (`genL`), `M_{1/0} = [[3,4],[2,3]]`
    (`genR`), both in `SL₂(ℤ)`. -/
def genL : Mat2 := ⟨2, 1, 1, 1⟩
def genR : Mat2 := ⟨3, 4, 2, 3⟩

/-- The Markoff matrix at a Stern-Brocot path (a word in the two generators). -/
def mMat : List Bool → Mat2
  | []     => I2
  | b :: t => mul (if b then genL else genR) (mMat t)

/-- ★★★★★ **Every Markoff matrix has `det = 1`** (`SL₂(ℤ)`) — by `det2_mul` + the det-1
    generators, the same det-1 invariant as the Farey-interval tree (`sbInterval_adj`). -/
theorem mMat_det1 (path : List Bool) : det2 (mMat path) = 1 := by
  induction path with
  | nil => show (1 : Int) * 1 - 0 * 0 = 1; ring_intZ
  | cons b t ih =>
      show det2 (mul (if b then genL else genR) (mMat t)) = 1
      rw [det2_mul]
      cases b
      · show det2 genR * det2 (mMat t) = 1; rw [ih]; show (3 * 3 - 4 * 2) * 1 = 1; ring_intZ
      · show det2 genL * det2 (mMat t) = 1; rw [ih]; show (2 * 1 - 1 * 1) * 1 = 1; ring_intZ

/-- ★★★★★ **Frobenius's determinant identity** (matrix form, the monotonicity engine).  For the
    mediant `M_t = M_r·M_s` with `det M_r = 1`, the cross-determinant
    `(M_r)ₐ·(M_t)_c − (M_r)_c·(M_t)ₐ = (M_s)_c = m_s`.  Since `m_s > 0`, this fixes the *sign* of
    the cross-determinant — exactly Zhang's Lemma 2 (slope `u_t/m_t` strictly monotone), the
    residue-map injectivity `SamePairInjective`.  Proof: it is `(M_s)_c · det M_r` (`ring_intZ`)
    `= (M_s)_c · 1`. -/
theorem markoff_frobenius (Mr Ms : Mat2) (hd : det2 Mr = 1) :
    Mr.a * (mul Mr Ms).c - Mr.c * (mul Mr Ms).a = Ms.c := by
  have hd' : Mr.a * Mr.d - Mr.b * Mr.c = 1 := hd
  show Mr.a * (Mr.c * Ms.a + Mr.d * Ms.c) - Mr.c * (Mr.a * Ms.a + Mr.b * Ms.c) = Ms.c
  calc Mr.a * (Mr.c * Ms.a + Mr.d * Ms.c) - Mr.c * (Mr.a * Ms.a + Mr.b * Ms.c)
      = Ms.c * (Mr.a * Mr.d - Mr.b * Mr.c) := by ring_intZ
    _ = Ms.c * 1 := by rw [hd']
    _ = Ms.c := by ring_intZ

/-- The Markov number at a node = the `(2,1)` matrix entry. -/
def markovNum (path : List Bool) : Int := (mMat path).c

/-- The residue at a node = `(M)₂₂ − (M)₂₁`. -/
def markovRes (path : List Bool) : Int := (mMat path).d - (mMat path).c

/-- Sanity: the root mediant `1/1 = (0/1)⊕(1/0)` gives `(m, u) = (5, 2)` — the Markov number `5`
    and its `√(−1)` residue `2` (`2²+1 = 5`). -/
theorem markov_root_node : markovNum [true, false] = 5 ∧ markovRes [true, false] = 2 := by
  refine ⟨?_, ?_⟩ <;> decide

end E213.Lib.Math.Real213.SternBrocotMarkov
