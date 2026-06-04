import E213.Lib.Math.Real213.MarkovInjectivity
import E213.Lib.Math.Real213.ModularElliptic
import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Tactic.List213
import E213.Lib.Math.Linalg213.DetN
import E213.Meta.Int213.Order

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
    (`genR`), both in `SL₂(ℤ)`.  These are the two interval endpoints; interior node matrices are
    mediant *products* `M_t = M_r·M_s` (NOT word products — `genL² = ⟨5,3,3,2⟩` has `a+d ≠ 3c`, so
    it is not a Markoff matrix). -/
def genL : Mat2 := ⟨2, 1, 1, 1⟩
def genR : Mat2 := ⟨3, 4, 2, 3⟩

/-- Interval of bounding Markoff matrices at a Stern-Brocot path (root = `(M_{0/1}, M_{1/0})`);
    each L/R step replaces one bound by the mediant `M_l·M_r`. -/
def mInterval : List Bool → Mat2 × Mat2
  | []         => (genL, genR)
  | true :: t  => ((mInterval t).1, mul (mInterval t).1 (mInterval t).2)
  | false :: t => (mul (mInterval t).1 (mInterval t).2, (mInterval t).2)

/-- The Markoff matrix at a node = the mediant of its two bounds, `M_t = M_l·M_r`. -/
def mNode (path : List Bool) : Mat2 := mul (mInterval path).1 (mInterval path).2

/-- Both bounds of every interval are in `SL₂(ℤ)` (`det = 1`), by `det2_mul` from the det-1
    generators. -/
theorem mInterval_det (path : List Bool) :
    det2 (mInterval path).1 = 1 ∧ det2 (mInterval path).2 = 1 := by
  induction path with
  | nil => exact ⟨by show (2 * 1 - 1 * 1 : Int) = 1; ring_intZ,
                  by show (3 * 3 - 4 * 2 : Int) = 1; ring_intZ⟩
  | cons b t ih =>
      cases b
      · refine ⟨?_, ih.2⟩
        show det2 (mul (mInterval t).1 (mInterval t).2) = 1
        rw [det2_mul, ih.1, ih.2]; ring_intZ
      · refine ⟨ih.1, ?_⟩
        show det2 (mul (mInterval t).1 (mInterval t).2) = 1
        rw [det2_mul, ih.1, ih.2]; ring_intZ

/-- ★★★★★ **Every Markoff node matrix has `det = 1`** (`SL₂(ℤ)`) — the mediant of two det-1
    bounds, the same det-1 invariant as the Farey-interval tree (`sbInterval_adj`). -/
theorem mNode_det1 (path : List Bool) : det2 (mNode path) = 1 := by
  show det2 (mul (mInterval path).1 (mInterval path).2) = 1
  rw [det2_mul, (mInterval_det path).1, (mInterval_det path).2]; ring_intZ

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

/-- ★★★★★ **Cayley–Hamilton Vieta recurrence** (matrix form, the Markov-equation engine).  With
    `det M_l = 1`, `(M_l·(M_l·M_r))_c = tr(M_l)·(M_l·M_r)_c − (M_r)_c` — from `M_l² = tr(M_l)·M_l − I`.
    Combined with the entry-shape `tr(M_l) = 3·(M_l)_c`, this is exactly the Markov Vieta jump
    `m' = 3·m₁·m₂ − m₃`, so the tree generates Markov triples (`markov_eq`).  Proof: the difference
    is `(M_r)_c·(1 − det M_l) = 0` (`ring_intZ`). -/
theorem markoff_vieta (Ml Mr : Mat2) (hd : det2 Ml = 1) :
    (mul Ml (mul Ml Mr)).c = (Ml.a + Ml.d) * (mul Ml Mr).c - Mr.c := by
  have hd' : Ml.a * Ml.d - Ml.b * Ml.c = 1 := hd
  show Ml.c * (Ml.a * Mr.a + Ml.b * Mr.c) + Ml.d * (Ml.c * Mr.a + Ml.d * Mr.c)
     = (Ml.a + Ml.d) * (Ml.c * Mr.a + Ml.d * Mr.c) - Mr.c
  calc Ml.c * (Ml.a * Mr.a + Ml.b * Mr.c) + Ml.d * (Ml.c * Mr.a + Ml.d * Mr.c)
      = ((Ml.a + Ml.d) * (Ml.c * Mr.a + Ml.d * Mr.c) - Mr.c)
        + Mr.c * (1 - (Ml.a * Ml.d - Ml.b * Ml.c)) := by ring_intZ
    _ = ((Ml.a + Ml.d) * (Ml.c * Mr.a + Ml.d * Mr.c) - Mr.c) + Mr.c * (1 - 1) := by rw [hd']
    _ = (Ml.a + Ml.d) * (Ml.c * Mr.a + Ml.d * Mr.c) - Mr.c := by ring_intZ

/-- Trace form of the Vieta recurrence: `tr(M_l²M_r) = tr(M_l)·tr(M_lM_r) − tr(M_r)` (det `M_l`=1). -/
theorem markoff_vieta_trace (Ml Mr : Mat2) (hd : det2 Ml = 1) :
    (mul Ml (mul Ml Mr)).a + (mul Ml (mul Ml Mr)).d
    = (Ml.a + Ml.d) * ((mul Ml Mr).a + (mul Ml Mr).d) - (Mr.a + Mr.d) := by
  have hd' : Ml.a * Ml.d - Ml.b * Ml.c = 1 := hd
  show (Ml.a*(Ml.a*Mr.a+Ml.b*Mr.c) + Ml.b*(Ml.c*Mr.a+Ml.d*Mr.c))
       + (Ml.c*(Ml.a*Mr.b+Ml.b*Mr.d) + Ml.d*(Ml.c*Mr.b+Ml.d*Mr.d))
     = (Ml.a+Ml.d) * ((Ml.a*Mr.a+Ml.b*Mr.c) + (Ml.c*Mr.b+Ml.d*Mr.d)) - (Mr.a+Mr.d)
  calc _ = ((Ml.a+Ml.d) * ((Ml.a*Mr.a+Ml.b*Mr.c) + (Ml.c*Mr.b+Ml.d*Mr.d)) - (Mr.a+Mr.d))
        + (Mr.a+Mr.d) * (1 - (Ml.a*Ml.d - Ml.b*Ml.c)) := by ring_intZ
    _ = _ := by rw [hd']; ring_intZ

/-- Right Vieta recurrence: `((M_l M_r) M_r)_c = tr(M_r)·(M_lM_r)_c − (M_l)_c` (det `M_r`=1). -/
theorem markoff_vieta_R (Ml Mr : Mat2) (hd : det2 Mr = 1) :
    (mul (mul Ml Mr) Mr).c = (Mr.a + Mr.d) * (mul Ml Mr).c - Ml.c := by
  have hd' : Mr.a * Mr.d - Mr.b * Mr.c = 1 := hd
  show (Ml.c*Mr.a+Ml.d*Mr.c)*Mr.a + (Ml.c*Mr.b+Ml.d*Mr.d)*Mr.c
     = (Mr.a+Mr.d)*(Ml.c*Mr.a+Ml.d*Mr.c) - Ml.c
  calc _ = ((Mr.a+Mr.d)*(Ml.c*Mr.a+Ml.d*Mr.c) - Ml.c) + Ml.c*(1 - (Mr.a*Mr.d-Mr.b*Mr.c)) := by ring_intZ
    _ = _ := by rw [hd']; ring_intZ

/-- Right trace recurrence: `tr((M_lM_r)M_r) = tr(M_r)·tr(M_lM_r) − tr(M_l)` (det `M_r`=1). -/
theorem markoff_vieta_trace_R (Ml Mr : Mat2) (hd : det2 Mr = 1) :
    (mul (mul Ml Mr) Mr).a + (mul (mul Ml Mr) Mr).d
    = (Mr.a + Mr.d) * ((mul Ml Mr).a + (mul Ml Mr).d) - (Ml.a + Ml.d) := by
  have hd' : Mr.a * Mr.d - Mr.b * Mr.c = 1 := hd
  show ((Ml.a*Mr.a+Ml.b*Mr.c)*Mr.a + (Ml.a*Mr.b+Ml.b*Mr.d)*Mr.c)
       + ((Ml.c*Mr.a+Ml.d*Mr.c)*Mr.b + (Ml.c*Mr.b+Ml.d*Mr.d)*Mr.d)
     = (Mr.a+Mr.d)*((Ml.a*Mr.a+Ml.b*Mr.c) + (Ml.c*Mr.b+Ml.d*Mr.d)) - (Ml.a+Ml.d)
  calc _ = ((Mr.a+Mr.d)*((Ml.a*Mr.a+Ml.b*Mr.c) + (Ml.c*Mr.b+Ml.d*Mr.d)) - (Ml.a+Ml.d))
        + (Ml.a+Ml.d)*(1 - (Mr.a*Mr.d-Mr.b*Mr.c)) := by ring_intZ
    _ = _ := by rw [hd']; ring_intZ

/-- ★★★★★ **The entry-shape (Markoff form) `tr = 3·(·)_c`** holds for both interval bounds AND the
    mediant, at every node — the keystone (Zhang Prop 7).  Proved as a *coupled invariant*: each
    L/R step's new mediant `tr = 3c` follows from the old mediant's via the Vieta + trace
    recurrences (`markoff_vieta(_trace)(_R)`) and `det = 1`.  This is what makes `markovNum` the
    actual Markov coefficient and (with `markoff_vieta`) gives the Markov equation on the tree. -/
theorem mInterval_shape (path : List Bool) :
    (mInterval path).1.a + (mInterval path).1.d = 3 * (mInterval path).1.c
    ∧ (mInterval path).2.a + (mInterval path).2.d = 3 * (mInterval path).2.c
    ∧ (mul (mInterval path).1 (mInterval path).2).a + (mul (mInterval path).1 (mInterval path).2).d
        = 3 * (mul (mInterval path).1 (mInterval path).2).c := by
  induction path with
  | nil => refine ⟨?_, ?_, ?_⟩ <;> decide
  | cons b t ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      have d1 := (mInterval_det t).1
      have d2 := (mInterval_det t).2
      cases b
      · refine ⟨h3, h2, ?_⟩
        show (mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).a
             + (mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).d
             = 3 * (mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).c
        rw [markoff_vieta_trace_R (mInterval t).1 (mInterval t).2 d2,
            markoff_vieta_R (mInterval t).1 (mInterval t).2 d2, h3, h1]; ring_intZ
      · refine ⟨h1, h3, ?_⟩
        show (mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).a
             + (mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).d
             = 3 * (mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).c
        rw [markoff_vieta_trace (mInterval t).1 (mInterval t).2 d1,
            markoff_vieta (mInterval t).1 (mInterval t).2 d1, h3, h2]; ring_intZ

/-- The node's entry-shape `tr(M_t) = 3·m_t` (`m_t = (M_t)_c`) — `markovNum` is the Markov
    coefficient.  Corollary of `mInterval_shape`. -/
theorem mNode_shape (path : List Bool) : (mNode path).a + (mNode path).d = 3 * (mNode path).c :=
  (mInterval_shape path).2.2

/-- The Markov number at a node = the `(2,1)` matrix entry of the mediant. -/
def markovNum (path : List Bool) : Int := (mNode path).c

/-- The residue at a node = `(M)₂₂ − (M)₂₁`. -/
def markovRes (path : List Bool) : Int := (mNode path).d - (mNode path).c

/-- Sanity: the first nodes are the Markov numbers `5, 13, 29` (root mediant `1/1` and its two
    children), with residues `2, 5, 12` (`2²+1=5`, `5²+1=2·13`, `12²+1=5·29`). -/
theorem markov_first_nodes :
    (markovNum [] = 5 ∧ markovRes [] = 2)
    ∧ (markovNum [true] = 13 ∧ markovRes [true] = 5)
    ∧ (markovNum [false] = 29 ∧ markovRes [false] = 12) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> decide

/-! ## §3 — the tree generates Markov triples -/

/-- Markov equation preserved by the Vieta jump `(x,y,z) → (x,z,3xz−y)` (over `ℤ`). -/
theorem markov_vieta_int (x y z : Int) (h : x * x + y * y + z * z = 3 * x * y * z) :
    x * x + z * z + (3 * x * z - y) * (3 * x * z - y) = 3 * x * z * (3 * x * z - y) := by
  have e : x * x + z * z + (3 * x * z - y) * (3 * x * z - y)
         = 3 * x * z * (3 * x * z - y) + ((x * x + y * y + z * z) - 3 * x * y * z) := by ring_intZ
  rw [h] at e; rw [e]; ring_intZ

/-- ★★★★★ **The Stern-Brocot/Markoff tree generates Markov triples.**  At every node, the triple of
    `(2,1)`-entries `(m_l, m_r, m_t)` (the two interval bounds and the mediant) satisfies the Markov
    equation `m_l² + m_r² + m_t² = 3·m_l·m_r·m_t`.  Proof: Vieta-jump induction — each L/R step's new
    mediant is `3·m₁·m₂ − m₃` (`markoff_vieta(_R)` + the entry-shape `mInterval_shape`), and the
    Markov equation is preserved by the jump (`markov_vieta_int`, inlined).  So `markovNum` ranges
    over exactly the Markov numbers — the semantic identification of the tree with the Markov tree. -/
theorem mInterval_markov (path : List Bool) :
    (mInterval path).1.c * (mInterval path).1.c + (mInterval path).2.c * (mInterval path).2.c
      + (mNode path).c * (mNode path).c
    = 3 * (mInterval path).1.c * (mInterval path).2.c * (mNode path).c := by
  induction path with
  | nil => show (1 : Int) * 1 + 2 * 2 + (mul genL genR).c * (mul genL genR).c
                = 3 * 1 * 2 * (mul genL genR).c
           decide
  | cons b t ih =>
      have d1 := (mInterval_det t).1
      have d2 := (mInterval_det t).2
      obtain ⟨h1, h2, _⟩ := mInterval_shape t
      have ihm : (mInterval t).1.c * (mInterval t).1.c + (mInterval t).2.c * (mInterval t).2.c
               + (mul (mInterval t).1 (mInterval t).2).c * (mul (mInterval t).1 (mInterval t).2).c
               = 3 * (mInterval t).1.c * (mInterval t).2.c * (mul (mInterval t).1 (mInterval t).2).c := ih
      cases b
      · show (mul (mInterval t).1 (mInterval t).2).c * (mul (mInterval t).1 (mInterval t).2).c
             + (mInterval t).2.c * (mInterval t).2.c
             + (mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).c
               * (mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).c
           = 3 * (mul (mInterval t).1 (mInterval t).2).c * (mInterval t).2.c
             * (mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).c
        rw [markoff_vieta_R (mInterval t).1 (mInterval t).2 d2, h2]
        have e : (mul (mInterval t).1 (mInterval t).2).c * (mul (mInterval t).1 (mInterval t).2).c
               + (mInterval t).2.c * (mInterval t).2.c
               + (3 * (mInterval t).2.c * (mul (mInterval t).1 (mInterval t).2).c - (mInterval t).1.c)
                 * (3 * (mInterval t).2.c * (mul (mInterval t).1 (mInterval t).2).c - (mInterval t).1.c)
             = 3 * (mul (mInterval t).1 (mInterval t).2).c * (mInterval t).2.c
               * (3 * (mInterval t).2.c * (mul (mInterval t).1 (mInterval t).2).c - (mInterval t).1.c)
               + (((mInterval t).1.c * (mInterval t).1.c + (mInterval t).2.c * (mInterval t).2.c
                   + (mul (mInterval t).1 (mInterval t).2).c * (mul (mInterval t).1 (mInterval t).2).c)
                  - 3 * (mInterval t).1.c * (mInterval t).2.c * (mul (mInterval t).1 (mInterval t).2).c) := by
          ring_intZ
        rw [e, ihm]; ring_intZ
      · show (mInterval t).1.c * (mInterval t).1.c
             + (mul (mInterval t).1 (mInterval t).2).c * (mul (mInterval t).1 (mInterval t).2).c
             + (mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).c
               * (mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).c
           = 3 * (mInterval t).1.c * (mul (mInterval t).1 (mInterval t).2).c
             * (mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).c
        rw [markoff_vieta (mInterval t).1 (mInterval t).2 d1, h1]
        have e : (mInterval t).1.c * (mInterval t).1.c
               + (mul (mInterval t).1 (mInterval t).2).c * (mul (mInterval t).1 (mInterval t).2).c
               + (3 * (mInterval t).1.c * (mul (mInterval t).1 (mInterval t).2).c - (mInterval t).2.c)
                 * (3 * (mInterval t).1.c * (mul (mInterval t).1 (mInterval t).2).c - (mInterval t).2.c)
             = 3 * (mInterval t).1.c * (mul (mInterval t).1 (mInterval t).2).c
               * (3 * (mInterval t).1.c * (mul (mInterval t).1 (mInterval t).2).c - (mInterval t).2.c)
               + (((mInterval t).1.c * (mInterval t).1.c + (mInterval t).2.c * (mInterval t).2.c
                   + (mul (mInterval t).1 (mInterval t).2).c * (mul (mInterval t).1 (mInterval t).2).c)
                  - 3 * (mInterval t).1.c * (mInterval t).2.c * (mul (mInterval t).1 (mInterval t).2).c) := by
          ring_intZ
        rw [e, ihm]; ring_intZ

/-! ## §4 — positivity of the Markoff matrix entries

  Every interval-bound matrix and every node mediant has all four entries `≥ 1` (strictly positive
  integers).  This is the prerequisite for the *sign* of Frobenius's cross-determinant
  (`markoff_frobenius` gives it `= m_s`, and `m_s ≥ 1 > 0`), hence for global monotonicity of the
  residue slope `u_t/m_t` (Zhang Lemma 2 = `SamePairInjective`).  Proved by tree induction: the
  generators have all entries `≥ 1`, and `mul` preserves "all entries `≥ 1`" (each product entry is
  a sum of two products of `≥ 1` factors). -/

/-- `z − 0 = z` (pure; `ring_intZ` does not simplify the literal `0`). -/
private theorem sub_zero_int (z : Int) : z - 0 = z := by
  show z + -(0 : Int) = z
  rw [E213.Meta.Int213.PolyIntM.neg_zeroZ]
  exact Int.add_zero z

/-- Int bridge: `0 ≤ b − a → a ≤ b`.  `a ≤ b` is `Int.NonNeg (b − a)`; `0 ≤ b − a` is
    `Int.NonNeg ((b−a) − 0)`, and `(b−a) − 0 = b − a`. -/
private theorem le_of_nonneg_sub {a b : Int} (h : 0 ≤ b - a) : a ≤ b := by
  show Int.NonNeg (b - a)
  have h' : Int.NonNeg ((b - a) - 0) := h
  rw [sub_zero_int] at h'; exact h'

/-- Int bridge (reverse): `a ≤ b → 0 ≤ b − a`. -/
private theorem nonneg_sub_of_le {a b : Int} (h : a ≤ b) : 0 ≤ b - a := by
  show Int.NonNeg ((b - a) - 0)
  rw [sub_zero_int]; exact h

/-- `1 ≤ x → 1 ≤ y → 1 ≤ x·y`.  `x·y − 1 = (x−1)(y−1) + ((x−1)+(y−1))`, a sum of nonnegatives. -/
private theorem one_le_mul {x y : Int} (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ x * y := by
  apply le_of_nonneg_sub
  have hx0 : 0 ≤ x - 1 := nonneg_sub_of_le hx
  have hy0 : 0 ≤ y - 1 := nonneg_sub_of_le hy
  have key : x * y - 1 = (x - 1) * (y - 1) + ((x - 1) + (y - 1)) := by ring_intZ
  rw [key]
  exact E213.Meta.Int213.add_nonneg
    (E213.Meta.Int213.mul_nonneg hx0 hy0) (E213.Meta.Int213.add_nonneg hx0 hy0)

/-- `1 ≤ x → 0 ≤ y → 1 ≤ x + y`.  `(x+y) − 1 = (x−1) + y`, a sum of nonnegatives. -/
private theorem one_le_add_nonneg {x y : Int} (hx : 1 ≤ x) (hy : 0 ≤ y) : 1 ≤ x + y := by
  apply le_of_nonneg_sub
  have hx0 : 0 ≤ x - 1 := nonneg_sub_of_le hx
  have key : (x + y) - 1 = (x - 1) + y := by ring_intZ
  rw [key]
  exact E213.Meta.Int213.add_nonneg hx0 hy

/-- `1 ≤ x → 0 ≤ x`.  `x − 0 = (x−1) + 1`. -/
private theorem nonneg_of_one_le {x : Int} (h : 1 ≤ x) : 0 ≤ x := by
  apply le_of_nonneg_sub
  have key : x - 0 = (x - 1) + 1 := by rw [sub_zero_int]; ring_intZ
  rw [key]
  exact E213.Meta.Int213.add_nonneg (nonneg_sub_of_le h) (by decide)

/-- A matrix is *positive* when all four entries are `≥ 1` (a positive-integer `SL₂`-matrix). -/
def posMat (M : Mat2) : Prop := 1 ≤ M.a ∧ 1 ≤ M.b ∧ 1 ≤ M.c ∧ 1 ≤ M.d

/-- `mul` preserves positivity: each product-matrix entry `p·r + q·s` is `≥ 1` (first product `≥ 1`,
    second product `≥ 1 ≥ 0`). -/
theorem posMat_mul {M N : Mat2} (hM : posMat M) (hN : posMat N) : posMat (mul M N) := by
  obtain ⟨ha, hb, hc, hd⟩ := hM
  obtain ⟨ha', hb', hc', hd'⟩ := hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · show 1 ≤ M.a * N.a + M.b * N.c
    exact one_le_add_nonneg (one_le_mul ha ha') (nonneg_of_one_le (one_le_mul hb hc'))
  · show 1 ≤ M.a * N.b + M.b * N.d
    exact one_le_add_nonneg (one_le_mul ha hb') (nonneg_of_one_le (one_le_mul hb hd'))
  · show 1 ≤ M.c * N.a + M.d * N.c
    exact one_le_add_nonneg (one_le_mul hc ha') (nonneg_of_one_le (one_le_mul hd hc'))
  · show 1 ≤ M.c * N.b + M.d * N.d
    exact one_le_add_nonneg (one_le_mul hc hb') (nonneg_of_one_le (one_le_mul hd hd'))

/-- ★★★★★ **Both interval bounds are positive `SL₂` matrices** (all entries `≥ 1`) at every node, by
    tree induction: the generators are positive, and each L/R mediant step is a `posMat_mul`. -/
theorem mInterval_pos (path : List Bool) :
    posMat (mInterval path).1 ∧ posMat (mInterval path).2 := by
  induction path with
  | nil =>
      exact ⟨by refine ⟨?_, ?_, ?_, ?_⟩ <;> decide,
             by refine ⟨?_, ?_, ?_, ?_⟩ <;> decide⟩
  | cons b t ih =>
      cases b
      · exact ⟨posMat_mul ih.1 ih.2, ih.2⟩
      · exact ⟨ih.1, posMat_mul ih.1 ih.2⟩

/-- ★★★★★ **Every Markoff node matrix is positive** (all entries `≥ 1`). -/
theorem mNode_pos (path : List Bool) : posMat (mNode path) :=
  posMat_mul (mInterval_pos path).1 (mInterval_pos path).2

/-- The Markov number at every node is `≥ 1` (strictly positive) — the cross-determinant of
    `markoff_frobenius` is `m_s ≥ 1 > 0`, fixing the monotonicity sign. -/
theorem markovNum_pos (path : List Bool) : 1 ≤ markovNum path :=
  (mNode_pos path).2.2.1

/-! ## §5 — the residue is a square root of `−1` mod the Markov number

  The residue `u_t = (M_t)₂₂ − (M_t)₂₁ = d − c` satisfies `u_t² ≡ −1 (mod m_t)` (with `m_t = c`),
  the defining congruence of the recovery (`markov_root_recovery` / `SqrtNegOneTwoRoots`).  This is
  a one-shot ring identity: with `det M_t = 1` and the entry-shape `a + d = 3c`,
  `u_t² + 1 = (c + d − b)·c`, so `m_t ∣ u_t² + 1`.  (Verified witness on the first node
  `M = ⟨8,11,5,7⟩`: `u² + 1 = 5 = (5 + 7 − 11)·5`.) -/

/-- ★★★★★ **The residue squares to `−1` modulo the Markov number** (exact integer form).  For every
    node, `u_t² + 1 = (m_t + d − b)·m_t` (`u_t = d − c`, `m_t = c`), using `det = 1` (`mNode_det1`)
    and the entry-shape `a + d = 3c` (`mNode_shape`).  The two correction terms
    `−(det − 1)` and `d·(tr − 3c)` vanish.  Pure ℤ ring identity:
    `(d−c)² + 1 = (c+d−b)·c − (ad−bc−1) + d·(a+d−3c)`. -/
theorem markovRes_sq (path : List Bool) :
    markovRes path * markovRes path + 1
    = ((mNode path).c + (mNode path).d - (mNode path).b) * (mNode path).c := by
  have hd : (mNode path).a * (mNode path).d - (mNode path).b * (mNode path).c = 1 := mNode_det1 path
  have hs : (mNode path).a + (mNode path).d = 3 * (mNode path).c := mNode_shape path
  show ((mNode path).d - (mNode path).c) * ((mNode path).d - (mNode path).c) + 1
     = ((mNode path).c + (mNode path).d - (mNode path).b) * (mNode path).c
  calc ((mNode path).d - (mNode path).c) * ((mNode path).d - (mNode path).c) + 1
      = ((mNode path).c + (mNode path).d - (mNode path).b) * (mNode path).c
        + (-(((mNode path).a * (mNode path).d - (mNode path).b * (mNode path).c) - 1))
        + (mNode path).d * (((mNode path).a + (mNode path).d) - 3 * (mNode path).c) := by ring_intZ
    _ = ((mNode path).c + (mNode path).d - (mNode path).b) * (mNode path).c
        + (-((1 : Int) - 1))
        + (mNode path).d * (3 * (mNode path).c - 3 * (mNode path).c) := by rw [hd, hs]
    _ = ((mNode path).c + (mNode path).d - (mNode path).b) * (mNode path).c := by ring_intZ

/-- ★★★★★ **`m_t ∣ u_t² + 1`** — the residue is a square root of `−1` modulo the Markov number, the
    `SqrtNegOneTwoRoots` congruence realised on every tree node (witness `m_t + d − b`). -/
theorem markovNum_dvd_res_sq_succ (path : List Bool) :
    markovNum path ∣ markovRes path * markovRes path + 1 :=
  ⟨(mNode path).c + (mNode path).d - (mNode path).b, by
    show markovRes path * markovRes path + 1
       = (mNode path).c * ((mNode path).c + (mNode path).d - (mNode path).b)
    rw [markovRes_sq]; ring_intZ⟩

/-! ## §6 — the Frobenius residue cross-determinant (the monotonicity engine)

  The residue version of `markoff_frobenius`: for the mediant `M_t = M_l·M_r` with `det M_r = 1`,
  `u_r·m_t − u_t·m_r = m_l` (`u_• = d − c`, `m_• = c`).  Since `m_l ≥ 1 > 0` (`mInterval_pos`), this
  pins the *sign* of the residue cross-determinant between the right bound and the node — the engine
  of Zhang's Lemma 2 (strict monotonicity of the residue slope `u_t/m_t`), the route to
  `SamePairInjective`.  Pure ℤ identity: the difference is `m_l·(det M_r − 1) = 0`.

  (The *left* analogue `u_t·m_l − u_l·m_t = m_r` is **not** a generic det-1 identity — it holds only
  on the tree, 54/2000 on random det-1 shape matrices — so it needs tree induction, deferred.) -/

/-- ★★★★★ **Frobenius residue cross-determinant** (generic, the monotonicity engine).  With
    `det M_r = 1`, `u_r·(M_l M_r)_c − u_t·m_r = m_l` where `u_r = (M_r)_d − (M_r)_c`,
    `u_t = (M_l M_r)_d − (M_l M_r)_c`, `m_r = (M_r)_c`, `m_l = (M_l)_c`.  Proof: the difference is
    `(M_l)_c·(det M_r − 1)` (`ring_intZ`) `= 0`. -/
theorem markoff_frobenius_res (Ml Mr : Mat2) (hd : det2 Mr = 1) :
    (Mr.d - Mr.c) * (mul Ml Mr).c - ((mul Ml Mr).d - (mul Ml Mr).c) * Mr.c = Ml.c := by
  have hd' : Mr.a * Mr.d - Mr.b * Mr.c = 1 := hd
  show (Mr.d - Mr.c) * (Ml.c * Mr.a + Ml.d * Mr.c)
     - ((Ml.c * Mr.b + Ml.d * Mr.d) - (Ml.c * Mr.a + Ml.d * Mr.c)) * Mr.c = Ml.c
  calc (Mr.d - Mr.c) * (Ml.c * Mr.a + Ml.d * Mr.c)
       - ((Ml.c * Mr.b + Ml.d * Mr.d) - (Ml.c * Mr.a + Ml.d * Mr.c)) * Mr.c
      = Ml.c + Ml.c * ((Mr.a * Mr.d - Mr.b * Mr.c) - 1) := by ring_intZ
    _ = Ml.c + Ml.c * ((1 : Int) - 1) := by rw [hd']
    _ = Ml.c := by ring_intZ

/-- ★★★★★ **Tree Frobenius residue identity**: at every node, `u_r·m_t − u_t·m_r = m_l` — the right
    interval bound's residue, the node's residue/number, and the left bound's number satisfy the
    Frobenius cross-determinant.  Corollary of `markoff_frobenius_res` at `det M_r = 1`
    (`mInterval_det`).  `m_l ≥ 1 > 0` fixes the slope's monotone sign. -/
theorem markovRes_cross (path : List Bool) :
    ((mInterval path).2.d - (mInterval path).2.c) * (mNode path).c
      - markovRes path * (mInterval path).2.c
    = (mInterval path).1.c :=
  markoff_frobenius_res (mInterval path).1 (mInterval path).2 (mInterval_det path).2

/-- ★★★★★ **The residue recovers `m_r` from `m_l`**: `m_t ∣ (u_t·m_l − m_r)`, i.e.
    `u_t·m_l ≡ m_r (mod m_t)` — the recovery congruence of `SamePairInjective` realised on every
    tree node.  Derived purely by modular arithmetic from the two preceding facts (NO tree
    induction): `markovRes_cross` gives `u_t·m_r ≡ −m_l`, and `markovNum_dvd_res_sq_succ` gives
    `u_t² ≡ −1`; multiplying the first by `u_t` and using the second yields `u_t·m_l ≡ m_r`.  The
    explicit witness is `q = u_t·u_r − (m_t + d − b)·m_r`, verified by the ring identity
    `u_t·m_l − m_r = m_t·q − m_r·(u_t²+1) + m_r·(m_t+d−b)·m_t` with the two substitutions. -/
theorem markovRes_recovery_dvd (path : List Bool) :
    markovNum path ∣ markovRes path * (mInterval path).1.c - (mInterval path).2.c := by
  refine ⟨markovRes path * ((mInterval path).2.d - (mInterval path).2.c)
          - ((mNode path).c + (mNode path).d - (mNode path).b) * (mInterval path).2.c, ?_⟩
  have hc := markovRes_cross path
  have hs := markovRes_sq path
  show markovRes path * (mInterval path).1.c - (mInterval path).2.c
     = (mNode path).c
       * (markovRes path * ((mInterval path).2.d - (mInterval path).2.c)
          - ((mNode path).c + (mNode path).d - (mNode path).b) * (mInterval path).2.c)
  rw [← hc]
  have e : markovRes path
             * (((mInterval path).2.d - (mInterval path).2.c) * (mNode path).c
                - markovRes path * (mInterval path).2.c)
           - (mInterval path).2.c
         = (mNode path).c
             * (markovRes path * ((mInterval path).2.d - (mInterval path).2.c)
                - ((mNode path).c + (mNode path).d - (mNode path).b) * (mInterval path).2.c)
           - (mInterval path).2.c * (markovRes path * markovRes path + 1)
           + (mInterval path).2.c
             * (((mNode path).c + (mNode path).d - (mNode path).b) * (mNode path).c) := by ring_intZ
  rw [e, hs]; ring_intZ

/-! ## §7 — strict slope monotonicity (Zhang Lemma 2, the right half)

  The Frobenius residue cross-determinant `u_r·m_t − u_t·m_r = m_l` (`markovRes_cross`) with
  `m_l ≥ 1 > 0` (`mInterval_pos`) gives the **strict** inequality `u_t·m_r < u_r·m_t`, i.e. the
  node's residue slope `u_t/m_t` is strictly below the right bound's `u_r/m_r`.  This is the right
  half of Zhang's Lemma 2 (the mediant slope lies strictly between the two bounds); the left half
  `u_l·m_t < u_t·m_l` needs the tree-specific identity `u_t·m_l − u_l·m_t = m_r` (deferred). -/

/-- Int bridge: `b − a = m` and `1 ≤ m → a < b`.  `a < b` is `Int.NonNeg (b − (a+1))`;
    `b − (a+1) = (b−a) − 1 = m − 1`, and `1 ≤ m` is `Int.NonNeg (m − 1)`. -/
private theorem lt_of_sub_eq_of_one_le {a b m : Int} (h : b - a = m) (hm : 1 ≤ m) : a < b := by
  show Int.NonNeg (b - (a + 1))
  have e : b - (a + 1) = (b - a) - 1 := by ring_intZ
  rw [e, h]; exact hm

/-- ★★★★★ **Strict slope monotonicity (right half of Zhang Lemma 2)**: `u_t·m_r < u_r·m_t` — the
    node's residue slope is strictly less than the right interval bound's.  Immediate from
    `markovRes_cross` (`u_r·m_t − u_t·m_r = m_l`) and `1 ≤ m_l` (`mInterval_pos`).  This is the
    strict monotonicity that, with the (deferred) left half, gives residue-injectivity along the
    tree. -/
theorem markov_node_slope_lt_right (path : List Bool) :
    markovRes path * (mInterval path).2.c
      < ((mInterval path).2.d - (mInterval path).2.c) * (mNode path).c :=
  lt_of_sub_eq_of_one_le (markovRes_cross path) (mInterval_pos path).1.2.2.1

/-! ## §8 — the tree-specific left Frobenius identity (left half of Zhang Lemma 2)

  `u_t·m_l − u_l·m_t = m_r` — the mirror of `markovRes_cross`, which is **not** a generic det-1
  identity (it needs the tree's recursion).  Proved by coupled induction using (i) the **residue
  Vieta recurrence** `u_t' = tr·u_t − u_r` (the residue `d−c` is linear, so it satisfies the same
  Cayley–Hamilton recurrence as the number `c`); (ii) `markoff_vieta`; (iii) the generic
  bound-residue identity `m_l·u_r − m_r·u_l = 3 m_l m_r − m_t` (needs only the right bound's shape);
  (iv) the IH and the generic `markovRes_cross`.  Then `markov_node_slope_gt_left` gives the left
  half of strict monotonicity — completing "mediant slope strictly between the two bounds". -/

/-- Residue Vieta recurrence (L): `u` (`=d−c`) satisfies the same recurrence as the number `c`,
    `u_{l²r} = tr(M_l)·u_{lr} − u_r` (det `M_l`=1).  The difference is `u_r·(1 − det M_l) = 0`. -/
theorem markoff_res_vieta (Ml Mr : Mat2) (hd : det2 Ml = 1) :
    (mul Ml (mul Ml Mr)).d - (mul Ml (mul Ml Mr)).c
    = (Ml.a + Ml.d) * ((mul Ml Mr).d - (mul Ml Mr).c) - (Mr.d - Mr.c) := by
  have hd' : Ml.a * Ml.d - Ml.b * Ml.c = 1 := hd
  show (Ml.c * (Ml.a * Mr.b + Ml.b * Mr.d) + Ml.d * (Ml.c * Mr.b + Ml.d * Mr.d))
       - (Ml.c * (Ml.a * Mr.a + Ml.b * Mr.c) + Ml.d * (Ml.c * Mr.a + Ml.d * Mr.c))
     = (Ml.a + Ml.d) * ((Ml.c * Mr.b + Ml.d * Mr.d) - (Ml.c * Mr.a + Ml.d * Mr.c)) - (Mr.d - Mr.c)
  calc (Ml.c * (Ml.a * Mr.b + Ml.b * Mr.d) + Ml.d * (Ml.c * Mr.b + Ml.d * Mr.d))
       - (Ml.c * (Ml.a * Mr.a + Ml.b * Mr.c) + Ml.d * (Ml.c * Mr.a + Ml.d * Mr.c))
      = ((Ml.a + Ml.d) * ((Ml.c * Mr.b + Ml.d * Mr.d) - (Ml.c * Mr.a + Ml.d * Mr.c)) - (Mr.d - Mr.c))
        + (Mr.d - Mr.c) * (1 - (Ml.a * Ml.d - Ml.b * Ml.c)) := by ring_intZ
    _ = _ := by rw [hd']; ring_intZ

/-- Residue Vieta recurrence (R): `u_{lr²} = tr(M_r)·u_{lr} − u_l` (det `M_r`=1). -/
theorem markoff_res_vieta_R (Ml Mr : Mat2) (hd : det2 Mr = 1) :
    (mul (mul Ml Mr) Mr).d - (mul (mul Ml Mr) Mr).c
    = (Mr.a + Mr.d) * ((mul Ml Mr).d - (mul Ml Mr).c) - (Ml.d - Ml.c) := by
  have hd' : Mr.a * Mr.d - Mr.b * Mr.c = 1 := hd
  show ((Ml.c * Mr.a + Ml.d * Mr.c) * Mr.b + (Ml.c * Mr.b + Ml.d * Mr.d) * Mr.d)
       - ((Ml.c * Mr.a + Ml.d * Mr.c) * Mr.a + (Ml.c * Mr.b + Ml.d * Mr.d) * Mr.c)
     = (Mr.a + Mr.d) * ((Ml.c * Mr.b + Ml.d * Mr.d) - (Ml.c * Mr.a + Ml.d * Mr.c)) - (Ml.d - Ml.c)
  calc ((Ml.c * Mr.a + Ml.d * Mr.c) * Mr.b + (Ml.c * Mr.b + Ml.d * Mr.d) * Mr.d)
       - ((Ml.c * Mr.a + Ml.d * Mr.c) * Mr.a + (Ml.c * Mr.b + Ml.d * Mr.d) * Mr.c)
      = ((Mr.a + Mr.d) * ((Ml.c * Mr.b + Ml.d * Mr.d) - (Ml.c * Mr.a + Ml.d * Mr.c)) - (Ml.d - Ml.c))
        + (Ml.d - Ml.c) * (1 - (Mr.a * Mr.d - Mr.b * Mr.c)) := by ring_intZ
    _ = _ := by rw [hd']; ring_intZ

/-- Generic bound-residue identity: `m_l·u_r − m_r·u_l = 3 m_l m_r − m_t` — needs only the right
    bound's entry-shape `M_r.a + M_r.d = 3 M_r.c`.  The difference is `M_l.c·(tr M_r − 3 m_r) = 0`. -/
theorem bound_res_identity (Ml Mr : Mat2) (hs : Mr.a + Mr.d = 3 * Mr.c) :
    Ml.c * (Mr.d - Mr.c) - Mr.c * (Ml.d - Ml.c) = 3 * Ml.c * Mr.c - (mul Ml Mr).c := by
  show Ml.c * (Mr.d - Mr.c) - Mr.c * (Ml.d - Ml.c)
     = 3 * Ml.c * Mr.c - (Ml.c * Mr.a + Ml.d * Mr.c)
  calc Ml.c * (Mr.d - Mr.c) - Mr.c * (Ml.d - Ml.c)
      = (3 * Ml.c * Mr.c - (Ml.c * Mr.a + Ml.d * Mr.c)) + Ml.c * ((Mr.a + Mr.d) - 3 * Mr.c) := by
        ring_intZ
    _ = (3 * Ml.c * Mr.c - (Ml.c * Mr.a + Ml.d * Mr.c)) + Ml.c * (3 * Mr.c - 3 * Mr.c) := by rw [hs]
    _ = 3 * Ml.c * Mr.c - (Ml.c * Mr.a + Ml.d * Mr.c) := by ring_intZ

/-- ★★★★★ **Tree-specific left Frobenius identity**: `u_t·m_l − u_l·m_t = m_r` at every node — the
    mirror of `markovRes_cross`, the missing half of Zhang's Lemma 2.  By coupled induction: the
    R-step closes via the IH; the L-step via `3·m_l·(IH) − (bound_res_identity)`, both using the
    residue + number Vieta recurrences and the right bound's entry-shape. -/
theorem markovRes_cross_left (path : List Bool) :
    markovRes path * (mInterval path).1.c
      - ((mInterval path).1.d - (mInterval path).1.c) * (mNode path).c
    = (mInterval path).2.c := by
  induction path with
  | nil => show ((mul genL genR).d - (mul genL genR).c) * genL.c
                - (genL.d - genL.c) * (mul genL genR).c = genR.c
           decide
  | cons b t ih =>
      have d1 := (mInterval_det t).1
      have d2 := (mInterval_det t).2
      have s1 := (mInterval_shape t).1
      have s2 := (mInterval_shape t).2.1
      have ihm : ((mul (mInterval t).1 (mInterval t).2).d - (mul (mInterval t).1 (mInterval t).2).c)
                   * (mInterval t).1.c
                 - ((mInterval t).1.d - (mInterval t).1.c) * (mul (mInterval t).1 (mInterval t).2).c
               = (mInterval t).2.c := ih
      cases b
      · -- R-step (false): interval (M_t, M_r); gR = u_t·m_l − u_l·m_t = m_r (the IH).
        show ((mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).d
              - (mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).c)
               * (mul (mInterval t).1 (mInterval t).2).c
             - ((mul (mInterval t).1 (mInterval t).2).d - (mul (mInterval t).1 (mInterval t).2).c)
               * (mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).c
           = (mInterval t).2.c
        rw [markoff_res_vieta_R (mInterval t).1 (mInterval t).2 d2,
            markoff_vieta_R (mInterval t).1 (mInterval t).2 d2, s2]
        calc _ = ((mul (mInterval t).1 (mInterval t).2).d - (mul (mInterval t).1 (mInterval t).2).c)
                   * (mInterval t).1.c
                 - ((mInterval t).1.d - (mInterval t).1.c) * (mul (mInterval t).1 (mInterval t).2).c
               := by ring_intZ
             _ = (mInterval t).2.c := ihm
      · -- L-step (true): interval (M_l, M_t); gL = m_t via 3·m_l·(IH) − (bound_res_identity).
        show ((mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).d
              - (mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).c) * (mInterval t).1.c
             - ((mInterval t).1.d - (mInterval t).1.c)
               * (mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).c
           = (mul (mInterval t).1 (mInterval t).2).c
        rw [markoff_res_vieta (mInterval t).1 (mInterval t).2 d1,
            markoff_vieta (mInterval t).1 (mInterval t).2 d1, s1]
        have hb := bound_res_identity (mInterval t).1 (mInterval t).2 s2
        calc _ = (mul (mInterval t).1 (mInterval t).2).c
                 + 3 * (mInterval t).1.c
                   * (((mul (mInterval t).1 (mInterval t).2).d - (mul (mInterval t).1 (mInterval t).2).c)
                        * (mInterval t).1.c
                      - ((mInterval t).1.d - (mInterval t).1.c)
                        * (mul (mInterval t).1 (mInterval t).2).c
                      - (mInterval t).2.c)
                 - ((mInterval t).1.c * ((mInterval t).2.d - (mInterval t).2.c)
                    - (mInterval t).2.c * ((mInterval t).1.d - (mInterval t).1.c)
                    - (3 * (mInterval t).1.c * (mInterval t).2.c
                       - (mul (mInterval t).1 (mInterval t).2).c)) := by ring_intZ
             _ = (mul (mInterval t).1 (mInterval t).2).c := by rw [ihm, hb]; ring_intZ

/-- ★★★★★ **Strict slope monotonicity (left half)**: `u_l·m_t < u_t·m_l` — the node's residue slope
    is strictly greater than the left bound's.  From `markovRes_cross_left`
    (`u_t·m_l − u_l·m_t = m_r`) and `1 ≤ m_r` (`mInterval_pos`).  With `markov_node_slope_lt_right`
    this completes Zhang's Lemma 2 on the tree: the mediant slope lies *strictly between* the two
    bounds' slopes, `u_l/m_l < u_t/m_t < u_r/m_r`. -/
theorem markov_node_slope_gt_left (path : List Bool) :
    ((mInterval path).1.d - (mInterval path).1.c) * (mNode path).c
      < markovRes path * (mInterval path).1.c :=
  lt_of_sub_eq_of_one_le (markovRes_cross_left path) (mInterval_pos path).2.2.2.1

/-! ## §9 — the residue window `0 < u_t < m_t/2` (canonical Markov window on every node)

  The root bounds have slopes `u/m = 0/1` (genL) and `1/2` (genR); strict monotonicity (§7–§8)
  confines every node strictly between, giving `0 < u_t < m_t/2` — the canonical window of
  `root_unique_below_half` realised on the tree.  Proved by induction carrying
  `windowMat M := 0 ≤ u ∧ 2u ≤ m` on **both** interval bounds; the node's *strict* window
  (`node_window_of_bounds`, from the slope inequalities + `0 ≤ u_l` / `2u_r ≤ m_r` + positivity)
  weakens to the bound invariant, so it propagates.  Needs a pure ℤ strict-order toolkit. -/

private theorem nonneg_add : ∀ {x y : Int}, Int.NonNeg x → Int.NonNeg y → Int.NonNeg (x + y)
  | _, _, ⟨p⟩, ⟨q⟩ => by show Int.NonNeg (Int.ofNat p + Int.ofNat q); exact ⟨p + q⟩

private theorem ofNat_succ_pos (n : Nat) : 0 < Int.ofNat (n + 1) := by
  show Int.NonNeg (Int.subNatNat (n + 1) 1)
  rw [E213.Meta.Int213.subNatNat_of_le (Nat.le_add_left 1 n)]
  exact ⟨n⟩

/-- `0 < z·k → 0 < k → 0 < z` (positive-factor cancellation), by case analysis on `z, k`. -/
private theorem pos_of_mul_pos_right : ∀ {z k : Int}, 0 < z * k → 0 < k → 0 < z
  | .ofNat (n + 1), _, _, _ => ofNat_succ_pos n
  | .ofNat 0, k, h, _ => by
      have hz : Int.ofNat 0 * k = 0 := E213.Meta.Int213.zero_mul k
      rw [hz] at h; exact absurd h (by decide)
  | .negSucc _, .ofNat 0, _, hk => absurd hk (by decide)
  | .negSucc _, .ofNat (_ + 1), h, _ => by nomatch h
  | .negSucc _, .negSucc _, _, hk => by nomatch hk

private theorem pos_sub_of_lt {a b : Int} (h : a < b) : 0 < b - a := by
  show Int.NonNeg ((b - a) - 1)
  have e : (b - a) - 1 = b - (a + 1) := by ring_intZ
  rw [e]; exact h

private theorem lt_of_pos_sub {a b : Int} (h : 0 < b - a) : a < b := by
  show Int.NonNeg (b - (a + 1))
  have e : b - (a + 1) = (b - a) - 1 := by ring_intZ
  rw [e]; exact h

private theorem lt_of_lt_of_le {a b c : Int} (h1 : a < b) (h2 : b ≤ c) : a < c := by
  show Int.NonNeg (c - (a + 1))
  have e : c - (a + 1) = (b - (a + 1)) + (c - b) := by ring_intZ
  rw [e]; exact nonneg_add h1 h2

private theorem lt_of_le_of_lt {a b c : Int} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  show Int.NonNeg (c - (a + 1))
  have e : c - (a + 1) = (b - a) + (c - (b + 1)) := by ring_intZ
  rw [e]; exact nonneg_add h1 h2

private theorem le_of_lt {a b : Int} (h : a < b) : a ≤ b := by
  show Int.NonNeg (b - a)
  have e : b - a = (b - (a + 1)) + 1 := by ring_intZ
  rw [e]; exact nonneg_add h ⟨1⟩

private theorem zero_le_of_nonneg {x : Int} (h : Int.NonNeg x) : 0 ≤ x := by
  show Int.NonNeg (x - 0); rw [sub_zero_int]; exact h

private theorem nonneg_of_zero_le {x : Int} (h : 0 ≤ x) : Int.NonNeg x := by
  have h' : Int.NonNeg (x - 0) := h; rw [sub_zero_int] at h'; exact h'

private theorem mul_le_mul_right {a b k : Int} (h : a ≤ b) (hk : 0 ≤ k) : a * k ≤ b * k := by
  show Int.NonNeg (b * k - a * k)
  have e : b * k - a * k = (b - a) * k := by ring_intZ
  rw [e]
  exact nonneg_of_zero_le (E213.Meta.Int213.mul_nonneg (zero_le_of_nonneg h) hk)

private theorem lt_of_mul_lt_mul_right {a b k : Int} (h : a * k < b * k) (hk : 0 < k) : a < b := by
  apply lt_of_pos_sub
  have hp : 0 < b * k - a * k := pos_sub_of_lt h
  have e : b * k - a * k = (b - a) * k := by ring_intZ
  rw [e] at hp
  exact pos_of_mul_pos_right hp hk

private theorem pos_add_pos {x : Int} (h : 0 < x) : 0 < x + x := by
  show Int.NonNeg ((x + x) - 1)
  have e : (x + x) - 1 = (x - 1) + x := by ring_intZ
  rw [e]
  refine nonneg_add h ?_
  show Int.NonNeg x
  have e2 : x = (x - 1) + 1 := by ring_intZ
  rw [e2]; exact nonneg_add h ⟨1⟩

private theorem lt_two_mul {a b : Int} (h : a < b) : 2 * a < 2 * b := by
  apply lt_of_pos_sub
  have e : 2 * b - 2 * a = (b - a) + (b - a) := by ring_intZ
  rw [e]; exact pos_add_pos (pos_sub_of_lt h)

/-- A matrix's residue/number lie in the (closed) Markov slope window `0 ≤ u ≤ m/2`. -/
def windowMat (M : Mat2) : Prop := 0 ≤ M.d - M.c ∧ 2 * (M.d - M.c) ≤ M.c

/-- The node's **strict** window `0 < u_t` and `2·u_t < m_t` from the slope inequalities
    (`markov_node_slope_gt_left/lt_right`) and the bounds' `0 ≤ u_l`, `2·u_r ≤ m_r` + positivity. -/
private theorem node_window_of_bounds (path : List Bool)
    (hL : 0 ≤ (mInterval path).1.d - (mInterval path).1.c)
    (hR : 2 * ((mInterval path).2.d - (mInterval path).2.c) ≤ (mInterval path).2.c) :
    0 < markovRes path ∧ 2 * markovRes path < markovNum path := by
  have hmt : (0 : Int) ≤ (mNode path).c := nonneg_of_one_le (markovNum_pos path)
  refine ⟨?_, ?_⟩
  · -- 0 < u_t: 0 ≤ u_l·m_t < u_t·m_l, cancel m_l > 0
    have h1 : (0 : Int) ≤ ((mInterval path).1.d - (mInterval path).1.c) * (mNode path).c :=
      E213.Meta.Int213.mul_nonneg hL hmt
    have h2 : (0 : Int) < markovRes path * (mInterval path).1.c :=
      lt_of_le_of_lt h1 (markov_node_slope_gt_left path)
    exact pos_of_mul_pos_right h2 (mInterval_pos path).1.2.2.1
  · -- 2·u_t < m_t: 2·(u_t·m_r) < 2·(u_r·m_t) = (2u_r)·m_t ≤ m_r·m_t, cancel m_r > 0
    have step1 : 2 * (markovRes path * (mInterval path).2.c)
               < 2 * (((mInterval path).2.d - (mInterval path).2.c) * (mNode path).c) :=
      lt_two_mul (markov_node_slope_lt_right path)
    have step2 : 2 * (((mInterval path).2.d - (mInterval path).2.c) * (mNode path).c)
               ≤ (mInterval path).2.c * (mNode path).c := by
      have e : 2 * (((mInterval path).2.d - (mInterval path).2.c) * (mNode path).c)
             = (2 * ((mInterval path).2.d - (mInterval path).2.c)) * (mNode path).c := by ring_intZ
      rw [e]; exact mul_le_mul_right hR hmt
    have step3 : 2 * (markovRes path * (mInterval path).2.c)
               < (mInterval path).2.c * (mNode path).c := lt_of_lt_of_le step1 step2
    have e2 : 2 * (markovRes path * (mInterval path).2.c)
            = (2 * markovRes path) * (mInterval path).2.c := by ring_intZ
    have e3 : (mInterval path).2.c * (mNode path).c
            = (mNode path).c * (mInterval path).2.c := by ring_intZ
    rw [e2, e3] at step3
    exact lt_of_mul_lt_mul_right step3 (mInterval_pos path).2.2.2.1

/-- ★★★★★ **Both interval bounds lie in the closed window `0 ≤ u ≤ m/2`** at every node, by
    induction: the generators do, and each new mediant's *strict* window (`node_window_of_bounds`)
    weakens to the closed one, so it propagates. -/
theorem mInterval_window (path : List Bool) :
    windowMat (mInterval path).1 ∧ windowMat (mInterval path).2 := by
  induction path with
  | nil => exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
  | cons b t ih =>
      have nw := node_window_of_bounds t ih.1.1 ih.2.2
      have nodeW : windowMat (mul (mInterval t).1 (mInterval t).2) :=
        ⟨nonneg_of_one_le nw.1, le_of_lt nw.2⟩
      cases b
      · exact ⟨nodeW, ih.2⟩
      · exact ⟨ih.1, nodeW⟩

/-- ★★★★★ **The residue window `0 < u_t < m_t/2`** at every node — the canonical Markov window of
    `MarkovInjectivity.root_unique_below_half`, realised on the tree.  Every node's residue is the
    unique sqrt of `−1` in `(0, m_t/2)`: it squares to `−1` (`markovNum_dvd_res_sq_succ`) AND lies
    strictly in the lower window half.  This completes Zhang's Lemma 2 on the tree. -/
theorem markov_window (path : List Bool) :
    0 < markovRes path ∧ 2 * markovRes path < markovNum path :=
  node_window_of_bounds path (mInterval_window path).1.1 (mInterval_window path).2.2

/-! ## §10 — the Markoff matrix tree ⊆ the Markov tree (forward bridge)

  Every matrix-tree node's `(2,1)`-entry triple `(m_l, m_r, m_t)` (as `Nat`) is `MarkovReachable`
  (`MarkovUniqueness`: root `(1,1,1)` + Vieta jumps + transpositions).  So the Markoff-matrix tree
  realises exactly the Markov tree, and every tree node inherits the reachable-triple theorems
  (pairwise coprimality, no `3 mod 4` factor, the `√(−1)` QR structure).  Proof: induction — each
  L/R mediant step is a Vieta jump (`markoff_vieta(_R)` + entry-shape give `m_t' = 3·m_i·m_j − m_k`),
  matched to the `jump` constructor after reordering by `swap`s.  Bridges ℤ→ℕ via `Int.toNat` (entries
  are positive, `mInterval_pos`). -/

open E213.Lib.Math.Real213.MarkovUniqueness (MarkovReachable)

private theorem toNat_of_nonneg : ∀ {a : Int}, 0 ≤ a → Int.ofNat a.toNat = a
  | .ofNat _, _ => rfl
  | .negSucc _, h => by nomatch h

private theorem toNat_add {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b).toNat = a.toNat + b.toNat := by
  obtain ⟨m, rfl⟩ : ∃ m, a = Int.ofNat m := ⟨a.toNat, (toNat_of_nonneg ha).symm⟩
  obtain ⟨n, rfl⟩ : ∃ n, b = Int.ofNat n := ⟨b.toNat, (toNat_of_nonneg hb).symm⟩
  rfl

private theorem toNat_mul {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * b).toNat = a.toNat * b.toNat := by
  obtain ⟨m, rfl⟩ : ∃ m, a = Int.ofNat m := ⟨a.toNat, (toNat_of_nonneg ha).symm⟩
  obtain ⟨n, rfl⟩ : ∃ n, b = Int.ofNat n := ⟨b.toNat, (toNat_of_nonneg hb).symm⟩
  rfl

/-- The ℤ Vieta jump equation `b + c' = 3·a·mt` (nonneg entries) transfers to the ℕ jump condition. -/
private theorem jump_eq_toNat {a b c' mt : Int}
    (hb : 0 ≤ b) (hc : 0 ≤ c') (ha : 0 ≤ a) (hmt : 0 ≤ mt) (he : b + c' = 3 * a * mt) :
    b.toNat + c'.toNat = 3 * a.toNat * mt.toNat := by
  have h3a : (0 : Int) ≤ 3 * a := E213.Meta.Int213.mul_nonneg (by decide) ha
  rw [← toNat_add hb hc, he, toNat_mul h3a hmt, toNat_mul (by decide) ha]
  rfl

/-- ★★★★★ **The Markoff matrix tree realises the Markov tree.**  Every node's `(2,1)`-entry triple
    `(m_l, m_r, m_t)` is `MarkovReachable` — the matrix tree is exactly Markov's tree of triples. -/
theorem mInterval_reachable (path : List Bool) :
    MarkovReachable (mInterval path).1.c.toNat (mInterval path).2.c.toNat (mNode path).c.toNat := by
  induction path with
  | nil =>
      show MarkovReachable 1 2 5
      exact MarkovReachable.jump
        (MarkovReachable.swap23
          (MarkovReachable.jump MarkovReachable.root (by decide : (1 : Nat) + 2 = 3 * 1 * 1)))
        (by decide : (1 : Nat) + 5 = 3 * 1 * 2)
  | cons b t ih =>
      have d1 := (mInterval_det t).1
      have d2 := (mInterval_det t).2
      have s1 := (mInterval_shape t).1
      have s2 := (mInterval_shape t).2.1
      have hA : (0 : Int) ≤ (mInterval t).1.c := nonneg_of_one_le (mInterval_pos t).1.2.2.1
      have hB : (0 : Int) ≤ (mInterval t).2.c := nonneg_of_one_le (mInterval_pos t).2.2.2.1
      have hC : (0 : Int) ≤ (mNode t).c := nonneg_of_one_le (markovNum_pos t)
      cases b
      · -- R-step (false): node = mul M_t M_r; jump m_l → m_t' = 3·m_t·m_r − m_l
        have hRv : (mNode (false :: t)).c
                 = 3 * (mul (mInterval t).1 (mInterval t).2).c * (mInterval t).2.c
                   - (mInterval t).1.c := by
          show (mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).c = _
          rw [markoff_vieta_R (mInterval t).1 (mInterval t).2 d2, s2]; ring_intZ
        have hC' : (0 : Int) ≤ (mNode (false :: t)).c := nonneg_of_one_le (markovNum_pos (false :: t))
        have heq : (mInterval t).1.c + (mNode (false :: t)).c
                 = 3 * (mul (mInterval t).1 (mInterval t).2).c * (mInterval t).2.c := by
          rw [hRv]; ring_intZ
        have hjump : (mInterval t).1.c.toNat + (mNode (false :: t)).c.toNat
                   = 3 * (mul (mInterval t).1 (mInterval t).2).c.toNat * (mInterval t).2.c.toNat :=
          jump_eq_toNat hA hC' hC hB heq
        show MarkovReachable (mNode t).c.toNat (mInterval t).2.c.toNat (mNode (false :: t)).c.toNat
        exact (((ih.swap23).swap12).swap23).jump hjump
      · -- L-step (true): node = mul M_l M_t; jump m_r → m_t' = 3·m_l·m_t − m_r
        have hLv : (mNode (true :: t)).c
                 = 3 * (mInterval t).1.c * (mul (mInterval t).1 (mInterval t).2).c
                   - (mInterval t).2.c := by
          show (mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).c = _
          rw [markoff_vieta (mInterval t).1 (mInterval t).2 d1, s1]
        have hC' : (0 : Int) ≤ (mNode (true :: t)).c := nonneg_of_one_le (markovNum_pos (true :: t))
        have heq : (mInterval t).2.c + (mNode (true :: t)).c
                 = 3 * (mInterval t).1.c * (mul (mInterval t).1 (mInterval t).2).c := by
          rw [hLv]; ring_intZ
        have hjump : (mInterval t).2.c.toNat + (mNode (true :: t)).c.toNat
                   = 3 * (mInterval t).1.c.toNat * (mul (mInterval t).1 (mInterval t).2).c.toNat :=
          jump_eq_toNat hB hC' hA hC heq
        show MarkovReachable (mInterval t).1.c.toNat (mNode t).c.toNat (mNode (true :: t)).c.toNat
        exact (ih.swap23).jump hjump

/-- ★★★★ **Every matrix-tree node triple is pairwise coprime** — inherited from
    `MarkovUniqueness.markov_reachable_coprime` via the forward bridge `mInterval_reachable`.  A
    demonstration that the matrix-tree nodes pick up the full reachable-triple theory. -/
theorem mNode_triple_coprime (path : List Bool) :
    E213.Lib.Math.Real213.MarkovUniqueness.MarkovPairwiseCoprime
      (mInterval path).1.c.toNat (mInterval path).2.c.toNat (mNode path).c.toNat :=
  E213.Lib.Math.Real213.MarkovUniqueness.markov_reachable_coprime (mInterval_reachable path)

/-! ## §11 — global slope injectivity (the genuine crux for `SamePairInjective`)

  The window (§9) only fixes each node's residue *within its own* `m_t`; closing `SamePairInjective`
  additionally needs that the map node ↦ slope `u_t/m_t` is **injective** across the whole tree (so
  two triples at the same `c` with the same windowed residue are the same node).  This follows the
  Stern-Brocot order: every node lies strictly between its interval bounds (§7–§8), the bounds nest
  as the tree deepens, so each subtree's slopes are confined strictly between the subtree-root's
  bounds — hence distinct paths give distinct slopes.  Slopes are compared by cross-multiplication
  (`slopeLt M N := u_M·m_N < u_N·m_M`, valid since `m > 0`). -/

private theorem mul_pos {a b : Int} (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  apply lt_of_pos_sub
  have e : a * b - 0 = a * b := by rw [sub_zero_int]
  rw [e]
  -- 0 < a*b : a ≥ 1, b ≥ 1 ⟹ a*b ≥ 1 ⟹ 0 < a*b
  exact one_le_mul ha hb

private theorem mul_lt_mul_right {a b k : Int} (h : a < b) (hk : 0 < k) : a * k < b * k := by
  apply lt_of_pos_sub
  have e : b * k - a * k = (b - a) * k := by ring_intZ
  rw [e]
  exact mul_pos (pos_sub_of_lt h) hk

private theorem lt_trans {a b c : Int} (h1 : a < b) (h2 : b < c) : a < c :=
  lt_of_lt_of_le h1 (le_of_lt h2)

/-- `slope M < slope N`, by cross-multiplication (`m > 0`): `(M.d−M.c)·N.c < (N.d−N.c)·M.c`. -/
def slopeLt (M N : Mat2) : Prop := (M.d - M.c) * N.c < (N.d - N.c) * M.c

/-- Fraction transitivity for slopes (all `m > 0`). -/
private theorem slope_trans {M N P : Mat2} (hM : 0 < M.c) (hN : 0 < N.c) (hP : 0 < P.c)
    (h1 : slopeLt M N) (h2 : slopeLt N P) : slopeLt M P := by
  have k1 : (M.d - M.c) * N.c * P.c < (N.d - N.c) * M.c * P.c := mul_lt_mul_right h1 hP
  have k2 : (N.d - N.c) * P.c * M.c < (P.d - P.c) * N.c * M.c := mul_lt_mul_right h2 hM
  have e : (N.d - N.c) * M.c * P.c = (N.d - N.c) * P.c * M.c := by ring_intZ
  rw [e] at k1
  have k3 : (M.d - M.c) * N.c * P.c < (P.d - P.c) * N.c * M.c := lt_trans k1 k2
  have e2 : (M.d - M.c) * N.c * P.c = (M.d - M.c) * P.c * N.c := by ring_intZ
  have e3 : (P.d - P.c) * N.c * M.c = (P.d - P.c) * M.c * N.c := by ring_intZ
  rw [e2, e3] at k3
  exact lt_of_mul_lt_mul_right k3 hN

/-- `slope M ≤ slope N`. -/
def slopeLe (M N : Mat2) : Prop := (M.d - M.c) * N.c ≤ (N.d - N.c) * M.c

private theorem le_refl_int (a : Int) : a ≤ a := by
  show Int.NonNeg (a - a)
  have e : a - a = 0 := by show a + -a = 0; exact E213.Meta.Int213.add_neg_cancel a
  rw [e]; exact ⟨0⟩

private theorem slopeLe_refl (M : Mat2) : slopeLe M M := le_refl_int _

private theorem slopeLt_imp_le {M N : Mat2} (h : slopeLt M N) : slopeLe M N := le_of_lt h

/-- Mixed transitivity `slope M ≤ slope N < slope P ⟹ slope M < slope P`. -/
private theorem slope_le_lt_trans {M N P : Mat2} (hM : 0 < M.c) (hN : 0 < N.c) (hP : 0 < P.c)
    (h1 : slopeLe M N) (h2 : slopeLt N P) : slopeLt M P := by
  have k1 : (M.d - M.c) * N.c * P.c ≤ (N.d - N.c) * M.c * P.c := mul_le_mul_right h1 (le_of_lt hP)
  have k2 : (N.d - N.c) * P.c * M.c < (P.d - P.c) * N.c * M.c := mul_lt_mul_right h2 hM
  have e : (N.d - N.c) * M.c * P.c = (N.d - N.c) * P.c * M.c := by ring_intZ
  rw [e] at k1
  have k3 : (M.d - M.c) * N.c * P.c < (P.d - P.c) * N.c * M.c := lt_of_le_of_lt k1 k2
  have e2 : (M.d - M.c) * N.c * P.c = (M.d - M.c) * P.c * N.c := by ring_intZ
  have e3 : (P.d - P.c) * N.c * M.c = (P.d - P.c) * M.c * N.c := by ring_intZ
  rw [e2, e3] at k3
  exact lt_of_mul_lt_mul_right k3 hN

/-- Mixed transitivity `slope M < slope N ≤ slope P ⟹ slope M < slope P`. -/
private theorem slope_lt_le_trans {M N P : Mat2} (hM : 0 < M.c) (hN : 0 < N.c) (hP : 0 < P.c)
    (h1 : slopeLt M N) (h2 : slopeLe N P) : slopeLt M P := by
  have k1 : (M.d - M.c) * N.c * P.c < (N.d - N.c) * M.c * P.c := mul_lt_mul_right h1 hP
  have k2 : (N.d - N.c) * P.c * M.c ≤ (P.d - P.c) * N.c * M.c := mul_le_mul_right h2 (le_of_lt hM)
  have e : (N.d - N.c) * M.c * P.c = (N.d - N.c) * P.c * M.c := by ring_intZ
  rw [e] at k1
  have k3 : (M.d - M.c) * N.c * P.c < (P.d - P.c) * N.c * M.c := lt_of_lt_of_le k1 k2
  have e2 : (M.d - M.c) * N.c * P.c = (M.d - M.c) * P.c * N.c := by ring_intZ
  have e3 : (P.d - P.c) * N.c * M.c = (P.d - P.c) * M.c * N.c := by ring_intZ
  rw [e2, e3] at k3
  exact lt_of_mul_lt_mul_right k3 hN

/-- Positivity of any node/bound `.c` entry (`= 0 < `, defeq to `1 ≤`). -/
private theorem c_pos_l (p : List Bool) : 0 < (mInterval p).1.c := (mInterval_pos p).1.2.2.1
private theorem c_pos_r (p : List Bool) : 0 < (mInterval p).2.c := (mInterval_pos p).2.2.2.1
private theorem c_pos_node (p : List Bool) : 0 < (mNode p).c := markovNum_pos p

/-- ★★★★★ **Interval nesting**: as the tree deepens (path `s ++ t`), the interval bounds nest in
    slope — the left bound only rises, the right bound only falls.  By induction on `s` using
    node-between-bounds (§7–§8). -/
theorem slope_nest (s t : List Bool) :
    slopeLe (mInterval t).1 (mInterval (s ++ t)).1
    ∧ slopeLe (mInterval (s ++ t)).2 (mInterval t).2 := by
  induction s with
  | nil => exact ⟨slopeLe_refl _, slopeLe_refl _⟩
  | cons b s' ih =>
      cases b
      · -- false / R-step: interval (mNode(s'++t), (mInterval(s'++t)).2)
        refine ⟨?_, ?_⟩
        · show slopeLe (mInterval t).1 (mNode (s' ++ t))
          exact slopeLt_imp_le
            (slope_le_lt_trans (c_pos_l t) (c_pos_l (s' ++ t)) (c_pos_node (s' ++ t))
              ih.1 (markov_node_slope_gt_left (s' ++ t)))
        · show slopeLe (mInterval (s' ++ t)).2 (mInterval t).2
          exact ih.2
      · -- true / L-step: interval ((mInterval(s'++t)).1, mNode(s'++t))
        refine ⟨?_, ?_⟩
        · show slopeLe (mInterval t).1 (mInterval (s' ++ t)).1
          exact ih.1
        · show slopeLe (mNode (s' ++ t)) (mInterval t).2
          exact slopeLt_imp_le
            (slope_lt_le_trans (c_pos_node (s' ++ t)) (c_pos_r (s' ++ t)) (c_pos_r t)
              (markov_node_slope_lt_right (s' ++ t)) ih.2)

/-- ★★★★★ **Subtree bounding**: every node in the subtree rooted at `t` (path `s ++ t`) has slope
    **strictly** between `t`'s interval bounds.  Nesting + node-between-bounds + slope transitivity. -/
theorem subtree_between (s t : List Bool) :
    slopeLt (mInterval t).1 (mNode (s ++ t)) ∧ slopeLt (mNode (s ++ t)) (mInterval t).2 := by
  refine ⟨?_, ?_⟩
  · exact slope_le_lt_trans (c_pos_l t) (c_pos_l (s ++ t)) (c_pos_node (s ++ t))
      (slope_nest s t).1 (markov_node_slope_gt_left (s ++ t))
  · exact slope_lt_le_trans (c_pos_node (s ++ t)) (c_pos_r (s ++ t)) (c_pos_r t)
      (markov_node_slope_lt_right (s ++ t)) (slope_nest s t).2

/-- Directional: every node in `t`'s **true**-subtree (path `s ++ true :: t`) has slope `<` node `t`
    (right bound of `true::t` is `mNode t`). -/
private theorem subtree_true_lt (s t : List Bool) :
    slopeLt (mNode (s ++ true :: t)) (mNode t) := (subtree_between s (true :: t)).2

/-- Directional: every node in `t`'s **false**-subtree has slope `>` node `t`. -/
private theorem subtree_false_gt (s t : List Bool) :
    slopeLt (mNode t) (mNode (s ++ false :: t)) := (subtree_between s (false :: t)).1

/-! ### Path injectivity of the slope map (Stern-Brocot ordering). -/

private theorem eq_nil_or_concat : ∀ (l : List Bool), l = [] ∨ ∃ L b, l = L ++ [b]
  | [] => Or.inl rfl
  | x :: xs => by
      rcases eq_nil_or_concat xs with h | ⟨L, b, h⟩
      · exact Or.inr ⟨[], x, by rw [h]; rfl⟩
      · exact Or.inr ⟨x :: L, b, by rw [h]; rfl⟩

private theorem concat_ne_nil : ∀ (xs : List Bool) (b : Bool), xs ++ [b] ≠ []
  | [], _ => by intro h; exact List.noConfusion h
  | _ :: _, _ => by intro h; exact List.noConfusion h

private theorem append_singleton_cancel : ∀ (as cs : List Bool) (b : Bool),
    as ++ [b] = cs ++ [b] → as = cs
  | [], [], _, _ => rfl
  | [], c :: cs, b, h => absurd (List.cons.inj h).2.symm (concat_ne_nil cs b)
  | a :: as, [], b, h => absurd (List.cons.inj h).2 (concat_ne_nil as b)
  | a :: as, c :: cs, b, h => by
      have hi := List.cons.inj h
      rw [hi.1, append_singleton_cancel as cs b hi.2]

private theorem concat_append (L : List Bool) (b : Bool) (base : List Bool) :
    (L ++ [b]) ++ base = L ++ b :: base := by
  rw [E213.Tactic.List213.append_assoc]; rfl

/-- Slope-comparison disjunction for two paths, with a shared deep suffix `base`. -/
private def DISJ (p q base : List Bool) : Prop :=
  slopeLt (mNode (p ++ base)) (mNode (q ++ base)) ∨ slopeLt (mNode (q ++ base)) (mNode (p ++ base))

/-- The empty path vs a nonempty one: the nonempty path is in a true- or false-subtree of `base`,
    so its slope is separated from `mNode base = mNode ([] ++ base)`. -/
private theorem nil_sep (q base : List Bool) (hq : q ≠ []) : DISJ [] q base := by
  rcases eq_nil_or_concat q with h | ⟨L, b, h⟩
  · exact absurd h hq
  · subst h
    unfold DISJ
    rw [concat_append L b base]
    cases b
    · exact Or.inl (subtree_false_gt L base)
    · exact Or.inr (subtree_true_lt L base)

private theorem length_concat (L : List Bool) (b : Bool) : (L ++ [b]).length = L.length + 1 := by
  rw [E213.Tactic.List213.length_append]; rfl

/-- ★★★★★ **Slope separation**: distinct paths (sharing deep suffix `base`) have separated slopes.
    Length-fuel induction peeling the shallow (root-adjacent) ends via `eq_nil_or_concat`.  The
    divergence point sits at a common node, with the two paths in its true/false subtrees. -/
private theorem slope_sep : ∀ (m : Nat) (base p q : List Bool), p.length ≤ m → p ≠ q → DISJ p q base
  | 0, base, p, q, hm, hpq => by
      rcases eq_nil_or_concat p with hp | ⟨Lp, bp, hp⟩
      · subst hp; exact nil_sep q base (fun hq => hpq hq.symm)
      · exact absurd (hp ▸ hm) (by rw [length_concat]; exact Nat.not_succ_le_zero _)
  | m + 1, base, p, q, hm, hpq => by
      rcases eq_nil_or_concat p with hp | ⟨Lp, bp, hp⟩
      · subst hp; exact nil_sep q base (fun hq => hpq hq.symm)
      · rcases eq_nil_or_concat q with hq | ⟨Lq, bq, hq⟩
        · subst hq; exact Or.symm (nil_sep p base hpq)
        · subst hp; subst hq
          have hlen : Lp.length ≤ m := by
            have hm' := hm; rw [length_concat] at hm'; exact Nat.le_of_succ_le_succ hm'
          show DISJ (Lp ++ [bp]) (Lq ++ [bq]) base
          unfold DISJ
          rw [concat_append Lp bp base, concat_append Lq bq base]
          cases bp <;> cases bq
          · -- false, false : same branch, recurse
            have hne : Lp ≠ Lq := fun he => hpq (by rw [he])
            exact slope_sep m (false :: base) Lp Lq hlen hne
          · -- false, true : p in false-subtree (>), q in true-subtree (<) of base
            exact Or.inr (slope_trans (c_pos_node (Lq ++ true :: base)) (c_pos_node base)
              (c_pos_node (Lp ++ false :: base))
              (subtree_true_lt Lq base) (subtree_false_gt Lp base))
          · -- true, false : p in true-subtree (<), q in false-subtree (>) of base
            exact Or.inl (slope_trans (c_pos_node (Lp ++ true :: base)) (c_pos_node base)
              (c_pos_node (Lq ++ false :: base))
              (subtree_true_lt Lp base) (subtree_false_gt Lq base))
          · -- true, true : same branch, recurse
            have hne : Lp ≠ Lq := fun he => hpq (by rw [he])
            exact slope_sep m (true :: base) Lp Lq hlen hne

/-- Slope equality (cross-multiplied). -/
def slopeEq (M N : Mat2) : Prop := (M.d - M.c) * N.c = (N.d - N.c) * M.c

private theorem lt_irrefl_int {a : Int} (h : a < a) : False := by
  have h0 : 0 < a - a := pos_sub_of_lt h
  have e : a - a = 0 := by show a + -a = 0; exact E213.Meta.Int213.add_neg_cancel a
  rw [e] at h0; exact absurd h0 (by decide)

private theorem slopeLt_ne {M N : Mat2} (hlt : slopeLt M N) (heq : slopeEq M N) : False := by
  unfold slopeLt at hlt; unfold slopeEq at heq; rw [heq] at hlt; exact lt_irrefl_int hlt

/-- ★★★★★ **Path injectivity of the slope map** (Stern-Brocot ordering): distinct tree paths have
    distinct node slopes.  Hence node `↦ u_t/m_t` is injective — the global injectivity that
    `SamePairInjective` needs (two triples at the same `c` with the same windowed residue have the
    same slope, hence are the same node). -/
theorem slope_path_inj (p q : List Bool) (heq : slopeEq (mNode p) (mNode q)) : p = q := by
  rcases (inferInstance : Decidable (p = q)) with hpq | he
  · exfalso
    have hd : DISJ p q [] := slope_sep p.length [] p q (Nat.le_refl _) hpq
    unfold DISJ at hd
    rw [E213.Tactic.List213.append_nil, E213.Tactic.List213.append_nil] at hd
    rcases hd with h | h
    · exact slopeLt_ne h heq
    · exact slopeLt_ne h heq.symm
  · exact he

/-! ## §12 — the reverse bridge: every ordered Markov triple (`c ≥ 5`) is a matrix-tree node

  `IsNode a b c` := some tree node has `(m_l, m_r, m_t) = (a, b, c)` (as `Nat`).  Each tree node has
  two children (Vieta up-moves); stated as `∃ d, IsNode … ∧ jump-eq` to avoid `Nat` subtraction.
  These drive the descent inversion (Piece B). -/

/-- A `Nat` triple `(a,b,c)` is realised by a matrix-tree node (`m_l = a`, `m_r = b`, `m_t = c`). -/
def IsNode (a b c : Nat) : Prop :=
  ∃ path : List Bool, (mInterval path).1.c.toNat = a ∧ (mInterval path).2.c.toNat = b
    ∧ (mNode path).c.toNat = c

/-- The **true**-child Vieta up-move: from node `(a,b,c)`, the true-child is `(a, c, d)` with
    `b + d = 3·a·c` (`d = 3ac − b`). -/
theorem node_true_child {a b c : Nat} (h : IsNode a b c) :
    ∃ d, IsNode a c d ∧ b + d = 3 * a * c := by
  obtain ⟨t, ha, hb, hc⟩ := h
  have d1 := (mInterval_det t).1
  have s1 := (mInterval_shape t).1
  have hLv : (mNode (true :: t)).c
           = 3 * (mInterval t).1.c * (mul (mInterval t).1 (mInterval t).2).c - (mInterval t).2.c := by
    show (mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).c = _
    rw [markoff_vieta (mInterval t).1 (mInterval t).2 d1, s1]
  have heq : (mInterval t).2.c + (mNode (true :: t)).c
           = 3 * (mInterval t).1.c * (mul (mInterval t).1 (mInterval t).2).c := by rw [hLv]; ring_intZ
  have hj : (mInterval t).2.c.toNat + (mNode (true :: t)).c.toNat
          = 3 * (mInterval t).1.c.toNat * (mul (mInterval t).1 (mInterval t).2).c.toNat :=
    jump_eq_toNat (nonneg_of_one_le (mInterval_pos t).2.2.2.1)
      (nonneg_of_one_le (markovNum_pos (true :: t))) (nonneg_of_one_le (mInterval_pos t).1.2.2.1)
      (nonneg_of_one_le (markovNum_pos t)) heq
  refine ⟨(mNode (true :: t)).c.toNat, ⟨true :: t, ha, hc, rfl⟩, ?_⟩
  have hc' : (mul (mInterval t).1 (mInterval t).2).c.toNat = c := hc
  rw [hb, ha, hc'] at hj
  exact hj

/-- The **false**-child Vieta up-move: from node `(a,b,c)`, the false-child is `(c, b, d)` with
    `a + d = 3·b·c` (`d = 3bc − a`). -/
theorem node_false_child {a b c : Nat} (h : IsNode a b c) :
    ∃ d, IsNode c b d ∧ a + d = 3 * b * c := by
  obtain ⟨t, ha, hb, hc⟩ := h
  have d2 := (mInterval_det t).2
  have s2 := (mInterval_shape t).2.1
  have hRv : (mNode (false :: t)).c
           = 3 * (mul (mInterval t).1 (mInterval t).2).c * (mInterval t).2.c - (mInterval t).1.c := by
    show (mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).c = _
    rw [markoff_vieta_R (mInterval t).1 (mInterval t).2 d2, s2]; ring_intZ
  have heq : (mInterval t).1.c + (mNode (false :: t)).c
           = 3 * (mul (mInterval t).1 (mInterval t).2).c * (mInterval t).2.c := by rw [hRv]; ring_intZ
  have hj : (mInterval t).1.c.toNat + (mNode (false :: t)).c.toNat
          = 3 * (mul (mInterval t).1 (mInterval t).2).c.toNat * (mInterval t).2.c.toNat :=
    jump_eq_toNat (nonneg_of_one_le (mInterval_pos t).1.2.2.1)
      (nonneg_of_one_le (markovNum_pos (false :: t))) (nonneg_of_one_le (markovNum_pos t))
      (nonneg_of_one_le (mInterval_pos t).2.2.2.1) heq
  refine ⟨(mNode (false :: t)).c.toNat, ⟨false :: t, hc, hb, rfl⟩, ?_⟩
  have hc' : (mul (mInterval t).1 (mInterval t).2).c.toNat = c := hc
  rw [ha, hb, hc'] at hj
  exact hj.trans (by ring_nat)

/-- Base node: the root `[]` realises `(1, 2, 5)`. -/
theorem isNode_root : IsNode 1 2 5 := ⟨[], by decide, by decide, by decide⟩

/-- **The descent step** (structural core of the reverse bridge): if the Vieta parent `{a, c'}`-pair
    (max `b`) is a node in either bound-order, and `c' + c = 3·a·b` (the up-jump), then `(a,b,c)` is a
    node (up to swapping `a,b`).  `a`-bound-order ↦ true-child, `c'`-bound-order ↦ false-child;
    `c = d` by `Nat` cancellation. -/
theorem descent_step {a b c c' : Nat} (hcc : c' + c = 3 * a * b)
    (hp : IsNode a c' b ∨ IsNode c' a b) : IsNode a b c ∨ IsNode b a c := by
  rcases hp with hp | hp
  · obtain ⟨d, hd, hjd⟩ := node_true_child hp
    have hcd : c = d := E213.Tactic.NatHelper.add_left_cancel_pure (hcc.trans hjd.symm)
    exact Or.inl (by rw [hcd]; exact hd)
  · obtain ⟨d, hd, hjd⟩ := node_false_child hp
    have hcd : c = d := E213.Tactic.NatHelper.add_left_cancel_pure (hcc.trans hjd.symm)
    exact Or.inr (by rw [hcd]; exact hd)

open E213.Lib.Math.Real213.MarkovTree (markovEq markov_symm)
open E213.Lib.Math.Real213.MarkovUniqueness
  (markov_le_3mul markov_mid_lt_max markov_partner_is_triple markov_vieta_partner_le
   markovEq_perm_cab markov_max_unique_5 markov_neighbor_eq)

set_option maxRecDepth 4000 in
/-- Bounded check: any `(a,b,c)` with `a,b ≤ 4`, `c ≤ 48` and the Markov equation has `c ≤ 5`. -/
private theorem markov_small_mid :
    ∀ a, a ≤ 4 → ∀ b, b ≤ 4 → ∀ c, c ≤ 48 →
      a * a + b * b + c * c = 3 * a * b * c → c ≤ 5 := by decide

/-- The middle entry of an ordered Markov triple with `c ≥ 6` is `≥ 5` (so the descent stays
    `≥ 5`).  Contrapositive `b ≤ 4 → c ≤ 5` via `markov_small_mid` (with `c ≤ 3ab ≤ 48`). -/
private theorem markov_mid_ge_5 {a b c : Nat} (h : markovEq a b c) (ha : 1 ≤ a) (hab : a ≤ b)
    (hc6 : 6 ≤ c) : 5 ≤ b := by
  rcases Nat.lt_or_ge b 5 with hb | hb
  · exfalso
    have hb4 : b ≤ 4 := Nat.le_of_lt_succ hb
    have ha4 : a ≤ 4 := Nat.le_trans hab hb4
    have hcpos : 0 < c := Nat.lt_of_lt_of_le (by decide) hc6
    have hc3 : c ≤ 3 * a * b := markov_le_3mul a b c hcpos h
    have hc48 : c ≤ 48 := Nat.le_trans hc3
      (Nat.le_trans (Nat.mul_le_mul (Nat.mul_le_mul_left 3 ha4) hb4) (by decide))
    exact absurd (Nat.le_trans hc6 (markov_small_mid a ha4 b hb4 c hc48 h)) (by decide)
  · exact hb

/-- The reverse bridge by Vieta descent (fuel = `c`): every ordered Markov triple with `5 ≤ c` is a
    matrix-tree node (up to swapping the two smaller entries).  Base `c = 5` ↦ root `(1,2,5)`; for
    `c ≥ 6` descend to the parent `{a, b, 3ab−c}` (max `b ≥ 5`, `markov_mid_ge_5`), recurse, and
    re-ascend by `descent_step`. -/
theorem reverse_of_fuel : ∀ (fuel a b c : Nat), c ≤ fuel → markovEq a b c → 1 ≤ a → a ≤ b →
    b ≤ c → 5 ≤ c → IsNode a b c ∨ IsNode b a c
  | 0, _, _, c, hf, _, _, _, _, h5 => absurd (Nat.le_trans h5 hf) (by decide)
  | fuel + 1, a, b, c, hf, hm, ha, hab, hbc, h5 => by
      rcases Nat.lt_or_ge c 6 with hclt | hcge
      · have hc5 : c = 5 := Nat.le_antisymm (Nat.le_of_lt_succ hclt) h5
        subst hc5
        obtain ⟨ha1, hb2⟩ := markov_max_unique_5 a (Nat.le_trans hab hbc) b hbc hab hm
        subst ha1; subst hb2
        exact Or.inl isNode_root
      · have hcpos : 0 < c := Nat.lt_of_lt_of_le (by decide) hcge
        have hc2 : 2 ≤ c := Nat.le_trans (by decide) hcge
        have hbc_strict : b < c := markov_mid_lt_max a b c hm ha hab hbc hc2
        have hc3 : c ≤ 3 * a * b := markov_le_3mul a b c hcpos hm
        have hcc : (3 * a * b - c) + c = 3 * a * b := E213.Tactic.NatHelper.sub_add_cancel hc3
        have hb5 : 5 ≤ b := markov_mid_ge_5 hm ha hab hcge
        have hc'b : 3 * a * b - c ≤ b := markov_vieta_partner_le a b c hm ha hab hbc_strict
        have hcp : markovEq a b (3 * a * b - c) := markov_partner_is_triple a b c hc3 hm
        have hbf : b ≤ fuel := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hbc_strict hf)
        have hc'pos : 1 ≤ 3 * a * b - c := by
          rcases Nat.eq_zero_or_pos (3 * a * b - c) with h0 | hp
          · exfalso
            have hpr := markov_neighbor_eq a b c hcpos hm
            rw [h0, Nat.mul_zero] at hpr
            have h1 : 1 ≤ a * a + b * b := Nat.le_trans (Nat.mul_pos ha ha) (Nat.le_add_right _ _)
            rw [hpr] at h1; exact absurd h1 (by decide)
          · exact hp
        rcases Nat.lt_or_ge a (3 * a * b - c) with hlt | hge
        · have m2 : markovEq a (3 * a * b - c) b := markov_symm a b (3 * a * b - c) hcp
          exact descent_step hcc
            (reverse_of_fuel fuel a (3 * a * b - c) b hbf m2 ha (Nat.le_of_lt hlt) hc'b hb5)
        · have m1 : markovEq (3 * a * b - c) a b := markovEq_perm_cab hcp
          exact descent_step hcc
            (Or.symm (reverse_of_fuel fuel (3 * a * b - c) a b hbf m1 hc'pos hge hab hb5))

/-- ★★★★★ **The reverse bridge.**  Every ordered Markov triple `(a,b,c)` with `1 ≤ a ≤ b ≤ c` and
    `5 ≤ c` is realised by a matrix-tree node (with the two smaller entries in either order).  The
    converse of `mInterval_reachable`; with `slope_path_inj` (§11) this closes the path from abstract
    triples to the window/injectivity machinery. -/
theorem reverse_bridge (a b c : Nat) (h : markovEq a b c) (ha : 1 ≤ a) (hab : a ≤ b)
    (hbc : b ≤ c) (h5 : 5 ≤ c) : IsNode a b c ∨ IsNode b a c :=
  reverse_of_fuel c a b c (Nat.le_refl c) h ha hab hbc h5

/-! ## §13 — assembly: tree-based Markov uniqueness for `c ≥ 5` with `SqrtNegOneTwoRoots`

  Two ordered triples at `c` ⟹ (reverse bridge) two nodes; each node's residue is a windowed
  `√(−1)` mod `c` (`markov_window` + `markovNum_dvd_res_sq_succ`, converted ℤ→ℕ); `root_unique`
  collapses them to one value ⟹ same slope ⟹ (`slope_path_inj`) same node ⟹ same triple. -/

open E213.Lib.Math.Real213.MarkovUniqueness (MarkovMaxUnique SqrtNegOneTwoRoots)
open E213.Lib.Math.Real213.MarkovInjectivity (root_unique_below_half)

/-- For nonneg `x < y` (ℤ), `x.toNat < y.toNat`.  Via `y = (x+1) + (y−(x+1))` and `toNat_add`. -/
private theorem int_toNat_lt {x y : Int} (hx : 0 ≤ x) (h : x < y) : x.toNat < y.toNat := by
  have h1 : (0 : Int) ≤ x + 1 := E213.Meta.Int213.add_nonneg hx (by decide)
  have h2 : (0 : Int) ≤ y - (x + 1) := nonneg_sub_of_le h
  have key : y = (x + 1) + (y - (x + 1)) := by ring_intZ
  rw [key, toNat_add h1 h2, toNat_add hx (by decide : (0 : Int) ≤ 1)]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)

private theorem nat_dvd_of_ofNat_dvd {a b : Nat} (ha : 1 ≤ a)
    (h : (Int.ofNat a) ∣ (Int.ofNat b)) : a ∣ b := by
  obtain ⟨k, hk⟩ := h
  rcases k with k' | j
  · exact ⟨k', by have h2 : Int.ofNat b = Int.ofNat (a * k') := hk; exact Int.ofNat.inj h2⟩
  · exfalso
    have hk2 : Int.ofNat b = Int.negOfNat (a * (j + 1)) := hk
    obtain ⟨m, hm⟩ : ∃ m, a * (j + 1) = Nat.succ m :=
      ⟨a * (j + 1) - 1, (Nat.succ_pred_eq_of_pos (Nat.mul_pos ha (Nat.succ_pos j))).symm⟩
    rw [hm] at hk2; exact Int.noConfusion hk2

/-- Each tree node's residue, as `Nat`, is a **windowed √(−1)** mod its Markov number:
    `2·r < m`, `r < m`, and `(r² + 1) % m = 0` (with `r = u_t.toNat`, `m = m_t.toNat`). -/
private theorem node_window_nat (p : List Bool) :
    (markovRes p).toNat < (mNode p).c.toNat
    ∧ 2 * (markovRes p).toNat < (mNode p).c.toNat
    ∧ ((markovRes p).toNat * (markovRes p).toNat + 1) % (mNode p).c.toNat = 0 := by
  have hw := markov_window p
  have hrnn : (0 : Int) ≤ markovRes p := nonneg_of_one_le hw.1
  have hmnn : (0 : Int) ≤ (mNode p).c := nonneg_of_one_le (markovNum_pos p)
  have hm1 : 0 < (mNode p).c.toNat :=
    int_toNat_lt (x := 0) (y := (mNode p).c) (by decide) (markovNum_pos p)
  have hhi : 2 * (markovRes p).toNat < (mNode p).c.toNat := by
    have h2r : (0 : Int) ≤ 2 * markovRes p := E213.Meta.Int213.mul_nonneg (by decide) hrnn
    have hlt := int_toNat_lt h2r hw.2
    rwa [toNat_mul (by decide) hrnn] at hlt
  have hlo : (markovRes p).toNat < (mNode p).c.toNat :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by decide)) hhi
  refine ⟨hlo, hhi, ?_⟩
  -- (r²+1) % m = 0 from m ∣ r²+1
  have hdvd : (mNode p).c ∣ markovRes p * markovRes p + 1 := markovNum_dvd_res_sq_succ p
  have e1 : Int.ofNat (markovRes p).toNat = markovRes p := toNat_of_nonneg hrnn
  have heq : Int.ofNat ((markovRes p).toNat * (markovRes p).toNat + 1)
           = markovRes p * markovRes p + 1 := by
    show Int.ofNat (markovRes p).toNat * Int.ofNat (markovRes p).toNat + 1 = _
    rw [e1]
  have hmof : (mNode p).c = Int.ofNat (mNode p).c.toNat := (toNat_of_nonneg hmnn).symm
  rw [← heq, hmof] at hdvd
  obtain ⟨q, hq⟩ := nat_dvd_of_ofNat_dvd hm1 hdvd
  rw [hq]; exact E213.Tactic.NatHelper.mul_mod_right _ _

/-- Extract a node path from the reverse bridge, with `m_t.toNat = c` and the two smaller entries
    matching `(a,b)` in one of the two bound-orders. -/
private theorem node_data {a b c : Nat} (h : IsNode a b c ∨ IsNode b a c) :
    ∃ p, (mNode p).c.toNat = c ∧
      ((a = (mInterval p).1.c.toNat ∧ b = (mInterval p).2.c.toNat)
       ∨ (a = (mInterval p).2.c.toNat ∧ b = (mInterval p).1.c.toNat)) := by
  rcases h with ⟨p, h1, h2, h3⟩ | ⟨p, h1, h2, h3⟩
  · exact ⟨p, h3, Or.inl ⟨h1.symm, h2.symm⟩⟩
  · exact ⟨p, h3, Or.inr ⟨h2.symm, h1.symm⟩⟩

/-- ★★★★★ **Tree-based Markov uniqueness for `c ≥ 5` with the two-roots input.**  `MarkovMaxUnique c`
    whenever `5 ≤ c` and `SqrtNegOneTwoRoots c`: two ordered triples at `c` are both tree nodes
    (`reverse_bridge`); each node's residue is the unique windowed `√(−1)` (`node_window_nat` +
    `root_unique_below_half`), so the residues — hence the slopes (same `c`) — coincide, so the
    nodes coincide (`slope_path_inj`), so the triples coincide. -/
theorem markov_max_unique_tree (c : Nat) (hc5 : 5 ≤ c) (h2 : SqrtNegOneTwoRoots c) :
    MarkovMaxUnique c := by
  intro a₁ b₁ a₂ b₂ hab1 hb1c hab2 hb2c hm1 hm2
  have hc2 : 2 ≤ c := Nat.le_trans (by decide) hc5
  have ha1 : 1 ≤ a₁ := E213.Lib.Math.Real213.MarkovUniqueness.markov_a_pos hc2 hm1
  have ha2 : 1 ≤ a₂ := E213.Lib.Math.Real213.MarkovUniqueness.markov_a_pos hc2 hm2
  obtain ⟨p1, hc1, hpair1⟩ := node_data (reverse_bridge a₁ b₁ c hm1 ha1 hab1 hb1c hc5)
  obtain ⟨p2, hc2', hpair2⟩ := node_data (reverse_bridge a₂ b₂ c hm2 ha2 hab2 hb2c hc5)
  obtain ⟨hlo1, hhi1, hmod1⟩ := node_window_nat p1
  obtain ⟨hlo2, hhi2, hmod2⟩ := node_window_nat p2
  rw [hc1] at hlo1 hhi1 hmod1
  rw [hc2'] at hlo2 hhi2 hmod2
  have hr12 : (markovRes p1).toNat = (markovRes p2).toNat :=
    root_unique_below_half c h2 hlo1 hlo2 hhi1 hhi2 hmod1 hmod2
  have hrnn1 : (0 : Int) ≤ markovRes p1 := nonneg_of_one_le (markov_window p1).1
  have hrnn2 : (0 : Int) ≤ markovRes p2 := nonneg_of_one_le (markov_window p2).1
  have hReq : markovRes p1 = markovRes p2 := by
    rw [← toNat_of_nonneg hrnn1, ← toNat_of_nonneg hrnn2, hr12]
  have hcc : (mNode p1).c = (mNode p2).c := by
    rw [← toNat_of_nonneg (nonneg_of_one_le (mNode_pos p1).2.2.1),
        ← toNat_of_nonneg (nonneg_of_one_le (mNode_pos p2).2.2.1), hc1, hc2']
  have hslope : slopeEq (mNode p1) (mNode p2) := by
    show markovRes p1 * (mNode p2).c = markovRes p2 * (mNode p1).c
    rw [hReq, hcc]
  have hpeq : p1 = p2 := slope_path_inj p1 p2 hslope
  subst hpeq
  rcases hpair1 with ⟨e1a, e1b⟩ | ⟨e1a, e1b⟩ <;> rcases hpair2 with ⟨e2a, e2b⟩ | ⟨e2a, e2b⟩
  · exact ⟨e1a.trans e2a.symm, e1b.trans e2b.symm⟩
  · have hLR : (mInterval p1).1.c.toNat = (mInterval p1).2.c.toNat :=
      Nat.le_antisymm (e1a ▸ e1b ▸ hab1) (e2b ▸ e2a ▸ hab2)
    exact ⟨e1a.trans (hLR.trans e2a.symm), e1b.trans (hLR.symm.trans e2b.symm)⟩
  · have hLR : (mInterval p1).1.c.toNat = (mInterval p1).2.c.toNat :=
      Nat.le_antisymm (e2a ▸ e2b ▸ hab2) (e1b ▸ e1a ▸ hab1)
    exact ⟨e1a.trans (hLR.symm.trans e2a.symm), e1b.trans (hLR.trans e2b.symm)⟩
  · exact ⟨e1a.trans e2a.symm, e1b.trans e2b.symm⟩

/-- ★★★★★ **Button's prime-power Markov uniqueness (∅-axiom, via the matrix tree).**  For an odd
    prime power `c = p^(k+1)` with `5 ≤ c`, the ordered Markov triple with maximum `c` is unique.
    The two-roots input is `sqrtNegOneTwoRoots_prime_pow`; the Farey-monotone recovery is the tree
    machinery (`reverse_bridge` + `slope_path_inj` + window).  Closes the infinite prime-power family
    of the Markov uniqueness conjecture. -/
theorem markov_prime_pow_unique (p k : Nat) (hp3 : 3 ≤ p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h5 : 5 ≤ p ^ (k + 1)) :
    MarkovMaxUnique (p ^ (k + 1)) :=
  markov_max_unique_tree (p ^ (k + 1)) h5
    (E213.Lib.Math.Real213.MarkovUniqueness.sqrtNegOneTwoRoots_prime_pow p k hp3 hpr)

/-! ## §14 — import: the Markov tree on the hyperbolic (φ) face of `SL₂`

  Main's `HyperbolicEllipticTrace` classifies a det-1 `2×2` matrix by `Δ = tr² − 4·det`: `Δ>0`
  hyperbolic (φ/Fibonacci scaling, golden `G=⟨2,1,1,1⟩` has `Δ=5`), `Δ<0` elliptic (π, orders 4/6).
  Every Markoff node matrix has `tr = 3·m_t` (`mNode_shape`) and `det = 1` (`mNode_det1`), so its
  discriminant is `Δ = 9·m_t² − 4 > 0`: **the entire Markov tree lives on the hyperbolic face**, and
  its left generator `genL = ⟨2,1,1,1⟩ = G` is exactly the golden `Δ=5` pole — the Markov-spectrum
  minimum `√5` (`GoldenFormMarkov`).  The `Δ = 9c²−4` is the discriminant of the Markov form. -/

/-- The discriminant of a node matrix is `tr² − 4·det = 9·m_t² − 4` (`tr = 3 m_t`, `det = 1`). -/
theorem markov_node_disc (path : List Bool) :
    ((mNode path).a + (mNode path).d) * ((mNode path).a + (mNode path).d) - 4 * det2 (mNode path)
    = 9 * ((mNode path).c * (mNode path).c) - 4 := by
  rw [mNode_shape path, mNode_det1 path]; ring_intZ

/-- ★★★★ **Every Markov node matrix is hyperbolic** (`Δ = 9 m_t² − 4 > 0`): the tree is a tree of
    scalings (the φ/Fibonacci face), `genL = G` the golden `Δ=5` pole.  Since `m_t ≥ 1`,
    `Δ = 5 + 9(m_t²−1) ≥ 5 > 0`. -/
theorem markov_node_hyperbolic (path : List Bool) :
    0 < ((mNode path).a + (mNode path).d) * ((mNode path).a + (mNode path).d)
        - 4 * det2 (mNode path) := by
  have h2 : 1 ≤ (mNode path).c * (mNode path).c :=
    one_le_mul (markovNum_pos path) (markovNum_pos path)
  have hnn : (0 : Int) ≤ 9 * ((mNode path).c * (mNode path).c - 1) :=
    E213.Meta.Int213.mul_nonneg (by decide) (nonneg_sub_of_le h2)
  have e : ((mNode path).a + (mNode path).d) * ((mNode path).a + (mNode path).d)
           - 4 * det2 (mNode path)
         = (5 : Int) + 9 * ((mNode path).c * (mNode path).c - 1) := by
    rw [mNode_shape path, mNode_det1 path]; ring_intZ
  rw [e]
  exact lt_of_sub_eq_of_one_le (sub_zero_int _) (one_le_add_nonneg (by decide) hnn)

/-! ## §15 — import: the `2×2` determinant is the general `DetN.det` at `n = 2`

  Main's `Linalg213/DetN` builds the general `n×n` determinant by cofactor (Laplace) expansion.  Its
  `det_two` formula `det 2 M = M₀₀·M₁₁ − M₀₁·M₁₀` is exactly the `det2` of the Markoff-matrix carrier.
  So every tree-determinant fact (`mNode_det1`: `det = 1` at each node) is an instance of the general
  determinant — and `det2_mul` (det multiplicative for `2×2`) is the `n=2` case of the (not-yet-proven
  general) `det(MN)=det M·det N`. -/

/-- `Mat2` as a row/column function `ℕ → ℕ → ℤ` (`⟨a,b,c,d⟩ = [[a,b],[c,d]]`). -/
def matFun (M : Mat2) : Nat → Nat → Int :=
  fun i j => if i = 0 then (if j = 0 then M.a else M.b) else (if j = 0 then M.c else M.d)

/-- ★★★★ **The Markoff-carrier `det2` is the general determinant at `n = 2`.** -/
theorem det2_eq_detN (M : Mat2) : det2 M = E213.Lib.Math.Linalg213.DetN.det 2 (matFun M) := by
  rw [E213.Lib.Math.Linalg213.DetN.det_two]; rfl

/-- Every Markoff node matrix has general determinant `1` (`mNode_det1` via `det2_eq_detN`). -/
theorem mNode_detN (path : List Bool) :
    E213.Lib.Math.Linalg213.DetN.det 2 (matFun (mNode path)) = 1 := by
  rw [← det2_eq_detN]; exact mNode_det1 path

/-- ★★★★ **General-determinant multiplicativity at `n = 2`** (`det(MN)=det M·det N`), the `2×2` case
    that the general `DetN` does not yet prove — contributed back via `det2_mul`. -/
theorem detN_two_mul (M N : Mat2) :
    E213.Lib.Math.Linalg213.DetN.det 2 (matFun (mul M N))
    = E213.Lib.Math.Linalg213.DetN.det 2 (matFun M) * E213.Lib.Math.Linalg213.DetN.det 2 (matFun N) := by
  rw [← det2_eq_detN, ← det2_eq_detN, ← det2_eq_detN]; exact det2_mul M N

/-! ## §16 — the mediant is the strict maximum of the node triple

  Building block toward the realized-windowed-root template (the composite-`c` reduction): the node
  number `m_t = (mNode).c` strictly exceeds both interval bound numbers `m_l, m_r`.  From the `mul`
  formula `m_t = m_l·M_r.a + M_l.d·m_r` and positivity (`mInterval_pos`): `m_t − m_r = m_l·M_r.a +
  (M_l.d−1)·m_r ≥ 1`, `m_t − m_l = M_l.d·m_r + m_l·(M_r.a−1) ≥ 1`.  (So in every node triple, `c` is
  the max — the orientation `markovEq`/recovery facts the template needs.) -/

/-- ★★★★ **The mediant is the strict max**: both interval bound numbers are `< m_t = (mNode).c`. -/
theorem mNode_max (path : List Bool) :
    (mInterval path).1.c < (mNode path).c ∧ (mInterval path).2.c < (mNode path).c := by
  obtain ⟨_, _, hlc, hld⟩ := (mInterval_pos path).1
  obtain ⟨hra, _, hrc, _⟩ := (mInterval_pos path).2
  refine ⟨lt_of_pos_sub ?_, lt_of_pos_sub ?_⟩
  · have e : (mNode path).c - (mInterval path).1.c
           = (mInterval path).1.d * (mInterval path).2.c
             + (mInterval path).1.c * ((mInterval path).2.a - 1) := by
      show ((mInterval path).1.c * (mInterval path).2.a
            + (mInterval path).1.d * (mInterval path).2.c) - (mInterval path).1.c = _
      ring_intZ
    rw [e]
    exact lt_of_sub_eq_of_one_le (sub_zero_int _)
      (one_le_add_nonneg (one_le_mul hld hrc)
        (E213.Meta.Int213.mul_nonneg (nonneg_of_one_le hlc) (nonneg_sub_of_le hra)))
  · have e : (mNode path).c - (mInterval path).2.c
           = (mInterval path).1.c * (mInterval path).2.a
             + ((mInterval path).1.d - 1) * (mInterval path).2.c := by
      show ((mInterval path).1.c * (mInterval path).2.a
            + (mInterval path).1.d * (mInterval path).2.c) - (mInterval path).2.c = _
      ring_intZ
    rw [e]
    exact lt_of_sub_eq_of_one_le (sub_zero_int _)
      (one_le_add_nonneg (one_le_mul hlc hra)
        (E213.Meta.Int213.mul_nonneg (nonneg_sub_of_le hld) (nonneg_of_one_le hrc)))

/-! ## §17 — the node residue is realized (recovery congruence, ℕ form)

  Toward the realized-windowed-root template: every node's windowed residue `r = u_t.toNat` recovers
  the right bound number via `(r·m_l) % c = m_r` (ℕ).  From `markovRes_recovery_dvd` (ℤ `c ∣ r·m_l −
  m_r`) + `mNode_max` (`m_r < c`), converted with the pure `ofNat_sub_ofNat` bridge. -/

/-- `ofNat c ∣ (ofNat A − ofNat B)` with `B < c`, `1 ≤ c` ⟹ `A % c = B` (pure ℤ→ℕ mod transfer). -/
private theorem mod_eq_of_ofNat_dvd_sub {A B c : Nat} (hc : 1 ≤ c) (hB : B < c)
    (h : (Int.ofNat c) ∣ (Int.ofNat A - Int.ofNat B)) : A % c = B := by
  rcases Nat.lt_or_ge A B with hAB | hAB
  · have h' : (Int.ofNat c) ∣ (Int.ofNat B - Int.ofNat A) := by
      obtain ⟨q, hq⟩ := h
      exact ⟨-q, by rw [E213.Meta.Int213.mul_neg, ← hq]; ring_intZ⟩
    rw [E213.Meta.Int213.Order.ofNat_sub_ofNat,
        E213.Meta.Int213.subNatNat_of_le (Nat.le_of_lt hAB)] at h'
    obtain ⟨k, hk⟩ := nat_dvd_of_ofNat_dvd hc h'
    have hBval : B = A + k * c := by
      rw [← E213.Tactic.NatHelper.add_sub_of_le (Nat.le_of_lt hAB), hk, Nat.mul_comm c k]
    have hmod : B % c = A % c := by
      rw [hBval]; exact E213.Tactic.NatHelper.add_mul_mod_self_pure A c k
    exact hmod.symm.trans (Nat.mod_eq_of_lt hB)
  · rw [E213.Meta.Int213.Order.ofNat_sub_ofNat, E213.Meta.Int213.subNatNat_of_le hAB] at h
    obtain ⟨k, hk⟩ := nat_dvd_of_ofNat_dvd hc h
    have hA : A = B + k * c := by
      rw [← E213.Tactic.NatHelper.add_sub_of_le hAB, hk, Nat.mul_comm c k]
    rw [hA, E213.Tactic.NatHelper.add_mul_mod_self_pure, Nat.mod_eq_of_lt hB]

/-- ★★★★ **The node residue recovers the right bound mod `c`**: `(r·m_l) % m_t = m_r` (ℕ). -/
theorem node_recovery_nat (p : List Bool) :
    ((markovRes p).toNat * (mInterval p).1.c.toNat) % (mNode p).c.toNat
    = (mInterval p).2.c.toNat := by
  have hrnn : (0 : Int) ≤ markovRes p := nonneg_of_one_le (markov_window p).1
  have hlnn : (0 : Int) ≤ (mInterval p).1.c := nonneg_of_one_le (mInterval_pos p).1.2.2.1
  have hmrnn : (0 : Int) ≤ (mInterval p).2.c := nonneg_of_one_le (mInterval_pos p).2.2.2.1
  have hc1 : 1 ≤ (mNode p).c.toNat :=
    int_toNat_lt (x := 0) (y := (mNode p).c) (by decide) (markovNum_pos p)
  have hmrc : (mInterval p).2.c.toNat < (mNode p).c.toNat := int_toNat_lt hmrnn (mNode_max p).2
  have e1 : Int.ofNat ((markovRes p).toNat * (mInterval p).1.c.toNat)
          = markovRes p * (mInterval p).1.c := by
    show Int.ofNat (markovRes p).toNat * Int.ofNat (mInterval p).1.c.toNat = _
    rw [toNat_of_nonneg hrnn, toNat_of_nonneg hlnn]
  have e2 : Int.ofNat (mInterval p).2.c.toNat = (mInterval p).2.c := toNat_of_nonneg hmrnn
  have e3 : Int.ofNat (mNode p).c.toNat = (mNode p).c :=
    toNat_of_nonneg (nonneg_of_one_le (mNode_pos p).2.2.1)
  have hd : (mNode p).c ∣ markovRes p * (mInterval p).1.c - (mInterval p).2.c :=
    markovRes_recovery_dvd p
  rw [← e1, ← e2, ← e3] at hd
  exact mod_eq_of_ofNat_dvd_sub hc1 hmrc hd

/-! ## §18 — the realized-windowed-root template (generalizing past `SqrtNegOneTwoRoots`)

  The composite-`c` reduction, made a ∅-axiom theorem.  `markov_max_unique_tree` needed
  `SqrtNegOneTwoRoots c` (≤ 2 roots **total**) — which fails for composite `c`.  The honest weakening:
  only the **realized** windowed roots need be unique.  Every node residue is realized
  (`node_realized`), so the template closes uniqueness from `WindowRealizedUnique`, a strictly weaker
  (and per-`c` decidable) hypothesis.  `SqrtNegOneTwoRoots ⟹ WindowRealizedUnique`, so Button is a
  special case. -/

/-- ★★★★ **The node residue is realized**: `(markovRes·m_l) % m_t = m_r` and `(m_r,m_l,m_t)` is a
    Markov triple, so the windowed residue `u_t.toNat` is recovered by an actual triple (`b = m_l`). -/
theorem node_realized (p : List Bool) :
    ∃ b, b < (mNode p).c.toNat ∧
      markovEq (((markovRes p).toNat * b) % (mNode p).c.toNat) b (mNode p).c.toNat := by
  refine ⟨(mInterval p).1.c.toNat,
    int_toNat_lt (nonneg_of_one_le (mInterval_pos p).1.2.2.1) (mNode_max p).1, ?_⟩
  rw [node_recovery_nat p]
  have ht := E213.Lib.Math.Real213.MarkovUniqueness.markov_reachable_is_triple (mInterval_reachable p)
  show (mInterval p).2.c.toNat * (mInterval p).2.c.toNat
       + (mInterval p).1.c.toNat * (mInterval p).1.c.toNat
       + (mNode p).c.toNat * (mNode p).c.toNat
     = 3 * (mInterval p).2.c.toNat * (mInterval p).1.c.toNat * (mNode p).c.toNat
  rw [show (mInterval p).2.c.toNat * (mInterval p).2.c.toNat
        + (mInterval p).1.c.toNat * (mInterval p).1.c.toNat
        + (mNode p).c.toNat * (mNode p).c.toNat
      = (mInterval p).1.c.toNat * (mInterval p).1.c.toNat
        + (mInterval p).2.c.toNat * (mInterval p).2.c.toNat
        + (mNode p).c.toNat * (mNode p).c.toNat from by ring_nat,
      show 3 * (mInterval p).2.c.toNat * (mInterval p).1.c.toNat * (mNode p).c.toNat
      = 3 * (mInterval p).1.c.toNat * (mInterval p).2.c.toNat * (mNode p).c.toNat from by ring_nat]
  exact ht

/-- **Realized windowed roots are unique**: among windowed `√(−1)` roots mod `c`, those realized by
    an actual Markov triple coincide.  Strictly weaker than `SqrtNegOneTwoRoots` (phantom roots may
    multiply), and decidable for each numeral `c`. -/
def WindowRealizedUnique (c : Nat) : Prop :=
  ∀ u₁ u₂ : Nat, u₁ < c → u₂ < c → 2 * u₁ < c → 2 * u₂ < c →
    (u₁ * u₁ + 1) % c = 0 → (u₂ * u₂ + 1) % c = 0 →
    (∃ b₁, b₁ < c ∧ markovEq ((u₁ * b₁) % c) b₁ c) →
    (∃ b₂, b₂ < c ∧ markovEq ((u₂ * b₂) % c) b₂ c) →
    u₁ = u₂

/-- ★★★★★ **The realized-windowed-root template.**  `MarkovMaxUnique c` from `5 ≤ c` and
    `WindowRealizedUnique c` — the genuine reduction of composite-`c` Markov uniqueness to phantom
    elimination.  (Same proof as `markov_max_unique_tree`, but feeding `h` the two node residues'
    realizations via `node_realized` instead of `root_unique_below_half`.) -/
theorem markov_max_unique_of_window_realized_unique
    (c : Nat) (hc5 : 5 ≤ c) (h : WindowRealizedUnique c) : MarkovMaxUnique c := by
  intro a₁ b₁ a₂ b₂ hab1 hb1c hab2 hb2c hm1 hm2
  have hc2 : 2 ≤ c := Nat.le_trans (by decide) hc5
  have ha1 : 1 ≤ a₁ := E213.Lib.Math.Real213.MarkovUniqueness.markov_a_pos hc2 hm1
  have ha2 : 1 ≤ a₂ := E213.Lib.Math.Real213.MarkovUniqueness.markov_a_pos hc2 hm2
  obtain ⟨p1, hcp1, hpair1⟩ := node_data (reverse_bridge a₁ b₁ c hm1 ha1 hab1 hb1c hc5)
  obtain ⟨p2, hcp2, hpair2⟩ := node_data (reverse_bridge a₂ b₂ c hm2 ha2 hab2 hb2c hc5)
  obtain ⟨hlo1, hhi1, hmod1⟩ := node_window_nat p1
  obtain ⟨hlo2, hhi2, hmod2⟩ := node_window_nat p2
  rw [hcp1] at hlo1 hhi1 hmod1
  rw [hcp2] at hlo2 hhi2 hmod2
  have hr12 : (markovRes p1).toNat = (markovRes p2).toNat := by
    obtain ⟨bb1, l1, eq1⟩ := node_realized p1; rw [hcp1] at l1 eq1
    obtain ⟨bb2, l2, eq2⟩ := node_realized p2; rw [hcp2] at l2 eq2
    exact h _ _ hlo1 hlo2 hhi1 hhi2 hmod1 hmod2 ⟨bb1, l1, eq1⟩ ⟨bb2, l2, eq2⟩
  have hrnn1 : (0 : Int) ≤ markovRes p1 := nonneg_of_one_le (markov_window p1).1
  have hrnn2 : (0 : Int) ≤ markovRes p2 := nonneg_of_one_le (markov_window p2).1
  have hReq : markovRes p1 = markovRes p2 := by
    rw [← toNat_of_nonneg hrnn1, ← toNat_of_nonneg hrnn2, hr12]
  have hcc : (mNode p1).c = (mNode p2).c := by
    rw [← toNat_of_nonneg (nonneg_of_one_le (mNode_pos p1).2.2.1),
        ← toNat_of_nonneg (nonneg_of_one_le (mNode_pos p2).2.2.1), hcp1, hcp2]
  have hslope : slopeEq (mNode p1) (mNode p2) := by
    show markovRes p1 * (mNode p2).c = markovRes p2 * (mNode p1).c
    rw [hReq, hcc]
  have hpeq : p1 = p2 := slope_path_inj p1 p2 hslope
  subst hpeq
  rcases hpair1 with ⟨e1a, e1b⟩ | ⟨e1a, e1b⟩ <;> rcases hpair2 with ⟨e2a, e2b⟩ | ⟨e2a, e2b⟩
  · exact ⟨e1a.trans e2a.symm, e1b.trans e2b.symm⟩
  · have hLR : (mInterval p1).1.c.toNat = (mInterval p1).2.c.toNat :=
      Nat.le_antisymm (e1a ▸ e1b ▸ hab1) (e2b ▸ e2a ▸ hab2)
    exact ⟨e1a.trans (hLR.trans e2a.symm), e1b.trans (hLR.symm.trans e2b.symm)⟩
  · have hLR : (mInterval p1).1.c.toNat = (mInterval p1).2.c.toNat :=
      Nat.le_antisymm (e2a ▸ e2b ▸ hab2) (e1b ▸ e1a ▸ hab1)
    exact ⟨e1a.trans (hLR.symm.trans e2a.symm), e1b.trans (hLR.trans e2b.symm)⟩
  · exact ⟨e1a.trans e2a.symm, e1b.trans e2b.symm⟩

/-- `SqrtNegOneTwoRoots ⟹ WindowRealizedUnique` — Button's two-roots input is a special case of the
    realized-uniqueness hypothesis (the realization witnesses are simply ignored, `root_unique`). -/
theorem window_realized_unique_of_sqrtNegOne (c : Nat) (h2 : SqrtNegOneTwoRoots c) :
    WindowRealizedUnique c :=
  fun u₁ u₂ hu1 hu2 hh1 hh2 hr1 hr2 _ _ =>
    root_unique_below_half c h2 hu1 hu2 hh1 hh2 hr1 hr2

/-! ## §19 — concrete composite closures (beyond Button), via the template

  The template closes composite `c` where Button's `SqrtNegOneTwoRoots` **fails** (≥ 4 roots).  For
  `ω = 2` (two odd prime factors `≡ 1 mod 4`) there are exactly two windowed roots `{P, Q}`; if `P`
  is phantom (`∀b<c ¬markovEq`), any realized windowed root is `Q`, so `WindowRealizedUnique c` holds.
  `window_realized_unique_of_one_phantom` reduces each `ω=2` composite to two `O(c)` `decide`s.
  Feasible for the first composite Markov numbers; `ω≥3` (`195025`, `196418`, `c≈2·10⁵`) and even
  `4181` exhaust the `decide` kernel — the method holds but needs a non-`decide` root enumerator.
  (A `List`-of-phantoms generalization is avoided: `List.Mem`'s `decide` is `Quot.sound`-dirty.) -/

/-- ★★★★ **One-phantom reducer**: windowed roots `⊆ {P, Q}` with `P` phantom ⟹ `WindowRealizedUnique`.
    (If `Q` is also phantom the conclusion is vacuous; otherwise `Q` is the unique realized root.) -/
theorem window_realized_unique_of_one_phantom (c P Q : Nat)
    (hroots : ∀ u, u < c → (u * u + 1) % c = 0 → 2 * u < c → u = P ∨ u = Q)
    (hphantom : ∀ b, b < c → ¬ markovEq ((P * b) % c) b c) : WindowRealizedUnique c := by
  intro u₁ u₂ h1c h2c hh1 hh2 hr1 hr2 hreal1 hreal2
  rcases hroots u₁ h1c hr1 hh1 with rfl | rfl
  · obtain ⟨b, hb, hmk⟩ := hreal1; exact absurd hmk (hphantom b hb)
  · rcases hroots u₂ h2c hr2 hh2 with rfl | rfl
    · obtain ⟨b, hb, hmk⟩ := hreal2; exact absurd hmk (hphantom b hb)
    · rfl

set_option maxRecDepth 400000 in
/-- `MarkovMaxUnique 65` (= 5·13, `SqrtNegOneTwoRoots` **false**, non-Markov): windowed `{8,18}`. -/
theorem markov_max_unique_65 :
    E213.Lib.Math.Real213.MarkovUniqueness.MarkovMaxUnique 65 :=
  markov_max_unique_of_window_realized_unique 65 (by decide)
    (window_realized_unique_of_one_phantom 65 8 18 (by decide) (by decide))

set_option maxRecDepth 400000 in
/-- ★★★★★ **`MarkovMaxUnique 610`** (= 2·5·61 = F₁₅): windowed `{133,233}`, `233` realized `(1,233,610)`. -/
theorem markov_max_unique_610 :
    E213.Lib.Math.Real213.MarkovUniqueness.MarkovMaxUnique 610 :=
  markov_max_unique_of_window_realized_unique 610 (by decide)
    (window_realized_unique_of_one_phantom 610 133 233 (by decide) (by decide))

set_option maxRecDepth 400000 in
/-- ★★★★★ **`MarkovMaxUnique 985`** (= 5·197): windowed `{183,408}`, `408` realized. -/
theorem markov_max_unique_985 :
    E213.Lib.Math.Real213.MarkovUniqueness.MarkovMaxUnique 985 :=
  markov_max_unique_of_window_realized_unique 985 (by decide)
    (window_realized_unique_of_one_phantom 985 183 408 (by decide) (by decide))

set_option maxRecDepth 400000 in
/-- ★★★★★ **`MarkovMaxUnique 1325`** (= 5²·53), first composite Markov number with the `2^ω=4` root
    explosion: windowed `{182,507}`, `507` realized `(13,34,1325)`, `182` phantom. -/
theorem markov_max_unique_1325 :
    E213.Lib.Math.Real213.MarkovUniqueness.MarkovMaxUnique 1325 :=
  markov_max_unique_of_window_realized_unique 1325 (by decide)
    (window_realized_unique_of_one_phantom 1325 182 507 (by decide) (by decide))

/-! ## §20 — the upper-fold pattern: the window is the transversal of the `±` involution

  Narrative: `theory/math/analysis/markov_uniqueness.md` "The upper-fold pattern" (§20–§26 here).

  The template `markov_max_unique_of_window_realized_unique` is not just a tool for closing numbers —
  it is the **upper-fold pattern** made into a theorem.  The roots of `x²≡−1 mod c` carry the natural
  **`±` involution** `σ(u) = c − u = −u mod c` (`neg_root_is_root`: `σ` preserves the root set,
  `σ²=id`).  The **window** `0 < u < c/2` (`markov_window`, where the tree's residue always lands) is a
  **transversal** of `σ` — it picks exactly one representative of each pair `{u, c−u}`
  (`window_excludes_partner`: if `u` is windowed its fold-partner `c−u` is not).  So:

    Markov uniqueness  =  fold by `σ` (window) + the realized fold-point is unique.

  This is the same fold the repo reads elsewhere as the unit's two faces (`HyperbolicEllipticTrace`,
  the `Δ`-sign φ/π split — §14 here), `0/∞` as one reciprocal hole (`ZeroInfinityHole`), and the
  `±`/Cassini sign (the fold's "non-value", `DetSpectrumPoles`).  `WindowRealizedUnique` = "the fold's
  realized non-value is unique." -/

/-- ★★★★ **The window excludes the fold-partner**: a windowed root `r` (`2r<c`) has its `±`-partner
    `c−r` *outside* the window (`2(c−r)>c`).  So the window is a transversal of `σ(u)=c−u`. -/
theorem window_excludes_partner (c r : Nat) (hrw : 2 * r < c) : c < 2 * (c - r) := by
  have hrc : r < c := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left r (by decide)) hrw
  have h2r : r + r < c := by rw [← Nat.two_mul]; exact hrw
  have hr_lt : r < c - r := by
    have h3 : r + r < r + (c - r) := by
      rw [E213.Tactic.NatHelper.add_sub_of_le (Nat.le_of_lt hrc)]; exact h2r
    exact Nat.lt_of_add_lt_add_left h3
  calc c = r + (c - r) := (E213.Tactic.NatHelper.add_sub_of_le (Nat.le_of_lt hrc)).symm
    _ < (c - r) + (c - r) := Nat.add_lt_add_right hr_lt (c - r)
    _ = 2 * (c - r) := (Nat.two_mul (c - r)).symm

/-- ★★★★★ **The window is the `±`-fold transversal**: for a root `r` of `x²≡−1 mod c` in the window,
    the fold-partner `c−r` is *also a root* (`neg_root_is_root`) but *not windowed*
    (`window_excludes_partner`).  So windowed roots = one representative per `±`-pair — the upper fold.
    `WindowRealizedUnique` is then exactly "the realized point of this fold is unique." -/
theorem window_fold_transversal (c r : Nat) (hrc : r < c)
    (hroot : (r * r + 1) % c = 0) (hrw : 2 * r < c) :
    ((c - r) * (c - r) + 1) % c = 0 ∧ ¬ (2 * (c - r) < c) :=
  ⟨E213.Lib.Math.Real213.MarkovInjectivity.neg_root_is_root c r (Nat.le_of_lt hrc) hroot,
   fun hcon => Nat.lt_irrefl c (Nat.lt_trans (window_excludes_partner c r hrw) hcon)⟩

/-! ## §21 — the next fold: the `√(−1)` root set is a torsor under the unit-root group, and §20's
`±` involution `σ` is that group's distinguished order-2 element `c−1 ≡ −1`

Templatizing §20 hits the next wall: at a composite `c` with `ω ≥ 2` distinct primes `≡ 1 mod 4`,
the windowed roots no longer reduce to a single `±`-pair — *phantom* roots survive (§19,
`markov_composite_separation`).  The structural reason, made `∅`-axiom here: the `√(−1)` roots form a
**torsor under the group of square-roots-of-unity** `SqrtUnity c = {e : e² ≡ 1 mod c}` — closed under
mod-multiplication (`sqrtUnity_mul`), and acting on the root set (`sqrtUnity_acts_on_root`: if `r` is a
`√(−1)` and `e` a unit-root, `e·r` is again a `√(−1)`).

The `±` involution `σ(r) = c−r` of §20 is *one* element of this group — multiplication by `c−1`:
`neg_one_sqrtUnity` ((c−1)² ≡ 1) + `neg_one_mul_is_neg` ((c−1)·r ≡ −r) pin `c−1 = −1` exactly.  The
window is the transversal of the `⟨c−1⟩ = {1, c−1}` *subgroup*'s action.

  - prime power `p^k`: `SqrtUnity = {1, c−1}` exactly → each orbit IS a `±`-pair → window picks one rep
    → uniqueness (Button, §13).
  - composite `ω ≥ 2`: `SqrtUnity ⊋ {1, c−1}` (a nontrivial `e ≠ ±1` exists, by `CRT`) → orbits are
    *larger* than `±`-pairs → the window leaves `2^{ω−1}` reps → the extras are the phantoms.

So the wall is again a fold, **one level up**: the involution is no longer `σ` alone but the whole
`SqrtUnity` group, with `σ = ·(c−1)` its distinguished order-2 generator (`σ² = id`,
`AddMod213.double_neg_mod_at`).  Markov realizability (`WindowRealizedUnique`) is the *second*
constraint that re-collapses the enlarged transversal to the one true residue — the recurring
upper-fold pattern, the same self-pointing read at the next resolution. -/

/-- A **square root of unity** mod `c`: `e² ≡ 1`.  The group acting on the `√(−1)` root torsor;
    `{1, c−1}` is always inside it, and equals it exactly at prime powers. -/
def SqrtUnity (c e : Nat) : Prop := (e * e) % c = 1

/-- `1` is the identity unit-root. -/
theorem one_sqrtUnity (c : Nat) (hc : 2 ≤ c) : SqrtUnity c 1 := by
  show (1 * 1) % c = 1
  rw [Nat.one_mul]; exact Nat.mod_eq_of_lt hc

/-- `c−1 ≡ −1` is a unit-root: `(c−1)² ≡ 1`.  This is `σ`'s membership in the group. -/
theorem neg_one_sqrtUnity (c : Nat) (hc : 2 ≤ c) : SqrtUnity c (c - 1) := by
  obtain ⟨e, he⟩ := Nat.le.dest hc
  have hceq : c = e + 2 := by rw [← he]; exact Nat.add_comm 2 e
  have hcd : c - 1 = e + 1 := by rw [hceq]; exact E213.Tactic.NatHelper.add_sub_cancel_right (e + 1) 1
  show (c - 1) * (c - 1) % c = 1
  rw [hcd, hceq, show (e + 1) * (e + 1) = 1 + e * (e + 2) from by ring_nat,
     E213.Tactic.NatHelper.add_mul_mod_self_pure 1 (e + 2) e]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide) (Nat.le_add_left 2 e))

/-- **`c−1` acts as additive negation**: `(c−1)·r + r ≡ 0`, i.e. `(c−1)·r ≡ −r mod c`.  Together with
    `neg_one_sqrtUnity` this is the exact identification `σ = ·(c−1) = ·(−1)` — the §20 fold *is* one
    element of the unit-root group. -/
theorem neg_one_mul_is_neg (c r : Nat) (hc : 1 ≤ c) : ((c - 1) * r + r) % c = 0 := by
  have hcc : c - 1 + 1 = c := Nat.succ_pred_eq_of_pos hc
  have hrr : (c - 1) * r + r = (c - 1 + 1) * r := by ring_nat
  rw [hcc] at hrr
  rw [hrr]
  exact E213.Tactic.NatHelper.mul_mod_right c r

/-- **The unit-root group is closed under mod-multiplication** — `SqrtUnity` is a group (monoid; with
    `c−1` it has the order-2 element and inverses).  `(ef)² = e²f² ≡ 1·1 = 1`. -/
theorem sqrtUnity_mul (c e f : Nat) (hc : 2 ≤ c)
    (he : SqrtUnity c e) (hf : SqrtUnity c f) : SqrtUnity c ((e * f) % c) := by
  show (((e * f) % c) * ((e * f) % c)) % c = 1
  rw [← E213.Meta.Nat.MulMod213.mul_mod_pure (e * f) (e * f) c,
      show (e * f) * (e * f) = (e * e) * (f * f) from by ring_nat,
      E213.Meta.Nat.MulMod213.mul_mod_pure (e * e) (f * f) c, he, hf, Nat.one_mul]
  exact Nat.mod_eq_of_lt hc

/-- ★★★★★ **The unit-root group acts on the `√(−1)` root set** — the root set is a torsor.  If `r` is
    a `√(−1)` mod `c` and `e` a unit-root (`e² ≡ 1`), then `e·r` is again a `√(−1)`:
    `(er)² + 1 = e²r² + 1 ≡ r² + 1 ≡ 0`.  The §20 `±`-pairing `neg_root_is_root` is the `e = c−1`
    instance.  For prime powers the group is `{±1}` so each orbit is a single `±`-pair (Button); for
    `ω ≥ 2` the group is larger and the extra orbit-members are the phantoms. -/
theorem sqrtUnity_acts_on_root (c e r : Nat) (he : SqrtUnity c e)
    (hr : (r * r + 1) % c = 0) :
    (((e * r) % c) * ((e * r) % c) + 1) % c = 0 := by
  have hsq : (((e * r) % c) * ((e * r) % c)) % c = (r * r) % c := by
    rw [← E213.Meta.Nat.MulMod213.mul_mod_pure (e * r) (e * r) c,
        show (e * r) * (e * r) = (e * e) * (r * r) from by ring_nat,
        E213.Meta.Nat.MulMod213.mul_mod_pure (e * e) (r * r) c, he, Nat.one_mul,
        E213.Meta.Nat.AddMod213.mod_mod]
  rw [E213.Meta.Nat.AddMod213.add_mod_gen, hsq,
      ← E213.Meta.Nat.AddMod213.add_mod_gen, hr]

/-! ## §22 — the fold is a product of folds: `SqrtUnity` factors through coprime components

The unit-root group of §21 is *multiplicative* across coprime factors: an `e` that is a unit-root mod
`m` and mod `n` is a unit-root mod `m·n` (`sqrtUnity_lift`).  So at `c = p₁^{a₁}·…·p_ω^{a_ω}` the group
`SqrtUnity c` contains the **product** of the per-prime-power groups `{1, c−1 mod pᵢ}` — one `±` fold
per prime.  That is exactly why `ω` controls the phantom count: `ω` independent `±` folds multiply to
`2^ω` unit-roots, the window's `⟨−1⟩`-transversal keeps `2^{ω−1}`, and all but one are phantoms.

The engine is `mul_dvd_of_coprime` (the previously-missing reusable primitive: coprime `m,n` dividing
`k` ⟹ `m·n ∣ k`, via `euclid_of_coprime`).  The concrete witness `phantom_is_unit_root_image_1325`
closes the loop: the nontrivial unit-root `476` at `1325 = 25·53` carries the realized root `507` to
the phantom `182` — the §21 torsor action made arithmetic. -/

/-- **Coprime multiplicative lift of divisibility**: `gcd(m,n)=1 ∧ m∣k ∧ n∣k ⟹ m·n ∣ k`.  The
    missing ∅-axiom primitive behind CRT-style composite reasoning, via `euclid_of_coprime`. -/
theorem mul_dvd_of_coprime (m n k : Nat) (hn : 1 < n) (hco : gcd213 m n = 1)
    (hm : m ∣ k) (hnk : n ∣ k) : m * n ∣ k := by
  obtain ⟨a, ha⟩ := hm
  have hna : n ∣ a :=
    E213.Lib.Math.ModArith.MarkovPrimeFactor.euclid_of_coprime m a n hn hco (ha ▸ hnk)
  obtain ⟨b, hb⟩ := hna
  exact ⟨b, by rw [ha, hb]; ring_nat⟩

/-- ★★★★★ **The fold is a product of folds** (`SqrtUnity` factors through coprime components): a
    unit-root mod `m` and mod `n` is a unit-root mod `m·n`.  `e²≡1 mod m ∧ e²≡1 mod n ⟹ e²≡1 mod m·n`.
    At a composite `c` with `ω` distinct prime factors this gives `SqrtUnity c ⊇ ∏ {±1 mod pᵢ}` — `ω`
    independent `±` folds, hence `2^ω` unit-roots and (after the window's `⟨−1⟩`-transversal)
    `2^{ω−1}` windowed reps, all but one phantom. -/
theorem sqrtUnity_lift (m n e : Nat) (hm : 1 < m) (hn : 1 < n) (hco : gcd213 m n = 1)
    (hem : (e * e) % m = 1) (hen : (e * e) % n = 1) : SqrtUnity (m * n) e := by
  have hDm := E213.Meta.Nat.AddMod213.div_add_mod (e * e) m
  rw [hem] at hDm
  have hdm : m ∣ (e * e - 1) := by
    refine ⟨e * e / m, ?_⟩
    rw [show e * e - 1 = (m * (e * e / m) + 1) - 1 from by rw [hDm],
        E213.Tactic.NatHelper.add_sub_cancel_right]
  have hDn := E213.Meta.Nat.AddMod213.div_add_mod (e * e) n
  rw [hen] at hDn
  have hdn : n ∣ (e * e - 1) := by
    refine ⟨e * e / n, ?_⟩
    rw [show e * e - 1 = (n * (e * e / n) + 1) - 1 from by rw [hDn],
        E213.Tactic.NatHelper.add_sub_cancel_right]
  obtain ⟨r, hr⟩ := mul_dvd_of_coprime m n (e * e - 1) hn hco hdm hdn
  have he1 : 1 ≤ e * e := hDm ▸ Nat.le_add_left 1 _
  have hee : e * e = 1 + r * (m * n) := by
    rw [Nat.mul_comm r (m * n), Nat.add_comm, ← hr]
    exact (E213.Tactic.NatHelper.sub_add_cancel he1).symm
  show (e * e) % (m * n) = 1
  rw [hee, E213.Tactic.NatHelper.add_mul_mod_self_pure 1 (m * n) r]
  exact Nat.mod_eq_of_lt
    (Nat.lt_of_lt_of_le hn (Nat.le_mul_of_pos_left n (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hm))))

/-- **A nontrivial unit-root at the composite Markov number `1325 = 25·53`**: `476² ≡ 1 mod 1325` with
    `476 ∉ {1, 1324}`.  `SqrtUnity 1325 ⊋ {±1}` — the `ω = 2` enlargement made concrete (via CRT:
    `476 ≡ 1 mod 25`, `476 ≡ −1 mod 53`). -/
theorem sqrtUnity_1325_nontrivial : SqrtUnity 1325 476 ∧ 476 ≠ 1 ∧ 476 ≠ 1324 :=
  ⟨show (476 * 476) % 1325 = 1 by decide, by decide, by decide⟩

/-- ★★★★★ **The phantom is the unit-root image of the realized root.**  At `c = 1325` the nontrivial
    unit-root `476` carries the *realized* root `507` to the *phantom* root `182`:
    `476·507 ≡ 182 mod 1325`.  Both are `√(−1)` (`507² ≡ 182² ≡ −1`); they share an orbit of the full
    `SqrtUnity` group but lie in *different* orbits of the `±`-subgroup `⟨c−1⟩` — exactly why the
    window cannot fold one onto the other and `182` survives as a phantom (§19,
    `markov_composite_separation`).  Concrete realization of `sqrtUnity_acts_on_root` + the §21–§22
    reading: the open Markov content is precisely the extra `±`-orbits produced by `ω ≥ 2`. -/
theorem phantom_is_unit_root_image_1325 :
    (476 * 507) % 1325 = 182 ∧ (507 * 507 + 1) % 1325 = 0 ∧ (182 * 182 + 1) % 1325 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §23 — nontrivial unit-root existence: the open content closed for `ω = 2`

The CRT *existence* the §21–§22 reading needs.  At `c = m·n` with `m, n ≥ 3` coprime there is an
`e ∉ {1, c−1}` with `e² ≡ 1 mod c`.  Construction: `e = 1 + m·t` with `t ≡ (n−2)·m⁻¹ mod n`, so
`e ≡ 1 mod m` and `e ≡ −1 mod n` — the CRT product element `(1, −1) ∈ Z/m × Z/n`, a non-diagonal
member of the unit-root group, hence `≠ ±1`.  `sqrtUnity_lift` (§22) certifies `e² ≡ 1 mod c`; the
modular inverse `m⁻¹` comes from `inverse_of_coprime`/`modBezout`.

This closes the *existence* half of the open Markov content at `ω = 2`: phantoms provably exist at
every two-factor composite — so uniqueness there is **not** free from root-counting, it must come from
Markov realizability (`WindowRealizedUnique`, §18).  The construction is the CRT product = product of
the two `±` folds, the §22 mechanism made constructive — the upper-fold pattern, one resolution down. -/

/-- Arithmetic helper: `1 + (n−2) = n−1` for `n ≥ 2`. -/
theorem aux_1_add_sub2 (n : Nat) (hn : 2 ≤ n) : 1 + (n - 2) = n - 1 := by
  obtain ⟨k, hk⟩ := Nat.le.dest hn
  have hk' : n = k + 2 := by rw [← hk]; exact Nat.add_comm 2 k
  rw [hk']
  exact Nat.add_comm 1 k

/-- Arithmetic helper: `(m·n − 1) % m = m − 1` for `m, n ≥ 1` (i.e. `m·n − 1 ≡ −1 mod m`). -/
theorem aux_pred_mul_mod (m n : Nat) (hm0 : 0 < m) (hn0 : 0 < n) : (m * n - 1) % m = m - 1 := by
  have hm_pred : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm0
  have hn_pred : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn0
  have hkey : m * (n - 1) + (m - 1) + 1 = m * n := by
    rw [Nat.add_assoc, hm_pred, show m * (n - 1) + m = m * ((n - 1) + 1) from by ring_nat, hn_pred]
  have hsplit : m * n - 1 = m * (n - 1) + (m - 1) := by
    rw [← hkey, E213.Tactic.NatHelper.add_sub_cancel_right]
  rw [hsplit, Nat.add_comm (m * (n - 1)) (m - 1), Nat.mul_comm m (n - 1),
      E213.Tactic.NatHelper.add_mul_mod_self_pure (m - 1) m (n - 1)]
  exact Nat.mod_eq_of_lt (Nat.sub_lt hm0 (by decide))

/-- ★★★★★ **Nontrivial unit-root existence (`ω = 2`).**  At `c = m·n`, `m, n ≥ 3` coprime, there is
    `e ∉ {1, c−1}` with `e² ≡ 1 mod c` — built by CRT as `e ≡ 1 mod m`, `e ≡ −1 mod n`.  So
    `SqrtUnity c ⊋ {±1}` *unconditionally* at every two-factor composite: the `2^ω`-root explosion is
    real, phantoms genuinely exist, and Markov uniqueness there cannot come from root-counting alone —
    it is exactly what `WindowRealizedUnique` (§18) must supply.  Closes the existence half of the open
    content at `ω = 2`. -/
theorem nontrivial_unit_root_exists (m n : Nat) (hm : 3 ≤ m) (hn : 3 ≤ n)
    (hco : gcd213 m n = 1) :
    ∃ e, SqrtUnity (m * n) e ∧ e ≠ 1 ∧ e ≠ m * n - 1 := by
  have hm0 : 0 < m := Nat.lt_of_lt_of_le (by decide) hm
  have hn0 : 0 < n := Nat.lt_of_lt_of_le (by decide) hn
  have hm1 : 1 < m := Nat.lt_of_lt_of_le (by decide) hm
  have hn1 : 1 < n := Nat.lt_of_lt_of_le (by decide) hn
  have hsinv : (m * (E213.Lib.Math.ModArith.ModBezout.modBezout m n).2) % n = 1 := by
    rw [E213.Lib.Math.ModArith.MarkovPrimeFactor.inverse_of_coprime m n hn0 hco,
        Nat.mod_eq_of_lt hn1]
  have htexists : ∃ t, (m * t) % n = n - 2 := by
    refine ⟨((n - 2) * (E213.Lib.Math.ModArith.ModBezout.modBezout m n).2) % n, ?_⟩
    rw [← E213.Meta.Nat.MulMod213.mul_mod_right_pure m
          ((n - 2) * (E213.Lib.Math.ModArith.ModBezout.modBezout m n).2) n,
        show m * ((n - 2) * (E213.Lib.Math.ModArith.ModBezout.modBezout m n).2)
           = (n - 2) * (m * (E213.Lib.Math.ModArith.ModBezout.modBezout m n).2) from by ring_nat,
        E213.Meta.Nat.MulMod213.mul_mod_right_pure (n - 2)
          (m * (E213.Lib.Math.ModArith.ModBezout.modBezout m n).2) n,
        hsinv, Nat.mul_one]
    exact Nat.mod_eq_of_lt (Nat.sub_lt hn0 (by decide))
  obtain ⟨t, ht⟩ := htexists
  have ham : (1 + m * t) % m = 1 := by
    rw [Nat.mul_comm m t, E213.Tactic.NatHelper.add_mul_mod_self_pure 1 m t]
    exact Nat.mod_eq_of_lt hm1
  have han : (1 + m * t) % n = n - 1 := by
    rw [E213.Meta.Nat.AddMod213.add_mod_gen, ht, Nat.mod_eq_of_lt hn1, aux_1_add_sub2 n hn1]
    exact Nat.mod_eq_of_lt (Nat.sub_lt hn0 (by decide))
  have hem : (1 + m * t) * (1 + m * t) % m = 1 := by
    rw [E213.Meta.Nat.MulMod213.mul_mod_pure, ham, Nat.one_mul]
    exact Nat.mod_eq_of_lt hm1
  have hen : (1 + m * t) * (1 + m * t) % n = 1 := by
    rw [E213.Meta.Nat.MulMod213.mul_mod_pure, han]
    exact neg_one_sqrtUnity n hn1
  refine ⟨1 + m * t, sqrtUnity_lift m n (1 + m * t) hm1 hn1 hco hem hen, ?_, ?_⟩
  · intro he
    rw [he, Nat.mod_eq_of_lt hn1] at han
    exact absurd (han.symm ▸ Nat.sub_le_sub_right hn 1 : (2 : Nat) ≤ 1) (by decide)
  · intro he
    rw [he, aux_pred_mul_mod m n hm0 hn0] at ham
    exact absurd (ham ▸ Nat.sub_le_sub_right hm 1 : (2 : Nat) ≤ 1) (by decide)

/-! ## §24 — orbit-injectivity: the unit-root group acts FREELY on the root set

The last piece for `ω = 2` uniqueness.  A `√(−1)` root `u` is a *unit* — its inverse is `c−u`
(`root_inverse`: `u·(c−u) ≡ 1`, since `u·(c−u) + (u²+1) = u·c + 1`).  Multiplication by a unit is
*cancellable* (`unit_cancel_of_inv`: `a·u ≡ b·u ⟹ a ≡ b`), so the unit-root group acts **freely** on
the root set.  Hence `e·u ≡ u ⟹ e ≡ 1` (`root_orbit_inj`) and `e·u ≡ (c−1)·u ⟹ e ≡ c−1`
(`root_orbit_inj_neg`): the orbit map `e ↦ e·u` is injective mod `c`.

Combined with §21–§23: the `2^ω` unit-roots give `2^ω` *distinct* roots (free action), the window's
`⟨−1⟩`-transversal keeps `2^{ω−1}` distinct windowed roots, and each is a distinct `±`-suborbit.  So
"how many windowed roots" is settled exactly (`= 2^{ω−1}`), and the ONLY remaining Markov question is
realizability — which of these `2^{ω−1}` suborbits carries a Markov triple.  `WindowRealizedUnique`
(§18) is precisely the statement that exactly one does.  This is the full structural reduction; the
residual arithmetic content (which suborbit realizes) is the genuine open Frobenius conjecture. -/

/-- ★★★★★ **Unit cancellation (free action), explicit inverse form**: if `u·s ≡ 1 mod c` then
    `a·u ≡ b·u mod c ⟹ a ≡ b mod c`.  Multiply both sides by the inverse `s` — no subtraction. -/
theorem unit_cancel_of_inv (c u s a b : Nat) (hs : (u * s) % c = 1)
    (h : (a * u) % c = (b * u) % c) : a % c = b % c := by
  calc a % c
      = (a * 1) % c := by rw [Nat.mul_one]
    _ = (a * ((u * s) % c)) % c := by rw [hs]
    _ = (a * (u * s)) % c := (E213.Meta.Nat.MulMod213.mul_mod_right_pure a (u * s) c).symm
    _ = ((a * u) * s) % c := by rw [show a * (u * s) = (a * u) * s from by ring_nat]
    _ = (((a * u) % c) * s) % c := E213.Meta.Nat.MulMod213.mul_mod_left_pure (a * u) s c
    _ = (((b * u) % c) * s) % c := by rw [h]
    _ = ((b * u) * s) % c := (E213.Meta.Nat.MulMod213.mul_mod_left_pure (b * u) s c).symm
    _ = (b * (u * s)) % c := by rw [show (b * u) * s = b * (u * s) from by ring_nat]
    _ = (b * ((u * s) % c)) % c := E213.Meta.Nat.MulMod213.mul_mod_right_pure b (u * s) c
    _ = (b * 1) % c := by rw [hs]
    _ = b % c := by rw [Nat.mul_one]

/-- **Unit cancellation, coprime form**: `gcd(u,c)=1 ⟹ (a·u ≡ b·u ⟹ a ≡ b)` — the inverse is produced
    from coprimality by `modBezout`.  The general statement that the unit-root group acts freely. -/
theorem unit_cancel (c u a b : Nat) (hc : 1 < c) (hu : gcd213 u c = 1)
    (h : (a * u) % c = (b * u) % c) : a % c = b % c := by
  have hs : (u * (E213.Lib.Math.ModArith.ModBezout.modBezout u c).2) % c = 1 := by
    rw [E213.Lib.Math.ModArith.MarkovPrimeFactor.inverse_of_coprime u c
          (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hc)) hu, Nat.mod_eq_of_lt hc]
  exact unit_cancel_of_inv c u (E213.Lib.Math.ModArith.ModBezout.modBezout u c).2 a b hs h

/-- **A `√(−1)` root is a unit, with explicit inverse `c−u`**: `u·(c−u) ≡ 1 mod c`.  From the identity
    `u·(c−u) + (u²+1) = u·c + 1`: the first summand `≡` the residue, `u²+1 ≡ 0`, `u·c ≡ 0`. -/
theorem root_inverse (c u : Nat) (hc : 1 < c) (hu : u ≤ c) (h : (u * u + 1) % c = 0) :
    (u * (c - u)) % c = 1 := by
  have hcu : (c - u) + u = c := E213.Tactic.NatHelper.sub_add_cancel hu
  have hid : u * (c - u) + (u * u + 1) = u * c + 1 := by
    rw [show u * (c - u) + (u * u + 1) = u * ((c - u) + u) + 1 from by ring_nat, hcu]
  have hL : (u * (c - u) + (u * u + 1)) % c = (u * (c - u)) % c := by
    rw [E213.Meta.Nat.AddMod213.add_mod_gen, h, Nat.add_zero, E213.Meta.Nat.AddMod213.mod_mod]
  have hR : (u * c + 1) % c = 1 := by
    rw [E213.Meta.Nat.AddMod213.add_mod_gen, Nat.mul_comm u c,
        E213.Tactic.NatHelper.mul_mod_right c u, Nat.zero_add,
        E213.Meta.Nat.AddMod213.mod_mod, Nat.mod_eq_of_lt hc]
  rw [← hL, hid]; exact hR

/-- ★★★★★ **Orbit-injectivity (`+` side)**: `e·u ≡ u mod c ⟹ e ≡ 1 mod c`.  Free action: cancel the
    unit `u` (inverse `c−u`). -/
theorem root_orbit_inj (c u e : Nat) (hc : 1 < c) (hu : u ≤ c) (hroot : (u * u + 1) % c = 0)
    (h : (e * u) % c = u % c) : e % c = 1 := by
  have hcancel := unit_cancel_of_inv c u (c - u) e 1 (root_inverse c u hc hu hroot)
    (by rw [Nat.one_mul]; exact h)
  rwa [Nat.mod_eq_of_lt hc] at hcancel

/-- ★★★★★ **Orbit-injectivity (`−` side)**: `e·u ≡ (c−1)·u mod c ⟹ e ≡ c−1 mod c`.  The fold-partner
    case — `e·u` lands on `σ(u)`'s orbit iff `e ≡ −1`. -/
theorem root_orbit_inj_neg (c u e : Nat) (hc : 1 < c) (hu : u ≤ c) (hroot : (u * u + 1) % c = 0)
    (h : (e * u) % c = ((c - 1) * u) % c) : e % c = c - 1 := by
  have hc0 : 0 < c := Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hc)
  have hcancel := unit_cancel_of_inv c u (c - u) e (c - 1) (root_inverse c u hc hu hroot) h
  rwa [Nat.mod_eq_of_lt (Nat.sub_lt hc0 (by decide))] at hcancel

/-! ## §25 — the payoff: `WindowRealizedUnique` reduces to one realizability check per phantom orbit

The §24 free action made operational.  Two *distinct* windowed roots `u₁ ≠ u₂` are related by a
**nontrivial** unit-root: with `e = u₂·u₁⁻¹ = u₂·(c−u₁)` one has `e·u₁ ≡ u₂` (`root_quotient`, via
`root_inverse`) and `e ∉ {1, c−1}` (`windowed_distinct_multiplier`, via `root_orbit_inj`-style
cancellation + `window_excludes_partner`).  So `WindowRealizedUnique c` (§18) holds as soon as **no
nontrivial-unit-root image of a realized windowed root is itself realized**
(`windowRealizedUnique_of_orbit`).

This is the full reduction: root-count (`= 2^{ω−1}`, §21–§24) + group structure are closed; the *only*
remaining content is realizability of a single distinguished `±`-suborbit — the genuine open Frobenius
conjecture, now isolated as an `∃!`-style realizability statement rather than a counting problem. -/

/-- **`(c−1)·u ≡ c−u mod c`** (the value of multiplication by `−1`): from `(c−1)·u = c·(u−1)+(c−u)`. -/
theorem neg_one_mul_mod (c u : Nat) (hc : 0 < c) (hu0 : 0 < u) (hu : u ≤ c) :
    ((c - 1) * u) % c = c - u := by
  have hc_pred : c - 1 + 1 = c := Nat.succ_pred_eq_of_pos hc
  have hu_pred : u - 1 + 1 = u := Nat.succ_pred_eq_of_pos hu0
  have hcu : (c - u) + u = c := E213.Tactic.NatHelper.sub_add_cancel hu
  have hL : (c - 1) * u + u = c * u := by
    rw [show (c - 1) * u + u = ((c - 1) + 1) * u from by ring_nat, hc_pred]
  have hR : c * (u - 1) + (c - u) + u = c * u := by
    rw [Nat.add_assoc, hcu, show c * (u - 1) + c = c * ((u - 1) + 1) from by ring_nat, hu_pred]
  have hsplit : (c - 1) * u = c * (u - 1) + (c - u) :=
    E213.Tactic.NatHelper.add_right_cancel_pure (hL.trans hR.symm)
  rw [hsplit, Nat.add_comm (c * (u - 1)) (c - u), Nat.mul_comm c (u - 1),
      E213.Tactic.NatHelper.add_mul_mod_self_pure (c - u) c (u - 1)]
  exact Nat.mod_eq_of_lt (Nat.sub_lt hc hu0)

/-- ★★★★★ **Distinct windowed roots are related by a nontrivial unit-root.**  If `e·u₁ ≡ u₂` with
    `u₁, u₂` distinct windowed roots, then `e ∉ {1, c−1}`: `e ≡ 1` would force `u₂ = u₁`; `e ≡ c−1`
    would force `u₂ = c−u₁`, non-windowed (`window_excludes_partner`).  The §24 free action, applied. -/
theorem windowed_distinct_multiplier (c u₁ u₂ e : Nat) (hc : 0 < c) (hu1pos : 0 < u₁)
    (hu1lt : u₁ < c) (hu1w : 2 * u₁ < c) (hu2w : 2 * u₂ < c) (hne : u₁ ≠ u₂)
    (he : (e * u₁) % c = u₂) : e % c ≠ 1 ∧ e % c ≠ c - 1 := by
  refine ⟨?_, ?_⟩
  · intro h1
    apply hne
    rw [← he, E213.Meta.Nat.MulMod213.mul_mod_left_pure e u₁ c, h1, Nat.one_mul,
        Nat.mod_eq_of_lt hu1lt]
  · intro h2
    have hu2eq : u₂ = c - u₁ := by
      rw [← he, E213.Meta.Nat.MulMod213.mul_mod_left_pure e u₁ c, h2,
          neg_one_mul_mod c u₁ hc hu1pos (Nat.le_of_lt hu1lt)]
    exact absurd hu2w (Nat.not_lt.mpr (Nat.le_of_lt (hu2eq ▸ window_excludes_partner c u₁ hu1w)))

/-- ★★★★★ **`WindowRealizedUnique` reduces to one realizability check per phantom orbit.**  If no
    nontrivial-unit-root image (`e ∉ {1,c−1}`, `e·u₁ ≡ u₂`) of a realized windowed root `u₁` is itself
    realized, then `WindowRealizedUnique c`.  Constructs the multiplier `e = u₂·(c−u₁)` (`root_quotient`
    + `windowed_distinct_multiplier`).  This is the full structural reduction of `ω`-composite Markov
    uniqueness to a single realizability question — the genuine open Frobenius content, isolated. -/
theorem windowRealizedUnique_of_orbit (c : Nat) (hc : 1 < c)
    (H : ∀ u₁ u₂ e, 0 < u₁ → u₁ < c → 2 * u₁ < c → (u₁ * u₁ + 1) % c = 0 →
         u₂ < c → 2 * u₂ < c → (u₂ * u₂ + 1) % c = 0 →
         e % c ≠ 1 → e % c ≠ c - 1 → (e * u₁) % c = u₂ →
         (∃ b₁, b₁ < c ∧ markovEq ((u₁ * b₁) % c) b₁ c) →
         ¬ (∃ b₂, b₂ < c ∧ markovEq ((u₂ * b₂) % c) b₂ c)) :
    WindowRealizedUnique c := by
  intro u₁ u₂ hu1lt hu2lt hu1w hu2w hr1 hr2 hreal1 hreal2
  by_cases hne : u₁ = u₂
  · exact hne
  · exfalso
    have hu1pos : 0 < u₁ := by
      rcases Nat.eq_zero_or_pos u₁ with h0 | hp
      · exfalso
        rw [h0, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hc] at hr1
        exact absurd hr1 (by decide)
      · exact hp
    have hinv : (u₁ * (c - u₁)) % c = 1 := root_inverse c u₁ hc (Nat.le_of_lt hu1lt) hr1
    have hkey : (((u₂ * (c - u₁)) % c) * u₁) % c = u₂ := by
      rw [← E213.Meta.Nat.MulMod213.mul_mod_left_pure (u₂ * (c - u₁)) u₁ c,
          show (u₂ * (c - u₁)) * u₁ = u₂ * ((c - u₁) * u₁) from by ring_nat,
          E213.Meta.Nat.MulMod213.mul_mod_right_pure u₂ ((c - u₁) * u₁) c,
          Nat.mul_comm (c - u₁) u₁, hinv, Nat.mul_one, Nat.mod_eq_of_lt hu2lt]
    have hmul := windowed_distinct_multiplier c u₁ u₂ ((u₂ * (c - u₁)) % c)
      (Nat.lt_of_lt_of_le (by decide) (Nat.le_of_lt hc)) hu1pos hu1lt hu1w hu2w hne hkey
    exact (H u₁ u₂ ((u₂ * (c - u₁)) % c) hu1pos hu1lt hu1w hr1 hu2lt hu2w hr2
      hmul.1 hmul.2 hkey hreal1) hreal2

/-! ## §26 — capstone: `MarkovMaxUnique` from the orbit realizability condition

The whole §20–§25 tower in one entry point.  `MarkovMaxUnique c` holds as soon as **no
nontrivial-unit-root image of a realized windowed root is itself realized** — the single residual
question after the structural reduction.  Everything else (root-count `= 2^{ω−1}`, the unit-root group,
its free action, the window `±`-transversal) is closed `∅`-axiom.

The remaining hypothesis `H` is exactly the open Frobenius content, now in its sharpest form: it is NOT
a counting statement but a *realizability* one — at a composite max `c`, the `2^{ω−1}` candidate
windowed residues are all genuine `√(−1)` roots (so root-counting cannot separate them), and Markov
uniqueness is precisely the assertion that the `±`-fold relation between any two of them obstructs
simultaneous realization.  For prime powers `H` is vacuous (`SqrtUnity = {±1}`, no nontrivial image),
recovering Button; for `ω ≥ 2` it is the live conjecture. -/

/-- ★★★★★ **Capstone — `MarkovMaxUnique` from one orbit realizability check.**  Composes
    `windowRealizedUnique_of_orbit` (§25) with `markov_max_unique_of_window_realized_unique` (§18).
    `H` = "no nontrivial-unit-root image (`e ∉ {1,c−1}`, `e·u₁ ≡ u₂`) of a realized windowed root `u₁`
    is itself realized."  This is the full ∅-axiom reduction of composite Markov uniqueness to a single
    realizability statement — the genuine open content, isolated. -/
theorem markov_max_unique_of_orbit (c : Nat) (hc5 : 5 ≤ c)
    (H : ∀ u₁ u₂ e, 0 < u₁ → u₁ < c → 2 * u₁ < c → (u₁ * u₁ + 1) % c = 0 →
         u₂ < c → 2 * u₂ < c → (u₂ * u₂ + 1) % c = 0 →
         e % c ≠ 1 → e % c ≠ c - 1 → (e * u₁) % c = u₂ →
         (∃ b₁, b₁ < c ∧ markovEq ((u₁ * b₁) % c) b₁ c) →
         ¬ (∃ b₂, b₂ < c ∧ markovEq ((u₂ * b₂) % c) b₂ c)) :
    MarkovMaxUnique c :=
  markov_max_unique_of_window_realized_unique c hc5
    (windowRealizedUnique_of_orbit c (Nat.lt_of_lt_of_le (by decide) hc5) H)

set_option maxRecDepth 400000 in
/-- ★★★★★ **End-to-end: `MarkovMaxUnique 1325` through the orbit tower.**  Discharges the §26 `H` at
    `c = 1325 = 25·53` using the structural machinery: the windowed roots are `{182, 507}` (one
    `decide`), `182` is the phantom (`∀ b, ¬ markovEq …`, one `decide`).  The genuinely new step is the
    `u₁ = u₂ = 507` case: a nontrivial `e` with `e·507 ≡ 507` would force `e ≡ 1` by `root_orbit_inj`
    (§24, free action), contradicting `e ∉ {1, c−1}`.  So the full §20–§26 tower closes a real
    `ω = 2` composite the structural way (not only via the `decide`-wall reducer §19). -/
theorem markov_max_unique_1325_via_orbit :
    E213.Lib.Math.Real213.MarkovUniqueness.MarkovMaxUnique 1325 := by
  apply markov_max_unique_of_orbit 1325 (by decide)
  intro u₁ u₂ e _hu1pos hu1lt hu1w hr1 hu2lt hu2w hr2 he1 _hec he_eq hreal1 hreal2
  have hroots : ∀ u, u < 1325 → (u * u + 1) % 1325 = 0 → 2 * u < 1325 → u = 182 ∨ u = 507 := by
    decide
  have hphantom : ∀ b, b < 1325 → ¬ markovEq ((182 * b) % 1325) b 1325 := by decide
  rcases hroots u₂ hu2lt hr2 hu2w with rfl | rfl
  · obtain ⟨b, hb, hmk⟩ := hreal2; exact absurd hmk (hphantom b hb)
  · rcases hroots u₁ hu1lt hr1 hu1w with rfl | rfl
    · obtain ⟨b, hb, hmk⟩ := hreal1; exact absurd hmk (hphantom b hb)
    · exact he1 (root_orbit_inj 1325 507 e (by decide) (by decide) (by decide)
        (he_eq.trans (Nat.mod_eq_of_lt (by decide)).symm))

/-! ## §27 — which suborbit realises: the tree residue is the distinguished realised windowed root

The Markov-tree determination of the realised `±`-suborbit.  §24–§26 settle the *count* of windowed
roots (`= 2^{ω−1}`) and reduce uniqueness to: among those suborbits, exactly one realises (`H`).  This
section names *which* one — the tree-node residue — and shows it always realises.  So `H`'s entire
open content is the converse: that no *other* suborbit realises. -/

/-- ★★★★★ **The tree residue is THE distinguished realised windowed root.**  For every Stern-Brocot
    path `p`, the node residue `u = markovRes p` mod `c = mNode p` is simultaneously a **windowed
    `√(−1)` root** (`node_window_nat`) and **realised** by the actual Markov triple `(m_r, m_l, c)`
    (`node_realized`, witness `b = m_l`).  So of the `2^{ω−1}` windowed `±`-suborbits, the
    tree-residue one always realises — the distinguished suborbit of the §25 reduction.  The open
    Frobenius content (`H`, §26) is exactly that *no other* suborbit realises. -/
theorem tree_residue_realized_windowed (p : List Bool) :
    (markovRes p).toNat < (mNode p).c.toNat
    ∧ 2 * (markovRes p).toNat < (mNode p).c.toNat
    ∧ ((markovRes p).toNat * (markovRes p).toNat + 1) % (mNode p).c.toNat = 0
    ∧ (∃ b, b < (mNode p).c.toNat ∧
        markovEq (((markovRes p).toNat * b) % (mNode p).c.toNat) b (mNode p).c.toNat) :=
  ⟨(node_window_nat p).1, (node_window_nat p).2.1, (node_window_nat p).2.2, node_realized p⟩

/-! ## §28 — the equivalence: `MarkovMaxUnique c ↔ WindowRealizedUnique c`

The frontier, mechanised.  `markov_max_unique_of_window_realized_unique` (§18) gives `(←)`; this
section adds `(→)` and assembles the iff.  Consequence: since recovery is closed (`slope_path_inj`)
the window-realized-uniqueness *is* Markov uniqueness — for composite `c` the open content `H`
(`windowRealizedUnique_of_orbit`) is therefore **exactly** the Frobenius conjecture at `c`, named in
the repo's orbit/window language.  No `decide`; reuses the §24 unit cancellation and §20 window fold.

`(→)`: two windowed roots `u₁,u₂` realised by triples `(aᵢ,bᵢ,c)` (`aᵢ=(uᵢ·bᵢ)%c`).  After orienting
each to `a≤b`, `MarkovMaxUnique` forces the unordered pairs equal — either aligned (`a₁=a₂, b₁=b₂`,
cancel the unit `b` ⟹ `u₁=u₂`) or crossed (`a₁=b₂, b₁=a₂` ⟹ `u₁u₂≡1` ⟹ `u₂≡c−u₁`, impossible for two
windowed roots by `window_excludes_partner`). -/

/-- First-two-entry symmetry of `markovEq` (`c` stays the maximum). -/
private theorem markovEq_swap12 (x y z : Nat) (h : markovEq x y z) : markovEq y x z := by
  show y * y + x * x + z * z = 3 * y * x * z
  rw [show y * y + x * x + z * z = x * x + y * y + z * z from by ring_nat,
      show 3 * y * x * z = 3 * x * y * z from by ring_nat]
  exact h

/-- ★★★★★ **`(→)` of the frontier equivalence**: `MarkovMaxUnique c → WindowRealizedUnique c`.  The
    residue map `triple ↦ windowed root` is injective on realised roots (cancel the unit middle
    entry), so uniqueness of triples gives uniqueness of realised windowed roots. -/
theorem markovMaxUnique_to_windowRealizedUnique (c : Nat) (hc5 : 5 ≤ c)
    (hmu : E213.Lib.Math.Real213.MarkovUniqueness.MarkovMaxUnique c) : WindowRealizedUnique c := by
  intro u₁ u₂ h1 h2 hw1 hw2 hr1 hr2 hreal1 hreal2
  obtain ⟨b₁, hb1, hmk1⟩ := hreal1
  obtain ⟨b₂, hb2, hmk2⟩ := hreal2
  have hc2 : 2 ≤ c := Nat.le_trans (by decide) hc5
  have hc1 : 1 < c := hc2
  have hc0 : 0 < c := Nat.lt_of_lt_of_le (by decide) hc2
  have ha1lt : (u₁ * b₁) % c < c := Nat.mod_lt _ hc0
  have ha2lt : (u₂ * b₂) % c < c := Nat.mod_lt _ hc0
  -- coprimality of the divisors b₁, b₂ (whatever the orientation)
  have hb1c : gcd213 b₁ c = 1 := by
    rcases Nat.le_total ((u₁ * b₁) % c) b₁ with h | h
    · exact (E213.Lib.Math.Real213.MarkovUniqueness.markov_ordered_coprime _ b₁ c hmk1
        (E213.Lib.Math.Real213.MarkovUniqueness.markov_a_pos hc2 hmk1) h (Nat.le_of_lt hb1)).2.2
    · exact (E213.Lib.Math.Real213.MarkovUniqueness.markov_ordered_coprime b₁ _ c
        (markovEq_swap12 _ _ _ hmk1)
        (E213.Lib.Math.Real213.MarkovUniqueness.markov_a_pos hc2 (markovEq_swap12 _ _ _ hmk1)) h
        (Nat.le_of_lt ha1lt)).2.1
  -- MarkovMaxUnique forces the unordered pair {a₁,b₁} = {a₂,b₂}
  have pairEq : ((u₁ * b₁) % c = (u₂ * b₂) % c ∧ b₁ = b₂)
              ∨ ((u₁ * b₁) % c = b₂ ∧ b₁ = (u₂ * b₂) % c) := by
    rcases Nat.le_total ((u₁ * b₁) % c) b₁ with hab1 | hba1 <;>
    rcases Nat.le_total ((u₂ * b₂) % c) b₂ with hab2 | hba2
    · exact Or.inl (hmu _ b₁ _ b₂ hab1 (Nat.le_of_lt hb1) hab2 (Nat.le_of_lt hb2) hmk1 hmk2)
    · exact Or.inr (hmu _ b₁ b₂ _ hab1 (Nat.le_of_lt hb1) hba2 (Nat.le_of_lt ha2lt)
        hmk1 (markovEq_swap12 _ _ _ hmk2))
    · exact Or.inr (And.intro (hmu b₁ _ _ b₂ hba1 (Nat.le_of_lt ha1lt) hab2 (Nat.le_of_lt hb2)
        (markovEq_swap12 _ _ _ hmk1) hmk2).2 (hmu b₁ _ _ b₂ hba1 (Nat.le_of_lt ha1lt) hab2
        (Nat.le_of_lt hb2) (markovEq_swap12 _ _ _ hmk1) hmk2).1)
    · exact Or.inl (And.intro (hmu b₁ _ b₂ _ hba1 (Nat.le_of_lt ha1lt) hba2 (Nat.le_of_lt ha2lt)
        (markovEq_swap12 _ _ _ hmk1) (markovEq_swap12 _ _ _ hmk2)).2 (hmu b₁ _ b₂ _ hba1
        (Nat.le_of_lt ha1lt) hba2 (Nat.le_of_lt ha2lt) (markovEq_swap12 _ _ _ hmk1)
        (markovEq_swap12 _ _ _ hmk2)).1)
  rcases pairEq with ⟨hae, hbe⟩ | ⟨hae, hbe⟩
  · -- aligned: cancel the unit b₁
    have hcanc : (u₁ * b₁) % c = (u₂ * b₁) % c := by rw [hae, hbe]
    have := unit_cancel c b₁ u₁ u₂ hc1 hb1c hcanc
    rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
  · -- crossed: u₁·u₂ ≡ 1 ⟹ u₂ ≡ c−u₁, impossible for two windowed roots
    exfalso
    have key : ((u₂ * u₁) * b₁) % c = (1 * b₁) % c := by
      rw [show (u₂ * u₁) * b₁ = u₂ * (u₁ * b₁) from by ring_nat,
          E213.Meta.Nat.MulMod213.mul_mod_right_pure u₂ (u₁ * b₁) c, hae, ← hbe,
          Nat.one_mul, Nat.mod_eq_of_lt hb1]
    have hu2u1 : (u₂ * u₁) % c = 1 := by
      have := unit_cancel c b₁ (u₂ * u₁) 1 hc1 hb1c key
      rwa [Nat.mod_eq_of_lt hc1] at this
    have hu1pos : 0 < u₁ := by
      rcases Nat.eq_zero_or_pos u₁ with h0 | hp
      · exfalso
        rw [h0, Nat.zero_mul, Nat.zero_add, Nat.mod_eq_of_lt hc1] at hr1
        exact absurd hr1 (by decide)
      · exact hp
    have hinv : (u₁ * (c - u₁)) % c = 1 := root_inverse c u₁ hc1 (Nat.le_of_lt h1) hr1
    have hcross : (u₂ * u₁) % c = ((c - u₁) * u₁) % c := by
      rw [hu2u1, Nat.mul_comm (c - u₁) u₁, hinv]
    have hu2eq := unit_cancel_of_inv c u₁ (c - u₁) u₂ (c - u₁) hinv hcross
    rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (Nat.sub_lt hc0 hu1pos)] at hu2eq
    exact Nat.lt_irrefl c
      (Nat.lt_trans (hu2eq.symm ▸ window_excludes_partner c u₁ hw1) hw2)

/-- ★★★★★ **The frontier equivalence**: `MarkovMaxUnique c ↔ WindowRealizedUnique c` (`5 ≤ c`).  Both
    directions ∅-axiom: `(→)` cancels the unit middle entry, `(←)` is the tree recovery
    (`slope_path_inj`).  So the §20–§27 window/orbit reduction is not merely *sufficient* for Markov
    uniqueness — it is **equivalent** to it.  For composite `c`, with `windowRealizedUnique_of_orbit`,
    the realisability hypothesis `H` is therefore exactly the Frobenius conjecture at `c`, named in the
    repo's orbit language. -/
theorem markovMaxUnique_iff_windowRealizedUnique (c : Nat) (hc5 : 5 ≤ c) :
    E213.Lib.Math.Real213.MarkovUniqueness.MarkovMaxUnique c ↔ WindowRealizedUnique c :=
  ⟨markovMaxUnique_to_windowRealizedUnique c hc5,
   markov_max_unique_of_window_realized_unique c hc5⟩

end E213.Lib.Math.Real213.SternBrocotMarkov
