import E213.Lib.Math.CayleyDickson.Levels.CayleyMoufang
import E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy
import E213.Meta.Algebra213.CDDoubleFlexible

/-!
# `FlexAlt213 Cayley` (Type A L3 integer octonions)

Cayley = `CDDouble Lipschitz` is an **alternative** normed *-algebra with a
scalar (central + nuclear) involution trace, i.e. a `FlexAlt213`.  We
register the instance by bridging each new field through
`toCDDouble : Cayley → CDDouble Lipschitz` (the same bridge `CayleyMoufang`
uses), backed by the generic `CDDouble`-over-`TraceNormed213` foundations
in `CDDoubleMoufang` (`cd_ofInt_nuc_{l,m,r}`, `cd_self_add_conj`,
`cd_conj_mul_self`):

  * `alt_left` / `alt_right` / `flexible` — `CayleyHeavy` (octonions are
    alternative);
  * `trace` / `self_add_conj` — `cd_self_add_conj`;
  * `conj_mul_self` — `cd_conj_mul_self`;
  * `ofInt_nuc_{l,m,r}` — `cd_ofInt_nuc_{l,m,r}`.

Once registered, the abstract `FlexAlt213` toolkit (`flex_cross_pair`,
`conj_sandwich`, `mm_conj`, `skew_conj`, `flex_polar`, …) specialises to
Cayley — the components of `Sedenion = CDDouble Cayley` flexibility.
-/

namespace E213.Lib.Math.CayleyDickson.Levels.Cayley

open E213.Meta.Algebra213
open E213.Lib.Math.CayleyDickson.Tower.CDDouble

/-- Cayley (octonion) trace: the Lipschitz trace of the real component. -/
def cay_trace (a : Cayley) : Int := cdm_trace (toCDDouble a)

/-- Trace polarization: `a + conj a = ofInt (trace a)`. -/
theorem cay_self_add_conj (a : Cayley) :
    a + Cayley.conj a = ofInt (cay_trace a) := by
  apply toCDDouble_inj
  rw [toCDDouble_add, toCDDouble_conj, toCDDouble_ofInt]
  exact cd_self_add_conj (toCDDouble a)

/-- Reverse self-norm: `conj a · a = ofInt (normSq a)`. -/
theorem cay_conj_mul_self (a : Cayley) :
    Cayley.conj a * a = ofInt (E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy.normSq a) := by
  apply toCDDouble_inj
  rw [toCDDouble_mul, toCDDouble_conj, toCDDouble_ofInt]
  exact cd_conj_mul_self (toCDDouble a)

/-- `ofInt` scalars are left-nuclear. -/
theorem cay_ofInt_nuc_l (z : Int) (a b : Cayley) :
    (ofInt z * a) * b = ofInt z * (a * b) := by
  apply toCDDouble_inj
  repeat rw [toCDDouble_mul]
  rw [toCDDouble_ofInt]
  exact cd_ofInt_nuc_l z (toCDDouble a) (toCDDouble b)

/-- `ofInt` scalars are middle-nuclear. -/
theorem cay_ofInt_nuc_m (z : Int) (a b : Cayley) :
    (a * ofInt z) * b = a * (ofInt z * b) := by
  apply toCDDouble_inj
  repeat rw [toCDDouble_mul]
  rw [toCDDouble_ofInt]
  exact cd_ofInt_nuc_m z (toCDDouble a) (toCDDouble b)

/-- `ofInt` scalars are right-nuclear. -/
theorem cay_ofInt_nuc_r (z : Int) (a b : Cayley) :
    a * (b * ofInt z) = (a * b) * ofInt z := by
  apply toCDDouble_inj
  repeat rw [toCDDouble_mul]
  rw [toCDDouble_ofInt]
  exact cd_ofInt_nuc_r z (toCDDouble a) (toCDDouble b)

/-- ★ `FlexAlt213 Cayley` — integer octonions as an alternative normed
    *-algebra with scalar-involution trace.  Reuses the existing
    `MoufangIntegerNormed213 Cayley`; adds trace, reverse-norm,
    nuclearity, and the three alternativity laws. -/
instance : FlexAlt213 Cayley where
  trace         := cay_trace
  self_add_conj := cay_self_add_conj
  conj_mul_self := cay_conj_mul_self
  ofInt_nuc_l   := cay_ofInt_nuc_l
  ofInt_nuc_m   := cay_ofInt_nuc_m
  ofInt_nuc_r   := cay_ofInt_nuc_r
  alt_left      := E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy.alt_left
  alt_right     := E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy.alt_right
  flexible      := E213.Lib.Math.CayleyDickson.Levels.CayleyHeavy.flexible

/-! ## Sedenion-flexibility components (`Sedenion = CDDouble Cayley`)

The `re`/`im` components of `(a·b)·a = a·(b·a)` on `Sedenion`, expressed as
pure `Cayley` identities in the four octonion coordinates
`p = a.re, q = a.im, r = b.re, s = b.im`.  Each is assembled from the
`FlexAlt213 Cayley` toolkit:

  * `re`: base `flexible` (`L1=R1`) + `conj_sandwich` (`L4=R3`) +
    `flex_cross_pair` (the cross-pair);
  * `im`: `mm_conj` + `skew_conj` (the skew-associator conj-invariance),
    with the `q·(s̄·q)` diagonal cancelling directly.
-/

/-- `re`-component of Sedenion flexibility. -/
theorem flexible_re (p q r s : Cayley) :
    (p * r + -(s.conj * q)) * p + -(q.conj * (s * p + q * r.conj))
      = p * (r * p + -(q.conj * s)) + -((q * r + s * p.conj).conj * q) := by
  have cm : ∀ x y : Cayley, (x * y).conj = y.conj * x.conj :=
    fun x y => NonAssocStarRing213.conj_mul x y
  have ca : ∀ x y : Cayley, (x + y).conj = x.conj + y.conj :=
    fun x y => NonAssocStarRing213.conj_add x y
  have cc : ∀ x : Cayley, x.conj.conj = x := fun x => NonAssocStarRing213.conj_conj x
  have hfl : (p * r) * p = p * (r * p) := FlexAlt213.flexible p r
  have hcs : q.conj * (q * r.conj) = (r.conj * q.conj) * q :=
    FlexAlt213.conj_sandwich q r
  have hcp : (s.conj * q) * p + q.conj * (s * p)
           = p * (q.conj * s) + (p * s.conj) * q :=
    FlexAlt213.flex_cross_pair p q s
  have hcj : (q * r + s * p.conj).conj = r.conj * q.conj + p * s.conj := by
    rw [ca (q * r) (s * p.conj), cm q r, cm s p.conj, cc p]
  have hAB : -((s.conj * q) * p) + -(q.conj * (s * p))
           = -(p * (q.conj * s)) + -((p * s.conj) * q) := by
    rw [← NonAssocRing213.neg_add ((s.conj * q) * p) (q.conj * (s * p)), hcp,
        NonAssocRing213.neg_add (p * (q.conj * s)) ((p * s.conj) * q)]
  rw [NonAssocRing213.add_mul (p * r) (-(s.conj * q)) p,
      NonAssocRing213.neg_mul (s.conj * q) p,
      NonAssocRing213.mul_add q.conj (s * p) (q * r.conj),
      NonAssocRing213.neg_add (q.conj * (s * p)) (q.conj * (q * r.conj)),
      hfl, hcs, hcj,
      NonAssocRing213.mul_add p (r * p) (-(q.conj * s)),
      NonAssocRing213.mul_neg p (q.conj * s),
      NonAssocRing213.add_mul (r.conj * q.conj) (p * s.conj) q,
      NonAssocRing213.neg_add ((r.conj * q.conj) * q) ((p * s.conj) * q),
      NonAssocRing213.add_assoc (p * (r * p)) (-((s.conj * q) * p))
        (-(q.conj * (s * p)) + -((r.conj * q.conj) * q)),
      ← NonAssocRing213.add_assoc (-((s.conj * q) * p)) (-(q.conj * (s * p)))
        (-((r.conj * q.conj) * q)),
      hAB,
      NonAssocRing213.add_assoc (p * (r * p)) (-(p * (q.conj * s)))
        (-((r.conj * q.conj) * q) + -((p * s.conj) * q)),
      ← NonAssocRing213.add_assoc (-(p * (q.conj * s))) (-((r.conj * q.conj) * q))
        (-((p * s.conj) * q)),
      NonAssocRing213.add_right_comm (-(p * (q.conj * s))) (-((r.conj * q.conj) * q))
        (-((p * s.conj) * q))]

/-- `im`-component of Sedenion flexibility. -/
theorem flexible_im (p q r s : Cayley) :
    q * (p * r + -(s.conj * q)) + (s * p + q * r.conj) * p.conj
      = (q * r + s * p.conj) * p + q * (r * p + -(q.conj * s)).conj := by
  have cm : ∀ x y : Cayley, (x * y).conj = y.conj * x.conj :=
    fun x y => NonAssocStarRing213.conj_mul x y
  have ca : ∀ x y : Cayley, (x + y).conj = x.conj + y.conj :=
    fun x y => NonAssocStarRing213.conj_add x y
  have cc : ∀ x : Cayley, x.conj.conj = x := fun x => NonAssocStarRing213.conj_conj x
  have cn : ∀ x : Cayley, (-x).conj = -(x.conj) := fun x => NonAssocStarRing213.conj_neg x
  have hmm : (s * p) * p.conj = (s * p.conj) * p := FlexAlt213.mm_conj s p
  have hsk : q * (p * r) + (q * r.conj) * p.conj
           = (q * r) * p + q * (p.conj * r.conj) := FlexAlt213.skew_conj q p r
  have hcj2 : (r * p + -(q.conj * s)).conj = p.conj * r.conj + -(s.conj * q) := by
    rw [ca (r * p) (-(q.conj * s)), cm r p, cn (q.conj * s), cm q.conj s, cc q]
  rw [NonAssocRing213.mul_add q (p * r) (-(s.conj * q)),
      NonAssocRing213.mul_neg q (s.conj * q),
      NonAssocRing213.add_mul (s * p) (q * r.conj) p.conj,
      NonAssocRing213.add_mul (q * r) (s * p.conj) p,
      hcj2,
      NonAssocRing213.mul_add q (p.conj * r.conj) (-(s.conj * q)),
      NonAssocRing213.mul_neg q (s.conj * q),
      hmm,
      NonAssocRing213.add_assoc (q * (p * r)) (-(q * (s.conj * q)))
        ((s * p.conj) * p + (q * r.conj) * p.conj),
      ← NonAssocRing213.add_assoc (-(q * (s.conj * q))) ((s * p.conj) * p)
        ((q * r.conj) * p.conj),
      NonAssocRing213.add_comm (-(q * (s.conj * q)) + (s * p.conj) * p)
        ((q * r.conj) * p.conj),
      ← NonAssocRing213.add_assoc (q * (p * r)) ((q * r.conj) * p.conj)
        (-(q * (s.conj * q)) + (s * p.conj) * p),
      hsk,
      NonAssocRing213.add_4_swap_mid ((q * r) * p) ((s * p.conj) * p)
        (q * (p.conj * r.conj)) (-(q * (s.conj * q))),
      NonAssocRing213.add_comm ((s * p.conj) * p) (-(q * (s.conj * q)))]

end E213.Lib.Math.CayleyDickson.Levels.Cayley
