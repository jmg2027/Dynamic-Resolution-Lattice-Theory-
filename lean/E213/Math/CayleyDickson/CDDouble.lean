import E213.Math.CayleyDickson.ZI
import E213.Math.CayleyDickson.ZIDomain
import E213.Math.CayleyDickson.ZIHom
import E213.Math.CayleyDickson.ZIArith

/-!
# Research: Cayley–Dickson doubling of ZI → Lipschitz integers

The **integer Lipschitz quaternions** arise as the CD doubling
of the Gaussian integers `ZI`:

  `Lipschitz ≅ ZI ⊕ ZI·j`,  `j² = -1`,  `ij = -ji = k`

with multiplication given by the classical CD formula

  (α, β) · (γ, δ) = (α·γ − conj δ · β,  δ·α + β · conj γ)

and involution

  conj (α, β) = (conj α, -β).

**Relationship to the Lens framework.**  CD doubling *exits*
the `ConjugationCodomain` typeclass: the result is
**non-commutative** (fails the commutative-binary-combine
axiom), so it cannot serve as a Lens codomain satisfying the
codomain hierarchy.  It is therefore a concrete example of how
to extend the algebraic zoo *past* what the Lens-admissibility
conditions single out — ℂ is the unique commutative
ConjugationCodomain endpoint; CD doubling continues into
non-commutative territory (ℍ-like) and beyond.

**Session scope.**  We formalise:
- the structure and multiplication,
- involutivity of `conj`,
- a concrete witness that multiplication is not commutative.

Deeper CD identities (norm multiplicativity, anti-
distributivity `conj(u·v) = conj v · conj u`) are polynomial
identities in 4 integer coordinates, amenable to `quad_norm`-
style tactics; deferred.
-/

namespace E213.Math.CayleyDickson.CDDouble


open E213.Math.CayleyDickson.ZI.ZI
open ZI

/-- The Lipschitz integer quaternion: CD-double of ZI. -/
structure Lipschitz where
  re : ZI
  im : ZI
  deriving DecidableEq

namespace Lipschitz

instance : Zero Lipschitz := ⟨⟨0, 0⟩⟩

/-- The generator `j` (new imaginary). -/
def J : Lipschitz := ⟨0, ⟨1, 0⟩⟩

/-- `I` lifted into the first copy of ZI. -/
def I' : Lipschitz := ⟨ZI.I, 0⟩

end Lipschitz

end E213.Math.CayleyDickson.CDDouble

namespace E213.Math.CayleyDickson.LipschitzLens

open E213.Math.CayleyDickson.CDDouble
open E213.Math.CayleyDickson.CDDouble.Lipschitz

open E213.Math.CayleyDickson.ZI

/-- **CD multiplication** on `Lipschitz`. -/
def mul (u v : Lipschitz) : Lipschitz :=
  ⟨u.re * v.re - v.im.conj * u.im,
   v.im * u.re + u.im * v.re.conj⟩

instance : Mul Lipschitz := ⟨mul⟩

/-- Componentwise equality. -/
theorem ext {u v : Lipschitz} (hr : u.re = v.re) (hi : u.im = v.im) :
    u = v := by cases u; cases v; congr

/-- **Conjugation** on `Lipschitz`: flip imaginary, ZI-conj the real. -/
def conj (u : Lipschitz) : Lipschitz := ⟨u.re.conj, -u.im⟩

/-- `conj` is involutive. -/
theorem conj_conj (u : Lipschitz) : (conj (conj u)) = u := by
  apply ext
  · show u.re.conj.conj = u.re
    exact ZI.conj_conj u.re
  · show -(-u.im) = u.im
    apply ZI.ext
    · show -(-u.im.re) = u.im.re; omega
    · show -(-u.im.im) = u.im.im; omega

/-- `conj` is not the identity. -/
theorem conj_ne_id : (conj : Lipschitz → Lipschitz) ≠ id := by
  intro h
  have hJ : conj J = id J := congrFun h J
  -- conj J = (conj 0, -(⟨1,0⟩)) = (0, ⟨-1, 0⟩)
  -- id J = J = (0, ⟨1, 0⟩)
  -- so need (⟨-1, 0⟩ : ZI) = ⟨1, 0⟩ → contradiction
  have : (conj J).im = (id J).im := by rw [hJ]
  have : (⟨-1, 0⟩ : ZI) = ⟨1, 0⟩ := this
  have : (-1 : Int) = 1 := (ZI.mk.injEq ..).mp this |>.1
  exact absurd this (by decide)

open E213.Math.CayleyDickson.ZI

-- ═══ Non-commutativity of CD multiplication ═══

/-- `I' * J`: via CD formula.  α=I, β=0, γ=0, δ=⟨1,0⟩.
    (I·0 − conj(⟨1,0⟩)·0, ⟨1,0⟩·I + 0·conj(0)) = (0, ⟨0,1⟩). -/
theorem I_mul_J : I' * J = ⟨0, ZI.I⟩ := by
  show mul I' J = ⟨0, ZI.I⟩
  unfold mul
  apply ext
  · show ZI.I * 0 - (⟨1, 0⟩ : ZI).conj * 0 = 0
    apply ZI.ext
    · show _ = (0 : Int); rfl
    · show _ = (0 : Int); rfl
  · show (⟨1, 0⟩ : ZI) * ZI.I + 0 * ZI.I.conj = ZI.I
    apply ZI.ext
    · show _ = (0 : Int); rfl
    · show _ = (1 : Int); rfl

/-- `J * I'`: α=0, β=⟨1,0⟩, γ=I, δ=0.
    (0·I − conj(0)·⟨1,0⟩, 0·0 + ⟨1,0⟩·conj(I)) = (0, ⟨0,-1⟩). -/
theorem J_mul_I : J * I' = ⟨0, ZI.negI⟩ := by
  show mul J I' = ⟨0, ZI.negI⟩
  unfold mul
  apply ext
  · show 0 * ZI.I - (0 : ZI).conj * (⟨1, 0⟩ : ZI) = 0
    apply ZI.ext
    · show _ = (0 : Int); rfl
    · show _ = (0 : Int); rfl
  · show 0 * 0 + (⟨1, 0⟩ : ZI) * ZI.I.conj = ZI.negI
    apply ZI.ext
    · show _ = (0 : Int); rfl
    · show _ = (-1 : Int); rfl

/-- **Multiplication is NOT commutative.**
    `I' * J = ⟨0, i⟩` but `J * I' = ⟨0, -i⟩` — these differ
    (the imaginary component sign flips), reproducing the
    quaternion identity `ij = -ji = k`. -/
theorem mul_not_commutative : ∃ u v : Lipschitz, u * v ≠ v * u := by
  refine ⟨I', J, ?_⟩
  intro h
  rw [I_mul_J, J_mul_I] at h
  have hr : (⟨0, ZI.I⟩ : Lipschitz).im = (⟨0, ZI.negI⟩ : Lipschitz).im := by
    rw [h]
  have : ZI.I = ZI.negI := hr
  have : (1 : Int) = -1 := (ZI.mk.injEq ..).mp this |>.2
  exact absurd this (by decide)

open E213.Math.CayleyDickson.ZI

/-- **Anti-distributivity of `conj` over `mul`** — the CD
    signature: `conj(u·v) = conj v · conj u` with *reversed*
    factor order, in contrast to Lens R4's same-order
    `conj_dist`.  The two agree iff the codomain is
    commutative (then `conj v · conj u = conj u · conj v`).

    Proof: each Lipschitz component is a ZI identity.  The re
    component uses `conj_sub/conj_mul/conj_conj/conj_neg/neg_mul/
    mul_neg/neg_neg/mul_comm`.  The im component similarly via
    `conj_conj/neg_mul` plus Int arithmetic. -/
theorem conj_mul_anti (u v : Lipschitz) :
    conj (u * v) = conj v * conj u := by
  apply ext
  · show (u.re * v.re - v.im.conj * u.im).conj
         = v.re.conj * u.re.conj - (-u.im).conj * (-v.im)
    rw [E213.Math.CayleyDickson.ZIArith.conj_sub, E213.Math.CayleyDickson.ZIHom.conj_mul, E213.Math.CayleyDickson.ZIHom.conj_mul, ZI.conj_conj,
        E213.Math.CayleyDickson.ZIArith.conj_neg, E213.Math.CayleyDickson.ZIArith.neg_mul, E213.Math.CayleyDickson.ZIArith.mul_neg, E213.Math.CayleyDickson.ZIArith.neg_neg,
        E213.Math.CayleyDickson.ZIDomain.mul_comm u.re.conj v.re.conj,
        E213.Math.CayleyDickson.ZIDomain.mul_comm v.im u.im.conj]
  · show -(v.im * u.re + u.im * v.re.conj)
         = (-u.im) * v.re.conj + (-v.im) * (u.re.conj).conj
    rw [ZI.conj_conj, E213.Math.CayleyDickson.ZIArith.neg_mul, E213.Math.CayleyDickson.ZIArith.neg_mul]
    apply ZI.ext
    · show -(v.im.re * u.re.re - v.im.im * u.re.im +
              (u.im.re * v.re.re - u.im.im * (-v.re.im)))
           = -(u.im.re * v.re.re - u.im.im * (-v.re.im))
             + -(v.im.re * u.re.re - v.im.im * u.re.im)
      omega
    · show -(v.im.re * u.re.im + v.im.im * u.re.re +
              (u.im.re * (-v.re.im) + u.im.im * v.re.re))
           = -(u.im.re * (-v.re.im) + u.im.im * v.re.re)
             + -(v.im.re * u.re.im + v.im.im * u.re.re)
      omega

open E213.Math.CayleyDickson.ZI

-- ═══ Lipschitz Add/Neg/Sub (for CD layer 2) ═══

instance : Add Lipschitz := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg Lipschitz := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub Lipschitz := ⟨fun u v => u + (-v)⟩

theorem add_re (u v : Lipschitz) : (u + v).re = u.re + v.re := rfl
theorem add_im (u v : Lipschitz) : (u + v).im = u.im + v.im := rfl
theorem neg_re (u : Lipschitz) : (-u).re = -u.re := rfl
theorem neg_im (u : Lipschitz) : (-u).im = -u.im := rfl

end E213.Math.CayleyDickson.LipschitzLens

/-
**Lipschitz universal associativity** `(u·v)·w = u·(v·w)` is a
12-variable polynomial identity over `Int`.  `quad_norm`'s
simp-set plus `omega` handles 6-variable ZI associativity, but
the 12-variable Lipschitz case has cross-terms beyond the
per-variable scope of `omega`'s linear decision procedure.  A
dedicated "tri-factor" tactic would close it.  Deferred.
-/

namespace E213.Math.CayleyDickson.LipschitzLens

/-- `I' ≠ 0` in Lipschitz. -/
theorem I'_ne_zero : I' ≠ (0 : Lipschitz) := by decide

/-- `J ≠ 0` in Lipschitz. -/
theorem J_ne_zero : J ≠ (0 : Lipschitz) := by decide

/-- **Generator products are non-zero in Lipschitz.**  Pairwise
    R3 at the generator level; full universal R3 (Hurwitz thm)
    is deferred (norm-multiplicativity). -/
theorem mul_generators_ne_zero :
    I' * J ≠ 0 ∧ J * I' ≠ 0 ∧ I' * I' ≠ 0 ∧ J * J ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **Hamilton's identity** at the Lipschitz level: `(ij)² = -1`.
    Since `i · j = k` (via `I_mul_J`), this computes the square
    of the derived third generator and confirms it equals
    `-1_Lipschitz`. -/
theorem K_squared : (I' * J) * (I' * J) = ⟨⟨-1, 0⟩, 0⟩ := by decide

/-- Equivalently: `i · j · j = -i` (one of the four-group
    identities on the quaternion generators). -/
theorem I_J_J : I' * (J * J) = -I' := by decide

/-- `j² = -1`. -/
theorem J_squared : J * J = ⟨⟨-1, 0⟩, 0⟩ := by decide

/-- `i² = -1`. -/
theorem I_squared : I' * I' = ⟨⟨-1, 0⟩, 0⟩ := by decide

-- ═══ Quaternion group Q_8 relations ═══
-- `K := I' * J` is the derived third generator (quaternion k).
-- Q₈ relations verify the classical Hamilton table; each
-- closed by `decide`.

/-- `k := i·j`. -/
def K : Lipschitz := I' * J

-- Check specific Q₈ relations via decide.

/-- `j · k = i`. -/
theorem J_mul_K : J * (I' * J) = I' := by decide

/-- `k · i = j`. -/
theorem K_mul_I : (I' * J) * I' = J := by decide

/-- `j · i = -k`.  (Distinct from `J_mul_I` above which shows
    the same product = `⟨0, negI⟩` directly.) -/
theorem J_mul_I_eq_neg_K : J * I' = -(I' * J) := by decide

/-- `k · j = -i`. -/
theorem K_mul_J : (I' * J) * J = -I' := by decide

/-- `i · k = -j`. -/
theorem I_mul_K : I' * (I' * J) = -J := by decide

-- ═══ Associativity at quaternion basis triples ═══
-- Lipschitz IS associative (quaternion associativity);
-- universal proof deferred.  Basis-level instances via `decide`.

/-- `(i·j)·k = i·(j·k)` where `k := i·j`. -/
theorem assoc_I_J_K : (I' * J) * (I' * J) = I' * (J * (I' * J)) := by decide

/-- `(i·j)·i = i·(j·i)`. -/
theorem assoc_I_J_I : (I' * J) * I' = I' * (J * I') := by decide

/-- `(i·i)·j = i·(i·j)`. -/
theorem assoc_I_I_J : (I' * I') * J = I' * (I' * J) := by decide

/-- `(j·i)·j = j·(i·j)`. -/
theorem assoc_J_I_J : (J * I') * J = J * (I' * J) := by decide

open E213.Math.CayleyDickson.ZI

/-- Lipschitz norm-squared: `u.re.normSq + u.im.normSq`. -/
def normSq (u : Lipschitz) : Int := u.re.normSq + u.im.normSq

/-- `|1|² = 1` (with `1 = ⟨⟨1,0⟩, 0⟩`). -/
theorem normSq_one : normSq ⟨⟨1, 0⟩, 0⟩ = 1 := by decide

/-- `|i|² = 1`. -/
theorem normSq_I : normSq I' = 1 := by decide

/-- `|j|² = 1`. -/
theorem normSq_J : normSq J = 1 := by decide

/-- `|i·j|² = |k|² = 1`. -/
theorem normSq_K : normSq (I' * J) = 1 := by decide

/-- `|1+i|² = 2`. -/
theorem normSq_one_plus_I : normSq (⟨⟨1, 0⟩, 0⟩ + I') = 2 := by decide

/-- `|-u|² = |u|²`. -/
theorem normSq_neg (u : Lipschitz) : normSq (-u) = normSq u := by
  show (-u).re.normSq + (-u).im.normSq = u.re.normSq + u.im.normSq
  unfold ZI.normSq
  show (-u.re).re * (-u.re).re + (-u.re).im * (-u.re).im +
       ((-u.im).re * (-u.im).re + (-u.im).im * (-u.im).im)
     = u.re.re * u.re.re + u.re.im * u.re.im +
       (u.im.re * u.im.re + u.im.im * u.im.im)
  rw [show (-u.re).re = -u.re.re from rfl,
      show (-u.re).im = -u.re.im from rfl,
      show (-u.im).re = -u.im.re from rfl,
      show (-u.im).im = -u.im.im from rfl,
      Int.neg_mul_neg, Int.neg_mul_neg,
      Int.neg_mul_neg, Int.neg_mul_neg]

open E213.Math.CayleyDickson.ZI E213.Tactic

/-- `|I' * J|² = |I'|² * |J|²` at concrete basis.  Sanity
    check before attempting the universal identity. -/
theorem normSq_mul_I_J :
    normSq (I' * J) = normSq I' * normSq J := by decide

/-- `|I'²|² = |I'|² * |I'|² = 1`. -/
theorem normSq_mul_I_I :
    normSq (I' * I') = normSq I' * normSq I' := by decide

/-- `|(1+I') * J|² = |1+I'|² * |J|² = 2 * 1 = 2`. -/
theorem normSq_mul_sum_basis :
    normSq ((⟨⟨1, 0⟩, 0⟩ + I') * J)
      = normSq (⟨⟨1, 0⟩, 0⟩ + I') * normSq J := by decide

end E213.Math.CayleyDickson.LipschitzLens

/-
**Lipschitz universal norm multiplicativity** `|uv|² =
|u|² · |v|²` (Hurwitz identity) is an 8-variable Int-
polynomial identity with ~100 terms on each side.  Beyond
`quad_norm`'s current 2-factor normalisation + omega stack.
A dedicated tactic extension is deferred.
-/

namespace E213.Math.CayleyDickson.LipschitzLens

open E213.Math.CayleyDickson.ZI

-- ═══ Projection simp lemmas for hurwitz_ring tactic ═══

/-- `.re` of `Lipschitz` multiplication. -/
theorem mul_re (u v : Lipschitz) :
    (u * v).re = u.re * v.re - v.im.conj * u.im := rfl

/-- `.im` of `Lipschitz` multiplication. -/
theorem mul_im (u v : Lipschitz) :
    (u * v).im = v.im * u.re + u.im * v.re.conj := rfl

/-- `.re` of `Lipschitz` conjugation. -/
theorem conj_re (u : Lipschitz) : (conj u).re = u.re.conj := rfl

/-- `.im` of `Lipschitz` conjugation. -/
theorem conj_im (u : Lipschitz) : (conj u).im = -u.im := rfl

/-- `.re` of Lipschitz `0`. -/
theorem zero_re : (0 : Lipschitz).re = 0 := rfl

/-- `.im` of Lipschitz `0`. -/
theorem zero_im : (0 : Lipschitz).im = 0 := rfl

open E213.Math.CayleyDickson.ZI

theorem sub_re (u v : Lipschitz) : (u - v).re = u.re - v.re := rfl

theorem sub_im (u v : Lipschitz) : (u - v).im = u.im - v.im := rfl

end E213.Math.CayleyDickson.LipschitzLens
