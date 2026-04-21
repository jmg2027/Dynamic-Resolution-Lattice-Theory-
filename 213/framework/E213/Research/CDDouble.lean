import E213.Research.ZI
import E213.Research.ZIDomain
import E213.Research.ZIHom
import E213.Research.ZIArith

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
the `R4Codomain` typeclass: the result is **non-commutative**
(fails R2), so it cannot serve as a Lens codomain satisfying
R1–R4 in the paper's sense.  It is therefore a concrete
example of how to extend the algebraic zoo *past* what the
Lens-admissibility conditions single out — ℂ is the unique
commutative R4 endpoint; CD doubling continues into
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

namespace E213.Research

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

end E213.Research

namespace E213.Research.Lipschitz

open E213.Research E213.Research.ZI

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

end E213.Research.Lipschitz

namespace E213.Research.Lipschitz

open E213.Research E213.Research.ZI

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

end E213.Research.Lipschitz

namespace E213.Research.Lipschitz

open E213.Research E213.Research.ZI

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
    Lipschitz.conj (u * v) = Lipschitz.conj v * Lipschitz.conj u := by
  apply ext
  · show (u.re * v.re - v.im.conj * u.im).conj
         = v.re.conj * u.re.conj - (-u.im).conj * (-v.im)
    rw [ZI.conj_sub, ZI.conj_mul, ZI.conj_mul, ZI.conj_conj,
        ZI.conj_neg, ZI.neg_mul, ZI.mul_neg, ZI.neg_neg,
        ZI.mul_comm u.re.conj v.re.conj,
        ZI.mul_comm v.im u.im.conj]
  · show -(v.im * u.re + u.im * v.re.conj)
         = (-u.im) * v.re.conj + (-v.im) * (u.re.conj).conj
    rw [ZI.conj_conj, ZI.neg_mul, ZI.neg_mul]
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

end E213.Research.Lipschitz

namespace E213.Research.Lipschitz

open E213.Research.ZI

-- ═══ Lipschitz Add/Neg/Sub (for CD layer 2) ═══

instance : Add Lipschitz := ⟨fun u v => ⟨u.re + v.re, u.im + v.im⟩⟩
instance : Neg Lipschitz := ⟨fun u => ⟨-u.re, -u.im⟩⟩
instance : Sub Lipschitz := ⟨fun u v => u + (-v)⟩

theorem add_re (u v : Lipschitz) : (u + v).re = u.re + v.re := rfl
theorem add_im (u v : Lipschitz) : (u + v).im = u.im + v.im := rfl
theorem neg_re (u : Lipschitz) : (-u).re = -u.re := rfl
theorem neg_im (u : Lipschitz) : (-u).im = -u.im := rfl

end E213.Research.Lipschitz

/-
**Lipschitz universal associativity** `(u·v)·w = u·(v·w)` is a
12-variable polynomial identity over `Int`.  `quad_norm`'s
simp-set plus `omega` handles 6-variable ZI associativity, but
the 12-variable Lipschitz case has cross-terms beyond the
per-variable scope of `omega`'s linear decision procedure.  A
dedicated "tri-factor" tactic would close it.  Deferred.
-/

namespace E213.Research.Lipschitz

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

end E213.Research.Lipschitz

namespace E213.Research.Lipschitz

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

end E213.Research.Lipschitz

namespace E213.Research.Lipschitz

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

end E213.Research.Lipschitz
