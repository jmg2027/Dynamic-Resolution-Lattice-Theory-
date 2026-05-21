import E213.Lib.Physics.AlphaEM.Brackets
import E213.Lib.Physics.AlphaEM.StructuralGap
import E213.Lib.Physics.Couplings.AlphaGUT

/-!
# 1/α_em augmented brackets — Dyson tail + SO(10) + Gram self-energy

Single-file consolidation (2026-05-05 merge of `BracketWithDysonTail`,
`SO10`, `GramSelfEnergy`).

Sub-namespaces (preserved):

  * `E213.Lib.Physics.AlphaEM.BracketWithDysonTail` — α_GUT/(NS+1) tail
  * `E213.Lib.Physics.AlphaEM.SO10`                 — α_GUT/(NS²·d) tail (15 ppb)
  * `E213.Lib.Physics.AlphaEM.GramSelfEnergy`       — α_em²/d² (0.18 ppb)

## Convergence chain (Python-verified, Lean-bracketed)

  baseline 5-term:                137.0354548   gap 4 ppm
  + α_GUT/(NS²·d) [SO(10)]:       137.0359966   gap 15 ppb
  + α_em²/d² [Gram self-energy]:  137.0359991   gap 0.18 ppb ★

  22000× tighter than baseline.  Lean certifies bracket containment;
  the GramSelfEnergy `213/10⁸` is α_em²/d² evaluated at observed α_em
  (not derived from atomic principles — see `StructuralGap.lean`).
-/

namespace E213.Lib.Physics.AlphaEM.BracketWithDysonTail

open E213.Lib.Physics.AlphaEM.V137 (inv_full_upper)
open E213.Lib.Physics.AlphaEM.V137Tight (inv_lower_tight)
open E213.Lib.Physics.Basel.Bound (S upper)

/-- inv_lower_tight(N) + 1/(100·upper(N)) as `(num, den)`. -/
def inv_lower_with_tail (N : Nat) : (Nat × Nat) :=
  let p := inv_lower_tight N
  let u := upper N
  (p.1 * (100 * u.1) + u.2 * p.2, p.2 * (100 * u.1))

/-- inv_full_upper(N) + 1/(100·S(N)) as `(num, den)`.  N ≥ 1. -/
def inv_upper_with_tail (N : Nat) : (Nat × Nat) :=
  let P := inv_full_upper N
  let s := S N
  (P.1 * (100 * s.1) + s.2 * P.2, P.2 * (100 * s.1))

/-- ★ Bracket-with-Dyson-tail capstone — bundles N=20/N=50 observed
    containment + N=20 candidate-asymptote containment. -/
theorem bracket_with_dyson_tail_master :
    -- N=20 contains Measurement-Lens 137.036
    (let lo := inv_lower_with_tail 20
     let hi := inv_upper_with_tail 20
     lo.1 * 1000 < 137036 * lo.2 ∧ 137036 * hi.2 < 1000 * hi.1)
    -- N=50 also contains 137.036
    ∧ (let lo := inv_lower_with_tail 50
       let hi := inv_upper_with_tail 50
       lo.1 * 1000 < 137036 * lo.2 ∧ 137036 * hi.2 < 1000 * hi.1)
    -- N=20 contains candidate asymptote 137.03545
    ∧ (let lo := inv_lower_with_tail 20
       let hi := inv_upper_with_tail 20
       lo.1 * 10000 < 1370354 * lo.2 ∧ 1370354 * hi.2 < 10000 * hi.1) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.AlphaEM.BracketWithDysonTail

namespace E213.Lib.Physics.AlphaEM.SO10

open E213.Lib.Physics.Basel.Bound
open E213.Lib.Physics.AlphaEM.V137Tight
open E213.Lib.Physics.AlphaEM.V137

/-! ## SO(10) next-order correction α_GUT/(NS²·d) = α_GUT/45.

  45 admits four atomic readings (Class C):
    NS²·d = 9·5 = 45
    dim adjoint SO(10) = 45
    3 generations × 15 fermions/gen
    NS·(C(d,2) + d) = NS·15 = 45

  Combined Dyson tail: α_GUT·(1/(NS+1) + 1/(NS²·d)) = α_GUT·49/180.
  Effect: candidate asymptote 137.0354548 → 137.0359970 (260× tighter).
  Residual: 15 ppb (still open in Open Problem #1b).
-/

/-- Add tail term `49/(4500·u)`: α_GUT·49/180 = 49/(4500·ζ(2)). -/
def add_so10_tail (p : Nat × Nat) (u : Nat × Nat) : Nat × Nat :=
  (p.1 * (4500 * u.1) + 49 * u.2 * p.2, p.2 * (4500 * u.1))

def inv_lower_so10 (N : Nat) : Nat × Nat :=
  add_so10_tail (inv_lower_tight N) (upper N)

def inv_upper_so10 (N : Nat) : Nat × Nat :=
  add_so10_tail (inv_upper N) (S N)

/-- ★ SO(10) augmented α_em capstone — atomic 45-reading, combined
    Dyson-tail rationals, lower<upper sanity, bracket containment of
    observed 137.036 and candidate 137.0360 at N=20. -/
theorem alpha_em_so10_capstone :
    -- 45 atomic reading: NS²·d = 9·5 = 45
    3 * 3 * 5 = 45
    -- combined Dyson tail rational 49/180
    ∧ 1 * 45 + 1 * 4 = 49 ∧ 4 * 45 = 180
    -- lower < upper at N=10 (sanity)
    ∧ (let lo := inv_lower_so10 10
       let hi := inv_upper_so10 10
       lo.1 * hi.2 < hi.1 * lo.2)
    -- bracket contains observed 137.036 at N=20
    ∧ (let lo := inv_lower_so10 20
       let hi := inv_upper_so10 20
       lo.1 * 1000 < 137036 * lo.2 ∧ 137036 * hi.2 < 1000 * hi.1)
    -- bracket contains candidate 137.0360 at N=20
    ∧ (let lo := inv_lower_so10 20
       let hi := inv_upper_so10 20
       lo.1 * 10000 < 1370360 * lo.2 ∧ 1370360 * hi.2 < 10000 * hi.1)
    -- ceiling sanity: hi < 138
    ∧ (let hi := inv_upper_so10 20
       hi.1 < 138 * hi.2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.AlphaEM.SO10

namespace E213.Lib.Physics.AlphaEM.GramSelfEnergy

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Physics.AlphaEM.SO10

/-! ## Gram self-energy α_em²/d² → 0.18 ppb residual.

  d² = 25 readings: block-pair total, Gram matrix DOF, α_GUT factor.
  α_em²/d² = "self-coupling at Gram dim".

  Self-consistency polynomial: 25·y³ = 25·X·y² + 1
  (X = 5-term + SO(10), y = 1/α_em).

  ** Caveat **: `213/10⁸` is α_em²/d² evaluated at observed α_em
  ≈ 1/137.036 — NOT derived from atomic principles.  Lean certifies
  bracket containment given this constant; structural derivation
  remains in `StructuralGap.lean`.
-/

/-- α_em²/d² ≈ 213/10⁸ (3.6 ppb error in input). -/
def alpha_em_sq_over_d_sq_approx : Nat × Nat := (213, 100000000)

/-- Add Gram self-energy to a (num, den) bracket entry. -/
def add_gram_self_energy (p : Nat × Nat) : Nat × Nat :=
  (p.1 * 100000000 + 213 * p.2, p.2 * 100000000)

def inv_lower_aug (N : Nat) : Nat × Nat :=
  add_gram_self_energy (inv_lower_so10 N)

def inv_upper_aug (N : Nat) : Nat × Nat :=
  add_gram_self_energy (inv_upper_so10 N)

/-- High-precision: 137.035999 = (137035999, 10⁶) ∈ bracket at N=20.
    Externally consumed by `AlphaEM.Capstone`. -/
theorem aug_bracket_contains_observed_high_precision :
    let lo := inv_lower_aug 20
    let hi := inv_upper_aug 20
    lo.1 * 1000000 < 137035999 * lo.2
    ∧ 137035999 * hi.2 < 1000000 * hi.1 := by decide

/-- ★ Gram self-energy augmented α_em capstone — d²=25 atomic reading,
    sanity, observed-bracket containment at multiple precisions. -/
theorem alpha_em_gram_capstone :
    -- d² = 25 atomic
    d * d = 25 ∧ 5 * 5 = 25
    -- lower < upper at N=10
    ∧ (let lo := inv_lower_aug 10
       let hi := inv_upper_aug 10
       lo.1 * hi.2 < hi.1 * lo.2)
    -- bracket contains 137.036 at N=20
    ∧ (let lo := inv_lower_aug 20
       let hi := inv_upper_aug 20
       lo.1 * 1000 < 137036 * lo.2 ∧ 137036 * hi.2 < 1000 * hi.1)
    -- bracket contains 137.035999 (high precision) at N=20
    ∧ (let lo := inv_lower_aug 20
       let hi := inv_upper_aug 20
       lo.1 * 1000000 < 137035999 * lo.2
       ∧ 137035999 * hi.2 < 1000000 * hi.1)
    -- lower < upper at N=20 (sharper sanity)
    ∧ (let lo := inv_lower_aug 20
       let hi := inv_upper_aug 20
       lo.1 * hi.2 < hi.1 * lo.2) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.AlphaEM.GramSelfEnergy
