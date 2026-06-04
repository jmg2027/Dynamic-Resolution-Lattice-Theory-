import E213.Lib.Math.Combinatorics.Logic.Predicate
import E213.Lib.Math.Combinatorics.Logic.Intuitionistic
import E213.Lib.Math.Combinatorics.Logic.Proof

/-!
# Logic 213 — Capstone synthesis

Three cluster witnesses + total bundle, all `#print axioms` ∅.

  * `predicate_witness` — De Morgan + double-negation atomic.
  * `intuitionistic_witness` — Bool LEM atomic, no Classical.
  * `proof_witness` — trajectory finiteness + composition additivity.
-/

namespace E213.Lib.Math.Combinatorics.Logic.Capstone

open E213.Lib.Math.Combinatorics.Logic.Predicate
open E213.Lib.Math.Combinatorics.Logic.Intuitionistic
open E213.Lib.Math.Combinatorics.Logic.Proof

/-- ★ **Predicate calculus witness** ★ — atomic Bool truth tables. -/
theorem predicate_witness (p q : Predicate) :
    predEq (notP (notP p)) p
    ∧ predEq (notP (andP p q)) (orP (notP p) (notP q))
    ∧ predEq (andP p truePred) p :=
  ⟨double_neg p, deMorgan_and p q, and_true_id p⟩

/-- ★ **Intuitionistic / constructive witness** ★ — Bool LEM
    is atomic; pointwise `andP p (notP p) = false`. -/
theorem intuitionistic_witness (b : Bool) (p : Predicate) (m k : Nat) :
    (b = true ∨ b = false)
    ∧ andP p (notP p) m k = false :=
  ⟨bool_lem b, and_neg_self_pointwise p m k⟩

/-- ★ **Proof-as-trajectory witness** ★ — proofs are finite
    `List Bool` with additive length. -/
theorem proof_witness (t₁ t₂ : Trajectory) :
    proofLength (compose t₁ t₂) = proofLength t₁ + proofLength t₂
    ∧ proofLength trivialProof = 0 :=
  ⟨proofLength_compose t₁ t₂, proofLength_trivial⟩

/-- ★★★ **Total witness** ★★★ — 4-fact grand bundle. -/
theorem total_witness (p : Predicate) (b : Bool) (m k : Nat)
    (t : Trajectory) :
    predEq (notP (notP p)) p
    ∧ (b = true ∨ b = false)
    ∧ andP p (notP p) m k = false
    ∧ proofLength (compose trivialProof t) = proofLength t :=
  ⟨double_neg p, bool_lem b, and_neg_self_pointwise p m k,
   by rw [compose_trivial_left]⟩

end E213.Lib.Math.Combinatorics.Logic.Capstone
