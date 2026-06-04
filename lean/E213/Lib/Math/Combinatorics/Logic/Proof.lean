import E213.Lib.Math.Combinatorics.Logic.Predicate

/-!
# Logic — Proof = trajectory

In 213, a proof is a **finite path** in the dyadic decision tree.
Each step = one bisection = one bit of evidence.  The "proof
object" is the `List Bool` representing the trajectory taken.

Atomic content:
  * `Trajectory := List Bool` — the proof path.
  * `proofLength` = number of bits / decisions = `List.length`.
  * `compose` = path concatenation = transitive logical inference.
  * `proof_length_zero`, `proof_length_succ` — atomic structure.

Cut elimination = collapsing a path with `[..., true, false, ...]`
inverse pairs.  Normalisation = walking the path to its terminal
decision.  Both expressible via `List Bool` operations.
-/

namespace E213.Lib.Math.Combinatorics.Logic.Proof

/-- A proof object is a trajectory: finite sequence of decisions. -/
abbrev Trajectory := List Bool

/-- The empty trajectory (axiomatic / immediate truth). -/
def trivialProof : Trajectory := []

/-- Proof length = number of decisions (= bit count). -/
def proofLength (t : Trajectory) : Nat := t.length

/-- Trivial proof has length 0 (rfl). -/
theorem proofLength_trivial : proofLength trivialProof = 0 := rfl

/-- Single-step proof has length 1. -/
theorem proofLength_singleton (b : Bool) : proofLength [b] = 1 := rfl

/-- Compose two proofs: concatenate trajectories.  Transitive
    logical inference. -/
def compose (t₁ t₂ : Trajectory) : Trajectory := t₁ ++ t₂

/-- Composition with trivial proof is identity. -/
theorem compose_trivial_left (t : Trajectory) :
    compose trivialProof t = t := List.nil_append t

/-- Length composition (additive). -/
theorem proofLength_compose : ∀ t₁ t₂ : Trajectory,
    proofLength (compose t₁ t₂) = proofLength t₁ + proofLength t₂
  | [], t₂ => by show t₂.length = 0 + t₂.length; rw [Nat.zero_add]
  | _ :: t₁, t₂ => by
    have ih : (t₁ ++ t₂).length = t₁.length + t₂.length :=
      proofLength_compose t₁ t₂
    show (t₁ ++ t₂).length + 1 = t₁.length + 1 + t₂.length
    rw [ih, Nat.add_right_comm]

/-- ★ **Proof-by-trajectory is finite** ★ — every proof has a
    finite, computable length.  No "infinite proof tree" possible
    in 213's bisection regime. -/
theorem proof_is_finite (t : Trajectory) :
    ∃ n : Nat, proofLength t = n := ⟨t.length, rfl⟩

/-- The "proof of `true`" is trivial (length 0). -/
def proofOfTrue : Trajectory := trivialProof

/-- ★ **Proof normalization (skeleton)** ★ — folding consecutive
    decisions; `[true, false]` is a "decided then undecided" pair.
    Full normalization (cut elimination) is left as continuation. -/
def normalize : Trajectory → Trajectory
  | [] => []
  | [b] => [b]
  | a :: b :: rest =>
    if a = b then a :: normalize (b :: rest)
    else normalize rest  -- mutual cancellation

/-- Normalize of trivial = trivial (rfl). -/
theorem normalize_trivial : normalize trivialProof = trivialProof := rfl

end E213.Lib.Math.Combinatorics.Logic.Proof
