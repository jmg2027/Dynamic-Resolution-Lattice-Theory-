import E213.Meta.Tactic.NatHelper
/-!
# Universal Δ⁴ 10-stratum Bool pattern — G111 COH-1 template

`pattern10` and `pattern10_eq_at` consolidate the byte-identical
content of `Prop52.pattern` / `Prop53.pattern` (10-component pattern
over `Cochain 5 2` and `Cochain 5 3`).  Both cochain types are
defeq-equal to `Fin 10 → Bool` (since `binom 5 2 = binom 5 3 = 10`),
so a single generic function + a single PURE pointwise equality
proof serves both.
-/

namespace E213.Lib.Math.Cohomology.Universal.Pattern10

open E213.Tactic.NatHelper (cases_lt_ten)

/-- ★ Generic 10-stratum Bool pattern.  ∅-axiom at def-level.  Used as
    `pattern : Cochain 5 2` and `Cochain 5 3` via the defeq
    `binom 5 2 = binom 5 3 = 10`. -/
def pattern10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Fin 10 → Bool :=
  fun i =>
    match i.val with
    | 0 => b0
    | 1 => b1
    | 2 => b2
    | 3 => b3
    | 4 => b4
    | 5 => b5
    | 6 => b6
    | 7 => b7
    | 8 => b8
    | _ => b9

/-- ★ Generic pointwise pattern equality.  PURE via
    `cases_lt_ten + subst`.  Specialises to `Cochain 5 2/3` at call
    site via defeq. -/
theorem pattern10_eq_at (σ : Fin 10 → Bool) (k : Fin 10) :
    σ k = pattern10
      (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩) (σ ⟨2, by decide⟩)
      (σ ⟨3, by decide⟩) (σ ⟨4, by decide⟩) (σ ⟨5, by decide⟩)
      (σ ⟨6, by decide⟩) (σ ⟨7, by decide⟩) (σ ⟨8, by decide⟩)
      (σ ⟨9, by decide⟩) k := by
  obtain ⟨n, hn⟩ := k
  show σ ⟨n, hn⟩ = pattern10 _ _ _ _ _ _ _ _ _ _ ⟨n, hn⟩
  rcases cases_lt_ten hn with h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> rfl

end E213.Lib.Math.Cohomology.Universal.Pattern10
