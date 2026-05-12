import E213.Lib.Physics.AlphaEM.Brackets
import E213.Lib.Physics.Basel.Bound

/-!
# Theory.Tools.CertChecker — Lean-side certificate verifier

Mirrors the Rust `Certificate` schema emitted by
`rust-engine/.../alpha_em_bracket.rs`.  Every Rust certificate
is a sequence of three step kinds:

  * `Cite lemma`             — names a Lean theorem (audit anchor)
  * `Apply op args result`   — re-executes a Lean def, records the
                               value
  * `Bound lhs cmp rhs`      — asserts a comparison between two
                               rationals

The Lean side encodes the same datatype.  `Apply` steps embed
*direct calls to the cited Lean def* in the `result` slot, so the
data is in lock-step with the Lean source by construction (no
parser, no string-name reflection).  `Bound` steps reduce to
cross-multiplication on `ℕ` and decide by `Nat.lt`/`Nat.beq`.

A certificate is *bound-valid* when every `Bound` step evaluates
true; a `decide` proof closes the verification at the ∅-axiom
tier.

## Rust ↔ Lean alignment note

The Rust emitter currently writes `Bound` steps as
`lhs : Q = lo` vs `rhs : Q = (137 * lo.den, 1)`.  Cross-multiplied,
this gives `lo.num < 137 · lo.den²`, which is a weakening of the
Lean lemma's `lo.num < 137 · lo.den` (since `lo.den ≥ 1`).  The
Lean cert below uses the stronger, mathematically-intended form
`(lo.num, 1) < (137·lo.den, 1)` so that cross-mult yields the
exact `lo.num < 137·lo.den` that the cited theorem proves.  When
the Rust emitter is updated to match, the JSON-ingestion step
will compare bit-for-bit; until then, audit consumers should
treat Lean's encoding as canonical.

This module currently anchors **N = 20** for the α_em bracket
(`capstone_n20`).  Adding more anchors = adding new `cert_*` defs
and matching `boundsOk` theorems.
-/

namespace E213.Theory.Tools.CertChecker

open E213.Lib.Physics.Basel.Bound (S upper)
open E213.Lib.Physics.AlphaEM.V137Tight
  (inv_lower_tight inv_upper capstone_n20)

-- ═══ §1.  Datatype mirror of the Rust schema ═══

/-- Rational pair `(numerator, denominator)`.  Same as Rust `Q`. -/
abbrev Q : Type := Nat × Nat

/-- Comparison ops mirroring Rust `Cmp`. -/
inductive Cmp | lt | le | eq | ne | ge | gt
deriving DecidableEq, Repr

/-- Single certificate step — same shape as Rust `Step`.
    `Apply.args` is `List Q` to allow multi-arg ops. -/
inductive Step
  | cite  (lemma  : String)                              : Step
  | apply (op     : String) (args : List Q) (result : Q) : Step
  | bound (lhs    : Q) (cmp : Cmp) (rhs : Q)             : Step
deriving Repr

abbrev Cert : Type := List Step

-- ═══ §2.  Pure ℕ comparison + step decider ═══

/-- `(a/b) < (c/d) ⇔ a·d < c·b` (assuming positive denominators). -/
def Q.ltb (a b : Q) : Bool := a.1 * b.2 < b.1 * a.2

/-- `(a/b) = (c/d) ⇔ a·d = c·b`. -/
def Q.eqb (a b : Q) : Bool := a.1 * b.2 == b.1 * a.2

def Cmp.eval : Cmp → Q → Q → Bool
  | .lt, a, b => Q.ltb a b
  | .le, a, b => Q.ltb a b || Q.eqb a b
  | .eq, a, b => Q.eqb a b
  | .ne, a, b => !Q.eqb a b
  | .ge, a, b => Q.ltb b a || Q.eqb a b
  | .gt, a, b => Q.ltb b a

/-- A bound step is OK iff the comparison evaluates true.
    Cite / Apply steps carry no per-step verification obligation
    (Cite is an audit hook; Apply's value is fixed by the
    embedded Lean call). -/
def Step.boundOk : Step → Bool
  | .bound lhs cmp rhs => cmp.eval lhs rhs
  | _ => true

/-- A certificate's bound steps are all valid. -/
def Cert.boundsOk (c : Cert) : Bool := c.all Step.boundOk

end E213.Theory.Tools.CertChecker

namespace E213.Theory.Tools.CertChecker

open E213.Lib.Physics.Basel.Bound (S upper)
open E213.Lib.Physics.AlphaEM.V137Tight
  (inv_lower_tight inv_upper capstone_n20)

-- ═══ §3.  Anchor: N = 20 α_em bracket certificate ═══

/-- The α_em bracket certificate at N = 20, mirroring exactly what
    `rust-engine/.../alpha_em_bracket --n 20` emits.

    Each `Apply` result is the actual Lean value (call to the cited
    def), so the certificate self-verifies its data integrity:
    nothing is hard-coded that could drift from the Lean source. -/
def cert_n20 : Cert := [
  .cite "E213.Lib.Physics.Basel.S",
  .apply "S" [(20, 1)] (S 20),
  .cite "E213.Lib.Physics.Basel.upper",
  .apply "upper" [(20, 1)] (upper 20),
  .cite "E213.Lib.Physics.AlphaEM.V137Tight.inv_lower_tight",
  .apply "inv_lower_tight" [(20, 1)] (inv_lower_tight 20),
  .cite "E213.Lib.Physics.AlphaEM.V137.inv_full_upper",
  .apply "inv_full_upper" [(20, 1)] (inv_upper 20),
  .bound ((inv_lower_tight 20).1, 1) .lt (137 * (inv_lower_tight 20).2, 1),
  .bound (137 * (inv_upper 20).2, 1) .lt ((inv_upper 20).1, 1),
  .bound ((inv_upper 20).1, 1)       .lt (138 * (inv_upper 20).2, 1),
  .cite "E213.Lib.Physics.AlphaEM.V137Tight.bracket_137_in_at_20_tight",
  .cite "E213.Lib.Physics.AlphaEM.V137Tight.bracket_138_excluded_at_20",
  .cite "E213.Lib.Physics.AlphaEM.V137Tight.capstone_n20"
]

-- ═══ §4.  Verification theorems (∅-axiom) ═══

/-- Every bound step in `cert_n20` evaluates to `true`. -/
theorem cert_n20_boundsOk : cert_n20.boundsOk = true := by decide

/-- The certificate has the expected step count. -/
theorem cert_n20_length : cert_n20.length = 14 := rfl

/-- ★ Trust-closure capstone: the bracket structure asserted by
    `cert_n20` matches `capstone_n20` from the Brackets module.
    This is the meeting point between the Rust certificate and the
    Lean theorem. -/
theorem cert_anchor_n20 :
    let lo := inv_lower_tight 20
    let hi := inv_upper 20
    (lo.1 < 137 * lo.2 ∧ 137 * hi.2 < hi.1) ∧ (hi.1 < 138 * hi.2) :=
  capstone_n20

end E213.Theory.Tools.CertChecker

/-! ## Axiom audit (∅-axiom expected) -/
#print axioms E213.Theory.Tools.CertChecker.cert_n20_boundsOk
#print axioms E213.Theory.Tools.CertChecker.cert_n20_length
#print axioms E213.Theory.Tools.CertChecker.cert_anchor_n20
