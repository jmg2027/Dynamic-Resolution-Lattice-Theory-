# PURE Lean — funext-avoidance pattern catalog

Reusable architectural patterns for closing sequence-level
identities in PURE Lean (∅-axiom, no Mathlib, no propext / Quot.sound
/ Classical / native_decide / funext).

Crystallized in the Math Algebra / Analysis work.
External LLM (Gemini Pro) consultation surfaced the four patterns
in response to a 5-blocker advice prompt; each was implemented in
Lean directly, all PURE.

## Pattern 1 — State Accumulator

**When**: Carry-chain induction appears to require polynomial
branching on prior digit / sequence positions.

**Move**: Compress the carry state to a **single Bool / Nat
constant-size aggregate** that captures everything the next step
needs.

**Witness**: `Lib/Math/NumberSystems/Padic/NegInvolutionFull.lean` +
`NegInvolutionPreserve.lean`.

  The `Zp.neg` carry at position k+1 turns out to be
  `1` iff `all_zero_below x (k+1) = true` (all digits below k+1
  are zero) — a single Bool, regardless of how many digits.

  - `all_zero_below x : Nat → Bool` (constant-size state)
  - `neg_carry_eq_state` — carry reduces to state
  - `neg_preserves_state` — `Zp.neg` preserves the state
  - `zp_neg_neg_digit_at` — full involution at every digit-k

**Key insight**: the polynomial blow-up was apparent, not real.
The relevant state was always 1 bit; the proof structure follows
the state, not the raw history.

## Pattern 2 — Bundled Subtype (with represents-witness)

**When**: An invariant (precision-monotonicity, "is an integer",
"satisfies a side condition") needs to be propagated through
every consumer of a structure.

**Move**: Bundle the invariant **inside** the structure as an
extra field carrying its proof, so downstream consumers receive
it implicitly.  Stronger: bundle a **representation witness** that
collapses the structure into a simpler algebraic class.

**Witness**: `Lib/Math/NumberSystems/Real213/ValidCut/ValidCutFramework.lean` (weak) +
`Lib/Math/NumberSystems/Real213/ValidCut/IntValidCut.lean` (strong).

  `IntValidCut := { cut, represents : Nat, is_integer : cutEq cut
  (constCut represents 1) }` carries "represents an integer" as a
  cutEq witness.  This lets `cutSum_assoc` reduce both
  parenthesizations to `constCut ((a+b)+c) 1`; `Nat.add_assoc`
  finishes.

  The weaker `ValidCut` (precision-monotonicity only) closes the
  framework but not the algebra; the stronger `IntValidCut` closes
  the algebra at the cost of restricting to the integer-extended
  class.

**Key insight**: hypothesis propagation is a code smell; if the
invariant is needed everywhere, it belongs in the type.  And:
the stronger the invariant, the smaller the eligible class but
the cleaner the algebra.

## Pattern 3 — Setoid Category (function equality via equivalence)

**When**: Function equality is required (e.g., `f ∘ g = h`) but
`funext` is not allowed.

**Move**: Define an explicit equivalence relation
`α ≃_X β := ∀ k, …` that captures the desired notion of
"equal at the application level".  Make a `Setoid` instance.
Bundle morphisms as `LensMap α β := { fn, respects : ∀ a b, a ≈ b →
fn a ≈ fn b }`.

**Witness**: `Lib/Math/NumberSystems/Padic/SetoidFramework.lean` +
`SetoidAlgebra.lean` + `ZpSqrtDSetoid.lean`.

  `ZpSeqEquiv x y := ∀ k, x.digits k = y.digits k` (pointwise
  digit equality).

  - `ZpSeqSetoid` — Setoid instance
  - `LensMap α β` — bundled morphism
  - `add_respects`, `neg_respects`, `mul_respects` — Zp ring ops
    preserve the equivalence
  - `zp_neg_neg_equiv_id` — function-level involution `Zp.neg ∘
    Zp.neg ≈ id`
  - Compositional chaining via `ZpSeqEquiv.trans` (triple,
    quadruple negation)

  Lifted to `ZpSqrtDEquiv` for pair-equivalence on the quadratic
  extension `ZpSqrtD = ZpSeq × ZpSeq`.

**Key insight**: function equality is a *decision about what to
call equal*, not a primitive.  Making the decision explicit as a
Setoid lets all reasoning happen at the equivalence level, with
no funext required.

## Pattern 4 — Residual Induction

**When**: Recursive correctness theorem (e.g., Hensel-lifted
inverse / square-root) requires carry-chain analysis that
diverges into polynomially many cases.

**Move**: Reformulate the recurrence at the **truncation /
residual level**: `X_n · Y_n = 1 + p^(n+1) · R_n`.  Express the
n→n+1 step as an exact integer identity on `R_n`, bypassing the
per-digit carry chain.

**Witness**: `Lib/Math/NumberSystems/Padic/HenselResidual.lean` (surfacing
existing `Padic/Hensel.lean`).

  `(Zp.mul x (Zp.invSeq x n)).trunc (n+1) = 1` for every n.

  - `residual_induction_correct` — truncation correctness at
    every n
  - `residual_induction_full_correct` — same for the diagonal
    `Zp.invFull`
  - `residual_induction_unique` — truncation-level uniqueness

  The Hensel step `Y_{n+1} = Y_n · (2 - X_n · Y_n)` is the
  classical formulation; its truncation-correctness recurrence
  IS the residual induction.

**Key insight**: when the carry chain is the obstacle, lift to
truncation arithmetic.  The recurrence at that level is
`Nat`-/`Int`-decidable; no carry tracking required.

## Cross-pattern relationships

| Pattern | 213 anchor | What it concretizes |
|---|---|---|
| State Accumulator | `seed/AXIOM/05_no_exterior.md` §5 self-pointing | Self-pointing affects next step only through *current* state |
| Bundled Subtype | `seed/AXIOM/05_no_exterior.md` §5.4 dichotomy avoidance | Invariant lives *inside* structure, not as external dichotomy |
| Setoid Category | `Lens/Foundations/SemanticAtom.lean` | Internal-relation equality, no external judge |
| Residual Induction | `seed/AXIOM/01_residue.md` | Trajectory-as-witness at the *truncation* level, not raw history |

All four patterns derive from the same 213-native stance: *equality
is internal consistency of distinguishing trajectories, never an
external authority claim on the system*.

## Methodology meta-rule

When a sequence-level identity blocks PURE closure, the first
move should be:

1. **State the carry / dependence structure** — what does the
   next step actually need from prior history?
2. **Compress to constant-size state** (Pattern 1) or **bundle
   into the type** (Pattern 2).
3. **If function equality is needed**, lift to Setoid (Pattern 3).
4. **If the recurrence is the obstacle**, reformulate at
   truncation (Pattern 4).

If none apply, the blocker may be genuinely structural (e.g.,
requires new cohomology infrastructure as in higher Steenrod
operations beyond K_{3,2}^{(c=2)} k = 2).

## How to verify

```bash
cd lean
lake build E213.Lib.Math.NumberSystems.Padic.NegInvolutionPreserve  # Pattern 1
lake build E213.Lib.Math.NumberSystems.Real213.ValidCut.IntValidCut           # Pattern 2
lake build E213.Lib.Math.NumberSystems.Padic.SetoidFramework         # Pattern 3
lake build E213.Lib.Math.NumberSystems.Padic.HenselResidual          # Pattern 4

python3 tools/scan_axioms.py E213.Lib.Math.NumberSystems.Padic.NegInvolutionPreserve
# ★ 4 PURE / 0 DIRTY — includes zp_neg_neg_digit_at (full involution)
```

## Citation guidance

  · `theory/essays/methodology/pure_funext_avoidance.md` (essay-side narrative)
  · This chapter (catalog-side reference)
  · `HANDOFF.md` (current session state)
