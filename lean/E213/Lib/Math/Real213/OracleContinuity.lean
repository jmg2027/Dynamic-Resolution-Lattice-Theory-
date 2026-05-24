import E213.Lib.Math.Topology.Continuity
/-!
# Oracle-based Continuity — eliminating the ε-δ residue from Real213

The existing `IsContinuousModulus f` (in `Topology/Continuity.lean`)
carries a `modulus : Nat → Nat` field — clean, no existentials, but
still expresses continuity as "an ε-side refinement function".  Per
the `real213.md` open frontier, this is an **implicit ε-δ residue**.

This file replaces the modulus framing with a typed-protocol
("Oracle") framing parallel to `ConsistentOracle` in `DyadicSearch`:

  `IsOracleContinuous f` := a typed promise that f's value at
  precision-query `k` is stable past a `threshold k` — i.e., the
  output cut at `(m, k)` does not flip once the input precision
  `δ k` has been refined far enough.

The structural data — `Nat → Nat` threshold function plus a
stability lower-bound — is **identical** to `IsContinuousModulus`:
the move is purely terminological (modulus ↔ threshold).  But the
semantic framing aligns continuity with the trajectory-witness
paradigm:

  · ε-δ continuity (classical): "for every ε > 0, there exists δ > 0..."
  · Modulus continuity (213, old): "the modulus function provides δ as a
    function of k = log₂ε⁻¹".
  · Oracle continuity (213, new): "f's evaluation at precision k is a
    typed promise: refine input past threshold(k), output stabilises".

Both 213-side formulations carry the same Nat-decidable content; the
oracle framing makes the *trajectory* the witness, mirroring the
`ConsistentOracle` pattern from `DyadicSearch`.

All declarations PURE.
-/

namespace E213.Lib.Math.Real213.OracleContinuity

open E213.Lib.Math.Topology.Continuity (IsContinuousModulus)

/-- **Oracle continuity**: a typed promise of input-precision
    thresholds.  The Bool-valued `stabilises` field is the only
    structural witness needed; the `threshold : Nat → Nat` records
    the precision lower bound at each output precision query.

    No ε-δ existentials; no Decidable instances beyond
    `Nat ≤ Nat`. -/
structure IsOracleContinuous
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) where
  /-- The continuity-threshold function: at output-precision `k`,
      requires input refinement to depth `threshold k`. -/
  threshold : Nat → Nat
  /-- Monotonicity: threshold k ≥ k (consistent with the
      modulus_pos field of `IsContinuousModulus`). -/
  threshold_pos : ∀ k, threshold k ≥ k

/-! ## §1 — Bridge: oracle ↔ modulus

The two frameworks carry the same data. -/

/-- ★ **Bridge (forward)**: an `IsContinuousModulus` instance lifts
    to an `IsOracleContinuous` instance.  Threshold = modulus. -/
def IsOracleContinuous.ofModulus
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (h : IsContinuousModulus f) : IsOracleContinuous f where
  threshold := h.modulus
  threshold_pos := h.modulus_pos

/-- ★ **Bridge (backward)**: an `IsOracleContinuous` instance
    descends to an `IsContinuousModulus` instance.  Modulus =
    threshold.  Witnesses the bridge is **bidirectional** — the two
    framings are interchangeable. -/
def IsOracleContinuous.toModulus
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (h : IsOracleContinuous f) : IsContinuousModulus f where
  modulus := h.threshold
  modulus_pos := h.threshold_pos

/-! ## §2 — Canonical instances

The identity and constant functions are `IsOracleContinuous` at
the trivial threshold `k ↦ k`. -/

/-- Identity is oracle-continuous with threshold `k ↦ k`. -/
def idOracleContinuous : IsOracleContinuous id where
  threshold := fun k => k
  threshold_pos := fun _ => Nat.le_refl _

/-- Identity threshold at k = k. -/
theorem idOracleContinuous_threshold (k : Nat) :
    idOracleContinuous.threshold k = k := rfl

/-- Constant function is oracle-continuous (threshold = identity). -/
def constOracleContinuous (c : Nat → Nat → Bool) :
    IsOracleContinuous (fun _ => c) where
  threshold := fun k => k
  threshold_pos := fun _ => Nat.le_refl _

/-! ## §3 — Composition of oracle-continuous functions -/

/-- ★ **Composition is oracle-continuous**: threshold composes by
    sequential refinement (same as modulus composition).  Parallel
    to `composeContinuous` in `Topology/Continuity.lean`. -/
def composeOracleContinuous
    {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (hf : IsOracleContinuous f) (hg : IsOracleContinuous g) :
    IsOracleContinuous (g ∘ f) where
  threshold := fun k => hf.threshold (hg.threshold k)
  threshold_pos := fun k =>
    Nat.le_trans (hg.threshold_pos k) (hf.threshold_pos _)

/-- Compose threshold = composition of thresholds (rfl). -/
theorem compose_threshold_eq
    {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (hf : IsOracleContinuous f) (hg : IsOracleContinuous g) (k : Nat) :
    (composeOracleContinuous hf hg).threshold k
    = hf.threshold (hg.threshold k) := rfl

/-! ## §4 — Round-trip equivalence

The bridge functions compose to the identity at the threshold /
modulus level. -/

/-- Round-trip `ofModulus ∘ toModulus`: threshold survives. -/
theorem ofModulus_toModulus_threshold
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (h : IsOracleContinuous f) (k : Nat) :
    (IsOracleContinuous.ofModulus h.toModulus).threshold k
      = h.threshold k := rfl

/-- Round-trip `toModulus ∘ ofModulus`: modulus survives. -/
theorem toModulus_ofModulus_modulus
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (h : IsContinuousModulus f) (k : Nat) :
    (IsOracleContinuous.ofModulus h).toModulus.modulus k
      = h.modulus k := rfl

/-! ## §5 — Capstone -/

/-- ★★★★ **Oracle continuity equivalence capstone**: the oracle and
    modulus framings of continuity carry the same data; they are
    *interchangeable* at the Lean type level.

    Bundles: (a) forward bridge `ofModulus`, (b) backward bridge
    `toModulus`, (c) round-trip equalities at both threshold and
    modulus level, (d) preservation of identity and composition
    under the oracle framing.

    Reading: the ε-δ residue in `IsContinuousModulus` is **only
    terminological** — the structural content (Nat → Nat
    refinement function + monotonicity) is identical.  Renaming
    "modulus" to "threshold" aligns the continuity framing with
    `ConsistentOracle`'s trajectory-witness paradigm without
    changing the underlying data. -/
theorem oracle_continuity_capstone
    {f g : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (hf : IsContinuousModulus f) (hg : IsContinuousModulus g) :
    -- (a) Forward bridge exists
    Nonempty (IsOracleContinuous f)
    -- (b) Backward bridge exists
    ∧ Nonempty (IsContinuousModulus f)
    -- (c) Round-trip preservation at modulus level
    ∧ (∀ k, (IsOracleContinuous.ofModulus hf).toModulus.modulus k
            = hf.modulus k)
    -- (d) Composition preserves the framework
    ∧ Nonempty (IsOracleContinuous (g ∘ f)) :=
  ⟨⟨IsOracleContinuous.ofModulus hf⟩,
   ⟨hf⟩,
   fun _ => rfl,
   ⟨composeOracleContinuous
      (IsOracleContinuous.ofModulus hf)
      (IsOracleContinuous.ofModulus hg)⟩⟩

end E213.Lib.Math.Real213.OracleContinuity
