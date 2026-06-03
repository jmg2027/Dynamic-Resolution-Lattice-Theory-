# G187 — The closure-move generalization: what survived the adversarial audit

**Status**: Tier-1 scratchpad.  Records a deep multi-agent investigation that began
from a user observation and ended by *rejecting* the first generalization and pinning
the one that survives — now partly a theorem (`NatPairToQPos` reciprocal involution).

## Origin

After founding the number tower `ℕ → ℤ → ℚ → ℝ` as a Lens-bundling chain
(`Lens/Number/{Difference,Ratio,Cauchy,Tower}Founding.lean`) and the working draft
`book/foundations/`, the user pushed: *"are the axes — completeness, counting,
difference, ratio — all separate?"*  This forced a sharper structural reading than the
linear tower, and a generalization hypothesis:

> **A number system = a word in a monoid of closure MOVES — {iterate, invert,
> complete, double} — applied to the residue's count-Lens.**  `ℕ→ℤ→ℚ→ℝ` is one
> traversal; `ℝ→ℂ→ℍ→𝕆` is the `double` move; the three repo "axis vocabularies"
> (refines / depth `(h,d)` / CD-grade) are orbits of different moves.

Three adversarial agents tested it (iterate / invert / move-monoid).

## What the audit REJECTED

The **move-monoid** framing is (b)-trending-(c): a useful narrative the repo's
`theory/essays/tower_atlas.md` already half-tells, but **not residue-forced**, and at
the point of formalization it imports the "free monoid on construction-functors"
stereotype the repo guards against (failure modes *External classification* +
*View promoted to identity*).  Concretely:

- The four "moves" do **not** share a carrier, so they cannot compose in one monoid.
  `double` (Cayley–Dickson) *exits* the Lens codomain (`CDDouble.lean:22`,
  non-commutative output); its result is not in the domain the other moves act on
  (`TwoTowersDivergence.divergence`).  A monoid needs a common carrier + composition;
  this fails both.
- "iterate" conflates two distinct repo objects — the breadth `Lens.refines` order
  and the number tower (`book/foundations` already separated these).
- depth `(h,d)` is a **measurement** coordinate on divergence, not a constructor that
  produces a number system — calling it a move is a category slip.
- The **iterate** agent's deeper catch: the native object is **not** the `+→×→^→…`
  hyperoperation ladder (imported Ackermann/tetration stereotype).  It is the
  `PrimitiveTower` — *one* arrow (`slash`) iterated; `+,×,^` are count-Lens *readings*
  layered over that single iterate (`tower_atlas`: "There is one tower").  And the
  iterate tower has **no top** — `DepthCeilingResidue.ceiling_residue_is_pointing_residue`:
  naming the ceiling is the Cantor self-cover, so the unboundedness *is* the residue
  (`= cantor_general`, the same engine as `FlatOntologyClosure.object1_not_surjective`).
  The user's "is there a residue ceiling stopping the iterate tower?" is answered
  *no* — and the absence is itself the residue.

**Lesson**: the unification should go *down* (all readings fall to one shared unit), not
*up* (operations promoted to objects in a monoid).  "Many objects, few moves" is the
wrong direction; "one orbit, many readings, one unit" is the repo's actual structure.

## What SURVIVED — the invert twin + the shared unit

Two things are real, residue-anchored, and (now) partly theorems:

### 1. The invert twin: `ℤ = invert(+)`, `ℚ = invert(×)` — one mechanism, two folds

- **PROVED (pair level)**: `NatPairToInt.npairEquiv (a,b)(c,d) ⟺ a+d=b+c` (additive
  diagonal) vs `NatPairToQPos.qpairEquiv (a,b)(c,d) ⟺ a·d=b·c` (multiplicative
  diagonal).  Same `pair + diagonal-quotient` construction, only the fold differs.
  `qpair_is_nat_pair_shaped : QPair = Nat213×Nat213 := rfl`.  Mirror refl/symm/trans
  proofs (additive vs multiplicative cancellation).
- **Caveat**: the two are *structurally* parallel, not literally one type across the
  files — `NatPairToInt` is on Lean `Nat` (projects to `Int` via `subNatNat`),
  `NatPairToQPos` on `Nat213` (no ℚ type to project to).  No shared Lean *functor*
  exists (no `MonoidPairCompletion M` instantiated twice) — that remains a promotion
  target (would turn "one move" from visual parallel into theorem).

### 2. The reciprocal involution — the gap, now closed (this session)

The invert agent's sharpest catch: ℤ's swap-involution structure
(`swap_realizes_negation`, `zero_unique_negation_fixed`, `zero_is_diagonal_collapse`)
had **no multiplicative twin** — the reciprocal-involution half was asserted only by
symmetry of the construction, never proved.  Closed it: `NatPairToQPos` now has 7
∅-axiom theorems (`18 pure / 0 dirty`):

| ℤ (additive, `NatPairToInt`) | ℚ_+ (multiplicative, `NatPairToQPos`) |
|---|---|
| swap `(a,b)↦(b,a)` = negation | `qSwap` = reciprocal |
| `−(−x)=x` (period-2) | `qSwap_involutive` (`1/(1/x)=x`) |
| `x+(−x)=0` | `qpair_mul_swap_eq_qOne` (`x·(1/x)=1`) ★ |
| `−0=0` | `qOne_reciprocal_fixed` (`1/1=1`) |
| `zero_is_diagonal_collapse` (diag → `0`) | `qpair_diagonal_collapse` (diag ~ `1`) |
| `zero_unique_negation_fixed` (full iff) | `reciprocal_fixed_of_unit` (forward half) |

**Open sub-gap**: the converse of the fixed-point characterization
(`b·b=a·a → a=b`, square-injectivity on `Nat213`) is not provable with the present
Peano law set (no order/monotonicity lemmas); the additive twin closes by `Int`
constructor analysis.  Adding `Nat213` square-injectivity (likely via a `lt`/strict-mono
lemma set) would complete the iff.

### 3. The shared unit — the actual answer to "how many axes?"

`tower_atlas.md`'s `grand_unification` conjunct H: count-step, invert-unit,
complete-floor, and CD's `{±1}` are **byte-identically the same `1`**.  The repo's
answer to "how many axes" is *one unit seen four ways*, proved by identity-of-the-unit,
not a composition algebra.  The reciprocal involution is the pair-level shadow: negation
fixes `0`, reciprocal fixes `1`, **both the swap-fixed diagonal `{(k,k)}`** — the
involution-fixed point is the axis unit, and the diagonal is the shared structure.

## Carryover / promotion targets

1. **DONE** — `Lens/Number/Nat213/Tower/PairCompletion.lean` (13 PURE).  A generic
   `CommCancelSemigroup` on `Nat213` (op + comm + assoc + right-cancel, **no unit**) with
   its pair-completion `pairEquiv M p q := M.op p.1 q.2 = M.op p.2 q.1`, equivalence-relation
   proofs, `swap` involution, and `combine`.  Key result `combine_swap_equiv_diagonal`:
   `x ∘ inv(x)` lands on the diagonal — the group identity **emerges** as the diagonal
   class, unit-free (which is *forced*: `Nat213` has no additive `0`, yet ℤ has one).
   Instantiated `addCCS` (`op=+` → ℤ model) and `mulCCS` (`op=·` → ℚ_+);
   `mulCCS_recovers_qpairEquiv : pairEquiv mulCCS = NatPairToQPos.qpairEquiv` (`Iff.rfl`).
   Capstone `invert_is_one_move` bundles it: ℤ and ℚ_+ are one construction read at `+`
   and `·`, the operation the only difference.  *"Invert is one move" is now a theorem,
   not two mirror files.*  (The literal common carrier is `Nat213`; the additive instance
   is a `Nat213`-pair ℤ model alongside the Lean-`Nat`-based `NatPairToInt`.)
2. **DONE** — `Lens/Number/Nat213/Order.lean` (8 PURE) + `NatPairToQPos.reciprocal_fixed_iff_unit`.
   Built a native strict order `lt a b := ∃ c, add a c = b` (Lean `Nat` order is
   propext-dirty, so it could not be borrowed): `lt_trichotomy` (structural), `lt_mul_self`
   (strict square-monotonicity, *purely from distributivity* — no order lemma), and the
   payoff `mul_self_inj` (`a·a = b·b → a = b`).  Transferred through the injective
   homomorphism `toNat` was unnecessary — the whole order is algebraic.  Then
   `reciprocal_fixed_iff_unit : qSwap p ~ p ↔ p ~ qOne` — the full multiplicative twin of
   `zero_unique_negation_fixed`, added to the capstone bundle (NatPairToQPos now 19 PURE).
   The reciprocal involution now matches the negation involution fact-for-fact.
3. `book/foundations/03_one_axis_or_many.md` §3.2: cite the reciprocal-involution twin
   as the *why* behind ℤ⊥ℚ — they are independent because they are the same swap read
   by two folds, fixing two units; the independence is the orthogonality of `+` and `·`,
   not a stacking.

## Frontier items (book/foundations ch5) — all resolved

1. **ℚ-on-ℤ mismatch** → honest direction taken: `RatioLensFounding` docstring corrected
   (content is `Nat`-level, imports neither ℤ nor difference-Lens; coupling is
   identity-of-the-unit, `SharedUnitAcrossReadings`); §6.7 stale ref + `N_U = d^(d²)`
   universe-constant phrasing fixed to the parametric `configCountD d n = d^(d^n)`.
2. **Exhaustiveness/uniqueness** → resolved as *no*: `refines` is a preorder (not total),
   the formalized `Lattice/Chain.refines_chain` (breadth) ≠ the number tower; ≥2 chains, so
   not unique — which is the answer (the hybrid verdict), not a gap.
3. **NT=2 ⟹ period-2** → `PairCompletion.swap_order_eq_NT` (order exactly NT=2; no period-k).
4. **ℚ obligation** → resolved as a choice: no exterior dialer compels the next rung; "must
   reach ℝ" → "can reach ℝ" (no-exterior discipline).
5. **Unify three axis-vocabularies** → `SharedUnitAcrossReadings.the_unit_is_one_across_readings`:
   the value `1` is one across count-difference / Möbius-det / Cassini / reciprocal.  The
   unification is identity-of-the-unit (downward), not an operator monoid (upward) — the
   move-monoid having been rejected for lack of a shared carrier.

## Bottom line

The deep audit did its job by *killing* the move-monoid and surfacing the honest
structure: one iterated `slash` (no top, the unboundedness is the residue); the invert
move as one mechanism on two folds (`ℤ:+ = ℚ:×`, now twinned down to the reciprocal
involution); and one shared unit read across the readings.  The generalization is real but
points *downward to the unit*, not upward to an operator algebra.
