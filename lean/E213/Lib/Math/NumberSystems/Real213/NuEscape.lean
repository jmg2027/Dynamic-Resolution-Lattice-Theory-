import E213.Lib.Math.NumberSystems.Real213.Core.Core
import E213.Lib.Math.NumberSystems.Real213.Mul.CutMul
import E213.Theory.Raw.API

/-!
# A Real213 cut is a residue escape (the νF bridge, ℝ on the one carrier)

Companion to the p-adic νF bridge (`Lib/Math/NumberSystems/Padic/NuEscape.lean`) and the König
νF bridge (`Lib/Math/Combinatorics/KonigConditional.lean`): a constructive real, like a p-adic
integer and a König branch, is **reached by no finite Raw** — and it rides the *same* νF carrier
(`CoResidue.SlashNu`, the binary König spine).

The bridge is the **cut-decision bit-stream** of the real.  `Real213.equiv` is defined by the
order-projection decisions `orderProj m k (abLens.view (xs i))` — the Dedekind-cut bits.
Sampling that table along the diagonal (resolution `k+1` at the `k`-th approximant) gives an
honest `Nat → Bool` extractor `cutBits` — **∅-axiom decidable**, computed off the approximants,
no modulus/existence needed.  It is *presentation-dependent* (it reads the sequence, not just
the equivalence class) — exactly as it must be: per `seed/AXIOM/05_no_exterior.md` and the
presentation-dependence theme, the bit-stream is a residue-internal pointing, the residue itself
is reached by none (`DepthCeilingResidue.diag_not_in_seq`, `Real213` reached-by-none on record).

`cutNu r := boolSpineSlashNu (cutBits r)` packages the real as a νF inhabitant on the **shared
binary carrier** (`Fin 2 ≃ Bool` — the same `boolSpine` König / 2-adic ride), and
`real_is_nu_escape` gives the reached-by-none.  Distinct cut-bit-streams give `Distinct` spines
(`real_cut_distinct`).  So ℝ, ℤ_p, and König all sit on **one νF carrier**.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.NuEscape

open E213.Theory (Raw)
open E213.Theory.Raw.CoResidue
open E213.Lens.Instances.AB
open E213.Lib.Math.Analysis.Cauchy.Archimedean
open E213.Lib.Math.NumberSystems.Real213.Core.Core (Real213)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMul (cutMul)

/-- The **cut-decision bit-stream** of a real: at depth `k`, the order-projection decision of the
    `k`-th approximant at resolution `k+1` (`orderProj 1 (k+1)` = "is `a/b ≤ 1/(k+1)`").  The
    diagonal of the Dedekind-cut table that defines `Real213.equiv` — a `Nat → Bool`, ∅-axiom
    decidable, read off the approximants. -/
def cutBits (r : Real213) : Nat → Bool :=
  fun k => orderProj 1 (k + 1) (abLens.view (r.xs k))

/-- ★ **A Real213 cut IS a residue escape.**  Its cut-decision bit-stream packages as a νF
    inhabitant (`SlashNu`) — the same binary carrier as a König branch and the 2-adic integer
    (`boolSpine`). -/
def cutNu (r : Real213) : SlashNu := boolSpineSlashNu (cutBits r)

/-- The real's cut is a genuine slash-νF co-tree: consistent and anti-reflexive. -/
theorem cut_is_nu (r : Real213) :
    Consistent (cutNu r).val ∧ AntiRefl (cutNu r).val :=
  (cutNu r).property

/-- ★★ **A Real213 cut is reached by no finite Raw.**  Its cut-bit-stream escape differs (as a
    labelled co-tree) from every finite Raw's embedding (`rawToSlashNu`), by `boolSpine_escapes`.
    So ℝ ⊂ the νF escapes, on the *same* `SlashNu` carrier as `KonigConditional` and
    `Padic.twoAdic_is_nu_escape` — a constructive real is a branch of König's binary tree, never
    a finite Raw, never a frozen value. -/
theorem real_is_nu_escape (r : Real213) (r0 : Raw) :
    (rawToSlashNu r0).val ≠ (cutNu r).val :=
  fun h => boolSpine_escapes (cutBits r) r0.val h.symm

/-- ★★★ **Reals differing on a cut bit give distinct νF inhabitants.**  Given a depth `k` where
    the cut-bit-streams differ (`cutBits r k ≠ cutBits r' k`), the spines differ at the depth-`k`
    left leaf (`boolSpine_inj`).  The honest ∅-axiom faithfulness on the cut presentation:
    pointwise difference of cut-decisions ⟹ `Distinct` co-trees (no `funext`, no `Cardinal`). -/
theorem real_cut_distinct {r r' : Real213} (h : ∃ k, cutBits r k ≠ cutBits r' k) :
    Distinct (cutNu r).val (cutNu r').val :=
  boolSpine_inj h

/-- ★★★ **A real's cut carries the shift dynamics.**  Its cut-bit spine is the shift → νF
    coalgebra hom of the cut-decision stream: the root branches, the left subtree reads the
    depth-0 cut bit `cutBits r 0`, and the right subtree is the spine of the *shifted* cut-bit
    stream.  So ℝ inherits the Bernoulli-shift sub-coalgebra on the shared carrier
    (`boolSpine_shift_coalgebra`) — the same dynamical structure as ℤ_p's digit-shift. -/
theorem real_shift_dynamics (r : Real213) :
    boolSpine (cutBits r) [] = none
    ∧ (∀ q, coLeftAt (boolSpine (cutBits r)) [] q = some (cutBits r 0))
    ∧ (∀ q, coRightAt (boolSpine (cutBits r)) [] q = boolSpine (fun n => cutBits r (n + 1)) q) :=
  boolSpine_shift_coalgebra (cutBits r)

/-- ★★★ **ℝ on the one νF carrier (capstone).**  A constructive real's cut presentation, like a
    König branch and a p-adic integer, rides the shared binary νF carrier (`SlashNu`):

    1. every real gives a νF inhabitant (consistent + anti-reflexive) via its cut-bit-stream;
    2. each is reached by no finite Raw (`real_is_nu_escape`);
    3. reals differing on a cut bit give `Distinct` inhabitants (`real_cut_distinct`).

    So König / ℤ_p / ℝ all sit on **one carrier** — the binary König spine — closing the
    one-carrier program (`Padic.padic_is_nu_escape` for the p-ary side).  ∅-axiom, pointwise. -/
theorem real_one_carrier :
    (∀ r : Real213, Consistent (cutNu r).val ∧ AntiRefl (cutNu r).val)
    ∧ (∀ (r : Real213) (r0 : Raw), (rawToSlashNu r0).val ≠ (cutNu r).val)
    ∧ (∀ r r' : Real213, (∃ k, cutBits r k ≠ cutBits r' k) → Distinct (cutNu r).val (cutNu r').val) :=
  ⟨cut_is_nu, real_is_nu_escape, fun _ _ h => real_cut_distinct h⟩

/-! ## ℝ's field operations preserve the carrier (transport-only, presentation-dependent)

ℝ's field arithmetic lives at the **cut-table** level (`Cut := Nat → Nat → Bool`, the `(m,k)`-cut
decision table): `cutSum` and `cutMul` (`Sum/CutSum`, `Mul/CutMul`).  Sampling a cut table on the
diagonal (`cutTableBits c k = c k (k+1)`) rides the same `boolSpine` carrier as `cutBits`, so the
field operations **preserve the carrier**: the spine of `cutSum cx cy` and of `cutMul cx cy` is
again reached by no finite Raw (`real_field_on_carrier`).  So ℝ, like ℤ_p, sits on the one carrier
as a `+`/`×`-closed set of escapes.

**Honest structural contrast with ℤ_p** (the limit of the one-carrier program): ℤ_p's carrier is
the *faithful* digit encoding, with a finite-state native `+` and a residue-field ring-hom readout
(`Padic/NuEscape`).  ℝ's cut presentation is **order-decision-based** (`orderProj`), not a digit
algebra, and the diagonal sampling is **presentation-dependent** — so on ℝ there is *no*
finite-state native operation and *no* ring-hom readout: the field is irreducibly **transport-only**
on the carrier.  This is by-design (a real is reached by none; the bit-stream is a residue-internal
pointing, `seed/AXIOM/05_no_exterior.md`), not a gap.  All ∅-axiom. -/

/-- A cut table's diagonal as a bit-stream (resolution `k+1` at scale `k`) — same shape as
    `cutBits`, on the abstract cut-table field-carrier. -/
def cutTableBits (c : Nat → Nat → Bool) : Nat → Bool := fun k => c k (k + 1)

/-- A cut table as a νF inhabitant on the shared `boolSpine` carrier. -/
def cutTableNu (c : Nat → Nat → Bool) : SlashNu := boolSpineSlashNu (cutTableBits c)

/-- ★★ **A cut table is reached by no finite Raw.**  Its diagonal bit-stream escape rides
    `boolSpine`, the same carrier as `cutBits`/König/ℤ_p. -/
theorem cutTable_is_escape (c : Nat → Nat → Bool) (r : Raw) :
    (rawToSlashNu r).val ≠ (cutTableNu c).val :=
  fun h => boolSpine_escapes (cutTableBits c) r.val h.symm

/-- ★★★ **ℝ's field operations preserve the carrier.**  The cut-table sum and product (`cutSum`,
    `cutMul` — ℝ's `+`/`×`, `Sum/CutSum`, `Mul/CutMul`) land back in the escapes: the spine of
    `cutSum cx cy` and of `cutMul cx cy` is reached by no finite Raw.  So ℝ, as the carrier subset
    of cut escapes, is closed under `+`/`×` — the ℝ analogue of `Padic.padic_ring_on_carrier`.
    (Honest: transport-only and presentation-dependent — ℝ's order-based cut admits no finite-state
    native op nor ring-hom readout, unlike ℤ_p's faithful digit carrier.) -/
theorem real_field_on_carrier :
    (∀ (cx cy : Nat → Nat → Bool) (r : Raw),
        (rawToSlashNu r).val ≠ (cutTableNu (cutSum cx cy)).val)
    ∧ (∀ (cx cy : Nat → Nat → Bool) (r : Raw),
        (rawToSlashNu r).val ≠ (cutTableNu (cutMul cx cy)).val) :=
  ⟨fun cx cy r => cutTable_is_escape (cutSum cx cy) r,
   fun cx cy r => cutTable_is_escape (cutMul cx cy) r⟩

end E213.Lib.Math.NumberSystems.Real213.NuEscape
