import E213.Lib.Math.Logic.Omniscience

/-!
# Reverse Mathematics 213 — choice as a free Lens parameter `σ`

Marathon field 17 (`blueprints/math/17_reverse_math_213.md`), choice-as-Lens.

**Thesis.** The axiom of choice is not an axiom to *assert* or *refuse*; it is a free
Lens parameter `σ` — a *section* of an inhabited family — that the operations read.
Different sections are different Lenses; the operations extend *differently* per section;
and all of this is **constructive per `σ`** (the sections are given by an explicit rule,
no choice axiom is invoked).  The classical non-constructivity appears *only* when one
demands a *canonical* `σ` with no rule attached — which 213 reads as the absence of an
exterior dialer (`seed/AXIOM/05_no_exterior.md` §5.1): there is no operand for "the"
choice, so it is a free parameter, not a missing theorem.

This file is the minimal ∅-axiom witness:

  * `F i := Bool` — an inhabited family whose every fiber genuinely has *two* elements
    (`true` and `false`), so a section is a real choice and there are many of them;
  * `sigmaL := fun _ => false`, `sigmaR := fun _ => true` — two explicit sections (Lenses),
    each total, computable, and ∅-axiom (no choice axiom);
  * `readOp σ n` — a finite operation reading the section: count of `i < n` with `σ i =
    true`.  It is **`σ`-dependent**: `readOp sigmaL 3 = 0` but `readOp sigmaR 3 = 3`.

The point theorem `choice_is_free_lens_parameter` bundles the two facts: the sections are
*distinct* Lenses (`sigmaL 0 ≠ sigmaR 0`) and the operation *depends* on which Lens is
chosen (`readOp sigmaL 3 ≠ readOp sigmaR 3`) — with **no canonical selection asserted**.

**LLPO tie-in.**  LLPO (`Omniscience.lean`) says an at-most-one-true stream's true index
is even *or* odd — a *binary* disjunction it does not *force* a side of.  That is exactly
the binary choice between the two sections `sigmaEven` (pick `true` on evens) and
`sigmaOdd` (pick `true` on odds): two distinct Lenses on the same family, *neither forced*.
LLPO = the `q = ±1` choice-Lens left unselected.  `sigmaEven`/`sigmaOdd` are built below
and shown distinct, ∅-axiom — the constructive content of the LLPO disjunction is the
*pair of sections*, not a verdict between them.

Pure-Lean: `Nat.rec`/`decide` on closed Bool/Nat goals, `Bool.noConfusion`, no `propext`.
-/

namespace E213.Lib.Math.Logic.ChoiceLens

/-- The inhabited family: every fiber is `Bool`, which has *two* elements (`true`,
    `false`).  A section `σ : ∀ i, F i` is therefore a genuine choice, and there are
    many — the family is the simplest one where "which section?" has real content.
    `abbrev` keeps `F i` reducible to `Bool`, so each fiber's `DecidableEq` is available. -/
abbrev F (_ : Nat) : Type := Bool

/-- **Choice Lens L** — the section picking `false` everywhere.  Total, explicit, no
    choice axiom. -/
def sigmaL : ∀ i, F i := fun _ => false

/-- **Choice Lens R** — the section picking `true` everywhere.  Total, explicit, no
    choice axiom. -/
def sigmaR : ∀ i, F i := fun _ => true

/-- The `σ`-reading operation: number of indices `i < n` with `σ i = true`.  A finite
    fold over the section — the operation "extends differently per section". -/
def readOp (σ : ∀ i, F i) : Nat → Nat
  | 0     => 0
  | n + 1 => (if σ n = true then 1 else 0) + readOp σ n

/-- Under Lens L the prefix-count is `0` at `n = 3`. -/
theorem readOp_sigmaL_3 : readOp sigmaL 3 = 0 := by decide

/-- Under Lens R the prefix-count is `3` at `n = 3`. -/
theorem readOp_sigmaR_3 : readOp sigmaR 3 = 3 := by decide

/-- ★ **The operation is `σ`-dependent.**  Same operation, same input `n = 3`, different
    result under the two Lenses — the choice is read, not erased. -/
theorem readOp_sigma_dependent : readOp sigmaL 3 ≠ readOp sigmaR 3 := by decide

/-- ★ **The two sections are distinct Lenses** (pointwise at `0`). -/
theorem sigmaL_ne_sigmaR_at_0 : sigmaL 0 ≠ sigmaR 0 := by decide

/-- ★★ **Choice is a free Lens parameter.**  Two explicit, total, ∅-axiom sections of the
    inhabited family `F` are *distinct* Lenses, and the reading operation `readOp`
    *depends* on which one is chosen — with no canonical section asserted.  The "axiom of
    choice" here is neither proved nor refused: it is the free parameter `σ`, and every
    `σ` is constructively available. -/
theorem choice_is_free_lens_parameter :
    sigmaL 0 ≠ sigmaR 0 ∧ readOp sigmaL 3 ≠ readOp sigmaR 3 :=
  ⟨sigmaL_ne_sigmaR_at_0, readOp_sigma_dependent⟩

/-! ## LLPO tie-in: the even/odd disjunction is the unforced binary choice-Lens -/

/-- **Choice Lens "even"** — pick `true` exactly on even indices.  The `q = +1` side of
    LLPO's even/odd disjunction. -/
def sigmaEven : ∀ i, F i := fun i => decide (i % 2 = 0)

/-- **Choice Lens "odd"** — pick `true` exactly on odd indices.  The `q = -1` side. -/
def sigmaOdd : ∀ i, F i := fun i => decide (i % 2 = 1)

/-- ★ **The even and odd choice-Lenses are distinct** (they disagree at `0`).  LLPO's
    disjunction (`Omniscience.LLPO`) is the assertion that *one* of these two sides holds;
    213 reads it as this *pair of sections* with neither forced — the binary choice-Lens
    left as a free parameter. -/
theorem sigmaEven_ne_sigmaOdd_at_0 : sigmaEven 0 ≠ sigmaOdd 0 := by decide

/-- The even/odd Lenses also read differently through `readOp`: on the prefix `n = 4`,
    `sigmaEven` fires on `{0,2}` (count `2`) and `sigmaOdd` on `{1,3}` (count `2`) — equal
    here, so the *distinctness* lives in *where* they fire, witnessed at `n = 1`. -/
theorem readOp_even_odd_differ_at_1 : readOp sigmaEven 1 ≠ readOp sigmaOdd 1 := by decide

end E213.Lib.Math.Logic.ChoiceLens
