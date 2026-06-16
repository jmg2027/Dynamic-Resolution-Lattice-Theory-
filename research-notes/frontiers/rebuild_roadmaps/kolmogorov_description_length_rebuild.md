# Kolmogorov / description-length rebuild (post-deletion of the bogus layer)

**What was deleted & the bogus mechanism.**  `Lib/Math/Probability/Information/Kolmogorov.lean`
(50 lines, deleted in `26c86991e`) welded the famous name "Kolmogorov complexity"
onto a literal `4`:

```lean
def axiomClauseCount : Nat := 4
def kolmogorov_213 : Nat := axiomClauseCount        -- "★ Kolmogorov complexity of 213 ★"
theorem kolmogorov_eq_clauses : kolmogorov_213 = 4 := rfl
theorem axiom_minimality (n) (h : kolmogorov_213 ≤ n) : 4 ≤ n := h     -- = `h`, identity
theorem truncation_at_minimum (extra) (h : 0 < extra) :
    kolmogorov_213 + extra > kolmogorov_213 := by ...  -- = "4 + extra > 4"
```

The whole content is: the Raw axiom is asserted to have "4 clauses", `K(213)` is
*defined* to be that `4`, and "minimality" is the arithmetic fact `4 + extra > 4`
plus the identity `h : 4 ≤ n ⊢ 4 ≤ n`.  No program, no machine, no encoded
object, no shortest-description theorem.  It is the count `4` renamed.

**The genuine content.**  Kolmogorov complexity `K(x)` = the length of the
*shortest program* (description) that outputs `x` in a *fixed universal model of
computation*.  Two non-trivial ingredients the deleted file had neither of:
1. a real **description language** (an instruction set + a decode/run semantics)
   so that "length of a description of `x`" is well-defined;
2. an **incompressibility** statement — for a specific object (or family), *no*
   description in that language is shorter than some bound.  This is the content;
   the constant `4` is not.

**The 213-native obstruction.**  213 lacks (a) a `Nat`-valued *length* function on
Raw terms or on instruction-words, and (b) any *running* semantics that decodes a
shorter word back to the target.  What it does have is real and unusually
well-suited:
- `Raw` itself is a free term language (atoms `a, b` + the binary distinguisher
  `slash`), so a Raw term *is* a finite description with an obvious structural
  size (node count).
- `seed/PROOF_ISA.md` + `lean/E213/Lens/ProofISA.lean` already fix a small
  **instruction set** (DISTINGUISH, READ/FOLD, DIAGONALIZE, GAP, SEPARATE,
  COMPILE-DOWN, REFLECT, LOOP), each a proven `∅`-axiom witness — a candidate
  "fixed universal model" with a finite alphabet.
- the genuine incompressibility kernel is already present as the **diagonal /
  Cantor** machinery: `Lens/Cardinality/Cantor.lean` (`cantor_general`,
  `cantor_raw_bool`) and `object1_not_surjective` — these are exactly the
  classical *source* of incompressibility (the diagonal object is the one no
  short enumeration reaches).

**Staged plan (citing genuine seams).**

- **Stage 1 — a real cost function + one honest incompressibility lemma.**
  Define `size : Raw → Nat` (the structural node-count of a Raw term: `size a =
  size b = 1`, `size (slash x y) = 1 + size x + size y`).  Then pick a concrete
  *family* of objects with a parametrised target — e.g. the `n`-fold left-nested
  slash `Lₙ` (a "counter") — and prove a genuine lower bound: **no Raw term of
  the same fold (decoding to `Lₙ` under a fixed evaluator `eval : Raw → α`) has
  `size < f(n)`** for an honest `f` growing with `n`.  The point is the lemma is
  about *all shorter descriptions*, not a renamed constant.  Target shape:
  `∀ t, eval t = target n → f n ≤ size t`.  This is a real "no shorter encoding"
  theorem; it must NOT reduce to `rfl` or to `h`.
- **Stage 2 — relativise to the ProofISA alphabet.**  Replace structural Raw-size
  by *instruction-word length* over the 8-instruction set (the fixed universal
  model), so the cost is genuinely the length of a *program* in the named ISA,
  and re-prove Stage 1's bound there.  The DIAGONALIZE archetype (`ProofISALifts.lean`,
  "lift cost: zero") is the natural witness that the diagonal object is its own
  shortest description.
- **Stage 3 — incompressibility from the diagonal.**  Show a *counting* statement:
  there are more length-`≤ k` targets than length-`< k` descriptions
  (`CountExistence.count_existence`, the `GAP`/`COUNT` instruction), so *most*
  objects of a family are incompressible — the genuine "almost all strings are
  random" theorem, compiled down the ISA rather than asserted.
- **Stage 4 — the residue reading.**  Connect to `object1_not_surjective`: the
  reached-by-none residue is the *limit* of incompressibility (no finite
  description covers it).  This is where 213's diagonal machinery and the
  classical halting-/Chaitin-incompressibility story meet — stated as a Lens
  fact, not a value.

**Honest scope.**  None of this "computes `K(213)`" — there is no canonical
universal machine in 213, so an *absolute* `K` (the additive-constant-up-to-a-fixed-U
quantity) is not available; what is reachable is a description-length *relative to
a declared language* (Raw-size, then ISA-word-length) plus genuine lower bounds.
Say plainly: 213 supplies the **incompressibility mechanism** (diagonal) and a
real relative cost, not an invariant absolute `K`.  Do NOT reintroduce any
`def kolmogorov_213 := <constant>`.

**Cross-references.**
- `lean/E213/Lens/Cardinality/Cantor.lean` (`cantor_general`, the incompressibility source)
- `seed/PROOF_ISA.md` + `lean/E213/Lens/ProofISA.lean` (the fixed instruction set)
- `lean/E213/Lib/Math/Foundations/ProofISALifts.lean` (DIAGONALIZE = zero-cost lift)
- `lean/E213/Lib/Math/Combinatorics/CountExistence.lean` (the COUNT/`GAP` existence engine)
- `seed/AXIOM/05_no_exterior.md` §5.4 (`object1_not_surjective`, the residue limit)
