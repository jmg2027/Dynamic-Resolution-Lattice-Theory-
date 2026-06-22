# Decomposition: quantum groups (U_q(g), q-integers, the R-matrix, Yang–Baxter, q→1, q=−1)

*213-decomposition per `../README.md` (model v7.1). A **fresh** field, and the single most
on-theme test of the calculus's central invariant: is the **deformation parameter `q`** of a
quantum group the SAME `q` as the **`q = ±1` residue tag** (`ResidueTag.multiplier`, ∓1)? The
thesis: a quantum group is `hopf_algebras.md`'s Hopf structure **deformed by `q`**, whose `q=±1`
specializations are EXACTLY the calculus's `q=±1` tag poles — classical at `q=+1`, super/fermionic
at `q=−1` — with the R-matrix the q-deformed swap (`FoldKlein.bothSwap`/`slash_comm`), Yang–Baxter
the braid coherence (`knots.md`), and the q-integer/q-binomial the count-reading deformed
(`QBinomial.lean`, BUILT). The bar is PREDICTION/REVELATION, and the verdict must be scrupulously
honest about identity-vs-containment-vs-suggestive on the `q`-question.*

## The decomposition (C / Reading q-deformed / Residue q=±1)

- **Construction `C` — `lie_theory.md`'s/`hopf_algebras.md`'s `C`, UNCHANGED.** A quantum group
  `U_q(g)` adds **no new construction**. The undeformed `U(g)` is `lie_theory.md`'s Aut-family read
  through the commutator (`Mat2Bracket.bracket A B := AB−BA`, the `q=−1` antisymmetry); the Hopf
  structure is `hopf_algebras.md`'s distinguishing read **in both directions at once** —
  multiplication `m` = the fold (`Convolution213.conv`), comultiplication `Δ` = the co-fold
  (`CoAppend213.splits`/`natSplits`), antipode `S` = the convolution-inverse (`mu_conv_one`,
  `bothSwap`). `U_q(g)` is that *same* `C` with **one `L`-parameter turned on**: a deformation dial
  `q`. No new distinguishing, no new atom.

- **Reading `L_q` — the count-reading carrying a `q`-deformation parameter.** This is the genuinely
  new datum, and it lands on an **existing `L`-axis** of the model, not a new primitive. The count
  reading (`cardinality.md`/`generating_functions.md`) is deformed: the ordinary count `[n] = n` and
  the ordinary binomial `C(n,k)` become the **q-integer** `[n]_q` and the **q-binomial** (Gaussian
  binomial) `[n,k]_q`. This is **BUILT ∅-axiom** — `Combinatorics/QBinomial.lean` (11/0) defines
  `qbinom q n k` (q-Pascal) at integer `q`, and `QBinomialSymmetry.lean` (12/0) proves general
  symmetry. The q-integer is the column `[m,1]_q`: `(q−1)·[m,1]_q = q^m − 1` (`qbinom_col1`), i.e.
  `[m]_q = (q^m−1)/(q−1) = 1+q+…+q^{m−1}`. So the deformation `q` is a **scaling sub-parameter on the
  count-reading's resolution axis** (README v7: the resolution axis carries `base` and `scaling`
  sub-parameters): `q` re-weights each unit of the count by a power of `q` before summing.

- **Residue — `q = ±1`, but read at TWO DIFFERENT `q`'s (the honest crux).** There are *two* `q=±1`
  events, and the decomposition's whole payoff is keeping them apart:
  - the **deformation-`q`'s specializations** `q=+1` (classical) and `q=−1` (fermionic), and
  - the **`ResidueTag` tag-`q`** (`multiplier .escape = −1`, `multiplier .converge = +1`), the
    unimodular swap/escape bit that signs `det`/`∂`/ℤ and runs Cantor/φ.
  The antipode `S` is the genuine tag-`q=−1` residue (`hopf_algebras.md`, `ResidueTag`,
  `bothSwap_no_fixed`). The deformation-`q=±1` is a *different* event, decided below.

## Re-seeing (⟨C | L_q⟩)

```
   a quantum group U_q(g)  =  ⟨ C (= U(g)'s Hopf structure, hopf_algebras.md) | the count-reading DEFORMED by q ⟩ ⊕ S (tag q=−1 antipode)

   undeformed U(g)         =  lie_theory.md's bracket  (Mat2Bracket.bracket = AB−BA, q=−1 antisymmetry)
   q-integer [n]_q         =  the count-reading scaled by q:  (q−1)·[n]_q = q^n − 1   (qbinom_col1)
   q-binomial [n,k]_q      =  the binomial count deformed (q-Pascal)                  (qbinom, qbinom_pascal)   BUILT
   q→1 classical limit     =  [n,k]_q → C(n,k)                                        (qbinom_q1: qbinom 1 n k = choose n k)   BUILT, GENERAL
   q=−1 specialization     =  the LUCAS/fermionic table [n,k]_{−1} = C(⌊n/2⌋,⌊k/2⌋)   (NOT a sign-fold — see Revelation)
   R-matrix / braiding     =  the q-deformed swap = cocommutativity (conv_comm) deformed; undeformed = bothSwap/slash_comm
   Yang–Baxter (RRR=...)   =  the braid coherence (knots.md's Bₙ relation), the deformed swap's associativity
   antipode S              =  the convolution-inverse, the TAG q=−1 residue            (mu_conv_one: μ∗1=ε; bothSwap_no_fixed)
   Hopf compatibility      =  hopf_algebras.md's bialgebra law Δ_+⇄Δ_×                 (OPEN, frontier F1 — inherited break)
```

The bracket above belongs to a single picture with `hopf_algebras.md`/`lie_theory.md`: the quantum
group is **the Hopf-deformed Lie algebra**, the deformation living entirely on one `L`-parameter (`q`
on the count), with the antipode/co-fold/character all inherited from those two notes unchanged.

## Revelation (collapse + forcing + the deformation-q vs tag-q verdict)

**Collapse — the q-binomial IS `cardinality.md`'s count-reading carrying a `q`-scaling parameter,
and `q→1` is a Lean theorem.** The classical limit is not asserted: `qbinom_q1` proves
`qbinom 1 n k = choose n k` **generally** (induction matching the Pascal recursion). So the
deformation dial at `q=+1` returns the ordinary count-reading — the undeformed/cocommutative/classical
limit `hopf_algebras.md` describes — **on the same `C`**, as a ∅-axiom theorem. This is a clean
collapse onto the resolution/scaling axis: `q` is a count-reweighting, `q=1` the no-reweighting point.

**Forcing — the antipode is forced as the `ResidueTag` tag-`q=−1`, inherited unchanged.** Nothing new:
the deformation does not touch the antipode's status. `S` is the convolution-inverse of `id`
(`mu_conv_one : μ∗1 = ε`, the antipode axiom verbatim, ×-cut), the fixed-point-free unimodular
involution `bothSwap` (`bothSwap_no_fixed`, "the antipode" `bothSwap_swaps_both`), landing on the
tag's `multiplier_unimodular` `±1` bit. The R-matrix's *undeformed* core is the swap
`conv_comm`/`bothSwap`/`slash_comm` (the cocommutative/symmetric braiding); the R-matrix deforms that
swap by `q`. So three Hopf data carry over verbatim from `hopf_algebras.md`.

**★ The deformation-`q` vs tag-`q` verdict — CONTAINMENT WITH ONE HONEST SURPRISE, not identity.**
This is the load-bearing test. The result, verified numerically against the BUILT `qbinom` (q-Pascal):

- **At `q=+1`:** the deformation collapses to the classical count (`qbinom_q1`, GENERAL Lean theorem).
  The tag-`q=+1` (`converge`, `multiplier = +1`) is the *undeformed/converging* pole. **These agree in
  spirit** — `q=+1` is "no deformation / classical / symmetric" on both sides, and `golden_is_converge`
  pins tag-`+1` to the conserved (undeformed) Cassini orbit. Suggestive-to-aligned.

- **At `q=−1`:** the surprise, and the honest break of the naive thesis. The deformation-`q=−1`
  specialization of `qbinom` is **NOT a sign-fold** — it produces the **Lucas/fermionic table**
  `[n,k]_{q=−1} = C(⌊n/2⌋, ⌊k/2⌋)` (zero when `n` even, `k` odd), e.g. row `n=4`: `[1,0,2,0,1]`,
  row `n=6`: `[1,0,3,0,3,0,1]` — **all non-negative integers, no `±1` swap anywhere** (verified by
  evaluating the exact `qbinom` recurrence). The `ResidueTag` tag-`q=−1` is by contrast a **unimodular
  `multiplier = −1`** (`bool_not_fixedPointFree`/`bothSwap`): a sign/swap bit, the *escape* pole.
  These are **genuinely different objects**: the deformation-`q` is a continuous (here integer-valued)
  scaling dial on the count; the tag-`q` is a discrete `±1` unimodular swap bit on the residue. They
  are **NOT the same `q`.**

- **The precise relation is CONTAINMENT, not identity.** The deformation-`q` is a *continuous
  parameter*; the tag-`q ∈ {+1,−1}` is the *unimodular boundary of its range*. The tag-`q=±1` is the
  **specialization locus** of the deformation-`q` at the two unimodular values — but the *content* read
  there differs by which structure you specialize: specialize the **count-reading** at `q=−1` and you
  get the fermionic Lucas table (no sign); specialize the **residue's self-map multiplier** at `q=−1`
  and you get the antisymmetry/escape sign-bit. So "the quantum-group `q` at `±1` = the tag `q`" is
  **false as an identity** and **true only as a containment**: the tag's `±1` is the unimodular pair
  the deformation dial passes through, while the *fermionic/super* reading classically attached to
  deformation-`q=−1` is a third thing (the count's `q=−1` value), distinct from the tag's swap bit.
  The honest one-line verdict: **the deformation-`q` and the tag-`q` share the `±1` locus by
  containment, not the same object — the naive "deformation-q IS the tag-q" is a BREAK.**

**The R-matrix / Yang–Baxter — PREDICTION + located break (the `knots.md` boundary, verbatim).** The
R-matrix is the q-deformed braiding; its undeformed limit is the swap `bothSwap`/`conv_comm`
(symmetric monoidal). Yang–Baxter `R₁₂R₁₃R₂₃ = R₂₃R₁₃R₁₂` is exactly the **braid-group coherence**
`knots.md` decomposed: `Bₙ = ⟨n strands | crossing-compositions⟩` EXTENDS (`groups.md`), but the
*knot-invariant / R-matrix-as-an-operator* side hits `knots.md`'s **located break** — the
crossing-resolution *move* (skein) and the ambient quotient are README v7.1's graded-relation slot and
the colimit/`q=−1` corner. So Yang–Baxter's *braid-relation* leg is grounded; the *R-matrix operator
solving it* is the named-not-built object, sitting precisely at `knots.md`'s boundary.

## VALIDATE verdict — **PREDICTION + BREAK** (the deformation-q ≠ tag-q; one inherited break, one knots-break)

The model's interior is unchanged; quantum groups consolidate `hopf_algebras.md` + `lie_theory.md`
under a *new `L`-parameter* (the deformation `q` on the count-reading) — but the on-theme test
**fails the naive identity and yields a precise BREAK**, the most valuable datum here.

1. **q-deformation = the count-reading's `q`-scaling sub-parameter; `q→1` classical = a Lean theorem.**
   `qbinom_q1` (GENERAL) gives the classical limit ∅-axiom; the q-integer/q-binomial are BUILT
   (`QBinomial`/`QBinomialSymmetry`, 11/0 + 12/0). No new primitive — the resolution axis's
   scaling sub-parameter (README v7) absorbs it. **EXTEND.**
2. **antipode/co-fold/braiding-core inherited verbatim from `hopf_algebras.md`** (tag-`q=−1`
   `mu_conv_one`/`bothSwap`; co-fold `natSplits`; swap `conv_comm`). **EXTEND.**
3. **★ deformation-`q` ≠ tag-`q` — CONTAINMENT, not identity (the thesis BREAKS at `q=−1`).** The
   deformation's `q=−1` is the fermionic Lucas table `C(⌊n/2⌋,⌊k/2⌋)` (no sign); the tag's `q=−1` is a
   unimodular swap/escape bit. They share the `±1` *locus* by containment (the tag's `±1` is the
   unimodular boundary the continuous deformation dial passes through), but are **different objects**.
   **BREAK of the naive identity; the containment is the true relation.**
4. **R-matrix-as-operator / Yang–Baxter operator = `knots.md`'s located break** (braid relation
   grounded, the skein/crossing move + R-matrix operator not built). **PARTIAL / inherited break.**

So a quantum group = `hopf_algebras.md`'s Hopf `C` + `lie_theory.md`'s bracket, with the count-reading
carrying a deformation `q` (BUILT, `q→1` a theorem), the antipode the tag-`q=−1` residue (inherited) —
but the deformation-`q` and the tag-`q` are **the same only by containment at the `±1` locus, not as
one object**, and at `q=−1` they read *different content* (fermionic count vs swap bit). This is a
clean PREDICTION with one decisive located BREAK on the central `q`-question.

## Verified Lean anchors (file:line:theorem — all grep + `tools/scan_axioms.py`-scanned this session)

| Datum | Theorem (file:line) | Purity (module tally) |
|---|---|---|
| ★ q-binomial def (q-Pascal) | `Lib/Math/Combinatorics/QBinomial.lean:36` `qbinom` (def), `:49` `qbinom_pascal` | **11 PURE / 0 DIRTY** ✓ |
| ★ q→1 classical limit (GENERAL) | `Lib/Math/Combinatorics/QBinomial.lean:60` `qbinom_q1` (`qbinom 1 n k = choose n k`) | PURE (in the 11) ✓ |
| q-integer column `(q−1)[m,1]_q=q^m−1` | `Lib/Math/Combinatorics/QBinomialSymmetry.lean:56` `qbinom_col1` | **12 PURE / 0 DIRTY** ✓ |
| q-binomial general symmetry `[n,k]_q=[n,n−k]_q` | `Lib/Math/Combinatorics/QBinomialSymmetry.lean:267` `qbinom_symm`; `:219` `qbinom_pascal_dual` | PURE (in the 12) ✓ |
| concrete q-values (q=2): `[4,2]_2=35` etc. | `Lib/Math/Combinatorics/QBinomial.lean:71` `qbinom_table_q2` | PURE (in the 11) ✓ |
| ★ tag-`q=±1` multiplier (∓1, unimodular) | `Lib/Math/Foundations/ResidueTag.lean:81` `multiplier`; `:86` `multiplier_unimodular`; `:73` `ResidueTag` | **55 PURE / 0 DIRTY** ✓ |
| tag two poles capstone | `Lib/Math/Foundations/ResidueTag.lean:228` `residue_tag_two_poles`; `:90` `tag_inj_multiplier` | PURE (in the 55) ✓ |
| tag-`q=+1` = converge/undeformed (φ) | `Lib/Math/Foundations/ResidueTag.lean:180` `golden_is_converge`; `:133` `escape_residue_outside` | PURE (in the 55) ✓ |
| antipode axiom `S⋆id=ε` (tag q=−1, ×-cut) | `Lib/Math/NumberTheory/DirichletIdentities.lean:50` `mu_conv_one` | **20 PURE / 0 DIRTY** ✓ (via hopf_algebras.md) |
| R-matrix undeformed swap = bothSwap (antipode/braiding) | `Lens/Number/FoldKlein.lean:31` `bothSwap` (def); `:58` `bothSwap_no_fixed`; `:50` `bothSwap_involutive`; `:53` `bothSwap_swaps_both` | **9 PURE / 0 DIRTY** ✓ |
| cocommutativity / symmetric braiding (the undeformed R) | `Meta/Nat/Convolution213.lean:156` `conv_comm`; `:87` `conv` (def); `:257` `conv_assoc` | **49 PURE / 0 DIRTY** ✓ (via hopf_algebras.md) |
| undeformed `slash_comm` (the bare swap) | `Theory/Raw/Slash.lean:40` `Raw.slash_comm` | PURE ✓ |
| undeformed bracket = U(g) (q=−1 antisymmetry) | `…/Real213/Mat2/Mat2Bracket.lean` `bracket`, `bracket_antisymm`, `jacobi`, `tr_bracket_zero` | **10 PURE / 0 DIRTY** ✓ (via lie_theory.md) |

Scan tallies this session (from repo root): `QBinomial` **11/0**, `QBinomialSymmetry` **12/0**,
`ResidueTag` **55/0**.

## Dropped / flagged (honest)

- **Named `quantumGroup` / `U_q` / `R_matrix` / `RMatrix` / `YangBaxter` / `braiding` /
  `quasitriangular` / `Drinfeld` / `qInt`/`q_integer` objects — ABSENT (grep-confirmed).** A
  case-insensitive grep over `lean/E213/` for these returns only false positives (`√5` in
  `ExceptionalTraceSeed.lean`, "triangular-matrix" in `IncidenceInversion.lean`; the `quantum` hits are
  all the **physics** deployment — `Lib/Physics/Quantum*.lean`, qubits/Bell/Bekenstein — not quantum
  *groups*). The predicted-not-built named bundles are confirmed absent; the **q-deformed count is
  built** (`QBinomial`/`QBinomialSymmetry`), the Hopf/antipode/braiding-core built unnamed (per
  `hopf_algebras.md`).
- **The fermionic/super reading of deformation-`q=−1` as a Lean theorem about `qbinom`** — the Lucas
  identity `[n,k]_{−1} = C(⌊n/2⌋,⌊k/2⌋)` is **verified numerically** (against the exact `qbinom`
  recurrence) but is **not a proved Lean theorem**; it is the buildable witness below. Not cited as an
  anchor — flagged as the computed observation that drives the BREAK verdict.
- **The R-matrix as an operator / Yang–Baxter as an operator equation — ABSENT** (`knots.md`'s located
  break: the skein/crossing move + ambient quotient). The braid *relation* leg is grounded
  (`groups.md`/`knots.md`); the R-matrix solving Yang–Baxter is the named-not-built object. Flagged,
  not asserted.
- **The bialgebra/Hopf compatibility `Δ_+⇄Δ_×` (frontier F1) — ABSENT**, inherited verbatim from
  `hopf_algebras.md` (the one law fusing `m` and `Δ`). The deformation does not close it. Flagged as
  the inherited open leg.

### Buildable witness (named, verified by computation)

The natural ∅-axiom closure of this note is **`qbinom_qm1_lucas`**: prove
`qbinom (−1) n k = (choose (n/2) (k/2) : Int)` when `¬(n even ∧ k odd)`, and `= 0` otherwise — the
deformation-`q=−1` fermionic specialization. **Verified true by computation** against the exact
`QBinomial.qbinom` recurrence (rows `n=0..6`: `[1]`, `[1,1]`, `[1,0,1]`, `[1,1,1,1]`, `[1,0,2,0,1]`,
`[1,1,2,2,1,1]`, `[1,0,3,0,3,0,1]`, matching `C(⌊n/2⌋,⌊k/2⌋)` with the even-`n`/odd-`k` zeros). This
would make the deformation-`q=−1`-≠-tag-`q=−1` BREAK a **Lean theorem** (the fermionic value is a
non-negative count, never the tag's swap `±1`), promoting the honest verdict from computation to
machine-checked. The classical leg (`q→1`) is already a theorem (`qbinom_q1`); only the `q=−1`
fermionic leg is unwritten.
