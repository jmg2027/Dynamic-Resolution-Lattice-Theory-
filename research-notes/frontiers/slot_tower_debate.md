# Slot-tower debate — two-round panel verdicts (the handle, the genesis)

Two-round multi-agent debate over the slot-tower arc
(`UnitList/UnitGrid/TwoThreeUnique/VpMul/BinTree213/HyperAssoc/Iterate213/
CoAppend213/Convolution213` + the originator's Raw-genesis probe).
Round 1: adversary / unifier / number theorist / foundations skeptic
(parallel).  Round 2: judge (the handle collision) + 213-native defender
(the genesis).  Every load-bearing claim below was source-verified by at
least one panelist.  This note records the **surviving verdicts** and the
**merged brick agenda**; it is the debate's record, not a chapter.

## Verdict A — thesis / mechanism / debt (the handle triage)

Three round-1 positions collided ("one handle = atom (in)distinguishability"
vs "the true unification is the count-rig (ℕ,+,×)" vs "everything is
promissory on `vp_separation`").  Judge's adjudication — they are
**consistent as a triage**:

| role | candidate | status |
|---|---|---|
| **THESIS** | atom-(in)distinguishability | aim; half proved (commutativity side), half instance-only (wall side) |
| **MECHANISM** | the count-rig `(ℕ,+,×)` via `iter_add`/`iter_mul` | proved; generates the tower and the surviving laws; covers the role-asymmetry ingredient, does **not** reach prime-independence |
| **DEBT** | `vp_separation` (UFD faithfulness) | OPEN; the only item converting the thesis from slogan to theorem |

**The adversary's split is real and survives**: at the proof level the
^-wall is **two independent facts** — base/exponent role-asymmetry
(`pow_not_comm`, prime-free, a closed-numeral `decide`) and
prime-independence (`two_three_unique`, parity/Euclid route) — sharing no
lemma.  Even a proved UFD fuses them only as **two named hypotheses of one
theorem** (the `exp`-iso bridge), not into one fact.  Every "one primitive
at two rungs" sentence is a promissory note against `vp_separation` until
that closes.

**Rank correction** (judge, fixing the adversary's ℕ² counterexample): the
wall is **visible at every rank ≥ 2** (ℕ² *is* the rank-2 exponent lattice;
`(1,0) ∦ (0,1)`); only **rank 1** (mod p, cyclic) kills it.  Rank — not
flatness rhetoric — is the load-bearing parameter.

**Fold criterion, honest form** (number theorist + adversary): scope to
**ℚ-exponents and `a, b ≥ 2`** (ℕ-folding fails at `4^x = 8`; `a=1`/`b=1`/
`a=0` undefine collinearity).  Direction split: **(⟹) necessity is
PROVABLE-NOW** — `a^r = b^q → r·vp p a = q·vp p b`, a 5-line `vp_pow`
corollary, cross-multiplied (log-free, ℚ-object-free); **(⟸) sufficiency
IS `vp_separation`** in disguise.  The wall's asymmetry = exactly this
easy/hard split.

**Found money** (judge, correcting the number theorist): the supposed
missing brick `exists_prime_factor` **already exists PURE** at
`Lib/Math/NumberTheory/FourSquare.lean:543`, producing definitionally the
`IsPrime213` shape.  `vp_separation`'s remaining work is the mechanical
strong-induction descent (`vp_div_prime` is a one-line `vp_mul` corollary).

**Unasked-for consequence** (number theorist): `vp_pow` already contains
**irrationality of `log_q p` for every distinct prime pair** — `q^a = p^b`
forces `a=b=0` by the same vp-collision; `two_three_unique` was one
instance of a family.  The wall is ∞-fold, not the `{2,3}` corner.

## Verdict B — the genesis (Raw → ℕ), corrected

Skeptic's four verdicts, cross-examined by the 213-native defender:

1. **"Pick one, append one" is petitio AS PHRASED** (ACCEPT) — "one" imports
   the cardinal it claims absent (CLAUDE.md "Count-Lens import as Raw").
   Fix is **theorem-backed, not lexical**: the act/readout separation is
   already `fromNat` (constructor) vs `count` (separate readout) with
   `count_fromNat` the recovery theorem; `1` is `count`'s readout of a
   single pointing, downstream, never an input.
2. **Succession**: §6.2's cascade ("and so on") question-begs as a
   *derivation* of succession (skeptic right to demote it) — but the right
   citation is **§5.7 + §6.6 non-separation** (the distinguishing event and
   its nesting trace are one residue read by two Lenses, neither prior),
   NOT "intrinsic nesting read dynamically" (which would make the frozen
   list prior — a Platonist import no-exterior equally bans).
3. **★ THE CENTERPIECE — the genesis primitive is `slash`, not `cons`.**
   Raw's sole referring mechanism is **binary, anti-reflexive,
   directionless** (`Raw.slash : Raw → Raw → (x ≠ y) → Raw`; `slash_comm`;
   no privileged operand, §6.1 chart-locality).  The first distinguishing
   is a *pair coming apart*, never a unary increment onto a privileged
   atom.  Iterating `slash` builds the **bracketed tree** (bracketing
   *forced into existence* — `parenthesisation_distinct`,
   `no_universal_slash_assoc`); the list/`cons` lives **two forgettings
   downstream**: `flatten` (drops bracketing — the *chosen* forgetting)
   then `count`/`append_comm` (drops order — *forced* by unit
   indistinguishability).  "Pointing = append = count = ℕ" reads the tower
   only at its top rung and back-projects onto the floor; the floor
   bifurcates, it does not increment.  The graded genesis
   `slash-distinguishing → BinTree → List → ℕ` (each arrow a named Lens,
   tagged forced/chosen) is already the existing Lean architecture.
   **Consequence for the essays**: `what_is_append.md`'s closing "below
   `append` there is only the single distinguishing act" is one rung too
   high — below `append` is the *binary* `slash`; the unary
   "single-distinguishing" reading is itself the count-Lens image.
4. **Completing vs never-finishing is NOT a forced choice** (defender
   refutes the skeptic's horn): completion is **per-pointing** (`Raw.fold`
   total, `count_fromNat` — Lambek-style), inexhaustibility is **of the
   residue** (`object1_not_surjective`) — two theorems about two objects,
   no contradiction.  "Never finishes" is true of the residue, false of
   any pointing; only the conflation is an error.

Comparative location (skeptic): the construction is **initial-algebra
(type-theoretic, Lambek)** with finitist-flavored prose and Benacerraf
supplying the individuation half; where prose and Lean conflict, the Lean
(completing, per-pointing) wins.

## Merged brick agenda (ranked; provenance = which panelist)

1. **`vp_separation`** — the keystone.  Prereq `exists_prime_factor`
   already PURE (`FourSquare.lean:543`); remaining = strong-induction
   descent via `vp_div_prime` (= one-line `vp_mul` corollary).  [NT, ADV,
   UNI all demanded]
2. **Fold ⟹ direction** — `a^r = b^q → ∀p prime, r·vp p a = q·vp p b`.
   PROVABLE-NOW, 5 lines on `vp_pow`.  [NT]
3. **`wall_is_atom_independence` (rank-2 fusion bridge)** — one theorem
   naming both wall ingredients over `exp`; rank-2 form PROVABLE-NOW,
   general form NEEDS(`vp_separation`).  [ADV, UNI]
4. **`no_compatible_order_mod_p`** — no translation-invariant strict order
   survives wrapping (`0<1<…<0` cycle).  PROVABLE-NOW ~15 lines; makes
   "order is the price of curvature" a theorem.  [NT — cheapest item]
5. **`comm_from_transpose`** — the one-statement commutativity theorem
   (swap + role-forgetting readout) covering append/grid/conv.
   PROVABLE-NOW (2-line core; per-instance content = the `hR`
   transpose-invariance, e.g. `heads_tails_total`).  [UNI]
6. **`mem_splits_append` (bialgebra compatibility)** — cuts of a
   concatenation = cuts falling in `l` or in `m`; "distributivity = the
   two Lenses commute" IS the bialgebra axiom.  PROVABLE-NOW on
   `mem_splits_iff` + `append_cancel`.  Antipode/Hopf NEEDS(ℤ-readout
   wiring).  [UNI]
7. **`conv_assoc` via `natSplits` coassociativity** — triple-cut reindex +
   `sumMap`; upgrades (glue, split, conv) to a verified convolution
   algebra.  PROVABLE-NOW but real (~half day).  [UNI]
8. **Tetration ghost** — `iter (a^·) (m·n) 1 = iter (iter (a^·) n) m 1` is
   a free `iter_mul` instance (PROVABLE-NOW); the companion **no-go**
   (`iter_mul_block` has no analog past `^` — the ghost is "real but
   unreadable") NEEDS a small irreducibility argument.  [UNI]
9. **`tower_iff_not_idem`** — tower of height ≥2 ⟺ rung-operator
   non-idempotent at the base; classifies which operators climb at all.
   PROVABLE-NOW.  [UNI]
10. **Hilbert parity instance** — "−1 is a non-square at exactly ∞ and
    p≡3(4): an even set" — ASSEMBLY of `int_sumSq_eq_zero` +
    `no_sqrt_neg_one_4k3` (both already proved).  [NT]
11. **`log_q p` irrational family** — per-pair PROVABLE-NOW (general form
    gated on `vp_separation`).  [NT]
12. **`discrete_log_exists`** — primitive-root orbit fills the units
    (one pigeonhole bridge; `segInt_pairwise` nearly does it).  [NT]

## Co-signed central claim (judge's final paragraph, compressed)

The climb `append→+→×→^` is one combinator (iteration) whose count slot is
additive-then-multiplicative (PROVED: `iter_add`/`iter_mul`; the
fold-one-rung-down = `iter_mul` surfacing as `pow_surviving`).  The climb
keeps comm+assoc through `×` and loses both at `^` (PROVED).
+-commutativity from unit-indistinguishability is PROVED; the wall as
×-atom distinguishability is PROVED **only in the rank-2 instance**
(`two_three_unique`), and at proof level the wall is **two independent
facts** (role-asymmetry + prime-independence) whose fusion over a faithful
`exp` awaits `vp_separation` (OPEN).  Thesis: atom-(in)distinguishability.
Mechanism: the count-rig.  Debt: `vp_separation`.
