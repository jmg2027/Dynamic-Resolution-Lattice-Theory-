# The Founding of the Number Tower — a working draft (준-책)

**A dense investigation of whether `ℕ → ℤ → ℚ → ℝ` is a complete tower, a single
axis, and a forced one.**

Mingu Jeong — theory.  Formalization, audit, and adversarial cross-examination by
Claude (Anthropic); see Acknowledgments.

---

## What this is, and why it is a draft

The companion volume `books/lens-tower/` (six chapters, `The Lens Tower`) *applies* the number
tower: it reads the order-2 orbit, the Cassini unit, and the disc edifice as a
readout three Lens-steps above the residue, and separates the native kernel from the
imported decoration.  It takes the tower `ℕ → ℤ → ℚ → ℝ` as given.

This volume asks whether that tower is *well-founded as a tower at all*.  Three
questions, none of which `books/lens-tower/` settled:

1. **Is it complete?**  Does the chain terminate at `ℝ`, or continue — to
   `ℝ → ℂ → ℍ → 𝕆`, or upward without end?
2. **Is it one axis?**  Is `ℕ → ℤ → ℚ → ℝ` a single growth direction, or does the
   linear presentation serialize several independent axes that the residue does not
   order?
3. **Is each step forced?**  Does the residue *force* each rung (count, difference,
   ratio, completion), or is each one Lens-*choice* among alternatives — the word
   `seed/AXIOM/06_lens_readings.md` §6.7 actually uses?

It is a **준-책 (semi-book / working draft)**.  Each claim below carries a status tag:

| Tag | Meaning |
|---|---|
| **PROVED** | A ∅-axiom Lean theorem in `lean/E213/` witnesses it (file:line given). |
| **DOCTRINE** | `seed/AXIOM/06_lens_readings.md` §6.7 (or another seed spec) asserts it; no Lean witness yet. |
| **OPEN** | Under investigation; the codebase does not settle it, and a draft must say so. |

The five frontier items the draft opened are now settled (Chapter 5.2): the `ℚ`-on-`ℤ`
coupling is identity-of-the-unit not build-dependency (`SharedUnitAcrossReadings`); the
bundling is provably *not* a unique chain (the substrate is a lattice with ≥2 chains);
period-2 is forced by `NT = 2` (`PairCompletion.swap_order_eq_NT`); `ℚ` is a Lens choice,
not an obligation (no exterior dialer); and the axis-vocabularies unify *downward* to one
shared unit, not upward into an operator monoid.  What remains genuinely open is left as
such and flagged.  When the build-side promotion gates are met, this is promoted to
`books/lens-tower/` proper per `theory/PROMOTION_CRITERIA.md`.

---

## Verdict summary

| Question | Verdict | Status |
|---|---|---|
| Does the bundling terminate at `ℝ`? | **Yes — `ℝ` is a Cauchy fixpoint**: completing `ℝ` again returns `ℝ`. | PROVED (`CauchyCompleteValid.limit_valid`) |
| Is `ℝ → ℂ → ℍ → 𝕆` a continuation? | **No — a different axis** (algebra-grade / dimension-doubling), exiting the commutative codomain world the number tower inhabits. | PROVED divergence (`TwoTowersDivergence.divergence`) |
| Is anything above `ℝ` endless? | **Yes, but not the number tower** — the resolution / completability diagonal has no top and bottoms out in the pointing residue. | PROVED (`TowerNativeCompleteness`) |
| One axis or many? | **Hybrid** — the linear chain serializes a *breadth* axis (`ℕ`), two *orthogonal inverse-closures* (`ℤ` additive, `ℚ` multiplicative), and a *character-changing limit* (`ℝ`); the substrate is a lattice of Lens refinements, not a chain. | PROVED (independence); unification resolved downward to one unit (`the_unit_is_one_across_readings`) |
| Is `ℚ` built on `ℤ`? | **No — sibling readings.** `RatioLensFounding` imports neither `ℤ` nor the difference-Lens; its content is `Nat`-level.  `ℚ` and `ℤ` are coupled at the shared unit `1`, not stacked. | PROVED (import graph + `the_unit_is_one_across_readings`) |
| Is each rung forced or chosen? | See Chapter 4. | (forcedness investigation) |

---

## Chapters

1. `01_three_questions.md` — the three questions, and what "complete / one axis /
   forced" can mean with no exterior to appeal to.
2. `02_completeness.md` — `ℝ` as the Cauchy fixpoint; Cayley–Dickson as an orthogonal
   axis; the endless resolution diagonal; the finite-config rationality reconciliation.
3. `03_one_axis_or_many.md` — breadth vs. the two inverse-closures vs. the limit;
   the lattice of Lens refinements; the `ℤ ⊥ ℚ` independence.
4. `04_forced_or_chosen.md` — per-rung forcedness; where the residue forces and where
   it only permits.
5. `05_open_frontier.md` — what remains open, and what would close it.
