# The Founding of the Number Tower — a working draft (준-책)

**A dense investigation of whether `ℕ → ℤ → ℚ → ℝ` is a complete tower, a single
axis, and a forced one.**

Mingu Jeong — theory.  Formalization, audit, and adversarial cross-examination by
Claude (Anthropic); see Acknowledgments.

---

## What this is, and why it is a draft

The companion volume `book/` (six chapters, `The Lens Tower`) *applies* the number
tower: it reads the order-2 orbit, the Cassini unit, and the disc edifice as a
readout three Lens-steps above the residue, and separates the native kernel from the
imported decoration.  It takes the tower `ℕ → ℤ → ℚ → ℝ` as given.

This volume asks whether that tower is *well-founded as a tower at all*.  Three
questions, none of which `book/` settled:

1. **Is it complete?**  Does the chain terminate at `ℝ`, or continue — to
   `ℝ → ℂ → ℍ → 𝕆`, or upward without end?
2. **Is it one axis?**  Is `ℕ → ℤ → ℚ → ℝ` a single growth direction, or does the
   linear presentation serialize several independent axes that the residue does not
   order?
3. **Is each step forced?**  Does the residue *force* each rung (count, difference,
   ratio, completion), or is each one Lens-*choice* among alternatives — the word
   `seed/AXIOM/06_lens_readings.md` §6.7 actually uses?

It is a **준-책 (semi-book / working draft)** and not a closed treatise because the
honest answer to all three is *partly settled, partly open*, and the open parts are
load-bearing.  Each claim below carries a status tag:

| Tag | Meaning |
|---|---|
| **PROVED** | A ∅-axiom Lean theorem in `lean/E213/` witnesses it (file:line given). |
| **DOCTRINE** | `seed/AXIOM/06_lens_readings.md` §6.7 (or another seed spec) asserts it; no Lean witness yet. |
| **OPEN** | Under investigation; the codebase does not settle it, and a draft must say so. |

When the open items close, this draft is promoted to `book/` proper per
`theory/PROMOTION_CRITERIA.md`.

---

## Verdict summary

| Question | Verdict | Status |
|---|---|---|
| Does the bundling terminate at `ℝ`? | **Yes — `ℝ` is a Cauchy fixpoint**: completing `ℝ` again returns `ℝ`. | PROVED (`CauchyCompleteValid.limit_valid`) |
| Is `ℝ → ℂ → ℍ → 𝕆` a continuation? | **No — a different axis** (algebra-grade / dimension-doubling), exiting the commutative codomain world the number tower inhabits. | PROVED divergence (`TwoTowersDivergence.divergence`) |
| Is anything above `ℝ` endless? | **Yes, but not the number tower** — the resolution / completability diagonal has no top and bottoms out in the pointing residue. | PROVED (`TowerNativeCompleteness`) |
| One axis or many? | **Hybrid** — the linear chain serializes a *breadth* axis (`ℕ`), two *orthogonal inverse-closures* (`ℤ` additive, `ℚ` multiplicative), and a *character-changing limit* (`ℝ`); the substrate is a lattice of Lens refinements, not a chain. | PROVED-adjacent; one key independence PROVED, the unification OPEN |
| Is `ℚ` built on `ℤ`? | **Not formally** — `RatioLensFounding` imports neither `ℤ` nor the difference-Lens; its content is `Nat`-level.  The "`ℚ` founds on the `ℤ` unit" link is doctrine, not a Lean dependency. | PROVED (import graph) / OPEN (whether it *should* depend) |
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
