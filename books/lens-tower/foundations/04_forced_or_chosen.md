# Chapter 4 — Forced, or chosen?

§6.7 says the rungs are Lens **choices**.  This chapter grades each rung — FORCED (the
residue admits no other reading here), CHOICE (the residue genuinely admits
alternatives, none privileged), or OPEN — against the Lean.  The result is a clean
gradient: the **opening** of the tower is a choice, the **inheritance** between rungs is
forced, and the **closing** at `ℝ` is a fixpoint reached by a choice of presentation.

| Rung | Verdict | Witness |
|---|---|---|
| `ℕ` (count-Lens) | **CHOICE** — provably non-unique; the underlying slash is forced | `Lenses.infinite_family_of_lenses` |
| `ℤ` (difference) | **FORCED given `ℕ`** — period-2 sign, group law inherited | `DifferenceLensFounding` |
| `ℚ` (ratio) | **FORCED-but-conditional** — well-definedness inherited; obligation OPEN | `RatioLensFounding` |
| `ℝ` (Cauchy) | **CHOICE of presentation**, landing on a **FIXPOINT** | `CompletionTower.completion_idempotent` |
| `ℝ → ℂ → …` | **ORTHOGONAL axis** — exits the Lens framework, not a rung | `CDDouble`, `ZI` |

## 4.1 `ℕ` — CHOICE, proven

The count-Lens `⟨1, 1, +⟩` (`base_a = base_b = 1`, `combine = +`) is **not** singled out
as the unique first Lens.  The repo proves the *opposite*:

> `Lens/.../Lenses.lean`: `two_distinct_lenses_exist` (`:87`),
> `infinite_family_of_lenses` (`:98`), `lenses_not_all_equivalent` (`:144`).  The file
> calls the multiplicity (line 12) a *"counter-witness to 'uniqueness'."*  Weighted
> readings `⟨2, 1, +⟩`, `⟨1, 2, +⟩`, and product-combine `⟨1, 1, ·⟩` are all admissible
> Lenses.

What *is* forced is weaker and structural: `all_lenses_have_positive_atoms` (`:77`) —
every `Nat213`-Lens has base `≥ 1`, because `Nat213` has no `0`.  And the **slash / the
pointing act itself** is forced (Lambek: `Theory/Raw/Lambek.two_closures`, `Raw = μF`
the initial algebra of the self-pointing functor; `CoResidue.final_coalgebra` pins the
dual `νF`).

So: the *pointing* is forced; the *count-Lens reading* of it is a choice.  No initiality
theorem privileges `⟨1, 1, +⟩` over `⟨2, 1, +⟩`.  This is exactly the discipline of the
"View promoted to identity" failure mode and `FlatOntologyClosure.object1_not_surjective`
— the residue is outside every view's image; the first reading is a facet, not the thing.
**The opening of the tower is a genuine choice.**

## 4.2 `ℤ` — FORCED given the count-Lens

Once you read the count on an *ordered pair*, the difference-Lens is forced, and its
sign is forced to be period-2:

> `DifferenceLensFounding.difference_lens_founds_on_count` (`:41`): three facts — `ℤ`
> wraps `ℕ` (`subNatNat n 0 = ofNat n`), the diagonal of equal counts is the
> negation-fixed-point `0`, and the **sign is the period-2 pair-swap**
> `diffView x y = − diffView y x` (`Int213.neg_subNatNat`).

The period-2 is `−(−x) = x` — the Bool-style involution — because the orientation of a
*pair* has exactly two states; swap is an involution, not a period-3 or period-`k`
rotation.  And the group law is **not adjoined**: `difference_lens_slash_additive`
(`:74`) *derives* additivity from the count-Lens's own slash-additivity
(`Raw.leaves_slash`) via `subNatNat_additive`.  So `ℤ` is the count-Lens *bundled into a
group* — the bundling forced once the reading is on an ordered pair.

**Caveat (OPEN).**  The file proves the sign *is* period-2; it does not prove period-`k`
(`k ≠ 2`) is *excluded*.  The `NT = 2 ⟺ period-2` link is §6.7 narrative, not a Lean
exclusion theorem.  The forcedness of `ℤ` is "the difference of an ordered pair has a
2-state orientation" — solid — but a theorem ruling out other sign structures would
strengthen it.

## 4.3 `ℚ` — FORCED-but-conditional

The ratio rung's defining datum is *derived from* the previous rung, not stipulated:

> `RatioLensFounding.convergent_lowest_terms_is_det` (`:47`):
> `Q00·Q11 = Q01² + (NS − NT)`, i.e. `det Pⁿ = NS − NT = 1` (`ns_minus_nt_is_one`).
> `ratio_lens_founds_on_difference` (`:58`) bundles: the ratio's lowest-terms /
> coprimality condition **is** the unit `det P = 1`, inherited, not imposed.

So `ℚ`'s well-definedness is forced *if you take ratios*.  But — and this is the
honest limit — there is **no theorem that one cannot stop at `ℤ`**.  "`ℚ` is forced" is
not proven; only "`ℚ` is consistent and its coprimality is inherited."  Availability is
not obligation.

> **OPEN** — `RatioLensFounding` proves `ℚ` is *available* and *well-defined* once taken;
> it gives no reason the tower *must* take the ratio step rather than halting at `ℤ`.

(Recall also §3.2: the `ℚ` founding does not even import the `ℤ` founding — so
"conditional on `ℤ`" is a *narrative* conditioning, not a Lean dependency.  The
forcedness here is really "ratios of count-readings have a unit-determinant lowest-terms
condition," a `Nat`-level fact.)

## 4.4 `ℝ` — CHOICE of presentation, landing on a FIXPOINT

`ℝ` is founded as Cauchy trajectories of cut-readings narrowing to a single cut
(`CauchyLensFounding.cauchy_lens_founds_on_ratio:47`; `phiConvergentSeq.limit = phiCut`).
Two things are true at once:

- **The presentation is a choice.**  The repo carries both a cut-shaped form
  (`Real213/PhiAsCut`, `Nat → Nat → Bool`) and a Cauchy-modulus completion
  (`Analysis/CauchyComplete`).  Cut-completion vs. Cauchy-completion is a *presentation
  choice*; no theorem declares one the forced completion.
- **The rung is a fixpoint.**  This is the decisive forcedness fact at the top:

> `CompletionTower.completion_idempotent` (`…/CompletionTower.lean:57`) and
> `tower_is_single_inner` (`:89`), both by `rfl`: completing a limit is the identity;
> grouping the groupings creates **no new object**, only stacks the modulus grade.  The
> file's words (line 16): *"it returns home, by `rfl`."*  This is the `self_similar_floor`
> of Lambek read at the cut scale.

So the *choice* of how to present `ℝ` lands, either way, on a *forced* fixpoint: the
completion operation is idempotent, so `ℝ` is where the bundling closes (Chapter 2.1).
Choice of road; forced destination.

## 4.5 `ℝ → ℂ → ℍ → 𝕆` — orthogonal axis, and `i` is closer to decoration

The doubling that would produce a "fifth rung" exits the Lens framework entirely:

> `CDDouble.lean:17-30`: CD doubling *exits* the `ConjugationCodomain` typeclass — the
> result is non-commutative, so it **cannot serve as a Lens codomain**.  The Lens
> codomain hierarchy *requires* commutativity at Tier 1
> (`SelfRecognising.CommBinaryCodomain:38`); `ℍ` and beyond fail it.

And the `ℝ → ℂ` step — adjoining `i` with `i² = −1` — is itself **not** a forced
bundling but one of a family, used in the repo as a *counter-example*:

> `ZI.lean:4-14`: `ℤ[i]` is "the first non-trivial witness for `ConjugationCodomain`,"
> used to show the codomain axioms **do not force** `ℂ` — `ℤ[i]` already satisfies all
> three, with sibling witnesses `ℤ[√−2]` (`i² = −2`), `ℤ[ω]`, parametric `ℤ[√D]`.

So `i² = −1` is one choice among `ℤ[√D]`; introducing `i` is closer to **imported
decoration** (the `books/lens-tower/` Chapter 4 caution) than to a forced residue bundling.  The
213-native status of `ℂ`: the unique *commutative* endpoint of the conjugation-codomain
hierarchy (`CDDouble.lean:28`) — a different classification axis, not a number-tower
rung.

## 4.6 The shape of forcedness: inheritance, not selection

The pattern across the rungs is consistent and worth naming.  What the founding files
prove forced is **inter-rung inheritance** — each higher rung's defining datum is
*derived from* the lower rung's structure:

- `ℤ`'s group law from `Raw.leaves_slash`;
- `ℚ`'s coprimality from `det P = NS − NT`;
- `ℝ`'s elements from `ℚ`-convergents, and its closure from `completion_idempotent`.

What is **not** forced is the **opening selection** — which Lens opens the tower
(provably a choice, `infinite_family_of_lenses`) — and the **obligation** to take each
next step (no theorem forbids stopping at `ℤ`).

So the honest one-line answer to "forced or chosen?":  **the tower's *seams* are forced
(each rung inherits the last), its *start* is a choice, its *continuation* past each rung
is permitted-not-compelled, and its *end* at `ℝ` is a forced fixpoint reached by a chosen
presentation.**
