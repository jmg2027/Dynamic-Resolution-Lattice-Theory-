import E213.Lens.Foundations.FlatOntologyClosure
import E213.Lens.Foundations.PredicateSelfEncoding

/-!
# ResidueReentry — the residue re-enters as the next operand, and the cover never closes

The self-cover has two halves, both ∅-axiom:

  * `FlatOntologyClosure`: `Object1 : Raw → (Raw → Bool)` is faithful (`object1_injective`)
    but **not total** (`object1_not_surjective`) — pointing leaves a residue, the
    predicates outside its image (`cantor_raw_bool`);
  * `PredicateSelfEncoding`: a (finite-prefix) predicate encodes **back** to a Raw
    (`predicateToRaw`), so the residue — itself a predicate — re-enters the *domain* of
    pointing.

This file closes the loop: the residue is not an exterior surplus that sits there;
encoded back to a Raw and pointed at again, it produces a fresh predicate — and the
re-pointing **still** leaves a residue.  The composite `P ↦ Object1 (predicateToRaw n P)`
(encode the predicate, point at the encoding) is **not surjective**
(`residue_reentry_never_closes`): its image lies inside `Object1`'s image, which already
misses the residue.  So naming the residue never recovers it; the act produces a new
object, leaving a new residue.

The self-cover therefore never closes: each turn leaves the residue, the residue
re-enters as a Raw, the next turn leaves it again.  The residue is perpetually the *next
operand* of pointing — the same self-applying, gapless re-entry the resolution tower
shows at the diagonalisation scale (`Cauchy/DepthHeightDiagonal.diag_self_applies`), here
at the foundational pointing scale.  `residue_perpetually_reenters` bundles the three
facts.

§3 pins the *concrete* form: §1 is an existence statement (non-surjectivity); here is a
**named predicate** that re-pointing provably sends to a *different* predicate.  The
criterion is sharp — `Object1 r` is true at **exactly one** Raw (`object1_true_unique`),
so re-pointing collapses any predicate to a single-Raw indicator, and therefore *any*
predicate true at two distinct Raws (`multipoint_not_object1`) is a concrete
non-fixed-point of `Object1 ∘ predicateToRaw n` (`reentry_nonfixed_of_multipoint`), with
an **explicit Raw of disagreement** (`multipoint_object1_differ_at`).  The cleanest member
is the *undifferentiated* predicate `fun _ => true` (`reentry_undifferentiated_nonfixed`):
naming the residue that draws no distinction yields, after re-pointing, the indicator of a
single Raw — false at every other Raw, so a different predicate.  "Naming the residue
yields a different predicate" is a machine-checked, point-witnessed fact, not only a
non-surjectivity.

All zero-axiom.
-/

namespace E213.Lens.Foundations.ResidueReentry

open E213.Theory (Raw)
open E213.Lens.Foundations.FlatOntology (Object1)
open E213.Lens.Foundations.FlatOntologyClosure (object1_injective object1_not_surjective)
open E213.Lens.Foundations.PredicateSelfEncoding (predicateToRaw predicateToRaw_kernel truthTableNat_const_false)
open E213.Lens.Number.Nat213.Raw (numeral numeral_ne_b)

/-! ## §1 — re-entering the residue never closes the cover -/

/-- ★★★ **The residue re-entry never closes the cover.**  Encode any predicate to a Raw
    (`predicateToRaw n`) and point at the encoding (`Object1`): the composite
    `P ↦ Object1 (predicateToRaw n P)` is **not surjective**.  Its image lies inside
    `Object1`'s image, which already misses the residue; so re-entering and re-pointing
    never produces the un-pointed predicates.  Naming the residue yields a fresh object,
    leaving a fresh residue — the cover never closes. -/
theorem residue_reentry_never_closes (n : Nat) :
    ¬ Function.Surjective (fun P : Raw → Bool => Object1 (predicateToRaw n P)) := by
  intro hsurj
  apply object1_not_surjective
  intro Q
  obtain ⟨P, hP⟩ := hsurj Q
  exact ⟨predicateToRaw n P, hP⟩

/-! ## §2 — the perpetual re-entry, bundled -/

/-- ★★★ **The residue is perpetually the next operand.**  Three facts of one loop:

    1. pointing is faithful but not total (`object1_injective` ∧ `object1_not_surjective`):
       every pointing leaves a residue;
    2. the residue re-enters the domain: every predicate `P` encodes to a Raw
       `predicateToRaw n P` (`predicate_self_encoding_closure`);
    3. re-entering and re-pointing never closes the cover
       (`residue_reentry_never_closes`).

    So the self-cover never closes: each turn leaves the residue, the residue re-enters
    as a Raw, the next turn leaves it again.  The residue is the perpetual next operand —
    the foundational instance of the gapless, self-applying re-entry. -/
theorem residue_perpetually_reenters (n : Nat) :
    (Function.Injective Object1 ∧ ¬ Function.Surjective Object1)
    ∧ (∀ P : Raw → Bool, ∃ r : Raw, r = predicateToRaw n P)
    ∧ ¬ Function.Surjective (fun P : Raw → Bool => Object1 (predicateToRaw n P)) :=
  ⟨⟨object1_injective, object1_not_surjective⟩,
   fun P => ⟨predicateToRaw n P, rfl⟩,
   residue_reentry_never_closes n⟩

/-! ## §3 — the concrete non-fixed-point witness

§1 says the re-pointing composite is not surjective.  Here is a *named* predicate it
provably fails to fix.  The mechanism: `Object1 r` is the indicator of a single Raw (true
at exactly `r`), so the composite `Object1 ∘ predicateToRaw n` always lands on a single-Raw
indicator — and any predicate that is true at two distinct Raws can therefore never be its
output. -/

/-- The two atoms differ — propext-free (`Tree.noConfusion`, not `decide`, which pulls
    `propext` through `DecidableEq Raw`). -/
private theorem a_ne_b : Raw.a ≠ Raw.b :=
  fun h => E213.Term.Internal.Tree.noConfusion (congrArg Subtype.val h)

/-- `Object1 r` is true at **exactly one** Raw: if `Object1 r s = true` then `s = r`.
    The indicator points at a single Raw — this single-pointedness is what makes the
    re-pointing collapse every predicate. -/
theorem object1_true_unique (r s : Raw) (h : Object1 r s = true) : s = r :=
  of_decide_eq_true h

/-- ★★ **Single-pointedness ⟹ a two-point predicate is no indicator.**  If `P` is true at
    two distinct Raws `s ≠ t`, then `P` is not `Object1 r` for *any* `r`: an indicator is
    true at exactly one Raw, so it cannot match a predicate that distinguishes two. -/
theorem multipoint_not_object1 (P : Raw → Bool) (s t : Raw)
    (hs : P s = true) (ht : P t = true) (hst : s ≠ t) (r : Raw) :
    Object1 r ≠ P := by
  intro h
  have hrs : Object1 r s = true := by rw [h]; exact hs
  have hrt : Object1 r t = true := by rw [h]; exact ht
  exact hst ((object1_true_unique r s hrs).trans (object1_true_unique r t hrt).symm)

/-- **The explicit Raw of disagreement.**  For a two-point predicate `P` (true at `s ≠ t`)
    and any `r`, the indicator `Object1 r` and `P` differ at whichever of `s`, `t` is not
    `r` (at least one must be, since `s ≠ t`).  The non-fixed-point is point-witnessed. -/
theorem multipoint_object1_differ_at (P : Raw → Bool) (s t : Raw)
    (hs : P s = true) (ht : P t = true) (hst : s ≠ t) (r : Raw) :
    ∃ u : Raw, Object1 r u ≠ P u := by
  by_cases hsr : s = r
  · -- s = r, so t ≠ r: `Object1 r` is false at t while `P t = true`
    refine ⟨t, ?_⟩
    have htr : t ≠ r := fun e => hst (hsr.trans e.symm)
    have hfalse : Object1 r t = false := decide_eq_false htr
    rw [hfalse, ht]; exact fun e => Bool.noConfusion e
  · -- s ≠ r: `Object1 r` is false at s while `P s = true`
    refine ⟨s, ?_⟩
    have hfalse : Object1 r s = false := decide_eq_false hsr
    rw [hfalse, hs]; exact fun e => Bool.noConfusion e

/-- ★★★ **Concrete non-fixed-point of the re-pointing composite.**  Any predicate `P` true
    at two distinct Raws is *not* fixed by `Object1 ∘ predicateToRaw n`: re-pointing encodes
    `P` to a single Raw and reads off that Raw's indicator, which is true at exactly one Raw
    and so cannot equal a two-point `P`.  This is the concrete form of
    `residue_reentry_never_closes` — a witnessed inequality, not only non-surjectivity. -/
theorem reentry_nonfixed_of_multipoint (n : Nat) (P : Raw → Bool) (s t : Raw)
    (hs : P s = true) (ht : P t = true) (hst : s ≠ t) :
    Object1 (predicateToRaw n P) ≠ P :=
  multipoint_not_object1 P s t hs ht hst (predicateToRaw n P)

/-- ★★★ **The undifferentiated predicate is a concrete non-fixed-point.**  The predicate
    that draws no distinction (`fun _ => true`, the residue's cleanest member) is true at
    both atoms `a ≠ b`, so re-pointing it (`Object1 (predicateToRaw n ·)`) returns a
    *different* predicate — the indicator of a single Raw, false at every other Raw.  The
    named instance of `reentry_nonfixed_of_multipoint`: naming the residue yields a
    different predicate, point-witnessed. -/
theorem reentry_undifferentiated_nonfixed (n : Nat) :
    Object1 (predicateToRaw n (fun _ : Raw => true)) ≠ (fun _ : Raw => true) :=
  reentry_nonfixed_of_multipoint n (fun _ => true) Raw.a Raw.b rfl rfl a_ne_b

/-- ★★★ **The concrete re-entry capstone.**  Bundles the universal non-closure (§1) with
    its concrete witness: the composite `Object1 ∘ predicateToRaw n` is not surjective AND
    the undifferentiated predicate is a named non-fixed-point with an explicit Raw of
    disagreement.  "The self-cover never closes" is realised both abstractly (a residue
    exists) and concretely (this predicate, re-pointed, is provably different — here). -/
theorem residue_reentry_concrete (n : Nat) :
    ¬ Function.Surjective (fun P : Raw → Bool => Object1 (predicateToRaw n P))
    ∧ Object1 (predicateToRaw n (fun _ : Raw => true)) ≠ (fun _ : Raw => true)
    ∧ ∃ u : Raw, Object1 (predicateToRaw n (fun _ : Raw => true)) u ≠ (fun _ : Raw => true) u :=
  ⟨residue_reentry_never_closes n,
   reentry_undifferentiated_nonfixed n,
   multipoint_object1_differ_at (fun _ => true) Raw.a Raw.b rfl rfl a_ne_b
     (predicateToRaw n (fun _ => true))⟩

/-! ## §4 — the exact fixed-point characterization

§3 gave the sufficient exclusion: a predicate true at two distinct Raws is never fixed.
Here is the *exact* fixed set.  The composite `Object1 ∘ predicateToRaw n` always lands on
an indicator `Object1 (·)`, so a fixed point must itself be an indicator — and not just
any: the one whose encoding **round-trips** (`predicateToRaw n (Object1 r) = r`).  So the
fixed points are exactly the round-tripping single-Raw indicators — a *proper* refinement
of "single-point": single-pointedness is necessary (`reentry_fixed_imp_single`) but the
round-trip condition is the rest.  `object1_true_exactly_one` records the single-Raw count
(`1`) that makes the indicator the lever. -/

/-- ★ **`Object1 r` is true at exactly one Raw.**  Existence (`Object1 r r = true`) and
    uniqueness (`Object1 r s = true → s = r`): the indicator's truth set has count `1` —
    the count-Lens unit that re-pointing collapses every predicate to. -/
theorem object1_true_exactly_one (r : Raw) :
    Object1 r r = true ∧ ∀ s : Raw, Object1 r s = true → s = r :=
  ⟨E213.Lens.Foundations.FlatOntology.Object1_self r, fun s h => object1_true_unique r s h⟩

/-- ★★★ **The fixed points are exactly the round-tripping indicators.**  `Object1
    (predicateToRaw n P) = P` holds **iff** `P` is the indicator of some Raw `r` whose
    encoding returns it: `P = Object1 r` and `predicateToRaw n (Object1 r) = r`.  Forward:
    a fixed `P` equals `Object1 (predicateToRaw n P)`, an indicator, and its encoding
    round-trips by the fixedness itself.  Backward: an indicator that round-trips is fixed
    by substitution.  So naming the residue closes only on the self-encoding indicators —
    the rest re-open. -/
theorem reentry_fixed_iff (n : Nat) (P : Raw → Bool) :
    Object1 (predicateToRaw n P) = P
      ↔ ∃ r : Raw, P = Object1 r ∧ predicateToRaw n (Object1 r) = r := by
  constructor
  · intro hfix
    exact ⟨predicateToRaw n P, hfix.symm, by rw [hfix]⟩
  · rintro ⟨r, hP, hrt⟩
    rw [hP, hrt]

/-- ★★ **A fixed point is single-pointed.**  The necessary half of the characterization:
    if `P` is fixed by re-pointing, it is true at most at one Raw (it is an indicator).
    The contrapositive of `reentry_nonfixed_of_multipoint`, via `reentry_fixed_iff`. -/
theorem reentry_fixed_imp_single (n : Nat) (P : Raw → Bool)
    (hfix : Object1 (predicateToRaw n P) = P) (s t : Raw)
    (hs : P s = true) (ht : P t = true) : s = t := by
  obtain ⟨r, hP, _⟩ := (reentry_fixed_iff n P).mp hfix
  rw [hP] at hs ht
  exact (object1_true_unique r s hs).trans (object1_true_unique r t ht).symm

/-- ★★★ **The fixed-point picture, bundled.**  The fixed points of re-pointing are exactly
    the round-tripping indicators (`reentry_fixed_iff`), and in particular single-pointed
    (`reentry_fixed_imp_single`); dually any two-point predicate is excluded
    (`reentry_nonfixed_of_multipoint`).  The residue closes only on the self-encoding
    single points; every distinction-drawing predicate re-opens. -/
theorem reentry_fixed_characterization (n : Nat) (P : Raw → Bool) :
    (Object1 (predicateToRaw n P) = P
       ↔ ∃ r : Raw, P = Object1 r ∧ predicateToRaw n (Object1 r) = r)
    ∧ (Object1 (predicateToRaw n P) = P
       → ∀ s t : Raw, P s = true → P t = true → s = t) :=
  ⟨reentry_fixed_iff n P, reentry_fixed_imp_single n P⟩

/-! ## §5 — a concrete single-point indicator that is NOT fixed

`reentry_fixed_iff` says single-pointedness is necessary but not sufficient — the encoding
must round-trip.  Here is the concrete witness that it genuinely fails: the indicator of the
atom `b` (`Object1 Raw.b`) is single-pointed, yet its encoding lands on `numeral 0 ≠ b` (no
numeral is `b`, `numeral_ne_b`), so re-pointing it gives a *different* indicator.  A
single-point predicate that is not a fixed point — the iff "fixed ⟺ single-point" is
genuinely proper. -/

/-- The encoding of `Object1 Raw.b` is `numeral 0`, not `b`: `Object1 b` is false on every
    numeral (no numeral is `b`), so its truth table is all-zero and encodes to `numeral 0`. -/
theorem object1_b_encodes_to_numeral_zero (n : Nat) :
    predicateToRaw n (Object1 Raw.b) = numeral 0 := by
  have hfalse : ∀ i : Nat,
      Object1 Raw.b (numeral i) = (fun _ : Raw => false) (numeral i) := by
    intro i
    show Object1 Raw.b (numeral i) = false
    exact decide_eq_false (numeral_ne_b i)
  rw [predicateToRaw_kernel n (Object1 Raw.b) (fun _ => false) (fun i _ => hfalse i)]
  show numeral (E213.Lens.Foundations.PredicateSelfEncoding.truthTableNat n (fun _ => false)) = numeral 0
  rw [truthTableNat_const_false]

/-- ★★★ **A single-point indicator that re-pointing does not fix.**  `Object1 Raw.b` is true
    at exactly one Raw (`object1_true_exactly_one`), yet `Object1 (predicateToRaw n (Object1
    b)) = Object1 (numeral 0) ≠ Object1 b` (since `numeral 0 ≠ b` and `Object1` is injective).
    So single-pointedness does **not** imply fixedness — the round-trip condition of
    `reentry_fixed_iff` is a genuine constraint, witnessed concretely. -/
theorem object1_b_singlepoint_nonfixed (n : Nat) :
    (Object1 Raw.b Raw.b = true ∧ ∀ s : Raw, Object1 Raw.b s = true → s = Raw.b)
    ∧ Object1 (predicateToRaw n (Object1 Raw.b)) ≠ Object1 Raw.b := by
  refine ⟨object1_true_exactly_one Raw.b, ?_⟩
  rw [object1_b_encodes_to_numeral_zero n]
  intro h
  exact numeral_ne_b 0 (object1_injective h)

end E213.Lens.Foundations.ResidueReentry
