# The number-system square: two Lenses, two orders, one ℚ

*Audited by a 4-expert adversarial round (algebra / logic / number
theory / skeptic); corrections integrated in place, theorem targets
T1–T4 below.*

## Ontology: the tuple tower (the no-quotient reading is primary)

> "연산(자연수,자연수) → 자연수 인 연산들로 결합된 자연수 슬롯들로
> 자연수 자유도를 통해 수체계를 만든다" — *number systems are built
> from ℕ-slots combined by (ℕ,ℕ)→ℕ operations, through ℕ degrees of
> freedom alone.*  (Mingu Jeong, 2026-06-11.)  No inverse operation,
> no partial operation, no new primitive object ever enters; negatives,
> fractions, and the imaginary unit are **addresses in slot space**,
> not new kinds of number — which is also why every theorem of this
> arc carries the empty axiom set: total ℕ-operations leave no seam
> for partiality, choice, or `propext` to enter.

Numbers are nested ℕ-tuples, and **the tuple is the number**: the
nesting is the axis structure.  `(1,3)` is a two-axis number; a
Gaussian-type number is `(p,q)` when the components are naturals,
`((p₁,p₂),(q₁,q₂))` when integers, four pairs when rationals.  A new
axis corresponds to a new operation; "integer / rational / complex /
irrational" are names for the **operation-history of the axes**, not
different kinds of number.  The cross-equations
(`subNatNat_eq_iff`, `ratioEquiv`, `ratioEqZ`, `qdiffEquiv`) are
**relations between tuple-numbers, not identities**: `(1,3) ≈ (2,4)`
holds; `(1,3) = (2,4)` does not.  Reduction (gcd-strip, lowest terms)
is the theorem that every ×-pair *relates to* a coprime one — that
this is possible at all is the content (Euclidean descent); applying
it silently flattens the axes into the classical "one-line" systems,
which is a quotient Lens — one reading, not the ontology.  Classical
notation (`p+qi`, fraction bars) overloads `+` and `/` to hide the
tupling: the `+` in `p+qi` is *not* ℕ's `+` but the axis-combination
of a new operation (the pair arithmetic the keystones define).  The
question-tuple of `f(x) = b` **in standard expanded form** is the
solution's representation: `x+x=b` standardizes to `2·x=b`, so
`x = (2,b)`; `a^x = b` gives `x = (a,b)` (`(2,8) ≈ 3` is a relation,
not an identity); `(1+x)(1+x)=b` expands to `x²+2x+1=b` — five slots.
Everything below that speaks of "normal forms" is to be read in this
register: the normal form is the distinguished point of a relation
orbit, and naming the orbit by it is the *flattened* reading.

**One mechanism, not two (the imaginary unit dissolved).**  Over
ℕ-slots no imaginary number can arise: `f(x) = b` with ℕ coefficients
and ℕ right-hand side never needs one (the folds never cross in that
direction — the ℕ-witness form of `int_sumSq_eq_zero`).  "`x² = −1`"
is not an ℕ-question at all; it is a question **whose slots are
already +-pairs**: `x^(n,n+2) = (m+1,m)`.  By the same slot-tuple
rule that built everything else, its solution is a number with two
pair-slots — four naturals, exactly `GaussTuple`'s 4-axis object.  So
there is no second "rigid axis" mechanism: what was called rigidity
is *the question's slots sitting one level up, with no witness at
that level* — the ordinary witness dichotomy applied on the upper
layer.  The imaginary unit is the **solvability supplement for
+-pair-coefficient equations**, born at exactly the layer where slots
carry the +-pair structure, undefined before it.  And the mechanism
is operation-uniform: `(a,b)·x = (c,d)` (e.g. `2x = −5` vs `2x = 5`)
likewise needs four naturals — the signed rationals — while
`(a,b)+x = (c,d)` stays at one pair (witness exists in ℤ).  Unfolding
the pair product shows the earlier 4-slot two-sided form
`ax₁ + bx₂ + d = c + ax₂ + bx₁` is not a postulate but the pair-slots'
components laid flat: **the "two sides" are the two components of the
pair slots** (`Int213.subNatNat_mul_eq_iff`, PURE).  Slot accounting
with fibers (`PairPow`): a pair-slot = one orbit coordinate + one
fiber coordinate; raw ℕ-counts over-count by the fibers, the fiber
transports into the value's own ×-riding (`pairPow_fiber`,
`pairPow_id`), and a question with all orbits fixed
(`x^(n,n+2) = (m+1,m)`) has zero effective slots — its solution is a
**constant of the layer**, as `2` is of ℕ.

**Each layer is closed under its own operation's slot-questions**
(PURE: `subNatNat_add_witness` — `(A,B)+x=(C,D)` has the on-the-nose
pair witness `(C+B, D+A)`; `ratio_mul_witness` — `(a/b)·x = c/d` has
the ratio witness `(b·c, a·d)`); new numbers come only from *other*
operations' questions.  Hence the sibling constants: **i is to
+-pair slots what √2 is to ×-pair slots** — both are 4-natural
addresses of pair-slot ^-questions, `√2 = ((2,1),(2,1))` and
`i = ((n,n+2),(m+1,m))`, differing only in which pair layer the slots
come from.  The witness criterion for `x^(a/b) = c/d` over ℚ₊ is
divisibility of the prime-exponent (valuation) vector by the exponent
denominator — the obstruction-readout ladder climbs again: sign
(2-valued) → remainder (`a`-valued) → **exponent residues**
(vector-valued), the `vp` ground of T3 / brick 5.

**The meta-operation (the pair layer of an arbitrary operation) — ★
first rung CLOSED** (`Meta/Nat/PairOp.lean`, 10 PURE / 0 DIRTY).  For
*any* `f : ℕ → ℕ → ℕ` (+, ×, ^, tetration, …), the pair layer is
built step by step, each step paying a stated price in properties of
`f`:

| step | price |
|---|---|
| pair `(a,b)`; relation `pairEq f := f a d = f c b`; refl, symm | **free** (any `f`) |
| relation transitive (`pairEq_trans`) | commutativity + associativity + cancellation at the middle slot (for `×` that is `0 < q₂` — why ratio transitivity needed positive resolution) |
| slotwise lift of `f` to pairs (`pairLift`) | free to define |
| lift respects the relation (`pairLift_congr_*`) | commutativity + associativity (the `exchange` medial law) |
| lifting a **different** operation onto the pairs | the interaction law between the two (distribution) — **open**, the next rung |

Instantiations: `pairEq_add_iff` (= `subNatNat_eq_iff`),
`pairEq_mul_iff` (the ratio cross-equation, definitional).  Open
nuggets: (i) for `f = ^` the free steps stand and the priced generic
proofs fail (no commutativity) — yet `pairEq ^` may still be
transitive over ℕ via unique factorization: the first place where
*holds* and *holds for the generic reason* split; (ii) the
different-operation lift (× on +-pairs = the cross rule) should fall
out of distribution as the lift-determining law — tetration's wall =
no interaction law = no canonical lift, restated at the meta level.

**§2 — everything forgotten (★ CLOSED, `PairOp` §2, 19 PURE total).**
Dropping all properties and re-deriving exposes the true jobs, finer
than the price table above:

1. **The question bifurcates at step zero**: `f a x = b` vs
   `f x a = b` are different questions — commutativity's first job is
   fusing the two pair kinds (`question_fuse`); the `^` root/log
   split originates *before* relations or lifts exist.
2. **The cross-equation is not primitive**: the witness relation
   (`sameWitness` — the questions share a solving `x`) is the
   original, free and symmetric for any `f`; the cross-equation is
   its shadow, cast by **action-commutation**
   `f a (f c x) = f c (f a x)` (`crossEq_of_sameWitness`) — strictly
   weaker than comm+assoc, which merely supply it
   (`action_comm_of_comm_assoc`); faithful back with cancellation
   (`sameWitness_of_crossEq`).
3. **Cancellation's true job is witness uniqueness**: transitivity of
   the witness relation *is* uniqueness of the middle witness
   (`sameWitness_trans`).
4. **The lift's true actor is the medial law alone**: "the witness of
   the product is the product of the witnesses" (`pairLift_witness`)
   needs neither commutativity nor associativity directly.

**The interaction-law rung — ★ CLOSED** (`PairOp` §5, 31 PURE
total, panel-designed minimal form).  `cross_rule_forced`:
bi-⊕-distributivity + the unit `M(1,0)(1,0) ≈ (1,0)` + three
annihilation instances (A1–A3, exactly minimal by dimension count —
4 corner readouts, one linear equation each) force
`M (a,b) (c,d) ≈ (ac+bd, ad+bc)` for every pair; full congruence and
extension are corollaries.  `pow_lift_impossible`: under the same
selector, `^` (a fortiori `↑↑`) has **no lift at all** — bi-additivity
over the readout admits only multiples of × (`2³ = 8 ≠ 6`).  The old
slogan "no interaction law → no canonical lift" split into two
theorems: with the selector, nonexistence; without it, abundant
extensions and no selector (e.g. flatten-and-apply via truncated
subtraction).  Panel corrections recorded: the adversary's
counterexamples show full congruence (H1) is *not* a needed
hypothesis (three instances suffice) and one-sided distributivity is
strictly weaker (counterexamples both ways); the 213-native reading —
a second lift would be a function-valued dial no internal datum
selects (§5.1) — may now be asserted since the uniqueness is proved.
Follow-on targets queued: `pairPow_unique` (the ^-lift onto exponent
+-pairs — second instance, two pair relations, E1/E2 law split),
wrap-layer ℤ/n multiplication (no cancellation needed), `gmul_unique`
(the self-generating tower: level n+1 arithmetic = level n + one
fold-back equation), and the retroactive naming of
`ratioLeZ_descends` as the relational instance of the schema.

**§3 — the list picture and the wrapping boundary (★ CLOSED,
`PairOp` §3, 22 PURE total).**  ℕ as the unit-started, unit-spaced
ordered list; the order is itself the +-witness question, so the §1–§2
vocabulary (commutativity, cancellation, medial, …) consists of
ℕ-internal statements about `f` — no external algebra language.  Two
poles:

- **Progressive** ("results only move backward along the list,
  without merging" = strict monotonicity in the unknown slot): the
  list pays §2's price — cancellation/witness-uniqueness is free
  (`cancel_of_strictMono`).
- **Wrapping** (mod: results can land forward): every free §2 step
  survives, the medial lift survives (`modAdd_medial`), and only
  pointwise cancellation dies (`modAdd_cancel_fails`) — informatively:
  the witness sets are arithmetic progressions, so wrapping pairs mint
  **periodic classes** (ℤ/n) instead of points.  And the wrap is not
  a new primitive — it is the fiber-position readout of a progressive
  question (`div_sandwich`'s remainder), closing the loop: progressive
  operations are primary; wrapping operations are their fiber
  readouts.

**§ −1 — the rung below `+` (★ CLOSED, `Meta/Nat/UnitList.lean`,
9 PURE / 0 DIRTY).**  The originator's floor: forget algebra entirely
and start from the list and order alone.  The sorted list is the list
of **units** — no sorting exists or is needed, since indistinguishable
elements make insertion order and count order one thing.  `append` is
the operation one diagonal below `+`: associative free, **not
commutative in general** (`append_not_comm_general`), but on unit
lists commutativity is **born** (`append_comm` — units bubble freely),
and `+` = the count readout of append (`count_append`), so
**the commutativity of `+` is the shadow of unit-list append
commutativity** (`add_comm_from_append`): counting forgets
arrangement, and what survives the forgetting commutes.  Two
readings, both Lens choices: the completed list with operations as
addresses, or operations as applications of append.

**The staircase programme (open).**  The diagonal ascent
`append → + → × → ^ → ↑↑` is iteration: `H_{n+1}(a,b)` = iterate `b`
times the action `H_n(a,·)`.  Conjectured structure to derive from
the list alone: (i) the **counter-append law**
`f^(b+c) = f^b ∘ f^c` is *free* at every rung — it is append at the
counter slot; (ii) each rung's interaction law (`a(b+c)=ab+ac`,
`a^(b+c)=a^b·a^c`) requires additionally the **translation property**
— the iterated action reads as combining-with-a-constant
(`f^b(x) = x ⊙ f^b(e)`), an action-commutation fact; (iii) the
translation property fails for `x ↦ a^x` (no readout linearizes it),
which is the staircase-level *reason* for the rung-3 wall already
proved at the pair level (`pow_lift_impossible`).
**Selector-relativity caution (originator)**: `pow_lift_impossible`'s
selector (bi-⊕-distributivity) is the ×-frame's own law — the theorem
says "tetration is not multiplication", frame-laden.  The native
selector is **staircase coherence**: the lift of rung n+1 = the
pair-counted iteration of rung n's action; pair counters need the
action's inverse, and each pair layer manufactures the inverse of the
*previous* rung's action (+-pairs invert `+a` → × on ℤ; ×-pairs
invert `×a` → `pairPow` on the ratio layer); the inverse of `a^·` is
the logarithm — grade 3, sandwich-family only — so it escapes every
finite slot layer.  Rebuild bricks: pair-counted iteration over an
invertible action; the cross rule re-derived as the ⊕-action iterated
`(c,d)` times (replacing the distributive selector); the native wall
theorem ("the required inverse escapes") in place of the
selector-relative nonexistence.  Separation
discipline (originator): pair-part and operation-part must stay
unmixed — `PairOp`'s `f`-parametrization is exactly that separation,
and the pair-layer operations are *derived* objects
(`pairLift_witness`, `cross_rule_forced`), never definitions.

**§4 — sandwich-first (★ CLOSED, `PairOp` §4, 25 PURE total).**  On
the sorted list, order is the proper probe; equality facts are its
shadows.  Probing with the sandwich splits its halves, a separation
invisible from the equality side: **existence needs no monotonicity**
— only reachable start + escape/progressivity (`sandwich_locates`,
via the scan `locate_exists`); **uniqueness needs only monotonicity**
(`sandwich_unique`).  `div_sandwich`/`affine_cross` are instances.
Adopted convention (originator): the wrap layer's `2 mod 2` is the
relation class of `2`, **not** `0` — the canonical-remainder function
is the flattening readout (least point of the progression), one Lens,
not the wrap's identity.

Open: class-wise witness uniqueness for mod in witness form
(`wrapEq n a b := ∃ i j, a + i·n = b + j·n`, with `% n` as its
flattening readout — the ℤ/n cross-equation without normalization;
ground: `Gcd213.mod_eq_exists_mul_add`).

## The square

```
        difference pair (+-question)
   ℕ ────────────────────────────▶ ℤ
   │                               │
   │ ratio pair                    │ ratio pair
   │ (×-question)                  │ (positive denominator)
   ▼                               ▼
   ℚ₊ ───────────────────────────▶ ℚ
        difference pair of ℚ₊
```

Four paths, two composite routes (ℕ→ℤ→ℚ and ℕ→ℚ₊→ℚ); a rational is a
nested ℕ-pair in two bracketings.  The ℕ→ℤ→ℚ route is closed
(`Rat213`: Int numerator × positive Nat denominator, normal form
exact).  The ℕ→ℚ₊ leg is `RatioLensFounding.ratioEquiv`; the ℚ₊→ℚ leg
(difference pairs of positive ratios) is **not yet built**.

## Why the routes converge (the principle, to be made a theorem)

**Distributivity is the commutation law of the two Lenses.**  The
difference fiber is a +-action `(a,b) ~ (a+c, b+c)`; the ratio fiber
is a ×-action `(a,b) ~ (ka, kb)`; `k(a+c) = ka + kc` says the
×-transport maps +-fibers to +-fibers, so quotienting in either order
lands in the same place.  Repo pins: the mixed keystone
`Int213.subNatNat_mul_ofNat` (difference pair × scalar), the ∣-side
`Gcd213.gcd213_mul_left`, and the canonical target
`Rat213.lowest_exists`/`lowest_unique` (any presentation normal-forms
to sign × coprime pair).  Contrast: where commutation *fails* —
order × sign, `OrderMul.mul_le_mul_right_nonpos` — the square does
not close and the positive cone must be carved out first.  Same
phenomenon, positive and negative instances.

Classical home (audit): the square is "group completion commutes with
localization" (K-theoretic commutation); categorically the right
statement is not a Beck distributive law but that the
group-completion monad on commutative monoids is a **commutative
(monoidal) monad** — a rig is a monoid in (CMon, ⊗), and
distributivity is the monoid datum the monad transports
(`subNatNat_mul_ofNat` is its Lean shadow).  What the 213/∅-axiom
framing adds is not the isomorphism but its **quotient-free form**:
normal-form confluence with a computable normalizer, checkable under
`#print axioms` (Mathlib-style proofs need `Quot.sound`).

## The detectors (judgment formulas across levels)

Each rung's judgment formula becomes, one level up, the membership
detector of the old system and the normal-form selector of the new:

| formula | in ℕ | in ℤ / ℚ₊ | in ℚ |
|---|---|---|---|
| sandwich (order) | witness dichotomy (`witness_total`/`not_both`) | sign readout (`subNatNat_eq_ofNat_iff`/`negSucc_iff`) | floor / integer part (`div_sandwich` lifted); ℤ-membership = denominator 1 |
| coprimality (∣) | a relation between two naturals | lowest-terms selector (`gcd_strip_coprime` + `coprime_repr_unique`) | canonical representative (`IsLowest`); ℕ/ℤ-membership = `b ∣ a`; Farey `det P = 1` |

In ℚ the two detectors are exactly the two normal-form projections:
order frame → sign + integer part; ∣ frame → coprime magnitude pair.
Audit upgrade: the sign readout *is* the residue readout of the
archimedean frame ({±} the "residue field" at ∞), the remainder the
residue readout at the finite frames — one readout-per-frame schema,
and **the frame list is exactly {order frame} ∪ {one ∣-frame per
prime}** (Ostrowski is the classical exhaustiveness statement for
this two-detector table).

## The equation ladder (extension of the square)

Each system is the totality domain of an equation class with ℕ
coefficients and **one unknown**:

| class | completion |
|---|---|
| `x + b = c` (monic, +) | ℤ |
| `a·x = b` (×) | ℚ₊ |
| `a·x + b = c·x + d` (two-sided degree 1) | ℚ |
| monic polynomial | algebraic integers |
| general polynomial | algebraic numbers |

Two rules to pin: (i) class = one reversed arrow + closure under the
available folds; degree = ×-question iterated on the unknown;
(ii) **monic ↔ ring-like, general leading coefficient ↔ field-like**
— at the top this is "monic = integral element" (the
leading-coefficient trick makes general = integral ∘ localization);
at the bottom it requires a theorem, not a table row: ℤ is the
integral closure of ℕ in ℚ **by the rational root theorem** (target
T2 below).  Boundary: non-polynomial questions (`a^x = b`) leave
equation-completion for sandwich-family completion (ℝ order-frame,
ℚ_p ∣-frame); note `a^x = b` can land anywhere (2^x=8 in ℕ, 4^x=8 in
ℚ, log₂3 transcendental) — the *class* is sandwich-only, not each
instance.

## Collapse vs rigid axis — a property of (question, frame) pairs

A pair-Lens either *collapses* (quotient by the operation's action —
ℕ→ℤ→ℚ, dimension stays 1) or stays a *rigid axis* (ℚ(√2) over ℚ;
ℝ→ℂ→ℍ→𝕆 Cayley–Dickson).  **The dichotomy is frame-indexed, not
absolute** — the repo itself proves both sides for `x² = −1`:

- invisible at the **archimedean** frame:
  `CompletionDichotomy.int_sumSq_eq_zero` (the `a²+b²` anisotropy
  certificate *at the real place*), `sq_eq_neg_sq_imp`,
  `no_rat_sqrt_neg_one`;
- **visible at the ∣-frame of every prime `p ≡ 1 (mod 4)`**:
  `ModArith/QRNegOne.qr_neg_one` (`∃ x, p ∣ x²+1`, PURE; `2²+1 = 5`),
  Hensel-liftable by the `Padic/` kit — ℚ₅(i) = ℚ₅, the extension
  *collapses* 5-adically; and `Padic/Teichmuller` already builds
  μ_{p−1} *inside* the ∣-frame completion.

So visibility of `x² = a` per frame **is the Legendre symbol**, the
two supplements + `quadratic_reciprocity` (all PURE in
`ModArith/`) are the **reciprocity law of frame-visibility**, and the
classical local-global (Hasse) structure is what the collapse-vs-rigid
axis becomes once "frame" is taken at its word.  Long target: the
Hilbert-symbol product formula = "the set of frames where a binary
quadratic question is invisible is finite and **even**" — a global
parity constraint on visibility, equivalent over ℚ to QR + the
supplements (no Hilbert-symbol module exists in the repo yet).

Non-circular form of the criterion (audit): "obstruction readout
valued in old data" must be a *specified equivariant map* δ from the
pair space into old data (sign : witness side; remainder : `Fin a`),
and the schema is **collapse-at-a-frame ⟺ δ admits an old-valued
section splitting the solution correspondence ⟺ the same-solution
equivalence has a PURE-constructible transversal** (existence +
uniqueness of a normal form).  Rigidity = a nontrivial symmetry of
the solution set survives every expansion the frame provides (±i
conjugation; `int_sumSq_eq_zero` certifies no archimedean choice).
Note the house discipline and this schema are one phenomenon: with
`Quot.sound` banned, a quotient can only enter the repo *as* a proved
transversal (`lowest_exists`/`lowest_unique`,
`witness_total`/`witness_not_both`) — "collapse ⟺ the transversal is
PURE-constructible" is the schema brick 4 should aim at.

The CD conjugation `(a,b)* = (a*, −b)` is the iterated sign-swap
(`neg_subNatNat`); the per-doubling law-loss ladder (order →
commutativity → associativity → norm composition) is combinatorially
derivable and partially PURE in `Lib/Math/Algebra/CayleyDickson/`.
Caution (audit): the CD doubling tower (dims 2,4,8) and the
**cyclotomic torsion tower** are distinct towers that coincide at `i`
and diverge at `ω` — `ImaginaryQuadraticUnitTrichotomy`'s 2/4/6 is
the crystallographic bound `φ(n) ≤ 2` (n ∈ {1,2,3,4,6}), not iterated
doubling; ω has minimal polynomial of degree 2 but torsion order 6,
and arises from no CD step.

## The hyperoperation refinement (^ splits along the normal form)

`^` is non-commutative, so it has **two** reverse questions: root
(`xⁿ = b`, algebraic) and log (`aˣ = b`, sandwich-family as a class).
The root-completion acts on the sign × magnitude normal form
**factorwise**:

| operation | exponent-lattice event | completion |
|---|---|---|
| + | ℕ → ℤ | ℤ |
| × | per-prime exponents ℕ^ω → ℤ^ω | ℚ₊ (= the +-completion re-run inside the exponent lattice) |
| ^ root | magnitude exponents ℤ^ω → ℚ^ω **and** sign torsion → μ_∞ | radicals (order-visible, absorbed by ℝ) + roots of unity (torsion → rigid *at the archimedean frame*; first rung `i`; frame-relative per the ∣-visibility above) |
| ^ log | leaves the lattice | sandwich-family only (the ℝ boundary) |

**The rule terminates at rung 3** (audit): the engine of the ×→^ step
is the exponent-law package (`a^{m+n} = a^m·a^n`, `(a^m)^n = a^{mn}`,
one-sided `(ab)^c = a^c b^c`), which makes exponents a
lattice/module; tetration satisfies **no** analogous law
(`(2↑↑2)↑↑2 = 256 ≠ 2↑↑4 = 65536`; `2⁴ = 4²` shows depth-2 fibers are
wild), so there is no exponent lattice to re-run anything inside —
state the rule as a rungs-1–3 theorem with the distributivity
hypothesis explicit plus a rung-4 **no-go** (`x^x = 2` is
transcendental: Gelfond–Schneider + unique factorization — ↑↑-roots
land outside *all* equation completions).  The ^-level "free parts
collapse, torsion parts rigid" survives with the frame index added.
Polar form `r·e^{iθ}` = the sign × magnitude normal form lifted
through the ^-completion.

## Question tuple vs answer axes (the representation principle, audited)

**The representation principle (grammar-relative form).**  Fix the
question grammar: admissible questions are crossings of two
**subtraction-free monotone folds** (terms of the positive signature
(0,1,+,×,^), monotone in the unknown); slots = the ℕ-positions of the
two terms.  This restriction is not a convention but the
*definition of locatability*: a question is admissible iff its answer
is pinned by a crossing sandwich (`div_sandwich_unique`,
`affine_cross_iff_div_sandwich` are the uniqueness certificates), and
Gödel/Cantor pairing is excluded because un-pairing is intrinsically
non-monotone.  Then: the solution is represented by the question's
slot tuple **modulo the same-solution equivalence, plus finite
orientation/selector bits**, and the well-defined invariant is the
**size of the canonical transversal** (the lowest-terms normal form),
not the raw slot count — e.g. ℚ: 4 slots + 2 orientation bits
pre-quotient, transversal = 2 naturals + 1 sign bit (`Rat213`);
`affine_cross_iff_div_sandwich` *reduces* the 4-slot form to 2 slots
(e, f) + orientation, so the 4-slot presentation is canonical-but-not
-minimal.  The principle as stated is an **upper bound**; minimality
lower bounds (no 1-slot monotone question pins √2) are unproved —
open.  The shadow of slot *count* is **degree**; classical **height**
is the slot *values*: representation cost refined =
(transversal size, max slot value), under which Northcott becomes
bare tuple counting (finitely many tuples below a bound; ≤ n
solutions each by `PolyRoot/FactorTheorem`) — the principle's genuine
content is relocating that finiteness from analysis to ℕ-counting.

**Grades, corrected**: the invariant is the **×-degree of the unknown
in the distributed, same-solution-minimized normal form** (raw
occurrence count is presentation-dependent: `x+x=b` is degree 1,
collapse; `(1+x)·(1+x)=b` has one syntactic occurrence but degree 2):

1. degree 1 — definable transversal, **collapse** (ℤ, ℚ₊, ℚ);
2. degree n ≥ 2 (irreducible after the polynomial gcd-strip) — the
   answer system grows n axes, **rigid over the base** (frame-relative
   absorption per the dichotomy section);
3. unknown in an exponent slot (`aˣ = b`) — no fold-back; the *class*
   completion is sandwich-family (instances may land low: `2^x = 8`).

**The mixed form, derived from the sandwich (the crossing rule).**
Slot attachment preserves monotonicity in the unknown (+-slots,
positive ×-slots, exponent slots; a subtraction slot would break it —
that data lives in the crossing **orientation**).  The general
question is "*where do two monotone folds cross*"; the constant is
the degenerate crossing partner.  Crossing sandwich:

```
        F(x) ≤ G(x)  ∧  G(x+1) < F(x+1)
```

For affine folds this **reduces exactly to the ÷-sandwich of the slot
differences** — closed PURE (`NatDiv213.affine_cross_iff_div_sandwich`,
`affine_cross_eq_div`: witness form `a = c + e`, `d = b + f`, location
`f / e`).  The reduction direction is 4 → 2 + orientation; the sign
data is the crossing orientation (steeper / starts-higher).
**Reach and selector (audit)**: any integer polynomial is a difference
of two ℕ-monotone folds, and clearing denominators on ℚ-grids
preserves this — so refined crossings reach exactly the **real
(order-visible) algebraic numbers**, never the complex ones (for
`x²+1` vs `0` the folds never cross: `int_sumSq_eq_zero`).  For
degree ≥ 2 the sandwich locates *a* crossing, not *the* root
(`x³+30` vs `20x` has two); the honest datum is (slot tuple,
**isolating window**), and the canonical witness-form selector is a
**Stern-Brocot path prefix** (a det-1 Farey interval certificate —
`Real213/SternBrocotMarkov.adj`), with Sturm/Descartes as the
decidability that a sufficient prefix exists.  The affine crossing is
the continued-fraction step (Euclid = iterate the ÷-sandwich and
swap), so the refined crossing *is* the repo's Stern-Brocot machinery
and "best rational approximations = record-setting crossings" is the
Markov-spectrum program already running in `Real213/`.

**Witness-form discipline (house rule, stated).**  Constructions are
phrased over ℕ-pairs only: extension systems are *targets being
described*, never *tools used in the description* — no inverse
operations or imported systems in hypotheses.  Every closed theorem
of this arc obeys it (`gcd_strip_coprime`'s `a = g·a₁`;
`subNatNat_eq_negSucc_iff`'s `b + (y+1) = a`; `affine_cross`'s
`a = c + e`).  Constructive content (audit): these proofs live in the
primitive-recursive (PRA/IΣ₁) fragment — witness-form hypotheses are
Σ₁-graph definitional extensions, so every theorem carries witness
extraction; and `eq_of_sandwich`'s positively-witnessed equality is
the discrete case where Bishop apartness is decidable — at the ℝ rung
the polarity flips (equality Π₁, apartness the Σ₁ primitive), so
lifting the dichotomy to ℝ→ℂ will need apartness-relative phrasing.

**The degree-n mix, same rule**: the crossing of `a·xⁿ + b` and
`c·xⁿ + d` in witness form — data `((c, e, b, f), n)`.  The
orientation dichotomy is total for `n = 1` (mismatch moves the
witness to the slot-swapped question, the x-reflection); **even folds
are reflection-symmetric, so a mismatched orientation cannot be
moved** — the archimedean rigidity (`int_sumSq_eq_zero`, the
cleared-denominator form at `n = 2`).  Fully general:
`Σ aᵢ x^{eᵢ} = Σ bⱼ x^{fⱼ}` — the equation data is itself a **pair of
ℕ-polynomial folds**: the pair structure recurs one level up, whose
lowest-terms normal form is the minimal polynomial (brick 6 — and the
precise mirror of `gcd_strip_coprime`/`coprime_repr_unique` one rung
up is **Gauss's lemma**: content/primitive-part = gcd-strip on
coefficient tuples, uniqueness via Euclid-for-polynomials with degree
as the descent measure).

The fold-back rule: adjoining α a priori creates axes α, α², …; the
equation sends the n-th power into the span of the first n, so the
axes stop at n; degree 1 folds α itself into the base (collapse);
k independent square roots give 2^k axes (compositum doubling, the
commutative twin of the CD tower; `ZSqrt*`/`ZOmega`/`ZI` the 2-axis
PURE instances, `HurwitzTower` the 4-axis).  **Algebraic vs
transcendental = finite fold-back vs infinite axes**, relative to the
polynomial grammar; with ^-slots admitted, finite-data questions pin
some transcendentals (log₂3), and the period class (volumes of
ℚ-semialgebraic regions — monotone under domain inclusion, hence
sandwich-locatable) sits strictly between — the boundary is a
**lattice of question grammars**, not a single line.

## Open bricks (theorem targets after the audit)

- **T1 (square-commutes) — ★ CLOSED** (`Rat213.qdiffEquiv` /
  `square_commutes` / `ratioEqZ_trans` / `qdiff_same_lowest`, all
  PURE; the ℤ-side keystone `Int213.subNatNat_eq_iff` — the
  difference-pair cross-equation, the ℤ-twin of `ratioEquiv` — added
  to Core).  `qdiffEquiv P R ↔ ratioEqZ (β P) (β R)` with
  `β = (subNatNat (p₁·q₂) (p₂·q₁), q₁·q₂)`, no positivity needed for
  the iff; with positive denominators both routes hit the same
  `IsLowest` representative.  Proof content = `subNatNat_mul_ofNat` +
  `subNatNat_eq_iff` + distributivity shuffles — bricks 1+2 closed:
  "distributivity is the commutation law of the two Lenses" is now a
  theorem.
- **T2 (bottom-rung integrality / rational root).**  Witness form:
  `gcd213 p q = 1 → 0 < q → pⁿ + Σ aᵢ pⁱ q^{n−i} = Σ bⱼ pʲ q^{n−j}
  (i,j < n) → q = 1` — "ℤ is the integral closure of ℕ in ℚ", making
  monic↔ring a theorem (n = 2 first; iterated
  `coprime_dvd_of_dvd_mul`).
- **T3 (exponent-lattice embedding).**  For prime p:
  `vp p (m·n) = vp p m + vp p n` and separation
  `(∀ p prime, vp p m = vp p n) → m = n` — turns "ℚ₊ = the exponent
  lattice" into mathematics, on top of `coprime_dvd_of_dvd_mul` +
  `le_vp_iff`.
- **T4 (frame-visibility dichotomy).**  For odd prime p:
  `(∃ x, p ∣ x² + 1) ↔ p % 4 = 1` — one direction is `qr_neg_one`
  (PURE, closed); the converse (p ≡ 3 → invisible) via the repo's
  Euler-criterion kit.  First theorem of the frame-indexed dichotomy;
  long target: Hilbert-symbol parity (invisible-frame set is even).
- **Brick 5 (magnitude side)**: the ℚ₊ exponent lattice and its
  divisible hull as the ^-root completion (`le_vp_iff` → radical
  tower); precision: the divisible hull of the *sign* factor alone is
  ℤ(2^∞); all of μ_∞ arises because root-completion adjoins ratios of
  solutions.
- **Brick 6 (minimal polynomial = lowest terms, one rung up)**:
  existence + uniqueness via Gauss's lemma as the gcd-strip mirror;
  ground: `PolyRoot/` (FactorTheorem, IntEuclid) + `ZSqrt*`.
- **Brick 7 (selector)**: the isolating-window selector as a
  Stern-Brocot path prefix with `adj` certificate — the bridge
  theorem "CF quotients of `f/e` = iterated ÷-sandwich locations =
  run-lengths of the Stern-Brocot path".
- The Lens-frame essay after the Lean closes, not before.
