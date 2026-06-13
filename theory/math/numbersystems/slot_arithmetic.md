# Slot arithmetic — number systems from ℕ-slots alone

> "연산(자연수,자연수) → 자연수 인 연산들로 결합된 자연수 슬롯들로
> 자연수 자유도를 통해 수체계를 만든다" — *number systems are built
> from ℕ-slots combined by (ℕ,ℕ)→ℕ operations, through ℕ degrees of
> freedom alone.*  (Mingu Jeong, 2026-06-11.)

A new-field consolidation: the closed ∅-axiom core of the slot
programme, organized conceptually.  Every theorem cited is PURE
(`#print axioms` empty); Lean is the source of truth.

## 1. The ontology: the tuple is the number

Numbers are nested ℕ-tuples; **the tuple is the number** and the
nesting is the axis structure.  `(1,3)` is a two-axis number — it
*relates to* `(2,4)` (the cross-equation holds) but does not *equal*
it.  "Integer / rational / complex" are names for the
**operation-history of the axes**, not kinds of number.  No inverse
operation, no partial operation, no new primitive object ever enters:
negatives, fractions, and the imaginary unit are **addresses in slot
space**.  Reduction (lowest terms, canonical remainders) exists as a
*theorem about relations* — every orbit touches a distinguished point
— and applying it is a flattening Lens, one reading among several,
never the default.  Classical notation (`p+qi`, fraction bars,
`2 mod 2 = 0`) overloads symbols to hide the tupling; in slot form
nothing is hidden.

This ontology and the ∅-axiom discipline are one choice: total
ℕ-operations in witness form (`a = c + e`, never `a − c`) leave no
seam for partiality, choice, or `propext` to enter.

## 1.5 The floor: append, and where commutativity is born

One rung below `+` sits append (`Meta/Nat/UnitList.lean`).  The
sorted list is the list of *units* — indistinguishable elements make
insertion order and count order one thing, so no sorting exists or is
needed.  Append is associative for any element type but **not
commutative in general** (`append_not_comm_general`); on unit lists
commutativity is **born** (`append_comm`, by bare induction:
indistinguishable units carry no position information), and `+` is the
count readout of append (`count_append`).  Hence `add_comm_from_append`:
**`+`-commutativity is unit-list append commutativity read through
counting** — counting forgets arrangement, and what survives commutes.

The same birth recurs one rung up, in 2-D.  The `a × b` unit **grid**
(`Meta/Nat/UnitGrid.lean`) — `a` rows of `b` indistinguishable units —
is counted row by row as `a · b` (`total_rows`) and, after the
transpose that re-lays it as `b` rows of `a`, as `b · a`
(`transpose_rows` then `total_rows` again).  The transpose neither
loses nor invents a cell (`heads_tails_total`: peeling a column
preserves the count, bare induction, because units carry no position),
so the two counts agree and **`×`-commutativity is born from the grid
transpose double-count** (`mul_comm_from_grid`) — no `Nat.mul_comm` in
the proof.  Segment gives `+`-comm, grid gives `×`-comm: the swap
symmetry that count-forgetting turns into commutativity is the
transpose — which is also why commutativity stops being free above the
grid, since `^`'s value-object is a tree with no transpose.

One rung *below* append the same theme appears from the other side.
The free binary magma (`Meta/Nat/BinTree213.lean`) remembers its
bracketing (`node_not_assoc`); `append` is that tree **quotiented by
associativity** (`flatten_assoc_collapse` *is* `append_assoc`), and
`count` forgets even that.  So the floor hands the tower two forgettings
— bracketing (associativity, free) and order-on-units (commutativity).
The tower keeps both through `×`, and `^` loses **both at once**:
non-commutative (`HyperAssoc.pow_not_comm`, `2^3 ≠ 3^2`) and
non-associative (`pow_not_assoc`, `(2^2)^3 = 64 ≠ 256 = 2^(2^3)` — the
bracketing the floor discarded, back as information).  `×` is the last
assoc+comm rung; the only law `^` keeps, `(aᵇ)ᶜ = a^(b·c)`
(`pow_surviving`), linearizes `^` back down to `×` on the exponent
rather than closing `^` over itself — which is why the tower folds one
rung down.

The floor's "operation = append" reading is uniform up the tower: `+` is
unit-list append read by counting (`count_append`); `×` is **factor-list
append** read by the product (`Shape213.shapeProduct_append`:
`shapeProduct (l ++ m) = shapeProduct l · shapeProduct m`) — the same `append`,
one rung up, with *number* atoms instead of indistinguishable units; and `^` is
**factor-list repeat** (`Shape213.shapeProduct_lrepeat`:
`shapeProduct (lrepeat l k) = (shapeProduct l)^k`).  So the whole tower is
list-native (append / append / repeat), on lists and ℕ⁺ — no `0`, no `−`, no
quotient.  And the laws split by **direction**: the *vertical* (recursion-
structural) laws — generic in the level `k`, properties of the `iter` recursion
itself — survive *every* rung past `^` (`HyperLadder.{hyperop_climb,
hyperop_right_one, hyperop_arg_two, hyperop_base_one}`), while the *horizontal*
(algebraic) laws comm/assoc are the ones that die at `^`; the surviving
`(aᵇ)ᶜ = a^(b·c)` is one vertical law.

**Counted** rather than appended, the same tower is the **simplex**.  Each rung's
degree-graded count is the multiset coefficient `C(n+k−1, k)` — Pascal's triangle
(`MultSystem.monoCount_closed`; `monoCount_pascal`, `totalCount_closed`) — the
lattice points of a simplicial cone (the `+`-line's elements become the `×`-axes,
their degree-`d` multisets the cone).  Stacking the rule once more — the `^`-rung
over the `×`-monomials as axes — keeps it a simplex: `hyperCount_simplex :
monoCount (totalCount k N) d = C(d + M−1, M−1)` (`M = totalCount k N`), the number of
axes exploding (`1 → C(N+k,k) → …`) while the shape stays invariant.  The natural
object is the **semigroup** (degree `≥ 1`); the identity is the isolated `+1`
(`monoCountPos_closed : Σ_{n=1}^N monoCount k n + 1 = C(N+k, k)`), and the
prime-valued `×`-system is exactly `{2,3,…}` (`MultSystemValue.two_le_nonempty_prime_prod`).
The gap between this *degree*-count and the prime *value*-count is prime counting
(`chebyshev_prime_counting.md`); the `^`-rung's base/exponent asymmetry is the new
*dilation* degree-of-freedom, `m^b` parallel to `m` in the cone
(`MultSystemValue.hyper_parallel`, `vp_p(m^b) = b·vp_p m`).

**The object tower, built.**  The re-foundation reads each rung as its own *object*
(free nesting, no numbers), with `ℕ` the forgetful count-readout — and the objects
now run the full `+ → × → ^ → ↑↑`:

- `+` = the 1-D unit **list** (`UnitList`); `×` = the 2-D unit **grid** (`UnitGrid`);
- `^` = the `b`-dimensional unit **cube** `hcube a b` (`Meta/Nat/UnitHyper`): `a`
  translated copies of the dimension-`b` cube glued along a new axis, with
  `count (hcube a b) = a^b` (`count_hcube`) and **`count = side ^ dim`**
  (`count_eq_side_pow_dim`) — base read as a *side* (a length), exponent as a
  *dimension* (an axis count), two different-typed readouts whose swap changes the
  object's dimension (`swap_changes_dim`: the positive form of `2^3 ≠ 3^2`);
- `↑↑` = a cube whose *dimension is itself a tower count* (`Meta/Nat/UnitTetra`):
  `count (tetra a b) = hyperop 4 a b` (`count_tetra`), `dim (tetra (a+1)(b+1)) =
  count (tetra (a+1) b)` (`dim_tetra_succ`) — the dimension-clock lifted a second time.

The asymmetry is the **degree-of-freedom `DOF = rung − 2`** (`HyperLadder.dofOfRung`),
pinned non-vacuously to operand interchangeability: `×` (rung 2) commutes, `DOF = 0`
(`dof_two_comm`); `^` (rung 3) is the first non-commutative rung, `DOF = 1`
(`dof_three_not_comm`); `↑↑` (rung 4), `DOF = 2` (`dof_four`, the `+1`-climb twice from
the commutative base).  The base climbs one tower-level per rung while the count stays
at the `+`-level — the dilation readout `hyper_parallel` seen geometrically as the
cube's per-dimension `×a` (`MultSystemValue.hcube_vp_radial`).

**Dimension is computed, not a cardinal.**  Each rung's graded count `monoCount k`
carries its dimension as a *finite signature*: the forward difference drops the rung by
one (`diff_drops_rung`), so the iterated `Δ^{k+1}` **annihilates** rung `k+1`
(`diffIter_dim_zero`; `Δ^k` lands on the constant `1`, `diffIter_dim_const`) — the
dimension is the least annihilation depth, no cardinal `∞`.  Its inverse is the partial
sum: `Σ^k 1 = monoCount(k+1)` (`sumfIter_const_one`, the Hilbert series `(1−x)^{−(k+1)}`
as iterated summation), with `Δ`/`Σ` the dimension ∓1 operators (`diff_sumf`: `Δ∘Σ =
shift`, the discrete fundamental theorem).  (The conceptual reading of this — `∞`/the
continuous as construction-produced *shapes* characterized by finite signatures, and
the discrete↔continuous spiral — is tracked as an active frontier in
`research-notes/frontiers/`.)

## 2. The list and the sandwich

ℕ is the unit-started, unit-spaced sorted list, and its order *is*
the +-witness question: `a ≤ b ↔ ∃x, a + x = b`.  Equality is
manufactured from order — the conjunction of two strict one-sided
bounds (`Int213.eq_of_sandwich`) — so the **sandwich, not the
equation, is the proper probe**.  The bounds must be **strict**, never
`≤`: since `a ≤ b ↔ a < b ∨ a = b`, a `≤`-sandwich already contains the
`=` it would found — circular, and the sandwich pointless.  With no `=`,
a list element is located only as "right after `a`, right before `b`",
unique **exactly when `b` is `a`'s next-next**: `a < e < a+2 ⟹ e = a+1`
(`StrictLocate213.locate_strict`).  `=` is the *output* of that pointing;
`≤` is the derivative `a < b+1`; the +-witness order is itself strict at
root (`a < b ↔ ∃x, a+(x+1)=b`).  Probing with the sandwich splits what
the equation fuses (`PairOp.sandwich_locates`, `sandwich_unique`):

* **existence** of a location needs no monotonicity — only a
  reachable start and escape (progressivity `x ≤ f x`, the list's
  "results only move backward");
* **uniqueness** needs only monotonicity.

`NatDiv213.div_sandwich` (the ÷-floor) and the affine crossing are
instances.  The general question form is not "fold = constant" but
"**where do two monotone folds cross**", and the affine crossing
reduces exactly to the ÷-sandwich of the slot differences
(`NatDiv213.affine_cross_iff_div_sandwich`, `affine_cross_eq_div`).

## 3. Questions, slots, witnesses

A question `f a x = b` mints the pair `(a, b)`; the solution **is**
the question's slot tuple, and the number of ℕ-slots in a question's
standard expanded form is the solution's representation budget.  A
pair-slot's two naturals are one **orbit coordinate** (the only part
an answer depends on) plus one **fiber coordinate** (position along
the relation orbit) — raw ℕ-counts over-count by the fibers, and the
fiber does not vanish but **transports**: moving along the exponent
orbit moves the value along its own ×-orbit
(`PairPow.pairPow_fiber`, `pairPow_id`).  A question with all orbit
coordinates fixed has zero effective slots: its solution is a
**constant of its layer**, as `2` is of ℕ.

Beneath the cross-equations sits the property-free **witness layer**
(`PairOp` §2).  For an arbitrary `f : ℕ → ℕ → ℕ` — tetration
included — dropping every algebraic property and re-deriving exposes
the true jobs:

| discovery | theorem |
|---|---|
| the question bifurcates at step zero (`f a x = b` vs `f x a = b`); commutativity's first job is fusing the two pair kinds — the `^` root/log split lives here | `question_fuse` |
| the witness relation (`∃x` solving both questions) is primitive: symmetric free, reflexive exactly where witnessed | `sameWitness_symm`, `sameWitness_refl` |
| **cancellation's true job is witness uniqueness** — transitivity of the witness relation *is* uniqueness of the middle witness | `sameWitness_trans` |
| the cross-equation is the witness relation's *shadow*, cast by action-commutation `f a (f c x) = f c (f a x)` (strictly weaker than comm+assoc, which merely supply it); faithful back with cancellation | `crossEq_of_sameWitness`, `sameWitness_of_crossEq`, `action_comm_of_comm_assoc` |
| the slotwise lift's true actor is the **medial law alone**: the witness of the product is the product of the witnesses | `pairLift_witness` |
| with comm+assoc(+cancellation at the middle slot) the cross-relation becomes equality-like and the lift respects it | `pairEq_trans`, `pairLift_congr_left/right`, `exchange` |

**The interaction theorem** (`PairOp` §5) closes the table's last
row in both directions.  The lift of × onto +-pairs is **forced**:
bi-⊕-distributivity, one unit value, and three annihilation instances
(each a single cross-equation, exactly minimal) determine the cross
rule `(a,b) ⊗ (c,d) ≈ (ac+bd, ad+bc)` on every pair, with full
congruence and extension as corollaries (`cross_rule_forced`).  Under
the same selector, an operation that does not already bi-distribute
on the base has **no lift at all**: bi-additivity over the
difference-Lens readout admits only multiples of ×, and `2³ = 8 ≠ 6`
kills `^`, a fortiori tetration (`pow_lift_impossible`) — though the
selector is itself the ×-frame's law, so the native form of the wall
is the staircase statement below, not this nonexistence.

On the list, the prices localize (`PairOp` §3): a **progressive**
operation (strictly monotone in the unknown — "backward only, no
merging") gets cancellation free from the list structure
(`cancel_of_strictMono`); a **wrapping** operation (mod) keeps every
free step and the medial lift (`modAdd_medial`) but loses pointwise
cancellation (`modAdd_cancel_fails`) — informatively: its witness
sets are arithmetic progressions, so wrapping pairs mint **periodic
classes** rather than points, and the wrap itself is the
fiber-position readout of a progressive question (the ÷-sandwich's
remainder), not a new primitive.

## 4. The first two layers and their readouts

Instantiating the pair layer at `+` and `×`:

* `pairEq Nat.add` is the difference-pair cross-equation — equality
  of `subNatNat` readouts (`PairOp.pairEq_add_iff`,
  `Int213.subNatNat_eq_iff`); the sign is **which orientation of the
  question carries the ℕ-witness** (`Int213.witness_total`,
  `witness_not_both`, `subNatNat_eq_ofNat_iff`/`negSucc_iff`) — a
  readout, not a choice.
* `pairEq Nat.mul` is the ratio cross-equation
  (`PairOp.pairEq_mul_iff`, `RatioLensFounding.ratioEquiv`); its
  obstruction readout is the remainder, `a`-valued, always locating
  (`NatDiv213.div_sandwich`, `div_eq_of_sandwich`,
  `mul_witness_iff_mod_eq_zero`).
* **Each layer is closed under its own operation's slot-questions**
  (`Int213.subNatNat_add_witness`,
  `RatioLensFounding.ratio_mul_witness`): new numbers come only from
  *other* operations' questions.

Reduction is a possibility theorem, not an identity: the Bezout-free
Euclid chain (`Gcd213.gcd213_mul_left` distributivity by Euclidean
descent → `coprime_dvd_of_dvd_mul` → `gcd_strip_coprime` +
`coprime_repr_unique`) shows every ×-pair *relates to* a coprime one
and that the coprime point of each orbit is unique.

## 5. Signed rationals and the commuting square

Order does not descend through the sign quotient — a nonpositive
factor reverses `≤` (`OrderMul.mul_le_mul_right_nonpos`) — so the
signed layer reads the sign off first and runs cross-`≤` on
magnitudes: `Rat213.lowest_exists` / `lowest_unique` (the
sign-carrying normal form, existence and uniqueness; mixed signs are
excluded by constructor mismatch), `ratioLeZ_descends` / `ratioLeZ_iff` (the
derived order is well-defined on the positive cone).

The two routes ℕ→ℤ→ℚ and ℕ→ℚ₊→ℚ are two bracketings of ℕ⁴, and
**distributivity is the commutation law of the two pair-Lenses**:
`Rat213.qdiffEquiv` (the ℚ₊→ℚ leg, subtraction-free) corresponds
exactly to the ℤ-route under the comparison map
(`square_commutes`, with `ratioEqZ_trans`), and both routes meet in
one lowest-terms representative (`qdiff_same_lowest`).  The proof
content is precisely the mixed keystones
(`Int213.subNatNat_mul_ofNat`, `subNatNat_eq_iff`) plus
distributivity shuffles.  The 4-slot two-sided linear form is not a
postulate: unfolding the pair product shows **the "two sides" are the
two components of the pair slots** (`Int213.subNatNat_mul_eq_iff`).

## 6. Layer constants: √2 and i are siblings

Over ℕ-slots no imaginary number can arise — `x² = −1` is not an
ℕ-question (two ℕ-folds never cross in that direction:
`CompletionDichotomy.int_sumSq_eq_zero`, the anisotropy certificate
at the order frame).  It is a question **whose slots are already
+-pairs** — `x^(n,n+2) = (m+1,m)` — and by the same slot rule its
solution is a two-pair-slot number: four naturals.  Likewise
`x^(2/1) = 2/1` has no ℚ₊-witness, so `√2 = ((2,1),(2,1))`:

> **i is to +-pair slots what √2 is to ×-pair slots** — sibling
> constants of sibling layers, distinguished only by which pair layer
> the slots come from.

The closed 4-axis object: `GaussTuple.gmul` (the product written
subtraction-free), `gmul_i_i` (`i ⊗ i` *is* the +-inverse unit,
definitionally — the new axis folds back at depth 2, which is why the
axis count stops), `gmul_readout` (through the difference-Lens the
tuple product reads out to exactly the classical complex product —
the readout is a Lens on the tuple, not the tuple's identity).
Frame-visibility is question-relative, not absolute: the ∣-frames at
`p ≡ 1 (mod 4)` see `x² = −1` (`ModArith/QRNegOne.qr_neg_one`), the
Legendre symbol is the per-frame visibility readout, and quadratic
reciprocity its reciprocity law.

## 7. Boundaries

* **Equation vs sandwich-family**: a fold-back rule (`a·αⁿ` returns
  to the span of lower powers) stops the answer axes at the degree;
  no fold-back (the unknown in an exponent slot, as a class) leaves
  finite tuples for cut data.  The boundary is grammar-relative — a
  lattice of question grammars, not one line.
* **The interaction wall**: with the distributive selector, lifting
  a different operation onto +-pairs exists iff it already
  bi-distributes on the base (`cross_rule_forced` /
  `pow_lift_impossible`); without the selector, congruent extensions
  abound and nothing internal selects one.  The native form: the
  staircase ascends by iteration, pair-counted iteration consumes the
  inverse of the previous rung's action, each pair layer manufactures
  exactly that inverse (definitionally: the pair *is* the question's
  answer), and `^`'s answers (logarithms) are where the chain breaks —
  their *linear* fold-back absence is a **proved theorem**
  (`TwoThreeUnique.two_three_unique`: `2^a·3^b = 2^c·3^d → a=c ∧ b=d`,
  the exponent vector is unique), and the exponent lattice it lives in
  is itself ℕ-native (`VpMul.vp_mul`: for prime `p`, `vp p (m·n) =
  vp p m + vp p n` — the valuation is additive, the lattice's axis
  arithmetic) and **faithful** (`VpSeparation.vp_separation`: equal
  valuations at every prime force equal numbers — unique factorization),
  so the linear criterion is a full iff — `a^r = b^q` exactly when the
  two exponent-vectors point the same way at every prime
  (`FoldCriterion.pow_eq_pow_iff_vp`), with `two_three_unique` the `2,3`
  case of "distinct primes never collide" (`FoldCriterion.prime_pow_unique`).
  Their nonlinear fold-back absence is open classically
  (Schanuel territory).
* **Wrapping**: progressive operations are primary; wrapping
  operations are their fiber readouts, and their canonical-remainder
  normal form is a flattening Lens (`2 mod 2` is the class of `2`,
  not `0`).

## 8. Where the research continues

The pair layer's interaction-law rung (different-operation lifts
determined by distribution), the witness-form wrap relation and its
class-wise uniqueness, the generic-vs-specific transitivity of
`pairEq ^` (unique factorization vs the generic price), the minimal
polynomial as the next rung's lowest-terms normal form (Gauss's
lemma as the gcd-strip mirror), the exponent-lattice embedding
(`vp` multiplicativity and separation), and the frame-visibility
dichotomy `(∃x, p ∣ x²+1) ↔ p % 4 = 1` — each a continuation of a
closed theorem above, recorded on the frontier board.
