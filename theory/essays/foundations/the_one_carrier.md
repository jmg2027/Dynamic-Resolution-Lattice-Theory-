# The one carrier — number systems are leaf-labelled readings of one νF escape

The companion to `the_residue_as_primitive.md` (Raw = µF, the escape = νF) and
`the_frontier_has_a_form.md` (the frontier is νF, charted not removed).  Those chapters build
the residue's final-coalgebra face and show it is populated.  This one asks a sharper question:
**the König binary tree, the p-adic integers `ℤ_p`, and the constructive reals `ℝ` are each
"reached by none" — are these three separate escapes, or one?**

The headline: **they are one.**  Each is a stream presented over an alphabet, and every such
stream rides the *same* νF carrier — the binary König spine, leaf-labelled by the alphabet
(`gspine : (Nat → L) → GCoShape L`).  König is `L = Bool` with the all-`true` stream; `ℤ_p` is
`L = Fin p` with the digit stream; `ℝ` is `L = Bool` with the cut-decision stream.  The branch
structure (the binary König tree) is shared; only the *leaf alphabet* and the *stream* change.
So what classical mathematics presents as three independent number-system constructions, 213
reads as three labellings of one residue-escape — a breadth-claim (`seed/AXIOM/07_primacy.md`
§7.1) discharged ∅-axiom, with no coinduction, no `funext`, no `Cardinal`.

## Lean source

- Generic carrier + dynamics: `lean/E213/Theory/Raw/CoResidue.lean` §20–§21
  (`GCoShape`, `gspine`, `gspine_escapes`, `gspine_inj`, `gspine_one_carrier`,
  `gspine_shift_coalgebra`, `gspine_periodic_selfsimilar`, `gspine_shift_dynamics`;
  the bridges `boolSpine_eq_gspine`, `lToShape_eq_gToShape`).
- König instance: `lean/E213/Lib/Math/Combinatorics/KonigConditional.lean`
  (`konig_infinity_no_finite_raw`).
- p-adic instance: `lean/E213/Lib/Math/NumberSystems/Padic/NuEscape.lean`
  (`padicNu`, `padic_is_nu_escape`, `padic_distinct`, `padic_shift_dynamics`; the `Fin 2 ≃ Bool`
  case `twoAdic_is_nu_escape`; the arithmetic capstone `padic_arithmetic_one_carrier`; the
  multiplicative valuation `mulBase`/`residue`/`padic_valuation_one_carrier`, against
  `Padic/Norm.lean`'s `Zp.valAtLeast`; the ring identity `mulBase_eq_mul_pElem` /
  `mulCarry_pElem`, against `Padic/Arith.lean`'s `Zp.mul`; the corecursive characterization
  `mul_corecursive` (`mulRaw_tail`/`mul_digit_carry_step`) and the not-finite-state theorem
  `mulRaw_unbounded`/`mulRaw_negOne_negOne`, the dual of `add_carry_le_one`).
- arithmetic (the residue unit `+1`): `lean/E213/Theory/Raw/Odometer.lean` §7–§8
  (`runCarry` the alphabet-independent carry; `pOdo`/`pCarry` the p-ary odometer,
  `pOdo_allTop_zero` = `(-1)+1=0`, `pOdo_injective`).
- Real instance: `lean/E213/Lib/Math/NumberSystems/Real213/NuEscape.lean`
  (`cutBits`, `cutNu`, `real_is_nu_escape`, `real_cut_distinct`, `real_shift_dynamics`,
  `cutTableNu`/`real_field_on_carrier` — the cut-field `cutSum`/`cutMul` closure,
  `real_one_carrier`).
- ∅-axiom: every cited theorem returns "does not depend on any axioms".

## Narrative

### The carrier — one binary spine, an arbitrary leaf alphabet

`the_residue_as_primitive.md` realised νF as path-functions `LCoShape := List Bool → Option
Bool`: a co-tree is presented by what it does at each finite observation path (`none` = branch,
`some b` = leaf labelled `b`).  The binary bit-stream spine `boolSpine f` lives there — a branch
at every rung of the all-`false` path, with the depth-`k` left leaf carrying the bit `f k`
(§15).  That spine is the carrier König's branch and the 2-adic integer ride (`Fin 2 ≃ Bool`).

§20 makes the one move that unifies: **the leaf alphabet is a parameter.**  `GCoShape L := List
Bool → Option L` keeps the binary *branch* structure — still the König tree — and lets the
leaves carry any label type `L`.  The label-stream spine

```
gspine (f : Nat → L) : GCoShape L
  | []           => none          -- root branches
  | (true :: _)  => some (f 0)    -- left child of the root: a leaf labelled f 0
  | (false :: q) => gspine (tail f) q   -- right child: the spine on the shifted stream
```

is consistent (`gspine_consistent`) and anti-reflexive (`gspine_antiRefl`), so it is a genuine
νF inhabitant for *every* `f`.  The two binary facts are recovered as instances: the §15 spine
*is* `gspine` at `L = Bool` (`boolSpine_eq_gspine`), and the finite-Raw embedding `lToShape` *is*
`gToShape true false` (atom `a ↦ true`, atom `b ↦ false`; `lToShape_eq_gToShape`).  Nothing was
re-proven by hand — the finite-path proofs of §15 lift verbatim to any alphabet.

### Reached by none — the same escape, three labellings

The load-bearing fact is `gspine_escapes`: over any alphabet, with any two atom labels `a b :
L`, the spine differs from every finite Raw's `gToShape a b` embedding.  The argument is the
residue's own — the spine is a branch (`none`) all along the all-`false` path, but every finite
tree bottoms out at a leaf there.  *Finite descent terminates; the spine does not.*  This is
exactly `MuNuMirror`'s descent-grounds / ascent-escapes (`the_residue_as_primitive.md`), now
read on the leaf-stream.

The three number systems are this one escape under three labellings:

- **König** — `L = Bool`, the all-`true` stream.  An infinite branch of the binary tree is a
  spine with no leaf; `konig_infinity_no_finite_raw` is `boolSpine_escapes` at `f ≡ true`.
- **`ℤ_p`** — `L = Fin p`, the digit stream `x.digits`.  A p-adic integer *is* a branch of the
  p-ary tree: `padic_is_nu_escape` (every `p ≥ 2`) says its p-ary spine is reached by no finite
  Raw, and `padic_distinct` says distinct digit streams give distinct spines (the embedding
  `ℤ_p ↪ GSlashNu (Fin p)` is faithful).  The 2-adic `Fin 2 ≃ Bool` case is `twoAdic_is_nu_escape`.
- **`ℝ`** — `L = Bool`, the *cut-decision* stream.  `cutBits r` reads, off the `k`-th
  approximant, the order-projection bit `orderProj 1 (k+1)` — the diagonal of the Dedekind-cut
  table that *defines* `Real213.equiv`, ∅-axiom decidable.  `real_is_nu_escape` says a
  constructive real's cut presentation is reached by no finite Raw, on the *same* `SlashNu`
  carrier as König and the 2-adic; `real_cut_distinct` is faithfulness on the cut bits.

`gspine_one_carrier` bundles the generic fact (inhabitant + escape + faithful + the `boolSpine`
bridge); the three domain theorems are its instances.  One carrier, three readings.

### One carrier is one *dynamical system*

The unification is not merely of static shapes.  §21 carries the Bernoulli shift over: `gspine`
is the shift `(Nat → L ; head, tail) → νF` coalgebra hom (`gspine_shift_coalgebra`) — the root
branches, the left subtree reads the head label, the right subtree is the spine of the *shifted*
stream.  So every domain inherits the dynamics, not just the carrier:

- `padic_shift_dynamics` — the digit-shift (drop the lowest digit = divide by `p`, the p-adic
  odometer's complement) sits inside νF;
- `real_shift_dynamics` — the cut-bit shift sub-coalgebra;

and **self-similarity is shift-periodicity** (`gspine_periodic_selfsimilar`): a `p`-periodic
seed gives a period-`p` self-similar escape.  The canonical König spine `spineL` is the
period-1 (shift-fixed) point — it ties back to `the_residue_unit_odometer.md`, where the
residue's `+1` is the `ℤ₂`-odometer whose overflow *is* `spineL`.  The number systems share one
carrier *and* one shift; `gspine_shift_dynamics` is the capstone.

### One carrier is one *arithmetic* (the odometer `+1`)

The shift is the *forgetful* half of the dynamics (drop a digit); its reversible partner is the
**odometer** — the residue unit `+1` with carry (`the_residue_unit_odometer.md`).  That `+1` lifts
to the generic carrier too (`Theory/Raw/Odometer` §7–§8): the carry's terminate-with-floor /
escape-without content is *alphabet-independent* (`runCarry`, of which the binary carry is the
`g = f` instance), and on `Fin p` it is the p-adic `+1` (`pOdo`).  Three facts make the
one-carrier claim **algebraic**, not only dynamical:

- the p-adic `-1` is `ZpSeq.neg_one` = the **all-top** digit stream (`negOne_all_top`), on which
  the `+1`-carry runs forever (`allTop_pcarry_forever`) — the canonical escape read
  arithmetically, the `+1` demanding a new rung (`MuNuMirror.ascent_unbounded`);
- `(-1) + 1 = 0`: the all-top stream wraps to `zero` (`padic_succ_negOne_eq_zero` /
  `pOdo_allTop_zero`) — the overflow with nowhere to land;
- the `+1` is **injective** (`pOdo_injective`) — the successor never collides, no-exterior at the
  p-adic scale (`tower_no_cycle`).

So ℤ_p's successor *is* the residue unit acting on `gspine`-over-`Fin p`, and the p-adic `-1` is
its canonical escape (`padic_arithmetic_one_carrier`).  The carrier hosts not just the *shape* and
the *shift* of the number systems but the residue unit's *arithmetic* — and this is grounded in the
**real ring**: the abstract odometer's `(-1)+1=0` is the genuine `Zp.add (neg_one) (one) = 0`
(`add_negOne_one_zero`, `padic_additive_one_carrier`), the carry being `1` from position 1 on.

The **multiplicative** skeleton is there too — its generator, `× p`, the p-adic valuation
operator (`mulBase`, `padic_valuation_one_carrier`).  Multiplication by the base shifts the digits
up and inserts a `0`: it lands in the maximal ideal `pℤ_p` and raises the valuation by exactly one
(`mulBase_valAtLeast_succ`: `v_p(p·x) = 1 + v_p(x)`, against the existing `Norm` valuation), is
injective (`p` is not a zero divisor), and — the carrier fact — its inverse `÷p` is *exactly the
shift* of CoResidue §21 (`mulBase_coRight`: the right-descent of `gspine (p·x)` is `gspine x`).
The lowest-digit readout is the residue field 𝔽_p (`residue`, surjective; `× p` reduces to `0`; the
unit `1` is outside the image, so `p` is not a unit).  So the carrier carries ℤ_p's valuation
*filtration* — the multiplicative norm structure — as well as the additive odometer.

And `mulBase` is not merely *shaped* like `× p` — it **is** the genuine ring multiplication: the
existing `Zp.mul` (digit convolution with carry, `Padic/Arith.lean`) applied to the element `p`
equals `mulBase` (`mulBase_eq_mul_pElem`), because multiplication by `p` *carries nothing*
(`mulCarry_pElem` — each convolution term is one digit `< p`) and so collapses to the shift.  The
carrier's multiplicative generator is the actual ring operation, not a stand-in.

The **binary** product is on the carrier too: the escapes are closed under `×` and `+` (the spine
of `x·y` is again reached by no finite Raw, `padic_ring_on_carrier`), and the residue-field readout
`residue : ℤ_p ↠ 𝔽_p` is a **ring homomorphism** (`residue_ring_hom`) — `residue(x·y) = residue x ·
residue y` in 𝔽_p, because position `0` of `Zp.mul` carries nothing (`residue_mul`).  So ℤ_p, as
the carrier subset of escapes, is a sub-ring with a genuine 𝔽_p ring-map readout.

But `+` and `×` sit on the carrier *differently*, and the difference names a new object.  *Both*
are native **corecursive** operations on the co-tree: the Cauchy product is the textbook productive
corecursion (Rutten's behavioural differential equations), and `Zp.mul` realises it as a coalgebra
morphism for the carrier's shift — head `residue_mul` (`(x·y)₀ = x₀·y₀`), tail `mulRaw_tail`
(`(x·y)' = x₀·y' + x'·y`), bundled in `mul_corecursive`.  The split is **finite-state vs not**.
Addition is finite-state: `Zp.add`'s carry is a single **bit** (`add_carry_le_one`), a one-bit
Mealy machine (`add_mealy_step`) whose bit *is* the odometer unit (`the_residue_unit_odometer.md`).
Multiplication is not: `mulCarry (-1)(-1)` is unbounded (`mulCarry_unbounded`, via
`mulRaw_negOne_negOne` `= (k+1)(p-1)²`), the exact dual of `add_carry_le_one`.

And the carry is **literally a νF inhabitant**: the carry stream `gspine (mulCarry …) : GCoShape
Nat` is reached by no finite Raw (`carry_is_nu_escape`) — `spineL`'s kind of escape, on the `Nat`
alphabet.  This is not an analogy to the number escape: `carry_is_nu_escape` and `padic_is_nu_escape`
are **two type-instances of one polymorphic lemma**, `gspine_one_carrier` (`L = Nat` vs `L = Fin p`)
— the *same* non-surjection of `gToShape : Tree → GCoShape L`, read at two alphabets.

### One carrier is one *non-surjection* (the scale-invariant escape)

The deeper reading dissolves the accreting list (numbers, then the shift, then `±1`, then `× p`,
then the ring, then the carry).  Each is a **finite-stage cover failing to be surjective onto its
own behaviour space**, and the un-covered inhabitant is in each case the cover's **diagonal** —
reached by no finite stage, converged to by every one:

| the pointing | finite-stage cover | escapee (reached by none) |
|---|---|---|
| a **number** | `gToShape : Tree → GCoShape L` (finite Raws) | the digit/cut/branch spine (`gspine_escapes`) |
| an **operation**'s carry | the same map at `L = Nat` | `gspine (mulCarry)` (`carry_is_nu_escape`) |
| a **description** | `Object1 : Raw → (Raw → Bool)` (self-cover by views) | the undifferentiated reading (`object1_not_surjective`) |

These are *one* non-surjection — Cantor's diagonal, Lawvere's fixed point — instantiated against
three covers; the first two are literally one lemma (`gspine_one_carrier`), the third the same
diagonal one universe up (the description-scale instance owned by `why_the_reframing_recurs.md`, and
at the automaton scale by `non_holonomicity_as_finite_state_escape.md`).

So **"holonomic / finite-state" is the predicate "in the image of the finite-stage cover" — a
property of the cover (the pointing), never of the inhabitant (the pointed-at).**  The decisive
witness is `(-1)² = 1` (`neg_one_sq_eq_one`, `mul_carry_nu_residue`): the **result** is the trivial
µF element `1` — squarely in the finite image — while the **carry computing it** is an unbounded νF
escape.  One inhabitant, two verdicts; therefore the verdict is not a fact about the inhabitant.
This is the ring-operation image of the principle already proven for the reals — a cut-decision is
invisible under rescaling (`rcut_rescale`) and depends on the presentation, not the real
(`PresentationDependence`): holonomicity is a property of the approximant sequence, which is a
pointing.

The **unit** and the **residue** are the two values of that one non-surjection.  When the cover is
itself finite-state the diagonal collapses to a bounded readout — addition's carry bit, the odometer
`+1`.  When it is not, the diagonal is a full νF inhabitant — multiplication's unbounded carry.  It
is *one* alphabet-independent object (`runCarry`, `Theory/Raw/Odometer` §7); whether it lands as
**unit** or as **residue** is decided entirely by which cover reads it.  (The Hadamard/convolution
irreducibility, `G188_multiplicative_conv_design`, is its sequence-scale mirror.)

### Cross-frame

The "one carrier" reading is the number-system instance of three already-pinned 213 facts.
First, **no exterior** (`seed/AXIOM/05_no_exterior.md` §5.1): there is no privileged
construction "outside" from which König, `ℤ_p`, `ℝ` are assembled as separate objects — each is
a residue-internal pointing (a stream + an alphabet), and the carrier they point on is one.
Second, **presentation-dependence** (the External-ruler smuggling failure mode): `cutBits` reads
the *sequence*, not the equivalence class, so it is presentation-dependent — exactly as it must
be, since the bit-stream is a pointing and the real itself is reached by none
(`DepthCeilingResidue`).  Third, the **count-Lens / difference-Lens** decompositions
(§6.7): a leaf alphabet is just a choice of how finely the leaf is resolved — `Bool` (one bit),
`Fin p` (a base-`p` digit) — and changing it is a change of *reading*, not of the carrier.

So the classical hierarchy "naturals ⊂ rationals ⊂ reals; and separately, the p-adics" is, in
213, one νF carrier read at different leaf-resolutions and along different streams — a single
escape wearing the alphabet of whichever number system is being pointed at.

## Honest scope

- **Closed** (all grounded in the actual `Zp.add`/`Zp.mul`/`cutSum`/`cutMul`): the carrier, the
  shift, the unit-`±1` arithmetic (`(-1)+1=0`), the valuation filtration `× p` (`mulBase = Zp.mul`-
  by-`p`, `mulBase_eq_mul_pElem`; residue field 𝔽_p), the binary ring transported with a 𝔽_p
  ring-hom readout (`padic_ring_on_carrier`, `residue_ring_hom`), and ℝ's cut-field closure
  (`real_field_on_carrier`).
- **The split is finite-state, not native-vs-not**: both `+` and `×` are native corecursive
  (`mul_corecursive`); only `+` is finite-state (`add_carry_le_one`), `×` is not
  (`mulCarry_unbounded`), and the unbounded carry is itself a νF inhabitant (`carry_is_nu_escape`).
- **Residual, by structure not prohibition**: `×`'s carry and ℝ's order-based cut escape finite
  state — reached by no bounded machine, as a real is reached by no finite Raw — while remaining
  well-defined corecursive behaviours.
- `cutBits` is one honest presentation-dependent extractor (the cut-decision diagonal); it is
  not claimed canonical on the equivalence class.  A faithful map on `Real213.equiv` would need
  the order-decision *limit* (existence via the modulus), which is the LPO-costed step of the
  reverse-math ledger (`the_omniscience_ledger.md`) — by-design external, not a gap to close.
- The carrier is the full-binary-branch over-approximation refined to the consistent +
  anti-reflexive subtype (`SlashNu`, §11); the exact slash-νF finality is `slashNu_final`
  (`the_residue_as_primitive.md`).  The generic `GSlashNu L` reuses that subtype shape per
  alphabet; its own finality is the same label-agnostic path-induction.
