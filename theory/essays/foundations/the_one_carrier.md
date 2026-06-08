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
  case `twoAdic_is_nu_escape`).
- Real instance: `lean/E213/Lib/Math/NumberSystems/Real213/NuEscape.lean`
  (`cutBits`, `cutNu`, `real_is_nu_escape`, `real_cut_distinct`, `real_shift_dynamics`,
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

- The unification is at the level of the *carrier and its shift*, not of the number systems'
  *arithmetic*.  `ℤ_p`'s ring structure and `ℝ`'s field structure are not claimed to descend
  from `gspine`; what is shared is the reached-by-none escape and the Bernoulli shift on the
  leaf-streams.  Whether the +1-with-carry odometer (`Theory/Raw/Odometer`,
  `the_residue_unit_odometer.md`) lifts to an *arithmetic* on the generic carrier — making the
  one-carrier claim an algebraic and not only a dynamical one — is the open frontier.
- `cutBits` is one honest presentation-dependent extractor (the cut-decision diagonal); it is
  not claimed canonical on the equivalence class.  A faithful map on `Real213.equiv` would need
  the order-decision *limit* (existence via the modulus), which is the LPO-costed step of the
  reverse-math ledger (`the_omniscience_ledger.md`) — by-design external, not a gap to close.
- The carrier is the full-binary-branch over-approximation refined to the consistent +
  anti-reflexive subtype (`SlashNu`, §11); the exact slash-νF finality is `slashNu_final`
  (`the_residue_as_primitive.md`).  The generic `GSlashNu L` reuses that subtype shape per
  alphabet; its own finality is the same label-agnostic path-induction.
