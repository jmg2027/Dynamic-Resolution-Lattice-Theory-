# Rederive — object-primary Lean track (SPEC §1 F-obj, milestone A2)

Fresh, self-contained Lean 4 package for the independent rederivation
program (`rederive/SPEC.md`).  Derived from `seed/ORIGIN_RAW.md` /
`seed/ORIGIN.md` ONLY; no other repository content was read or imported.

- Toolchain: `leanprover/lean4:v4.16.0`.  **Zero dependencies** (no
  Mathlib, no `require` lines) — Lean 4 core only.
- Contract: `lake build` clean, **0 sorry, 0 axioms**.
  `Rederive/AxiomCheck.lean` runs `#print axioms` on every theorem;
  every line reports *"does not depend on any axioms"* (verified: 35/35;
  no `propext`, no `Quot.sound`, no `Classical.choice`).

## Files

| File | Content |
|---|---|
| `Rederive/Tree.lean` | The free difference structure: atoms, total order, unordered pairing, symmetry + recoverability |
| `Rederive/Object1.lean` | Self-indication, faithfulness, the Cantor diagonal, residue shape |
| `Rederive/AxiomCheck.lean` | `#print axioms` audit for every theorem |

## Design decision: unorderedness without quotients

ORIGIN_RAW §3 demands an *unordered* pairing of two *distinct*
somethings ("no absolute order"; "nothing exists to distinguish x from
x").  Lean inductives are ordered, and the obvious fix — quotient by
the swap — would drag in `Quot.sound`, breaking the zero-axiom
contract.  Encoding chosen (SPEC §1's smart-constructor option):

1. `Tree` = ordered inductive (`a`, `b`, `node l r`).
2. `Tree.cmp : Tree → Tree → Ordering` — a total lexicographic
   comparison, with proved trichotomy facts: `cmp_refl`,
   `eq_of_cmp_eq` (eq ⇒ equal), `cmp_oswap` (antisymmetry in swap
   form), `cmp_lt_or_gt_of_ne` (totality).
3. `pairing x y` = smart constructor that **sorts** the two children
   into canonical order.  Unorderedness is then a *theorem*
   (`pairing_comm`), not a quotient.

Why not the canonicality-subtype variant: `Subtype` works axiom-free
too, but every constructor application would carry a sortedness proof
obligation through all downstream statements; the smart constructor
keeps the API one-sorted and pushes canonicality into the definition.
Cost (stated honestly): raw `node x y` with `x` above `y`, and
`node x x`, still inhabit `Tree`; all pairing theorems therefore
hypothesize `x ≠ y` and speak about `pairing`, never raw `node`.  A
canonicality predicate carving out exactly the pairing-generated
subfamily is future work (see Open, below).

The `x ≠ y` side-condition (no self-pair, SPEC choice C4) is not baked
into `pairing`'s type (that would need a proof-carrying constructor);
`pairing` is total, its theorems assume distinctness.  The `eq` branch
of `pairing` is arbitrary and unreachable under the hypotheses used.

## What is proved (all ∅-axiom)

### Pairing laws (`Rederive/Tree.lean`)

- `pairing_comm : pairing x y = pairing y x` — the symmetry law
  (holds even without distinctness, since `cmp = eq` forces `x = y`).
- `pairing_inj : x ≠ y → u ≠ v → pairing x y = pairing u v →
  (x = u ∧ y = v) ∨ (x = v ∧ y = u)` — child-recoverability up to the
  unordered swap.
- `pairing_ne` — contrapositive: distinct unordered pairs give
  distinct composites.
- `children_pairing : x ≠ y → children (pairing x y) = some (x,y) ∨
  … = some (y,x)` — the unordered pair is computably recoverable.
- `pairing_ne_a`, `pairing_ne_b` — composites are never atoms.
- `a_ne_b` — the first distinction is real (SPEC choice C2).

### Self-indication and the diagonal (`Rederive/Object1.lean`)

- `object1 r x = beq x r` with hand-written structural `beq`
  (`beq_refl`, `eq_of_beq`, `beq_eq_false_of_ne`) and a transparent
  `DecidableEq` built from it (no `Classical`, verified axiom-free).
- `object1_injective : r ≠ s → object1 r ≠ object1 s` — faithfulness
  (plus the stronger extensional form `object1_injective_ext`).
- `object1_not_surjective : ∀ f : Tree → Tree → Bool, ∃ p, ∀ r, p ≠ f r`
  — the constructive Cantor diagonal, witness `diag f = fun x => !(f x x)`.
  Fully constructive; the inequality `p ≠ f r` needs no funext (refuted
  at the point `r` via `congrFun`).
- `diag_object1_eq_false` — the diagonal of `object1` itself is
  pointwise constant-false: the first concrete residue inhabitant, and
  a consistency check against the shape theorem below.

### Residue shape (first step of the hard half)

- `inImageExt_iff_uniqueIndicator :
  (∃ r, ∀ x, p x = object1 r x) ↔ (∃ r, p r = true ∧ ∀ x, p x = true → x = r)`
  — the extensional image of self-indication is **exactly** the
  single-point indicators.
- Corollaries: `constFalse_not_inImageExt` / `constFalse_ne_object1`,
  `constTrue_not_inImageExt` / `constTrue_ne_object1`,
  `twoIndicator_not_inImageExt` / `twoIndicator_ne_object1 (u ≠ v)` —
  the empty view, the total view, and every two-point indicator are
  residue, both extensionally and intensionally.
- `inImageExt_of_eq` — intensional image membership implies
  extensional membership (the axiom-free direction).

## What remains open (stated precisely)

1. **Intensional image characterization.**  The direction
   `(∀ x, p x = object1 r x) → p = object1 r` is exactly
   function extensionality; Lean core proves `funext` from
   `Quot.sound`, which the contract forbids.  Hence the shape theorem
   is stated extensionally.  This is a *representation* boundary, not
   a mathematical gap: every negative statement (what is NOT in the
   image) is proved intensionally, and positive membership is used
   only extensionally.  Nothing downstream so far needs the
   intensional converse.
2. **Full residue stratification** (memo A2's hard half, beyond step
   one): grading the complement of the image by descriptive
   complexity — e.g. finite-support indicators of size k (proved
   residue here only for k = 0 and k = 2 and for cofinite support via
   const-true), then non-finite-support predicates.  A candidate next
   theorem: `p` with finite support of size ≥ 2 is residue, uniformly
   in the support list.
3. **Canonical subfamily.**  A predicate `Canon : Tree → Prop`
   (children strictly `cmp`-ordered at every node) identifying the
   image of the pairing-generated family inside the ordered carrier,
   with `Canon (pairing x y)` for canonical distinct `x y`, and an
   induction principle for canonical trees.  Not needed for A2 but
   needed before the event-system work (task A3) speaks of "all
   Trees".

## Classical concepts relied on (for the bilingual ledger)

| Internal | Nearest classical object |
|---|---|
| `Tree` | free magma on 2 generators, restricted to distinct-argument, unordered application |
| `cmp` | lexicographic linear order on terms |
| `pairing` | canonical representative of an unordered pair (sorting normal form — the standard quotient-free encoding) |
| `object1` | singleton indicator / characteristic function; Kronecker delta |
| `object1_not_surjective` | Cantor's diagonal argument (constructive form; Lawvere fixed-point schema in Boolean instance) |
| `inImageExt_iff_uniqueIndicator` | image of the singleton embedding `X → 2^X` = atoms of the Boolean algebra `2^X` |
| extensional-vs-intensional split | function extensionality (independence from Lean's axiom-free core) |
