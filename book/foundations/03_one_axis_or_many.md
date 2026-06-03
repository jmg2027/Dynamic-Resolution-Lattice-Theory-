# Chapter 3 — One axis, or several serialized?

The staircase `ℕ → ℤ → ℚ → ℝ` is drawn as a line.  This chapter shows the line is a
**serialization** of structure that is not intrinsically linear: a single *breadth*
axis, two *orthogonal inverse-closures*, and a *character-changing limit* — sitting on
a substrate that is a **lattice of Lens refinements**, not a chain.  The verdict is
**hybrid**: the residue supports the chain, but it does not single it out.

## 3.1 The four steps are not one operation iterated

Read what each rung actually *does*.

- **`ℕ` — breadth.**  The count-Lens `⟨1, 1, +⟩` reads how many leaves a slash-chain
  has: `leaves(x/y) = leaves x + leaves y` (`Lens/LensCore.lean`, `Raw.leaves_slash`).
  One number, the breadth of the pointing.
- **`ℤ` — additive-inverse closure.**  The difference-Lens closes the count under `−`:
  `diffView x y = subNatNat (leaves x) (leaves y)`, sign the period-2 swap
  (`DifferenceLensFounding.lean:33-47`).  This is the `+/−` axis.
- **`ℚ` — multiplicative-inverse closure.**  The ratio-Lens closes the count under
  `÷`: cross-multiplication `ratioEquiv`, lowest terms the unit `det P = NS − NT`
  (`RatioLensFounding.lean:34-62`).  This is the `×/÷` axis.
- **`ℝ` — limit.**  Not an algebraic closure at all: the Cauchy completion of
  `ℚ`-trajectories (`CauchyLensFounding.lean`).

Additive-inverse closure and multiplicative-inverse closure are *different directions*.
Drawing `ℤ` before `ℚ` puts `+/−` before `×/÷` — but nothing in the residue says the
additive closure must precede the multiplicative one.  That ordering is the
serialization.

## 3.2 `ℤ ⊥ ℚ`: the founding of `ℚ` does not cite the founding of `ℤ`

The sharpest evidence that the linear order is a convention is in the import graph of
the founding files themselves.  The `06_lens_readings.md` §6.7 narrative — and the
docstring of `RatioLensFounding` — *say* `ℚ` "founds on" the `ℤ`-rung's unit.  But the
Lean does not depend on `ℤ` at all:

> `Lens/Number/RatioLensFounding.lean:1-2` imports **only**
> `Mobius213.Px.PnFibonacciUniversal` and `Mobius213OneAsGlue` — **neither**
> `DifferenceLensFounding` **nor** `Meta.Int213`.  Its entire content is `Nat`-level:
> `ratioEquiv (p q : Nat × Nat)`; `convergent_lowest_terms_is_det` uses
> `Q00·Q11 = Q01² + (NS − NT)` where `NS NT : Nat` and `NS − NT` is **`Nat` truncated
> subtraction**; `ns_minus_nt_is_one : NS − NT = 1 := by decide`.

So "`det P = NS − NT`" is a `Nat` / pair-level fact.  The `ℚ`-rung's coprimality datum
does **not** require the integers.  The narrative claim that `ℚ` founds on the
difference-Lens unit is a *gloss asserting a serialization the formal artifact does not
need*.  `ℤ` and `ℚ` are two orthogonal inverse-closures of the *same* count-Lens, and
the founding files witness exactly that independence.

This is not a defect in the Lean — it is the Lean being more honest than the narrative.
(OPEN: whether §6.7 should be amended so the doctrine matches the import graph, or
whether a genuine `ℚ`-on-`ℤ` dependence should be *added*.  Both are coherent; the draft
flags the mismatch rather than silently picking one.)

## 3.3 The repo already carries an explicit two-axis invariant

The breadth/additive/multiplicative split is not a reading imposed here — the codebase
*independently* proves a two-coordinate invariant on the depth side:

> `Lib/Math/Cauchy/DepthTower.lean:12-45`: two lifts — `diff s n = s(n+1) − s n` (the
> **additive** lift, tames polynomial growth, residual degree `d`) and
> `ratioLift s n = s(n+1) / s n` (the **multiplicative** lift, tames exponential
> growth, height `h`) — and a **pair invariant `(h, d)`** (`atTowerCoord`): "The full
> invariant is a *pair* `(h, d)`."  `DepthOrdinal` reads it as `ω·h + d < ω²`;
> `DepthOmegaTower` extends to an `ω^ω` ladder.

The additive axis and the multiplicative axis are *the same two directions* that
distinguish `ℤ` from `ℚ`, here proven orthogonal on the sequence side
(`ratio_is_diff_on_exponent`: `ratioLift` is `diff` conjugated through the exponent).
The number tower flattens this two-coordinate structure into the single word "`ℝ`."

## 3.4 The substrate is a lattice, not a chain

`Lens.refines` is a **preorder** on kernel-fineness (`LensCore.lean:90`,
`Lattice/Preorder.lean`), with antisymmetry only at the kernel level — distinct-codomain
Lenses with equal kernels are not order-identified, so it is a *partial* order.  On top
of it the repo builds a genuine **lattice** with joins and meets (`Lens/Lattice.lean`
bundles `Join, Meet, IndexedJoin, FamilyJoin, FamilyMeet, Lattice`).

A total order — a *chain* — is available as one *witness* among many, but the chain the
repo actually exhibits is **not** the number tower:

> `Lens/Lattice/Chain.lean:14`: the 4-step chain `idLens → leaves → parity →
> constLens` (finest to coarsest).  This is the **breadth/coarsening** chain.

There is **no Lean theorem** placing `ℕ, ℤ, ℚ, ℝ` as a `refines`-chain.  The founding
capstone `number_tower_is_lens_bundling` (`TowerFounding.lean:48`) is a **conjunction of
four independent rung-facts**, not an ordered chain: it asserts each rung is a bundling,
but imposes no `refines`-order linking them.  The "tower" is a chosen *path*; the
substrate is the lattice.

## 3.5 Verdict: hybrid

The linear `ℕ → ℤ → ℚ → ℝ` is a **serialization convention**.  What the residue forces
(per the Lean) is:

- one **count-Lens** (breadth);
- two **orthogonal inverse-closures** — additive (`ℤ`) and multiplicative (`ℚ`) — shown
  independent both in the founding import graph (§3.2) and on the depth side
  (`DepthTower`, §3.3);
- a **character-changing limit** (`ℝ`), an algebraically different kind of step;

organized as a **lattice of Lens refinements**, of which the narrative tower picks one
chain — and not even the chain the repo formalizes (`Lattice/Chain.lean` formalizes the
breadth chain instead).

So: **not one axis, and not a forced line.**  A breadth axis, two orthogonal
inverse-axes, and a limit, drawn as a staircase by convention.  The residue supports the
staircase; it does not single it out.

## 3.6 Open threads

- **OPEN** — the breadth axis (`Lens/`) and the depth axes
  (`Lib/Math/Cauchy/Depth*`, `(h, d)`) are not unified under one Lens-lattice theorem.
  Whether `(h, d)`-depth and `refines`-breadth are coordinates of one structure or two
  unrelated orders is unsettled.
- **OPEN** — three "axis" vocabularies coexist without a unifying statement:
  `Lens.refines` (breadth), depth `(h, d)`, and the Cayley–Dickson grade axis (Ch. 2).
  A single theorem relating them would close the "how many axes, really?" question.
- **OPEN** — should §6.7 be amended to match the `ℤ ⊥ ℚ` import-graph independence, or
  should a genuine `ℚ`-on-`ℤ` dependence be added to the founding?
