# Decomposition: dimension / degree / pole-order ("fold-height")

*213-decomposition per `../README.md`, answering its open shape-question: "should
**fold-height** be an explicit readable feature — is it what dimension / degree /
pole-order are?"*

## The decomposition

- **Construction `C`** — *any* construction is a **nesting**: the distinguishing applied,
  then applied again to what it produced, iterated. The build-tree. In Lean a `Raw` is
  exactly this: an atom (`a`/`b`) or a `slash x y` of two *already-built* distinct Raws
  (`Raw.decompose`, `Lambek.lean`) — every construction is one of these, exhaustively
  and exclusively (`Lambek.self_completion_no_partial`).
- **Reading `L↑`** — the **height-reading**: project a construction to **how deep it
  nests** — forget *what* was distinguished, keep only the count of layers down to the
  floor. Lean shadow: `Raw.depth`, with the one defining step
  `Raw.depth_slash : (slash x y h).depth = 1 + max x.depth y.depth` (`Levels.lean`) and
  floor `Raw.a.depth = Raw.b.depth = 0` (`Lambek.atoms_are_floor`). One more
  distinguishing = `+1` to the height.
- **Residue** — `L↑` is massively many-to-one (every construction of a given depth reads
  the same number); the residue is *which build-tree* you had — `depth` forgets all of it
  but the layer count. And one scale up, *naming all heights at once* re-produces the
  global non-surjection (`DepthHeightDiagonal.height_diagonal_escapes`): the height ladder
  has no top finite rung (`MuNuMirror.ascent_unbounded`).

## Re-seeing

```
   "dimension n"   =  ⟨ a build nesting n times | L↑ = depth ⟩   (n-simplex = n+1 vertices, depth n)
   "degree n"      =  ⟨ a difference/Casoratian orbit | L↑ = polyDepth ⟩
   "pole order"    =  ⟨ a meromorphic orbit | L↑ = polyDepth at the 0/∞ hole ⟩
   "nesting depth" =  ⟨ a Raw | L↑ = Raw.depth ⟩
   one more distinguishing  =  +1 to the height  (Raw.depth_slash;  ascent_adds_unit)
```

## Revelation (collapse + forcing)

**Collapse.** "Dimension" (of a simplex/space), "degree" (of a polynomial / linear
recurrence), "pole order" (of a meromorphic function), and "nesting depth" are **one
reading — the height-reading `L↑` — applied to four different constructions**, not four
notions. They are the same `(·, L↑)`: each is "count the layers of the build down to the
floor." In Lean the *same* finite-height parameter recurs across the constructions: the
simplicial dimension table reads off the build's faces (`Simplex.FaceTerms.simplex_face_counts`,
`binom d k`), the recurrence's algebraic order is `polyDepth d` (`DepthAperyCubic.aperyTop_depth_exact`:
depth exactly 3, not 2), and the determinant's pole structure is read by the *same*
`polyDepthZ` measure (`DetSpectrumPoles.det_spectrum_poles_and_center`: the center is
`polyDepthZ 0`, the ceiling has no finite depth). Four classical words, one axis.

**Forcing.** The height is not a chosen label — it is **forced** and **well-founded,
strictly increasing under one more distinguishing**. One slash adds exactly one unit
(`Raw.depth_slash`; `MuNuMirror.ascent_adds_unit`: `(rawTower (n+1)).depth = (rawTower
n).depth + 1`); every part is *strictly* shallower than its whole (`Lambek.depth_drops`,
`Lambek.part_depth_lt`); and the peel relation is **well-founded** — no infinite descent,
the floor is the atoms and nothing else (`Lambek.isPart_wf`, `Lambek.no_infinite_descent`,
`Lambek.terminal_iff_atom`). The *same* well-founded height is what carries the
factorization recursion (`Factorization.acc_lt`/`wf_lt` driving `exists_factorization`)
and what makes degree strictly force growth (`PolyDepthMonotone.posTop_evStrictMonoZ`:
`polyDepthZ (e+1)` ⟹ eventual strict monotonicity). Height is forced because it *is* the
well-founded measure of the build — you cannot dial it; you can only nest once more
(`+1`) or not.

## Note for the technique

**Verdict on the README shape-question: YES — fold-height should be a first-class
readable axis of `C`.** The decomposition earns it on the calculus's own terms (collapse +
forcing), not by decree:

1. It pays by **collapse**: four classical concepts (dimension, degree, pole-order,
   nesting depth) become *one reading*, exactly the kind of payoff the revelation rule
   demands. That is impossible to state without naming height as a readable feature.
2. It is **structurally forced**, not stipulated: height is the *well-founded measure*
   already living in `C` (`isPart_wf`, `acc_lt`) — `L↑` only reads out what the build's
   own descent already carries. So promoting it to an explicit axis adds no new
   primitive; it names a feature the construction was forced to have.
3. It is the **mirror of the direction-axis** (`integers.md`): direction is the *Bool/swap*
   sub-structure some readings consume; height is the *Nat/count* sub-structure the
   height-reading consumes. Together they suggest `C` carries two optional read-off axes —
   a **swap-bit** (direction → sign, orientation) and a **depth-count** (height →
   dimension, degree, pole-order) — each ignored by readings that don't need it (the
   count-reading ignores both).

Residue note (the README's third shape-question, glimpsed here): the height-residue
**stratifies**. Per-reading, `L↑` forgets *which* build (anti-image of one depth value);
one scale up, naming the whole height ladder reproduces the *global* non-surjection
(`height_diagonal_escapes`, the `ω^ω`/`ε₀`-direction) — the same self-cover as
`object1_not_surjective`, now read at the height scale. So the depth-axis does not escape
the residue; it relocates it to the act of naming "all heights."

---

### Verified Lean anchors (file : theorem)

- `Theory/Raw/Lambek.lean` : `decompose`, `depth_drops`, `atoms_are_floor`,
  `part_depth_lt`, `isPart_wf`, `no_infinite_descent`, `terminal_iff_atom`,
  `self_completion_no_partial`
- `Theory/Raw/Levels.lean` : `Raw.depth_slash` (the `1 + max` defining step)
- `Theory/Raw/MuNuMirror.lean` : `ascent_unbounded`, `ascent_adds_unit`
- `Lens/Number/Nat213/Factorization.lean` : `acc_lt`, `wf_lt`, `exists_factorization`
  (height as the well-founded recursion measure)
- `Lib/Math/Analysis/Cauchy/DepthAperyCubic.lean` : `aperyTop_depth_exact` (degree =
  finite `polyDepth`, exactly 3 not 2)
- `Lib/Math/Analysis/Cauchy/PolyDepthMonotone.lean` : `posTop_evStrictMonoZ` (depth
  strictly forces growth)
- `Lib/Math/Algebra/DetSpectrumPoles.lean` : `det_spectrum_poles_and_center` (pole
  structure read by the same `polyDepthZ` height)
- `Lib/Physics/Simplex/FaceTerms.lean` : `simplex_face_counts` (dimension = build's face
  table)
- `Lib/Math/Analysis/Cauchy/DepthHeightDiagonal.lean` : `height_diagonal_escapes`,
  `epsilon_direction` (the height ladder has no top; residue one scale up)
- `theory/essays/foundations/the_form_of_the_residue.md` — "finite depth/tower shadow"
  (cites `rawTower`, `tower_ascent_isPart`, `height_diagonal_escapes`,
  `object1_not_surjective`)
