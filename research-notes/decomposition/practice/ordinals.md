# Decomposition: ordinals / well-ordering / transfinite height

*213-decomposition of "the ordinals" — successor, limit, `ω`, well-foundedness — per
`../README.md` (model v3). Tests one hypothesis: an ordinal is the **fold-height reading
of `dimension.md` pushed past every finite stage**, and a limit ordinal is the
height-reading's **residue** (`cardinality.md`) when the ascent is unbounded — `ω` tagged
`q = +1` (a converging-style order-type limit), not a god above the finite.*

## The decomposition

- **Construction `C`** — the same nesting as `dimension.md`: distinguishing applied, then
  applied again to what it produced, iterated. The build-tree (`Raw`: an atom, or a
  `slash x y h` of two already-built distinct Raws — `Lambek.decompose`). Ordinals are not
  a *new* construction; they are this construction's **ascent direction** made the object.
  The explicit upward stream is the self-pointing tower `rawTower n = a/(a/(…/b))`, which
  peels from its successor at every rung (`MuNuMirror.tower_ascent_isPart`).
- **Reading `L↑`** — the **height-reading** of `dimension.md`, unchanged: project a
  construction to *how deep it nests* (`Raw.depth`, defining step
  `Raw.depth_slash : (slash x y h).depth = 1 + max x.depth y.depth`). One more
  distinguishing = `+1` to the height (`MuNuMirror.ascent_adds_unit`:
  `(rawTower (n+1)).depth = (rawTower n).depth + 1`). An **ordinal is the value `L↑`
  reads**, taken along the ascent — the order-type of the heights below it. A *successor*
  ordinal is `L↑` of one-more-nesting; a *limit* ordinal is what `L↑` forces when the
  ascent has no finite cap.
- **Residue** — the height-ladder has **no top finite rung**: for every bound `N` the rung
  `rawTower (N+1)` reads deeper (`MuNuMirror.ascent_unbounded : ∀ N, ∃ r, N < r.depth`).
  The **residue of `L↑` over the unbounded ascent is `ω`** — the reached-by-none limit of
  the cofinal finite heights. Named one scale up, "all the heights at once" reproduces the
  global non-surjection (`DepthHeightDiagonal.height_diagonal_escapes`, the
  `ω^ω`/`ε₀`-direction). `ω` is the *converging* pole of `cardinality.md`'s residue: it has
  an order-type fixed point (the ascent asymptotes *to* it), so it carries **`q = +1`**,
  the same residue the escaping diagonal carries at `q = −1`.

## Re-seeing — successor, limit, and ω are the height-reading and its residue

```
   "ordinal α"          =  ⟨ a build ascending | L↑ = depth, read as order-type ⟩
   "successor α+1"      =  ⟨ one more distinguishing on α's build | L↑ ⟩   (depth +1; ascent_adds_unit)
   well-ordering        =  P(⟨ C | L↑ ⟩)  — descent on L↑ is well-founded   (isPart_wf; no_infinite_descent)
   ordinal induction    =  the same well-founded recursion on L↑            (Factorization.wf_lt / acc_lt)
   "ω" (first limit)    =  Residue(L↑, C) over the unbounded ascent, q=+1   (ascent_unbounded; converging pole)
   "ε₀ / ω^ω-direction" =  Residue named one scale up                       (height_diagonal_escapes)
```

Two faces of one operator, exactly the `the_form_of_the_residue.md` split "descent grounds,
ascent is unbounded": read **downward**, `L↑` is well-founded — every part is *strictly*
shallower than its whole (`Lambek.part_depth_lt`), the peel relation is well-founded
(`Lambek.isPart_wf`), there is no infinite descent (`Lambek.no_infinite_descent`), the
floor is the atoms and nothing else (`Lambek.terminal_iff_atom`,
`Lambek.atoms_are_floor`). That **is** well-ordering / the foundation axiom: the ordinal
rank of the build is well-founded, so transfinite induction is just `wf_lt.induction`
(`Factorization.acc_lt`/`wf_lt` driving `exists_factorization`). Read **upward**, the same
height has an explicit total stream with no finite cap (`ascent_unbounded`) — the
ω-ascent.

## Revelation (residue-surfaced + collapse + forcing)

**ω = the height-reading's residue, tagged `q = +1`.** A limit ordinal is not a completed
infinite object discovered above the finite; it is `dimension.md`'s height-reading `L↑`
re-identified as a *residue* over an unbounded ascent — `cardinality.md`'s
"reading + forced residue" pattern applied to the depth axis instead of the count axis.
`ω` carries the **converging** sign of the README's `q = ±1` find: the cofinal finite
heights asymptote *to* it (order-type fixed point, `q = +1`), the mirror of the *escaping*
diagonal (`q = −1`, `OneDiagonal.no_surjection_of_fixedpointfree`,
`CassiniUnimodular.cassini_law_one_at_two_multipliers`). So `ω` and Cantor's escaping
diagonal are **one residue at its two unimodular poles**, now exhibited a third time — on
the height axis.

**Collapse.** Successor ordinal, "dimension/degree +1", and "one more rung of the tower"
are *one move*: `+1` to `L↑` (`Raw.depth_slash`; `MuNuMirror.ascent_adds_unit`). Limit
ordinal, "pole at the height-ceiling", and "the uncountable diagonal" are *one residue*
read on the depth axis (`height_diagonal_escapes` = `object1_not_surjective` relocated one
scale up). The whole successor/limit dichotomy collapses to **`L↑` + its residue** — the
two faces `dimension.md` and `cardinality.md` already named, here shown to be the *same
pair* viewed along the ascent.

**Forcing.** Well-ordering is not stipulated for ordinals — it is **forced** because `L↑`
is the well-founded measure already living in `C` (`isPart_wf`, `part_depth_lt`,
`Factorization.acc_lt`). "Every non-empty set of ordinals has a least element" /
transfinite induction *is* `wf_lt.induction`; you cannot dial the height, you can only nest
once more (`+1`) or hit the floor. The ordinal hierarchy adds **no new primitive** over
`dimension.md` + `cardinality.md`: successor = the height-axis's `+1`, limit = the
height-axis's residue.

## Note for the technique

**1. Does this confirm Residue = the limit of an unbounded reading, `q = +1`?** Yes — and
this is the cleanest confirmation so far that the `q = +1` (converging) pole is *real* and
not just φ's special case. `cardinality.md` surfaced the residue at `q = −1` (escape,
fixed-point-free diagonal); `golden_ratio.md` surfaced `q = +1` for φ (an algebraic fixed
point). Ordinals give `q = +1` for an *order-type* limit (`ω`): the residue of an unbounded
height-ascent, asymptoted-to but reached-by-none. The same `(C, L↑)` that gave dimension
now gives the whole ordinal ladder once you read its residue. So the model **EXTENDS** — no
new primitive; ordinals = `dimension.md`'s axis + `cardinality.md`'s residue rule + the
README's `q` tag, all three at once.

**2. Does fold-height + its residue give the whole ordinal hierarchy?** Honestly: **the
first limit, yes; the full hierarchy, only in direction.** What is *certified* in Lean is:
the finite ascent with `+1` (`ascent_adds_unit`), its unboundedness (`ascent_unbounded` =
the `ω`-residue), well-founded descent / transfinite induction (`isPart_wf`,
`no_infinite_descent`, `wf_lt`), and the residue named one scale up
(`height_diagonal_escapes`, explicitly tagged "`ω^ω`/`ε₀`-direction"). What is *not*
certified is iterated transfinite arithmetic (`ω+ω`, `ω·ω`, `ε₀` as a closed value) — the
file names the *direction* (`epsilon_direction`), it does not build the tower of limits.
That is the honest grounding ceiling: the calculus *predicts* the higher ordinals as
iterated residues-of-residues (each `height_diagonal_escapes` one scale up), but only the
first limit and the direction of the next are Lean-anchored.

**3. Where EXACTLY does the finite-signature rule bite — is the first limit the model's
honest boundary?** **Yes, and precisely at `ω`.** Below `ω`, `L↑` *closes*: every height is
read by a finite `Raw.depth`, a genuine inhabited value — successor ordinals are no
residue at all, just `+1`. At `ω` the reading stops closing: there is no `Raw` of depth
`ω` (`ascent_unbounded` says every rung is finite and deeper rungs exist), so `ω` is
**named only by its finite generator** — the cofinal sequence `rawTower`, the
well-founded ascent — never grasped as a completed object. This is the
`the_form_of_the_residue.md` rule "infinity is the residue's shape, not a god above the
finite" biting exactly: `ω`'s finite signature is the never-capping ascent
`∀ N, ∃ r, N < r.depth`, the computable operand; the completed `ω` never is. So the model's
honest boundary **is** the first limit, and it caps there *correctly* — it does not pretend
to inhabit `ω`, it points at `ω`'s generator. The model neither breaks nor over-claims: it
EXTENDS to `ω` and the *direction* of `ε₀`, and is honest that the transfinite *arithmetic*
above `ω` is predicted-but-not-built.

---

### Verified Lean anchors (file : theorem) — all grep-confirmed

- `Theory/Raw/Lambek.lean` : `decompose`, `depth_drops`, `atoms_are_floor`,
  `part_depth_lt`, `isPart_wf`, `no_infinite_descent`, `terminal_iff_atom`
  (well-foundedness = the ordinal rank of the build; descent grounds)
- `Theory/Raw/Levels.lean` : `Raw.depth_slash` (the `1 + max` defining step; successor `+1`)
- `Theory/Raw/MuNuMirror.lean` : `ascent_unbounded` (`∀ N, ∃ r, N < r.depth` = the
  ω-ascent, no finite cap), `ascent_adds_unit` (successor = depth `+1`),
  `tower_ascent_isPart` (each rung peels from the next), `descent_wf_ascent_unbounded`
  (the two faces bundled)
- `Lens/Number/Nat213/Factorization.lean` : `acc_lt`, `wf_lt`, `exists_factorization`
  (native well-founded order = ordinal/transfinite induction)
- `Lib/Math/Analysis/Cauchy/DepthHeightDiagonal.lean` : `height_diagonal_escapes`,
  `epsilon_direction` (the height-residue one scale up; the `ω^ω`/`ε₀` direction)
- `Lens/Foundations/FlatOntologyClosure.lean` : `object1_not_surjective` (the global
  self-cover non-surjection the height-residue relocates)
- `Lens/Foundations/OneDiagonal.lean` : `no_surjection_of_fixedpointfree` (the `q = −1`
  escaping pole of the residue)
- `Lib/Math/Algebra/CassiniUnimodular.lean` : `cassini_law_one_at_two_multipliers`
  (the `q = ±1` two-poles law; `ω` is the `q = +1` reading)
- `theory/essays/foundations/the_form_of_the_residue.md` — "Infinity is the residue's
  shape, not a god above it" + "Descent grounds, ascent is unbounded"

### Dropped citations (could not verify or out of scope)

- No Lean theorem for transfinite *arithmetic* (`ω+ω`, `ω·ω`, `ε₀` as a closed ordinal)
  exists; `epsilon_direction` names the **direction** only, so claims about iterated limit
  ordinals are flagged as predicted-not-built, not cited as proven.
- `tower_ascent_isPart`'s "total upward stream" is cited for the ascent's existence, not as
  a constructed transfinite tower beyond `ω`.
