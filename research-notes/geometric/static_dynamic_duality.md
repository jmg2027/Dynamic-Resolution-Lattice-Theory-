# Order is not intrinsic; the two descriptions coincide (μF ≅ νF) for this reading

*Tier 1.  Two further observations on the generative cycle, both landing on the
axiom docs.*

## 1. Dependency / order is not natural to the structure (§2.3)

Up to cycle 1 an order is natural (one line → one point, a unique start).  From
cycle 2, imposing an order or dependency requires *choosing* where to start
drawing — which line, which point — and the choice is canonical only at cycle 1.
So order/dependency is not an intrinsic feature; it is a reading.  Even the
"operation poset" used to get the configuration lattice imports a directionality
the structure does not carry.

This is §2.3 **self-completion** verbatim: "the four clauses are **not steps in a
construction** … aspects of one event, **not stages of a process**."  No external
time exists to sequence the events (§6.2), so the natural description is the
*static* completed structure with local consistency, and any *construction order*
is a Lens (canonical only in the degenerate cycle-1 case).  This is stronger than
"no global cycle number": there is no intrinsic order at all.

## 2. Two descriptions, one structure — and they coincide here (§5.7, Lambek)

A structure can be stated two ways, with no difference and no preference between
them:

- **Dynamic** (constructive, `μF` / initial algebra): "S is built — each line
  gives a point, each point draws its lines."
- **Static** (completed, `νF` / final coalgebra): "S is complete; in S every line
  has its point, every point its line-relations" — a consistency / fixed-point.

§5.7: an internal observer cannot prefer one (no external time axis).  And the two
faces **cannot be viewed at once**, so investigating the structure means surveying
*both* — the same reason the atlas surveys many readings.

The good news, and the reason this structure is tractable: its two faces
**coincide** — it is a self-fixed-point, `μF ≅ νF` (Lambek), the
"describe = reconstruct" case (`MobiusSelfForm.self_reconstruction_master` G139;
`Theory/Raw/{MuNuMirror, Lambek}`; `theory/essays/foundations/
the_residue_as_primitive.md`).  Concretely:

- **complete-graph / simplex reading**: the construction limit and the completed-S
  consistency are the *same* complete graph.  `μF ≅ νF`.
- **betweenness / midpoint reading**: the construction yields the countable dyadic
  points; the completion is the continuum segment.  `μF` (countable) `≠ νF`
  (continuum), and the gap is `object1_not_surjective` — reached by none.

So "most codomains do not coincide" is exactly the generic `μF ≠ νF`: the
constructive and the completed descriptions disagree, and the disagreement is the
residue.  The simplex reading sits at the special coincidence, which is why its
static and dynamic faces look identical and it is the easy one to study.

## Seed alignment

- §2.3 self-completion ⇒ order is not stages of a process ⇒ the static description
  is primary, dynamic order is a Lens.
- §5.7 frozen vs dynamic ⇒ the two descriptions, neither preferred; can't view
  both at once ⇒ survey both.
- `μF ≅ νF` (Lambek, `MuNuMirror`) ⇒ the coincidence for the simplex reading;
  `μF ≠ νF` ⇒ the residue gap for the generic reading.

## Closed ∅-axiom (the arithmetic face)

The complete-graph reading's coincidence is ∅-axiom (build + `scan_axioms` PURE,
6/0): `lean/E213/Lib/Math/Geometry/AngleStructure/SimplexSelfForm.lean`.  The
completed-S edge count and the constructive step are the *same recursion* —
`edgesK (m+1) = edgesK m + m` holds by **`rfl`** (`complete_step`): each new vertex
joins all earlier (dynamic), which is exactly the completed `C(m,2)` count
(static).  `edges_at_stages` gives `C(m,2)` at the rule's stages, `rule_sequence`
the point sequence `2,3,5,12,68`.  So "static = dynamic" for this reading is a
definitional equality — the cleanest possible witness of the `μF ≅ νF`
coincidence (the categorical version remains `Theory/Raw/MuNuMirror`).

## Open frontier

For which readings does `μF ≅ νF` hold in general?  The complete-graph reading
does (now ∅-axiom); betweenness does not (`object1_not_surjective`).
Characterizing the coincidence class — the readings whose constructive and
completed faces agree — is the same question as which readings have no residue
gap, and the general characterization is open.
