# How the infinite is proved, through the shapeLens

*Tier 1.  Renders §1.0′ (`seed/AXIOM/01_residue.md`) geometrically: the primitive
proof technique for the infinite is diagonalization, diagonalization is the
residue, and through the `shapeLens` (point = object, line = relation) it is the
slash itself.  Figure: `infinity_proof_mechanism.py`.*

## The mechanism (one move)

> Point at the totality (a self-cover); the something distinguishable from all of
> it (the residue) is forced to exist; the forcing **is** the proof.

Skeleton: `d(x) = ¬ cover(x)(x)`.  The cover is a self-map `T → (T → 2)`; the
residue `d` lies in the codomain but not the image — forced, never enumerated.

| theorem | self-cover | anti-diagonal residue |
|---|---|---|
| Cantor | reals as a list | a real flipping the n-th digit of the n-th |
| Russell | sets, `∈` | `R = {x : x ∉ x}` |
| Gödel | proofs, `Prov` | `G = "G is unprovable"` |
| Turing | machines, `halt` | the diagonal non-halting machine |
| Tarski | sentences, `True` | the liar |
| **213** | `Object1 : Raw → (Raw → Bool)` | `λ r. ¬ Object1 r r` (`cantor_raw_bool`) |

## Through the shapeLens

- **Local diagonal = the slash.**  Pointing at `{a, b}`, the relation `a/b` is
  distinguishable from `a` and from `b` (anti-reflexivity + freshness) — a point
  outside that two-element totality.  The slash is the one-step diagonal.
- **Global diagonal = the slash across a whole enumeration.**  The Cantor grid
  (rows = enumerated points, columns = their incidence) flipped on the diagonal is
  the local move applied to every listed point at once.
- **Non-closure = the proof.**  The generative graph (each relation a fresh point)
  never reaches the complete graph from inside; the frontier is always outside the
  prior set.  That non-closure is `object1_not_surjective`.

## The proof (repo)

`Lens/FlatOntologyClosure.object1_not_surjective` (= `cantor_raw_bool`), ∅-axiom:
`Object1 : Raw → (Raw → Bool)` is the self-cover; `δ := fun r => ¬ Object1 r r` is
in `Raw → Bool`; if `δ = Object1 r₀` then `δ r₀ = Object1 r₀ r₀ = ¬ Object1 r₀ r₀`,
contradiction; so `δ` is reached by no `Raw`.  §1.0′ names this the engine of the
deepest proofs about the infinite.

## Why this is proof, not construction

The diagonal does not *enumerate* the residue; it *forces* it.  `δ` is not
"constructed" (that would be one more finite pointing); rather "no finite cover
catches `δ`" is *proved*.  Hence the finite/compact readouts (the counts we
proved — `edgesK`, `cfgIdeals`, the angle) live at every finite stage and are
∅-axiom; "all of it" is the residue reached by no stage — its unreachability is
itself the theorem.  **Handling the infinite = iterating the slash; each totality
forces a residue outside it; the object need never be completed — the non-closure
is the content.**

## Relativization (a caveat, not a hedge)

This is one self-cover Lens (`Object1`).  Any other self-covering reading forces
its own anti-diagonal residue, so "many Lenses carry non-surjectivity"; and "the
residue is outside *every* view" is what a single view (`Object1`) states from
within (self-check lint #0 — no view is promoted to ontology).  The slash
(residue) is in the image of no cover; that is §5.1 no-exterior appearing *as a
proof*.
