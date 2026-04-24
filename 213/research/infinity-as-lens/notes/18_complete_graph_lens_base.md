# 18 — Complete graph as the bottom-most Lens (2026-04-24)

## Mingu's observation

> "213이 기하학적으로 직관적이고 완전그래프라는 게
> 포인트가 될 것이라고 생각해. (물론 그것도 원론적으론
> 렌징이지만 실용적으론) 이거만 해도 렌즈의 조건이나
> 형태들을 연구할 수 있으니."

## The connection DRLT ↔ 213

DRLT's axiom (root `CLAUDE.md`):
> "Things exist with pairwise relations.
> `G_ij = ⟨ψ_i | ψ_j⟩`."

The complete graph K_n on n objects, with a weight
(or amplitude) on every edge, is the geometric realisation
of "things + pairwise relations".  213's Raw axiom
(two primitive distinctions + binary pairing) is the
**same content**, encoded as a free inductive type rather
than a graph.

**Claim**: The complete-graph Lens is the
lowest-commitment Lens on Raw that preserves the pairwise
relation structure.  Every other mathematically fruitful
Lens on Raw factors through it at some stage.

## Why complete graph, not a generic graph

- The Raw axiom's symmetry (Def 2.1 swap + Thm 2.2
  involution in PAPER.md) treats `a` and `b` interchangeably.
  Any Lens that preserves this symmetry cannot privilege
  any edge — every pairing `x ⋄ y` is on equal footing
  with `y ⋄ x` (slash_comm).
- "All pairs relate" is the minimal structure consistent
  with the axiom's non-asymmetry.  Any weaker structure
  (an incidence graph, a tree) privileges some pairs over
  others; that privilege is a further Lens choice.

## Strict Raw-purist caveat

Even the complete graph is a Lens.  It chooses:
- a vertex set V (already a collection, already a Lens on
  the Raw enumeration);
- an edge-weight codomain (integers, reals, amplitudes, …);
- a specific pairing assignment.

The claim is not that K_n is "Raw itself" but that it is
the **closest visualisable image** of Raw — the Lens at
which the geometric intuition turns on and beyond which
every choice adds strictly more commitment.

## Practical payoff (why this matters)

1. **Visual intuition.**  Human brains process graphs
   dramatically faster than linear symbolic forms.  Every
   theorem about Raw has a K_n-picture.
2. **Tool reuse.**  Graph theory supplies
   decades of tools (spectral graph theory, cycle space,
   chromatic invariants, graph minors) that become
   automatic Lens-classifiers.
3. **Algebraic ↔ geometric transit.**  DRLT physics lives
   in K_n (5-simplex → K_5, 600-cell → K_{120}, etc.).
   Mathematical results derived in 213 are automatically
   transportable to DRLT's K_n pictures.
4. **Lens-as-graph-fold.**  Every 213 Lens can be rewritten
   as a partition / contraction / colouring of K_n.  The
   Lens catalogue becomes a catalogue of graph-fold
   primitives.

## Existing mathematics that already uses this Lens

Without calling it so:
- **Cayley graphs** (groups as K_n folds).
- **Dynkin diagrams** (Lie algebras as graph contractions).
- **Feynman diagrams** (QFT amplitudes as weighted K_n).
- **Schreier / Bruhat–Tits buildings.**
- **Graph C*-algebras, quantum graphs** (quantum
  information theory).

Each of these is a research programme that has
rediscovered the complete-graph Lens under a different
name.  213 names it once.

## Research agenda this opens

1. **Rewrite R1–R5 as K_n-fold conditions.**
   - R1 (faithfulness): edge-preservation up to
     isomorphism.
   - R2 (symmetry): graph-automorphism compatibility.
   - R3 (non-vanishing): no edge class collapses.
   - R4 (conj compatibility): involution–coloring
     coherence.
   - R5 (distinguishing): orbit separation.
2. **Define `CompleteGraphLens : Lens (K ∞)`** in Lean
   (target: a representation of the complete graph on
   Raw terms, with the pair-decomposition map).
3. **Factorisation theorem (conjecture).** Every Lens in
   the 213 catalogue factors through `CompleteGraphLens`
   up to a further graph-fold stage.

## Status

Observation stage.  No Lean yet.  One session to prototype
`CompleteGraphLens.lean`, one more to express a few
existing Lenses as factoring through it.

## Relationship to other notes

- `notes/17_existence_mode_lens.md`: the existence-mode
  axis is orthogonal — K_n can be read Platonic (fully
  drawn) or constructive (edges added as pairs are
  formed).
- `notes/19_lens_not_functor.md`: K_n Lens itself is not
  a functor; it is a representation-theoretic Lens on Raw.
- `notes/20_bridge_search_infrastructure.md`: K_n
  supplies the common substrate in which bridge-Lens
  meets can be *computed*.
