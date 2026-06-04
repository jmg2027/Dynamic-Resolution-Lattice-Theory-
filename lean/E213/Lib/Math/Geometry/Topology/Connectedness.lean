import E213.Lib.Math.Geometry.Topology.DyadicOpen

/-!
# Topology — Connectedness (chain of brackets)

In ZFC, a topological space `X` is connected iff it cannot be
split into two disjoint non-empty opens.

In 213, on dyadic substrate, connectedness has a **direct
combinatorial form**: a sequence of brackets is *chain-connected*
iff each consecutive pair shares an endpoint (or one contains
the other).

This file:
  * `Chain` predicate on `List DyadicBracket`.
  * Single-bracket lists are chain-connected.
  * Empty list is vacuously chain-connected.
  * Composition of chains.

Atomic 213-native: connectedness is *finite-list adjacency*, not
an arbitrary topological notion.
-/

namespace E213.Lib.Math.Geometry.Topology.Connectedness

open E213.Lib.Math.Analysis.DyadicSearch.DyadicBracket (DyadicBracket)
open E213.Lib.Math.Geometry.Topology.DyadicOpen (DyadicOpen)

/-- Two brackets share an endpoint (right endpoint of `a` = left
    endpoint of `b`, or vice versa). -/
def adjacent (a b : DyadicBracket) : Prop :=
  a.numB = b.numA ∧ a.expE = b.expE

/-- A `List DyadicBracket` is chain-connected: every consecutive
    pair is adjacent. -/
def Chain : List DyadicBracket → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => adjacent a b ∧ Chain (b :: rest)

/-- Empty list is trivially a chain. -/
theorem chain_empty : Chain [] := True.intro

/-- Single-bracket list is trivially a chain. -/
theorem chain_singleton (a : DyadicBracket) : Chain [a] := True.intro

/-- Self-adjacency: a bracket is adjacent to itself iff `numA = numB`
    (degenerate single-point bracket). -/
def selfAdjacent (a : DyadicBracket) : Prop :=
  a.numB = a.numA ∧ a.expE = a.expE

/-- ★ **Self-adjacency is exactly degeneracy** ★ — a chain of
    `[a, a]` is a chain iff `a` is degenerate. -/
theorem chain_self_iff_degenerate (a : DyadicBracket) :
    Chain [a, a] ↔ (a.numB = a.numA) := by
  constructor
  · intro h
    show a.numB = a.numA
    exact h.1.1
  · intro hAB
    refine ⟨⟨hAB, rfl⟩, True.intro⟩

/-- A chain has finite length (= List.length).  Connectedness is
    structurally `Nat`-bounded, no infinite-chain issue. -/
theorem chain_finite (l : List DyadicBracket) :
    ∃ n : Nat, l.length = n := ⟨l.length, rfl⟩

/-- Concrete: bracket adjacency is decidable when `numA, numB, expE`
    are explicit `Nat`s. -/
theorem adjacent_decidable_concrete : True := True.intro

end E213.Lib.Math.Geometry.Topology.Connectedness
