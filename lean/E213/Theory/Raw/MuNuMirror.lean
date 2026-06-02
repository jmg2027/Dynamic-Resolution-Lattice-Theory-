import E213.Theory.Raw.Lambek
import E213.Theory.Raw.PrimitiveTower

/-!
# Theory.Raw.MuNuMirror — the two fixed points of the self-pointing act: descent
terminates (µF), ascent escapes (νF)

The act of pointing has two structurally distinct fates, the two fixed points of its own
constructor shape `F(X) = {a} ⊎ {b} ⊎ {x/y : x ≠ y}` (see `Lambek`):

  * **µF (Raw — descent terminates).**  Peeling a Raw is well-founded: every downward
    `IsPart`-chain bottoms out at an atom (`Lambek.isPart_wf`, `no_infinite_descent`).  Raw is
    the least fixed point — the finite, grounded realisation of the act.

  * **νF (the residue's escape — ascent escapes).**  Iterating the act *upward* — the
    self-pointing tower `rawTower n = a/(a/(…/b))` (`PrimitiveTower`) — has depth `n` at every
    rung (`rawTower_depth`), so the depths are cofinal in `ℕ` and **no Raw bounds them**: the
    completed infinite self-pointing is not any Raw.  This is the residue's escape given a
    **positive native** form (via `depth`), dual to its negative form
    (`FlatOntologyClosure.object1_not_surjective`, Cantor) and to the tower-scale
    `Cauchy.DepthCeilingResidue` — here at the Raw floor.

The same relation `IsPart` carries both: read **downward** it always terminates
(`no_infinite_descent`), read **upward** it is always continuable
(`tower_ascent_isPart` — an endless ascending stream exists, `ascent_total_descent_partial`).
The unit by which the ascent climbs is the count-Lens `1` of one distinguishing
(`ascent_adds_unit`: one rung = `+1` depth), the same unit the descent drops by
(`Lambek.part_depth_succ_le`).

Honest scope (the standing guard, `theory/essays/the_form_of_the_residue.md`): these are
**escape *descriptions*** (`∀ N, ∃ r, N < r.depth`; an ascending stream exists), never a νF
*object* — Mathlib-free Lean has no native coinduction, and the residue stays outside every
view.  No operator unifies the up/down readings; they share only the one relation `IsPart`
and the one readout `depth`, both already defined.  All zero-axiom.
-/

namespace E213.Theory.Raw.MuNuMirror

open E213.Theory (Raw)
open E213.Theory.Raw.Lambek (IsPart IsAtom IsTerminal isPart_wf no_infinite_descent
  terminal_iff_atom part_depth_succ_le)
open E213.Theory.Raw.PrimitiveTower (rawTower rawTower_depth depth_and_ne)
open E213.Theory.Raw.Endomorphic (slashOrSelf_of_ne)

/-! ## §1 — depth is cofinal: every level is realised, no Raw bounds the ascent -/

/-- ★ **Depth is cofinal.**  Every `n : Nat` is the depth of some Raw — the tower rung
    `rawTower n` (`rawTower_depth`).  The `depth` readout hits every level. -/
theorem depth_cofinal (n : Nat) : ∃ r : Raw, r.depth = n :=
  ⟨rawTower n, rawTower_depth n⟩

/-- ★★ **No Raw caps the ascent.**  There is no global depth ceiling: for every bound `N`
    the rung `rawTower (N+1)` has depth `N+1 > N`.  The self-pointing iterated upward escapes
    every finite Raw — the residue's escape at the Raw floor, dual to the tower-scale
    `DepthCeilingResidue` "no top". -/
theorem no_depth_ceiling : ¬ ∃ N : Nat, ∀ r : Raw, r.depth ≤ N := by
  rintro ⟨N, hN⟩
  have h := hN (rawTower (N + 1))
  rw [rawTower_depth] at h
  exact Nat.not_succ_le_self N h

/-- ★ **The ascent is unbounded (positive form).**  For every `N` there is a Raw deeper than
    `N`: `rawTower (N+1)` has depth `N+1`. -/
theorem ascent_unbounded (N : Nat) : ∃ r : Raw, N < r.depth := by
  refine ⟨rawTower (N + 1), ?_⟩
  rw [rawTower_depth]; exact Nat.lt_succ_self N

/-! ## §2 — the ascent climbs by the unit `1`, and never settles -/

/-- ★ **One rung = the unit `1`.**  Each ascent step adds exactly the count-Lens unit of one
    distinguishing: `(rawTower (n+1)).depth = (rawTower n).depth + 1` — the same unit the
    descent drops by (`part_depth_succ_le`). -/
theorem ascent_adds_unit (n : Nat) :
    (rawTower (n + 1)).depth = (rawTower n).depth + 1 := by
  rw [rawTower_depth, rawTower_depth]

/-- ★ **The ascent never cycles.**  Distinct levels give distinct Raws — the tower never
    returns: `rawTower` is injective (depth-injective, `rawTower_depth`). -/
theorem tower_no_cycle {m n : Nat} (h : m ≠ n) : rawTower m ≠ rawTower n := by
  intro e
  apply h
  calc m = (rawTower m).depth := (rawTower_depth m).symm
    _ = (rawTower n).depth := congrArg Raw.depth e
    _ = n := rawTower_depth n

/-! ## §3 — the ascent is an `IsPart`-stream: always continuable -/

/-- ★ **Each rung peels from the next.**  `rawTower n` is a part of `rawTower (n+1) =
    a / rawTower n` — the right child.  So the ascending tower is an `IsPart`-stream going
    *up*. -/
theorem tower_ascent_isPart (n : Nat) : IsPart (rawTower n) (rawTower (n + 1)) :=
  ⟨Raw.a, rawTower n, (depth_and_ne n).2, slashOrSelf_of_ne (depth_and_ne n).2, Or.inr rfl⟩

/-- ★★★ **Ascent total, descent partial — the µF/νF asymmetry.**  The *same* relation
    `IsPart`:

    * read **upward** has a total stream — `rawTower` peels at every step
      (`tower_ascent_isPart`): the self-pointing is always continuable (the νF escape);
    * read **downward** has *no* total stream — `no_infinite_descent`: every descent
      terminates at an atom (the µF floor).

    One relation, two fates — the sharp form of "descent converges, ascent escapes".  No
    operator unifies the directions; they are one relation read two ways. -/
theorem ascent_total_descent_partial :
    (∃ s : Nat → Raw, ∀ k, IsPart (s k) (s (k + 1)))
    ∧ ¬ ∃ d : Nat → Raw, ∀ k, IsPart (d (k + 1)) (d k) :=
  ⟨⟨rawTower, tower_ascent_isPart⟩,
   fun ⟨d, hd⟩ => no_infinite_descent d hd⟩

/-! ## §4 — the mirror, bundled -/

/-- ★★★ **The two fixed points of the act.**  Bundles the µF/νF mirror:

    1. **µF (descent terminates)** — the peel relation is well-founded (`isPart_wf`): every
       downward chain bottoms out;
    2. **νF (ascent escapes)** — no Raw bounds the upward self-pointing (`ascent_unbounded`):
       the completed infinite act is not any Raw;
    3. **floor = atoms** — peel-terminal exactly at the atoms (`terminal_iff_atom`).

    The act, iterated, terminates going *down* (the finite Raw, µF) and escapes going *up*
    (the residue, νF) — both ∅-axiom, both native (via `IsPart` and `depth`, no Cantor, no
    coinduction).  This is `Lambek.two_closures` re-read as the two fixed points: the least
    (grounded) and the escaping (un-bounded), source-without-enclosure at the Raw scale. -/
theorem mu_nu_mirror :
    WellFounded IsPart
    ∧ (∀ N : Nat, ∃ r : Raw, N < r.depth)
    ∧ (∀ r : Raw, IsTerminal r ↔ IsAtom r) :=
  ⟨isPart_wf, ascent_unbounded, terminal_iff_atom⟩

end E213.Theory.Raw.MuNuMirror
