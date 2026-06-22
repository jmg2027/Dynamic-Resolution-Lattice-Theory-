import E213.Theory.Raw.Lambek
import E213.Theory.Raw.PrimitiveTower

/-!
# Theory.Raw.MuNuMirror — the self-pointing act: descent terminates, ascent is unbounded

The act of pointing, read through its peel relation `IsPart` (`Lambek`), has two contrasting
facts — and they are an **existential** and a **universal-negation**, not two symmetric faces:

  * **descent terminates** — `Lambek.no_infinite_descent`: there is *no* total downward
    `IsPart`-chain; every descent bottoms out at an atom (`isPart_wf`).  This is the
    well-founded floor (Raw = µF).

  * **ascent is unbounded** — the self-pointing tower `rawTower n = a/(a/(…/b))`
    (`PrimitiveTower`) has depth `n` at every rung (`rawTower_depth`), and each rung peels
    from the next (`tower_ascent_isPart`), so there is an *explicit total upward*
    `IsPart`-stream and the `Raw`-depths are cofinal in `ℕ`: no finite Raw caps them
    (`ascent_unbounded`).

These are the depth/finite **shadow** of the µF/νF distinction.  Honest scope: there is **no
νF object here** — `ascent_unbounded` is `∀ N, ∃ r, N < r.depth`, a statement about every
*finite* Raw, not a completed infinite one; a native final `F`-coalgebra (νF) is an open
piece, blocked by Mathlib-free coinduction.  And the up/down facts are not symmetric
"readings of one operator": the ascent is one explicit stream (`rawTower`), the descent is a
universal-negation taken straight from `Lambek`.  No operator unifies them; they share only
the relation `IsPart` and the readout `depth`, both already defined.  All zero-axiom.

Narrative: `theory/essays/foundations/the_residue_as_primitive.md` (Raw = µF, the escape = νF).
-/

namespace E213.Theory.Raw.MuNuMirror

open E213.Theory (Raw)
open E213.Theory.Raw.Lambek (IsPart IsAtom IsTerminal isPart_wf no_infinite_descent
  terminal_iff_atom part_depth_succ_le)
open E213.Theory.Raw.PrimitiveTower (rawTower rawTower_depth depth_and_ne)
open E213.Theory.Raw.Endomorphic (slashOrSelf slashOrSelf_of_ne)

/-! ## §1 — `depth` is cofinal over Raw -/

/-- ★ **Depth is cofinal.**  Every `n : Nat` is the depth of some Raw — the tower rung
    `rawTower n` (`rawTower_depth`).  The `depth` readout hits every level. -/
theorem depth_cofinal (n : Nat) : ∃ r : Raw, r.depth = n :=
  ⟨rawTower n, rawTower_depth n⟩

/-- ★ **No finite Raw caps the depths.**  For every bound `N` the rung `rawTower (N+1)` has
    depth `N+1 > N`: the depths are unbounded over Raw (`∀ N, ∃ r, N < r.depth`).  This is the
    finite/depth shadow of the open νF object (a native final `F`-coalgebra), **not** a νF
    carrier — it quantifies over finite Raws, it does not construct an infinite one. -/
theorem ascent_unbounded (N : Nat) : ∃ r : Raw, N < r.depth := by
  refine ⟨rawTower (N + 1), ?_⟩
  rw [rawTower_depth]; exact Nat.lt_succ_self N

/-! ## §2 — the ascent climbs by the unit `1`, and never returns -/

/-- ★ **One rung = the unit `1`.**  Each ascent step adds exactly the count-Lens unit of one
    distinguishing: `(rawTower (n+1)).depth = (rawTower n).depth + 1` — the same unit the
    descent drops by (`part_depth_succ_le`). -/
theorem ascent_adds_unit (n : Nat) :
    (rawTower (n + 1)).depth = (rawTower n).depth + 1 := by
  rw [rawTower_depth, rawTower_depth]

/-- ★ **The ascent never cycles.**  Distinct levels give distinct Raws — the tower never
    returns: `rawTower` is depth-injective (`rawTower_depth`). -/
theorem tower_no_cycle {m n : Nat} (h : m ≠ n) : rawTower m ≠ rawTower n := by
  intro e
  apply h
  calc m = (rawTower m).depth := (rawTower_depth m).symm
    _ = (rawTower n).depth := congrArg Raw.depth e
    _ = n := rawTower_depth n

/-- ★ **The successor (growing) reading is non-idempotent** — `S r := slashOrSelf a r`
    (the ascent step, `rawTower (n+1) = S (rawTower n)`) satisfies `S (S r) ≠ S r` on the
    tower: applying it twice strictly raises depth, so it never settles.  This is the exact
    **mirror of the closure monad's idempotence** (`Order.GaloisConnection.clo_idempotent`,
    `T² = T`): the distinguishing's ascent is the *growing* (free-flavoured) endo-reading the
    *converging* (closure) corner lacks — the two values of the decomposition calculus's
    **iteration-character** axis, orthogonal to the `q = ±1` residue tag (the same ascent is
    growing here yet `q=+1`-converging as a residue, `ordinals.md`).  ∅-axiom. -/
theorem succ_not_idempotent (n : Nat) :
    slashOrSelf Raw.a (slashOrSelf Raw.a (rawTower n)) ≠ slashOrSelf Raw.a (rawTower n) := by
  show rawTower (n + 2) ≠ rawTower (n + 1)
  exact tower_no_cycle (Nat.succ_ne_self (n + 1))

/-! ## §3 — the ascent is an explicit total `IsPart`-stream -/

/-- ★★ **Each rung peels from the next.**  `rawTower n` is a part of
    `rawTower (n+1) = a / rawTower n` — the right child.  So `rawTower` is a *total* upward
    `IsPart`-stream.  (The genuinely new content of this file: an explicit total ascending
    stream, against which the imported `no_infinite_descent` is the downward
    universal-negation.) -/
theorem tower_ascent_isPart (n : Nat) : IsPart (rawTower n) (rawTower (n + 1)) :=
  ⟨Raw.a, rawTower n, (depth_and_ne n).2, slashOrSelf_of_ne (depth_and_ne n).2, Or.inr rfl⟩

/-- ★★ **Ascent total, descent partial (an existential vs a universal-negation).**  The
    relation `IsPart`:

    * read **upward** has an *explicit total* stream — `rawTower` peels at every step
      (`tower_ascent_isPart`): there is an endless ascending self-pointing;
    * read **downward** has *no* total stream — `no_infinite_descent` (taken from `Lambek`):
      every descent terminates at an atom.

    Note the asymmetry is between an existential witness and a universal-negation; the descent
    half is not new here, and these are not symmetric "two faces of one operator". -/
theorem ascent_total_descent_partial :
    (∃ s : Nat → Raw, ∀ k, IsPart (s k) (s (k + 1)))
    ∧ ¬ ∃ d : Nat → Raw, ∀ k, IsPart (d (k + 1)) (d k) :=
  ⟨⟨rawTower, tower_ascent_isPart⟩,
   fun ⟨d, hd⟩ => no_infinite_descent d hd⟩

/-! ## §4 — convenience bundle -/

/-- **Convenience bundle** (no new logical content beyond its conjuncts): well-founded
    descent (`isPart_wf`, from `Lambek`), depth-unboundedness (`ascent_unbounded`, the finite
    shadow), and the floor (`terminal_iff_atom`, from `Lambek`).  Pairs the three facts that
    describe the act's down/up behaviour at the Raw scale; it does not capture any infinite
    object. -/
theorem descent_wf_ascent_unbounded :
    WellFounded IsPart
    ∧ (∀ N : Nat, ∃ r : Raw, N < r.depth)
    ∧ (∀ r : Raw, IsTerminal r ↔ IsAtom r) :=
  ⟨isPart_wf, ascent_unbounded, terminal_iff_atom⟩

end E213.Theory.Raw.MuNuMirror
