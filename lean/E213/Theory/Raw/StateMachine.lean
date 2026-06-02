import E213.Theory.Raw.Lambek
import E213.Theory.Raw.CoResidue
import E213.Theory.Raw.MuNuMirror
import E213.Theory.Raw.PrimitiveTower

/-!
# Theory.Raw.StateMachine — the FSM / coalgebra Lens reading

A `§6` Lens reading of the already-built `Lambek` / `CoResidue` / `MuNuMirror` objects through
the state-machine dictionary.  *Not* a claim that the residue **is** a state machine — that
would promote a reading to identity.  Every theorem here is about the existing coalgebra
objects, read as:

  | FSM | 213 / Lean |
  |---|---|
  | next-state logic `δ` | the coalgebra `c : X → Option Bool × X × X` / `coOut` |
  | run the machine (seed → trace) | the anamorphism `lAna` / `ana` |
  | **determinacy** (behaviour fixed by transition) | finality `lAna_unique` / `slashNu_final` |
  | terminal / halt state | an atom (peel-terminal, `Lambek.terminal_iff_atom`) |
  | non-degenerate transition (distinct successors) | the slash's `x ≠ y` / anti-reflexivity |
  | the all-branch self-loop (successors identical), excluded | `allBranchL` (`∉ SlashNu`) |
  | free-running counter | `rawTower` (`depth` = cycle count) |
  | state decodes to its next-state (Lambek forward; round-trip `rebuild`) | `decompose` + `terminal_iff_atom` |

All carriers are function types, so everything is stated **pointwise** (no `funext`); no
`simp` / `decide` / `DecidableEq Raw` (which would pull `propext`).  All zero-axiom.

Narrative: `theory/essays/the_residue_as_state_machine.md`.
-/

namespace E213.Theory.Raw.StateMachine

open E213.Theory (Raw)
open E213.Theory.Raw.Lambek (IsAtom IsTerminal decompose terminal_iff_atom)
open E213.Theory.Raw.CoResidue (LCoShape allBranchL AntiRefl coLeftAt coRightAt lAna lAna_unique)
open E213.Theory.Raw.PrimitiveTower (rawTower rawTower_depth)
open E213.Theory.Raw.MuNuMirror (tower_no_cycle)

/-! ## §1 — state ≅ transition (the µF Lambek reading) -/

/-- ★★ **A state decodes to a terminal atom or a branch with two distinct next-states.**  The
    register value reads as either a halt (atom — no successor) or a node branching to **two
    distinct** next-states (`x ≠ y` — a *non-degenerate* transition); and it is terminal iff
    it is an atom.  The Lambek *decode* (the forward half — the register decodes to its
    next-state; the round-trip `build ∘ decode = id` is `Lambek.rebuild`), non-degeneracy
    built in. -/
theorem state_transition_decode (r : Raw) :
    (r = Raw.a ∨ r = Raw.b ∨ ∃ (x y : Raw) (h : x ≠ y), r = Raw.slash x y h)
    ∧ (IsTerminal r ↔ IsAtom r) :=
  ⟨decompose r, terminal_iff_atom r⟩

/-! ## §2 — determinacy: the transition determines the behaviour -/

/-- ★★★ **Determinacy.**  Any two behaviours `h`, `h'` that both implement the transition `c`
    (the slash-coalgebra hom equations — root `·B`, branch `·Ln`/`·Rn`, leaf `·Ls`/`·Rs`)
    agree at every state and trace: `∀ x p, h x p = h' x p`.  The behaviour is *uniquely
    determined* by the next-state logic — finality read as determinacy (two applications of
    `lAna_unique`, pointwise; the `h = h'` form would need `funext`). -/
theorem transition_determines_behaviour {X : Type} (c : X → Option Bool × X × X)
    (h h' : X → LCoShape)
    (hB : ∀ x, h x [] = (c x).1)
    (hLn : ∀ x p, (c x).1 = none → h x (true :: p) = h (c x).2.1 p)
    (hLs : ∀ x p b, (c x).1 = some b → h x (true :: p) = some b)
    (hRn : ∀ x p, (c x).1 = none → h x (false :: p) = h (c x).2.2 p)
    (hRs : ∀ x p b, (c x).1 = some b → h x (false :: p) = some b)
    (h'B : ∀ x, h' x [] = (c x).1)
    (h'Ln : ∀ x p, (c x).1 = none → h' x (true :: p) = h' (c x).2.1 p)
    (h'Ls : ∀ x p b, (c x).1 = some b → h' x (true :: p) = some b)
    (h'Rn : ∀ x p, (c x).1 = none → h' x (false :: p) = h' (c x).2.2 p)
    (h'Rs : ∀ x p b, (c x).1 = some b → h' x (false :: p) = some b) :
    ∀ (x : X) (p : List Bool), h x p = h' x p :=
  fun x p =>
    (lAna_unique c h hB hLn hLs hRn hRs x p).trans
      (lAna_unique c h' h'B h'Ln h'Ls h'Rn h'Rs x p).symm

/-! ## §3 — the excluded self-loop (anti-reflexivity = non-degenerate transition) -/

/-- ★★★ **The all-branch self-loop is excluded.**  `allBranchL` — every node a branch, *both*
    successors the identical state (`coLeftAt allBranchL [] = coRightAt allBranchL []`, both
    constantly `none`) — is **not** anti-reflexive: at the root branch its two successors do
    not differ at any trace, so `¬ Distinct`.  Hence the degenerate transition (a register
    stepping to two copies of one next-state) is forbidden from the residue's νF carrier
    `SlashNu`.  (Refuted pointwise: every witness path collapses; no `funext`.) -/
theorem self_loop_excluded : ¬ AntiRefl allBranchL := by
  intro hAR
  obtain ⟨q, hq⟩ := hAR [] rfl
  exact hq rfl

/-- ★★ **The excluded state is exactly the transition self-loop.**  `allBranchL` is a fixpoint
    of the next-state map — both successors are the state itself (`coLeftAt allBranchL [] =
    coRightAt allBranchL [] = allBranchL`, pointwise) — and that *same* state is the one
    excluded (`self_loop_excluded`).  So this excluded degenerate state is precisely the
    transition-fixpoint (the pure self-loop); a non-degenerate transition never fixpoints. -/
theorem self_loop_is_excluded_fixpoint :
    ((∀ q, coLeftAt allBranchL [] q = allBranchL q)
      ∧ (∀ q, coRightAt allBranchL [] q = allBranchL q))
    ∧ ¬ AntiRefl allBranchL :=
  ⟨⟨fun _ => rfl, fun _ => rfl⟩, self_loop_excluded⟩

/-! ## §4 — the free-running counter never returns -/

/-- ★★ **The counter strictly increases and never revisits a state.**  On the free-running
    counter `rawTower`, a later cycle has strictly greater `depth` (cycle count) and is a
    distinct register value: `m < n → (rawTower m).depth < (rawTower n).depth ∧ rawTower m ≠
    rawTower n`.  No state recurs — the counter is acyclic. -/
theorem counter_no_return {m n : Nat} (h : m < n) :
    (rawTower m).depth < (rawTower n).depth ∧ rawTower m ≠ rawTower n := by
  refine ⟨?_, tower_no_cycle (Nat.ne_of_lt h)⟩
  rw [rawTower_depth, rawTower_depth]; exact h

end E213.Theory.Raw.StateMachine
