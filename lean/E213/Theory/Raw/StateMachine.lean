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
  | reachable state (built from an initial atom) | `BuildsIn` (`n`-step build relation) |
  | behavioural / trace equivalence (same observable behaviour) | `TraceEq` (`= ¬ Distinct`, no bisimulation) |
  | state decodes to its next-state (Lambek forward; round-trip `rebuild`) | `decompose` + `terminal_iff_atom` |

All carriers are function types, so everything is stated **pointwise** (no `funext`); no
`simp` / `decide` / `DecidableEq Raw` (which would pull `propext`).  All zero-axiom.

Narrative: `theory/essays/the_residue_as_state_machine.md`.
-/

namespace E213.Theory.Raw.StateMachine

open E213.Theory (Raw)
open E213.Theory.Raw.Lambek (IsAtom IsTerminal IsPart decompose terminal_iff_atom
  slash_has_part part_depth_succ_le depth_drops)
open E213.Theory.Raw.CoResidue (LCoShape allBranchL AntiRefl coLeftAt coRightAt lAna lAna_unique
  Distinct slash_children_distinct lToShape)
open E213.Theory.Raw.PrimitiveTower (rawTower rawTower_depth)
open E213.Theory.Raw.MuNuMirror (tower_no_cycle tower_ascent_isPart)

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

/-! ## §5 — reachability: every state is built from an initial (atom) state -/

/-- **Reachability in exactly `n` build-steps.**  `BuildsIn n seed top` — there is a chain
    `seed = r₀, r₁, …, rₙ = top` where each `rᵢ` is a *part* (immediate predecessor /
    constituent next-state) of `rᵢ₊₁` (`IsPart rᵢ rᵢ₊₁`).  This is the **`n`-step** build
    relation — `refl` (zero steps) plus one-step `IsPart`-extension (the upward reading of the
    peel relation `IsPart`); it is the iterate `IsPartᵇⁿ`, *not* a transitive closure (no
    `trans` is proved).  One step builds a bigger state from one of its constituents.  In the
    FSM reading, `seed` is an initial register value and `top` is reached after `n`
    build-steps. -/
inductive BuildsIn : Nat → Raw → Raw → Prop where
  | refl (r : Raw) : BuildsIn 0 r r
  | step {n : Nat} {seed mid top : Raw} :
      BuildsIn n seed mid → IsPart mid top → BuildsIn (n + 1) seed top

/-- ★★★ **The free-running counter reaches every level — in exactly that many build-steps.**
    From the initial atom `b` (`rawTower 0 = b`), the counter `rawTower n` is reached in
    *exactly* `n` build-steps, each adding one rung (`tower_ascent_isPart`).  Read as an FSM:
    starting from the reset state, the free-running counter reaches its `n`-th value after
    `n` clock ticks — and (`counter_reaches_every_level`) that state has `depth = n`, so every
    level is reached. -/
theorem counter_reachable (n : Nat) : BuildsIn n Raw.b (rawTower n) := by
  induction n with
  | zero => exact BuildsIn.refl Raw.b
  | succ k ih => exact BuildsIn.step ih (tower_ascent_isPart k)

/-- ★★ **Every level is reached.**  Packaging `counter_reachable` with `rawTower_depth`: in
    `n` build-steps from `b` the counter reaches a state of `depth = n` — so for every level
    `n` there is a reachable state at exactly that depth (the counter is a *clock*: step count
    = level reached). -/
theorem counter_reaches_every_level (n : Nat) :
    BuildsIn n Raw.b (rawTower n) ∧ (rawTower n).depth = n :=
  ⟨counter_reachable n, rawTower_depth n⟩

/-- ★★★ **Every state is reachable from an initial (atom) state, within `depth` build-steps.**
    For *any* register value `r` there is *an* atom `seed` (`a` or `b`, whichever floors that
    state — not a unique reset) and a step count `k ≤ r.depth` with `BuildsIn k seed r`: every
    state is built up from an atomic floor, and the build never takes more steps than the
    state's depth (`k ≤ r.depth` — an upper bound, not an equality).  This is **reachability of
    the whole µF carrier** from the initial states — the synthesizable invariant.  Proved by
    depth-bounded strong induction (the `isPart_wf` shape) via `decompose`; no `Raw.rec`. -/
theorem every_state_reachable (r : Raw) :
    ∃ seed : Raw, IsAtom seed ∧ ∃ k : Nat, k ≤ r.depth ∧ BuildsIn k seed r := by
  have key : ∀ n : Nat, ∀ r : Raw, r.depth < n →
      ∃ seed : Raw, IsAtom seed ∧ ∃ k : Nat, k ≤ r.depth ∧ BuildsIn k seed r := by
    intro n
    induction n with
    | zero => intro r hr; exact absurd hr (Nat.not_lt_zero _)
    | succ m ih =>
        intro r hr
        rcases decompose r with ha | hb | ⟨x, y, hxy, hr_eq⟩
        · exact ⟨Raw.a, Or.inl rfl, 0, Nat.zero_le _, by rw [ha]; exact BuildsIn.refl Raw.a⟩
        · exact ⟨Raw.b, Or.inr rfl, 0, Nat.zero_le _, by rw [hb]; exact BuildsIn.refl Raw.b⟩
        · subst hr_eq
          have hpart : IsPart x (Raw.slash x y hxy) := slash_has_part x y hxy
          have hxle : x.depth + 1 ≤ (Raw.slash x y hxy).depth := part_depth_succ_le _ _ hpart
          have hxdlt : x.depth < m :=
            Nat.lt_of_lt_of_le (depth_drops x y hxy).1 (Nat.le_of_lt_succ hr)
          obtain ⟨seed, hseed, j, hj, hbuild⟩ := ih x hxdlt
          exact ⟨seed, hseed, j + 1,
            Nat.le_trans (Nat.add_le_add_right hj 1) hxle, BuildsIn.step hbuild hpart⟩
  exact key (r.depth + 1) r (Nat.lt_succ_self _)

/-! ## §6 — behavioural / trace equivalence is pointwise (not bisimulation) -/

/-- **Trace (behavioural) equivalence**: two behaviours agree at *every* observation path.
    `TraceEq s t := ∀ q, s q = t q`.  In the FSM reading: two states are behaviourally
    equivalent when their output traces coincide on every input string.  Stated *pointwise*
    (the `s = t` form would need `funext`). -/
def TraceEq (s t : LCoShape) : Prop := ∀ q : List Bool, s q = t q

/-- ★ **Trace equivalence is an equivalence relation** (reflexive, symmetric, transitive) —
    pointwise, ∅-axiom.  Behavioural equivalence behaves as a congruence on observable traces. -/
theorem traceEq_equivalence :
    (∀ s, TraceEq s s)
    ∧ (∀ s t, TraceEq s t → TraceEq t s)
    ∧ (∀ s t u, TraceEq s t → TraceEq t u → TraceEq s u) :=
  ⟨fun _ _ => rfl,
   fun _ _ h q => (h q).symm,
   fun _ _ _ h1 h2 q => (h1 q).trans (h2 q)⟩

/-- ★★★ **Trace equivalence is exactly non-distinctness — equality and the positive inequality
    are complementary, no bisimulation.**  `TraceEq s t ↔ ¬ Distinct s t`: two behaviours are
    trace-equivalent precisely when there is *no* differing observation path.  The forward way
    is immediate; the reverse uses only the *decidable* equality of `Option Bool` (`¬¬(s q = t
    q) → s q = t q`, `Decidable.byContradiction`) — **not** a coinductive bisimulation.  This
    is the whole point of the construction: inequality is *positive* (a single witness path,
    `Distinct`), so equality is its plain decidable complement; co-data equality never needs a
    bisimulation here. -/
theorem traceEq_iff_not_distinct (s t : LCoShape) : TraceEq s t ↔ ¬ Distinct s t := by
  constructor
  · rintro h ⟨q, hq⟩
    exact hq (h q)
  · intro h q
    exact Decidable.byContradiction (fun hne => h ⟨q, hne⟩)

/-- ★★ **Distinct states are behaviourally distinguished.**  If two behaviours are `Distinct`
    (differ at some path), they are *not* trace-equivalent — the witnessing path observably
    separates them.  Immediate from `traceEq_iff_not_distinct`. -/
theorem distinct_states_not_traceEq (s t : LCoShape) (hd : Distinct s t) : ¬ TraceEq s t :=
  fun hEq => (traceEq_iff_not_distinct s t).1 hEq hd

/-- ★★ **The residue's `x ≠ y` is observable separation.**  Two distinct finite states embed
    as behaviourally *distinguished* traces: from `x ≠ y` the children `lToShape x`, `lToShape
    y` differ at a constructible path (`slash_children_distinct`), so they are not
    trace-equivalent.  The slash's disequality reads as: the two next-states are observably
    different machines. -/
theorem slash_children_not_traceEq {x y : E213.Term.Internal.Tree} (h : x ≠ y) :
    ¬ TraceEq (lToShape x) (lToShape y) :=
  distinct_states_not_traceEq _ _ (slash_children_distinct x y h)

/-- ★★★ **Same transition ⟹ trace-equivalent (determinacy as trace equivalence).**  Any two
    behaviours `h`, `h'` implementing the same transition `c` are trace-equivalent at every
    state: `TraceEq (h x) (h' x)`.  This is `transition_determines_behaviour` read through the
    equivalence relation — finality says the trace is *determined* (one equivalence class per
    state), so two implementations land in the same class. -/
theorem behaviours_traceEq {X : Type} (c : X → Option Bool × X × X)
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
    (h'Rs : ∀ x p b, (c x).1 = some b → h' x (false :: p) = some b)
    (x : X) : TraceEq (h x) (h' x) :=
  fun p => transition_determines_behaviour c h h' hB hLn hLs hRn hRs
    h'B h'Ln h'Ls h'Rn h'Rs x p

end E213.Theory.Raw.StateMachine
