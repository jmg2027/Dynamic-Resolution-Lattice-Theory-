import E213.Theory.Raw.Core
import E213.Theory.Raw.Slash
import E213.Theory.Raw.Swap

/-!
# Theory.Raw.Async: the asynchronous growth ladder (fused semantics)

Raw growth as an asynchronous event system: a state is the list of
points so far; one event kind — `fire x y` — contrasts two distinct
present points whose pair is absent and adjoins `Raw.slash x y`.
(The line/point two-event split is a Lens on this one constructor;
this file fixes the *fused* reading.  Event-indexed boundaries are
semantics-tagged; the residue-level clauses are the ones provable
here.)

The forced ladder:

  * **Step 1 is forced** — from `{a, b}` the only successor is
    adjoining `a/b` (`step1_forced`).
  * **Step 2 is canonical up to swap** — exactly two successors,
    the `Raw.swap`-conjugate pair adjoining `a/(a/b)` or `b/(a/b)`
    (`level2_canonical`, `level2_swap_partner`).
  * **Step 3 diverges beyond swap** — two 3-step runs reach
    snapshots that are not membership-equal even after a global
    swap: the depth-2 completion vs a depth-3 fork
    (`level3_diverges`).

So determinism ends at the first composite, one further firing is
swap-canonical, and the next firing is where simultaneity
convention (foliation choice) becomes observable.  No run is forced
through the 5-element depth-≤2 census; what distinguishes that
census is order-internal (its past-completeness, proven in
`Lib/Math/Foundations/UniverseChain/RawPastCompleteness.lean`).
-/

namespace E213.Theory.Async

open E213.Theory

-- ═══ named small terms ═══

def ab : Raw := Raw.slash Raw.a Raw.b (by decide)
def aab : Raw := Raw.slash Raw.a ab (by decide)
def bab : Raw := Raw.slash Raw.b ab (by decide)
/-- The depth-3 fork witness `a/(a/(a/b))`. -/
def aaab : Raw := Raw.slash Raw.a aab (by decide)

-- ═══ the event system (fused) ═══

/-- A state: the points present so far. -/
abbrev State := List Raw

/-- The initial state: the two atoms. -/
def init : State := [Raw.a, Raw.b]

/-- One asynchronous event: contrast two distinct present points
    whose pair is absent, adjoining the pair. -/
inductive Step : State → State → Prop where
  | fire (s : State) (x y : Raw) (h : x ≠ y)
      (hx : x ∈ s) (hy : y ∈ s) (hnew : Raw.slash x y h ∉ s) :
      Step s (Raw.slash x y h :: s)

/-- `n`-step reachability from `init`. -/
inductive ReachN : Nat → State → Prop where
  | zero : ReachN 0 init
  | succ {n : Nat} {s t : State} :
      ReachN n s → Step s t → ReachN (n + 1) t

/-- Snapshot equality as point-sets (order-free membership). -/
def MemEq (s t : State) : Prop := ∀ r : Raw, r ∈ s ↔ r ∈ t

-- ═══ membership case analysis ═══

private theorem mem_two {r x y : Raw} : r ∈ [x, y] → r = x ∨ r = y
  | .head _ => Or.inl rfl
  | .tail _ (.head _) => Or.inr rfl
  | .tail _ (.tail _ h) => nomatch h

private theorem mem_three {r x y z : Raw} :
    r ∈ [x, y, z] → r = x ∨ r = y ∨ r = z
  | .head _ => Or.inl rfl
  | .tail _ h => Or.inr (mem_two h)

-- ═══ the ladder ═══

/-- ★ **Step 1 is forced**: the only successor of `init` adjoins
    `a/b`. -/
theorem step1_forced (t : State) (h : Step init t) :
    t = [ab, Raw.a, Raw.b] := by
  cases h with
  | fire x y hxy hx hy hnew =>
    cases mem_two hx with
    | inl hxa =>
      cases mem_two hy with
      | inl hya => exact absurd (hxa.trans hya.symm) hxy
      | inr hyb =>
        subst hxa; subst hyb
        rfl
    | inr hxb =>
      cases mem_two hy with
      | inl hya =>
        subst hxb; subst hya
        rw [Raw.slash_comm Raw.b Raw.a hxy]
        rfl
      | inr hyb => exact absurd (hxb.trans hyb.symm) hxy

/-- ★★ **Step 2 is canonical up to swap**: every 2-step state is
    exactly one of the two swap-conjugate level-2 snapshots. -/
theorem level2_canonical (t u : State)
    (h1 : Step init t) (h2 : Step t u) :
    u = [aab, ab, Raw.a, Raw.b] ∨ u = [bab, ab, Raw.a, Raw.b] := by
  have ht := step1_forced t h1
  subst ht
  cases h2 with
  | fire x y hxy hx hy hnew =>
    cases mem_three hx with
    | inl hxab =>
      cases mem_three hy with
      | inl hyab => exact absurd (hxab.trans hyab.symm) hxy
      | inr hy' =>
        cases hy' with
        | inl hya =>
          subst hxab; subst hya
          exact Or.inl (by rw [Raw.slash_comm ab Raw.a hxy]; rfl)
        | inr hyb =>
          subst hxab; subst hyb
          exact Or.inr (by rw [Raw.slash_comm ab Raw.b hxy]; rfl)
    | inr hx' =>
      cases hx' with
      | inl hxa =>
        subst hxa
        cases mem_three hy with
        | inl hyab => subst hyab; exact Or.inl rfl
        | inr hy' =>
          cases hy' with
          | inl hya => exact absurd hya.symm hxy
          | inr hyb =>
            subst hyb
            exact absurd (List.Mem.head _) hnew
      | inr hxb =>
        subst hxb
        cases mem_three hy with
        | inl hyab => subst hyab; exact Or.inr rfl
        | inr hy' =>
          cases hy' with
          | inl hya =>
            subst hya
            have he : Raw.slash Raw.b Raw.a hxy = ab :=
              Raw.slash_comm Raw.b Raw.a hxy
            rw [he] at hnew
            exact absurd (List.Mem.head _) hnew
          | inr hyb => exact absurd hyb.symm hxy

/-- The two level-2 outcomes are one swap orbit (and the forced
    step-1 point is swap-fixed). -/
theorem level2_swap_partner :
    Raw.swap aab = bab ∧ Raw.swap bab = aab ∧ Raw.swap ab = ab :=
  ⟨Subtype.ext rfl, Subtype.ext rfl, Subtype.ext rfl⟩

-- ═══ concrete 3-step runs ═══

/-- The depth-2 completion snapshot. -/
def d2state : State := [bab, aab, ab, Raw.a, Raw.b]

/-- A depth-3 fork snapshot: `a/(a/(a/b))` built before `b/(a/b)`. -/
def forkState : State := [aaab, aab, ab, Raw.a, Raw.b]

-- Explicit membership terms (the core `∈`-decidability instance for
-- lists routes through propext; constructors keep the runs PURE).

private theorem notmem_nil {r : Raw} : r ∉ ([] : List Raw) :=
  fun h => nomatch h

private theorem notmem_cons {r x : Raw} {l : List Raw}
    (h1 : r ≠ x) (h2 : r ∉ l) : r ∉ (x :: l) := fun h =>
  match h with
  | .head _ => h1 rfl
  | .tail _ h' => h2 h'

private theorem stepA : Step init [ab, Raw.a, Raw.b] :=
  Step.fire init Raw.a Raw.b (by decide)
    (.head _) (.tail _ (.head _))
    (notmem_cons (by decide) (notmem_cons (by decide) notmem_nil))

private theorem stepB :
    Step [ab, Raw.a, Raw.b] [aab, ab, Raw.a, Raw.b] :=
  Step.fire [ab, Raw.a, Raw.b] Raw.a ab (by decide)
    (.tail _ (.head _)) (.head _)
    (notmem_cons (by decide) (notmem_cons (by decide)
      (notmem_cons (by decide) notmem_nil)))

private theorem stepComplete :
    Step [aab, ab, Raw.a, Raw.b] d2state :=
  Step.fire [aab, ab, Raw.a, Raw.b] Raw.b ab (by decide)
    (.tail _ (.tail _ (.tail _ (.head _)))) (.tail _ (.head _))
    (notmem_cons (by decide) (notmem_cons (by decide)
      (notmem_cons (by decide) (notmem_cons (by decide) notmem_nil))))

private theorem stepFork :
    Step [aab, ab, Raw.a, Raw.b] forkState :=
  Step.fire [aab, ab, Raw.a, Raw.b] Raw.a aab (by decide)
    (.tail _ (.tail _ (.head _))) (.head _)
    (notmem_cons (by decide) (notmem_cons (by decide)
      (notmem_cons (by decide) (notmem_cons (by decide) notmem_nil))))

theorem reach3_d2 : ReachN 3 d2state :=
  .succ (.succ (.succ .zero stepA) stepB) stepComplete

theorem reach3_fork : ReachN 3 forkState :=
  .succ (.succ (.succ .zero stepA) stepB) stepFork

private theorem bab_notmem_fork : bab ∉ forkState :=
  notmem_cons (by decide) (notmem_cons (by decide)
    (notmem_cons (by decide) (notmem_cons (by decide)
      (notmem_cons (by decide) notmem_nil))))

/-- ★★★ **Step 3 diverges beyond swap**: two 3-step runs reach
    snapshots that disagree as point-sets, and still disagree after
    a global `Raw.swap` — the witness point is `b/(a/b)`, present
    in the depth-2 completion (and in the swap image of the fork's
    own partner) but absent from the fork.  From here on, "which
    snapshot" is a foliation (simultaneity) choice. -/
theorem level3_diverges :
    ∃ u v : State, ReachN 3 u ∧ ReachN 3 v
      ∧ ¬ MemEq u v ∧ ¬ MemEq u (v.map Raw.swap) :=
  ⟨forkState, d2state, reach3_fork, reach3_d2,
   fun h => absurd ((h bab).mpr (.head _)) bab_notmem_fork,
   fun h => absurd ((h bab).mpr (.tail _ (.head _))) bab_notmem_fork⟩

end E213.Theory.Async
