import E213.Theory.Raw.Async
import E213.Theory.Raw.Rec

/-!
# Theory.Raw.Async: reachability, closure invariant, joinability

The conflict-free half of the asynchronous growth system
(`Theory/Raw/Async.lean`): reachable snapshots are subterm-closed
(`reach_closed`), any two reachable snapshots embed in a common
reachable snapshot (`reach_joinable` — events never disable each
other, so divergent observers are only incomparable, never in
conflict, and re-converge in finitely many steps with no fairness
assumption), and every Raw is reached by some run
(`every_raw_reached`, fairness-free existential) — indeed every
finite point-set jointly (`list_reached`).

Decidability of membership is hand-rolled (`memDec`): the core
list-`∈` instance routes through propext.
-/

namespace E213.Theory.Async

open E213.Theory

/-- Reachability from `init` (unindexed). -/
def Reach (s : State) : Prop := ∃ n, ReachN n s

theorem reach_init : Reach init := ⟨0, .zero⟩

/-- Hand-rolled decidable membership (propext-free). -/
def memDec (r : Raw) : (l : List Raw) → Decidable (r ∈ l)
  | [] => isFalse (fun h => nomatch h)
  | x :: l =>
    match decEq r x with
    | isTrue he => isTrue (by rw [he]; exact List.Mem.head l)
    | isFalse hne =>
      match memDec r l with
      | isTrue hm => isTrue (List.Mem.tail x hm)
      | isFalse hn => isFalse (fun h => match h with
          | .head _ => hne rfl
          | .tail _ h' => hn h')

private theorem mem_two' {r x y : Raw} : r ∈ [x, y] → r = x ∨ r = y
  | .head _ => Or.inl rfl
  | .tail _ (.head _) => Or.inr rfl
  | .tail _ (.tail _ h) => nomatch h

private theorem mem_cons {r x : Raw} {l : List Raw}
    (h : r ∈ x :: l) : r = x ∨ r ∈ l :=
  match h with
  | .head _ => Or.inl rfl
  | .tail _ h' => Or.inr h'

-- ═══ invariants ═══

theorem step_mono {s t : State} (hst : Step s t) :
    ∀ r, r ∈ s → r ∈ t := by
  cases hst with
  | fire x y hxy hx hy hnew => exact fun r hr => List.Mem.tail _ hr

theorem reachN_atoms {n : Nat} {s : State} (h : ReachN n s) :
    Raw.a ∈ s ∧ Raw.b ∈ s := by
  induction h with
  | zero => exact ⟨List.Mem.head _, List.Mem.tail _ (List.Mem.head _)⟩
  | succ _ hstep ih =>
    exact ⟨step_mono hstep _ ih.1, step_mono hstep _ ih.2⟩

/-- Subterm-closedness of a snapshot: every present pair's parts
    are present. -/
def ClosedIn (s : State) : Prop :=
  ∀ (x y : Raw) (h : x ≠ y), Raw.slash x y h ∈ s → x ∈ s ∧ y ∈ s

/-- ★ **Closure invariant**: every reachable snapshot is
    subterm-closed (each point's causal past is present). -/
theorem reachN_closed {n : Nat} {s : State} (h : ReachN n s) :
    ClosedIn s := by
  induction h with
  | zero =>
    intro x y hxy hm
    cases mem_two' hm with
    | inl he => exact absurd he (Raw.slash_ne_a x y hxy)
    | inr he => exact absurd he (Raw.slash_ne_b x y hxy)
  | succ _ hstep ih =>
    cases hstep with
    | fire u v huv hu hv hnew =>
      intro x y hxy hm
      cases mem_cons hm with
      | inl he =>
        cases Raw.slash_inj he with
        | inl hp =>
          exact ⟨by rw [hp.1]; exact List.Mem.tail _ hu,
                 by rw [hp.2]; exact List.Mem.tail _ hv⟩
        | inr hp =>
          exact ⟨by rw [hp.1]; exact List.Mem.tail _ hv,
                 by rw [hp.2]; exact List.Mem.tail _ hu⟩
      | inr hm' =>
        have hxy' := ih x y hxy hm'
        exact ⟨List.Mem.tail _ hxy'.1, List.Mem.tail _ hxy'.2⟩

theorem reach_closed {s : State} (h : Reach s) : ClosedIn s :=
  have ⟨_, hn⟩ := h
  reachN_closed hn

-- ═══ joinability (conflict-freeness) ═══

/-- Replay a run on top of any reachable snapshot: the target's
    points all embed into a common reachable extension. -/
theorem reach_extend {n : Nat} {t : State} (ht : ReachN n t) :
    ∀ {s : State}, Reach s →
      ∃ u, Reach u ∧ (∀ r, r ∈ s → r ∈ u) ∧ (∀ r, r ∈ t → r ∈ u) := by
  induction ht with
  | zero =>
    intro s hs
    refine ⟨s, hs, fun _ hr => hr, fun r hr => ?_⟩
    have ⟨m, hm⟩ := hs
    have hab := reachN_atoms hm
    cases mem_two' hr with
    | inl he => exact by rw [he]; exact hab.1
    | inr he => exact by rw [he]; exact hab.2
  | succ _ hstep ih =>
    intro s hs
    have ⟨u, hu, hsu, htu⟩ := ih hs
    cases hstep with
    | fire x y hxy hx hy hnew =>
      match memDec (Raw.slash x y hxy) u with
      | isTrue hmem =>
        refine ⟨u, hu, hsu, fun r hr => ?_⟩
        cases mem_cons hr with
        | inl he => exact by rw [he]; exact hmem
        | inr h' => exact htu r h'
      | isFalse hn =>
        have ⟨m, hm⟩ := hu
        refine ⟨Raw.slash x y hxy :: u,
          ⟨m + 1, .succ hm
            (Step.fire u x y hxy (htu x hx) (htu y hy) hn)⟩,
          fun r hr => List.Mem.tail _ (hsu r hr),
          fun r hr => ?_⟩
        cases mem_cons hr with
        | inl he => exact by rw [he]; exact List.Mem.head _
        | inr h' => exact List.Mem.tail _ (htu r h')

/-- ★★ **Joinability**: any two reachable snapshots embed in a
    common reachable snapshot.  Conflict-freeness in finite form —
    no fairness, no limit object. -/
theorem reach_joinable {s t : State} (hs : Reach s) (ht : Reach t) :
    ∃ u, Reach u ∧ (∀ r, r ∈ s → r ∈ u) ∧ (∀ r, r ∈ t → r ∈ u) :=
  have ⟨_, htn⟩ := ht
  reach_extend htn hs

-- ═══ totality ═══

/-- ★★★ **Every Raw is reached**: for each term some run constructs
    it (fairness-free existential — the asynchronous system's limit
    is all of Raw, stated finitely). -/
theorem every_raw_reached (r : Raw) : ∃ s, Reach s ∧ r ∈ s := by
  induction r using Raw.rec with
  | a => exact ⟨init, reach_init, List.Mem.head _⟩
  | b => exact ⟨init, reach_init, List.Mem.tail _ (List.Mem.head _)⟩
  | slash x y h ihx ihy =>
    have ⟨s, hs, hxs⟩ := ihx
    have ⟨t, ht, hyt⟩ := ihy
    have ⟨u, hu, hsu, htu⟩ := reach_joinable hs ht
    match memDec (Raw.slash x y h) u with
    | isTrue hmem => exact ⟨u, hu, hmem⟩
    | isFalse hn =>
      have ⟨m, hm⟩ := hu
      exact ⟨Raw.slash x y h :: u,
        ⟨m + 1, .succ hm
          (Step.fire u x y h (hsu x hxs) (htu y hyt) hn)⟩,
        List.Mem.head _⟩

/-- Every finite point-set is *jointly* reached: the finite-downset
    form of "the limit is all of Raw". -/
theorem list_reached (P : List Raw) :
    ∃ u, Reach u ∧ ∀ r, r ∈ P → r ∈ u := by
  induction P with
  | nil => exact ⟨init, reach_init, fun _ hr => nomatch hr⟩
  | cons x P ih =>
    have ⟨s, hs, hxs⟩ := every_raw_reached x
    have ⟨t, ht, htP⟩ := ih
    have ⟨u, hu, hsu, htu⟩ := reach_joinable hs ht
    refine ⟨u, hu, fun r hr => ?_⟩
    cases mem_cons hr with
    | inl he => exact by rw [he]; exact hsu x hxs
    | inr h' => exact htu r (htP r h')

end E213.Theory.Async
