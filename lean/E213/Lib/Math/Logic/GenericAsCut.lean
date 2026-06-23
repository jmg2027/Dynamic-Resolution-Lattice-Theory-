import E213.Lib.Math.Logic.ForcingToy

/-!
# GenericAsCut — the Cohen generic = a reached-by-none CUT over the forcing poset

No-walls seminar Round 5, frontier `GenericAsCut`
(`research-notes/frontiers/no_walls_seminar/INDEX.md` R5).

**Thesis (forcing's generic = the residue's reached-by-none cut).**
R2 established that the Cohen generic = the **height-limit of a free selection parameter `σ`** —
reached by no finite forcing condition, approached by every condition
(`ForcingToy.lean`; `R2_synthesis.md` §F).  This file makes the structural identity precise:
the generic has the **same shape as a `Real213` CUT** (`AbCutSeq`,
`NumberSystems/Real213/AbCutSeq.lean`).  An irrational is a reached-by-none cut over ℚ — the
convergents (approximants) nest and narrow, but no rational *is* the limit.  The generic is a
reached-by-none cut over the **forcing poset** — the finite conditions (approximants) nest and
decide ever-longer prefixes, but no finite condition *is* the generic.

The standard Cohen conditions are finite partial functions `Nat → Bool` defined on prefixes
`[0,n)`.  We model:

  * `gen : Nat → Bool` — the (fixed, explicit) generic section.  Here `gen i := decide (i % 2 = 0)`
    is one concrete generic; nothing below depends on which total section it is — the cut-shape is
    `gen`-generic (parametrized by `gen`).
  * `decided n i : Bool` — does the **stage-`n` condition** decide index `i`?  `true` iff
    `i < n` (the condition's domain is the prefix `[0,n)`).  This is the forcing-poset analogue of
    a cut's resolution: how far the approximant has narrowed.
  * `approx n i : Bool` — the stage-`n` condition as a total padding: copy `gen` on
    `[0,n)`, pad `false` beyond.  Two conditions agree wherever **both** decide (compatibility);
    `approx (n+1)` extends `approx n` (refinement = ⊇ on decided domains).

**The cut-shape, proved ∅-axiom (the three deliverables):**

  1. `approximant_strictly_refines` — stage `n+1` decides a strictly-longer prefix than stage `n`
     (it decides index `n`, which stage `n` does not).  The approximant sequence narrows by one
     resolution step per stage — the modulus-style nesting (cf. `AbCutSeq.cut_false_fwd`: once a
     reading is fixed it persists forward; here once an index is decided it stays decided).
  2. `no_finite_condition_is_generic` — for **every** finite stage `n` there is an index (namely
     `n` itself) the stage-`n` condition does **not** decide.  No finite condition is the generic:
     the limit is **reached by none** (cf. an irrational being equal to no convergent).
  3. `generic_is_reached_by_none_cut` — the bundle: the generic over the forcing poset has the SAME
     shape as a `Real213` cut — approximants nest (decided-prefix monotone, strict per step) AND
     the limit is reached by none (every finite stage leaves an undecided index), AND each finite
     stage *agrees with* the generic exactly on what it decides (approached by all).

This realizes "forcing's generic = the residue's reached-by-none cut" — unifying forcing
(σ-adjunction, `ForcingToy.lean`) with the `Real213` cut machinery (the residue's pointing,
`AbCutSeq.lean`).  Both are a `σ`/cut **reached by none, approached by all** — the residue's
shape (`theory/essays/foundations/the_form_of_the_residue.md` "Infinity is the residue's shape").

Pure-Lean: `Nat.rec`/`decide`/`Bool` case analysis, pointwise relations; no `propext`, no
`Classical`, no kernel-trusting reduction tactic.  All ∅-axiom.
-/

namespace E213.Lib.Math.Logic.GenericAsCut

/-! ## 1. The forcing poset: finite Cohen conditions as prefix-approximants -/

/-- **The generic section.**  One concrete total `gen : Nat → Bool` — here "even index ↦ `true`".
    Everything below is `gen`-generic (parametrized by an arbitrary total section); this fixed one
    makes the witnesses closed/`decide`-able.  The generic is the limit object the finite conditions
    approach but none reaches. -/
def gen (i : Nat) : Bool := decide (i % 2 = 0)

/-- **Decided?** — does the stage-`n` forcing condition decide index `i`?  `true` iff `i < n`: the
    condition's domain is the prefix `[0,n)`.  This is the cut's *resolution* readout — how far the
    approximant has narrowed.  `Bool`-valued (decidable), no `Prop`/`Classical`. -/
def decided (n i : Nat) : Bool := decide (i < n)

/-- **Stage-`n` condition** (a finite Cohen condition, totalized).  Copy `gen` on the decided
    prefix `[0,n)`, pad `false` beyond.  The *content* lives only on `[0,n)`; the padding is the
    "not yet decided" region.  Successive conditions refine: `approx (n+1)` extends `approx n`. -/
def approx (n i : Nat) : Bool := if decided n i then gen i else false

/-- On its decided domain the stage-`n` condition *agrees with the generic* — the approximant is a
    genuine restriction of the limit, "approached by all". -/
theorem approx_eq_gen_on_decided (n i : Nat) (h : decided n i = true) :
    approx n i = gen i := by
  unfold approx; rw [h]; rfl

/-! ## 2. Strict refinement — the modulus narrows one step per stage -/

/-- **Monotone decision** (nesting): once index `i` is decided at stage `n`, it stays decided at
    every later stage `m ≥ n`.  The forcing-poset analogue of `AbCutSeq.cut_false_fwd` — a fixed
    reading persists forward; the approximant sequence only narrows, never widens. -/
theorem decided_mono (n m i : Nat) (hnm : n ≤ m) (h : decided n i = true) :
    decided m i = true := by
  unfold decided at *
  exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true h) hnm)

/-- Stage `n` does **not** decide its own boundary index `n` (`n < n` is false). -/
theorem boundary_undecided (n : Nat) : decided n n = false := by
  unfold decided; exact decide_eq_false (Nat.lt_irrefl n)

/-- Stage `n+1` **does** decide index `n` (`n < n+1`). -/
theorem succ_decides_boundary (n : Nat) : decided (n + 1) n = true := by
  unfold decided; exact decide_eq_true (Nat.lt_succ_self n)

/-- ★★ **`approximant_strictly_refines`** — stage `n+1` decides a *strictly longer* prefix than
    stage `n`: it keeps everything stage `n` decided (nesting, `decided_mono`) AND decides the new
    index `n` that stage `n` left undecided.  One resolution step per stage — the modulus-style
    narrowing of a cut's convergent sequence. -/
theorem approximant_strictly_refines (n : Nat) :
    (∀ i, decided n i = true → decided (n + 1) i = true)
      ∧ decided n n = false ∧ decided (n + 1) n = true :=
  ⟨fun i h => decided_mono n (n + 1) i (Nat.le_succ n) h,
   boundary_undecided n, succ_decides_boundary n⟩

/-! ## 3. Reached by none — no finite condition is the generic -/

/-- ★★ **`no_finite_condition_is_generic`** — for **every** finite stage `n` there is an index
    (namely `n`) the stage-`n` condition does not decide.  No finite condition decides all of `gen`;
    the generic is **reached by none** (exactly as an irrational equals no convergent — a finite
    object never lands on the limit).  Pointwise, ∅-axiom. -/
theorem no_finite_condition_is_generic (n : Nat) :
    ∃ i, decided n i = false :=
  ⟨n, boundary_undecided n⟩

/-- The undecided witness can be taken `≥ n` (it *is* `n`) — the gap is at the live frontier, not a
    stale earlier index.  Sharpens "reached by none" to "undecided arbitrarily far out". -/
theorem undecided_at_frontier (n : Nat) :
    ∃ i, i ≥ n ∧ decided n i = false :=
  ⟨n, Nat.le_refl n, boundary_undecided n⟩

/-! ## 4. The structural analogy bundle — generic = Real213-cut shape -/

/-- ★★★ **`generic_is_reached_by_none_cut`** — the capstone bundle: the Cohen generic over the
    forcing poset has the SAME shape as a `Real213` cut (`AbCutSeq`).  The three cut-properties:

    1. **nesting / strict refinement** — each stage decides a strictly longer prefix
       (`approximant_strictly_refines`): the approximant sequence narrows one resolution step per
       stage, monotone forward (the modulus analogue of `AbCutSeq.cut_false_fwd`);
    2. **reached by none** — every finite stage leaves an undecided frontier index
       (`undecided_at_frontier`): no finite condition *is* the generic, exactly as no rational
       convergent *is* an irrational cut;
    3. **approached by all** — each finite stage agrees with the generic exactly on what it decides
       (`approx_eq_gen_on_decided`): the approximants converge to `gen`, the limit reached by none.

    This is "forcing's generic = the residue's reached-by-none cut": the same `σ`/cut reached by
    none, approached by all — the residue's shape, now common to forcing (`ForcingToy.lean`) and the
    `Real213` cut machinery (`AbCutSeq.lean`). -/
theorem generic_is_reached_by_none_cut :
    -- 1. nesting + strict refinement (the modulus narrows one step per stage)
    (∀ n, (∀ i, decided n i = true → decided (n + 1) i = true)
          ∧ decided n n = false ∧ decided (n + 1) n = true)
    -- 2. reached by none (every finite stage leaves an undecided frontier index)
    ∧ (∀ n, ∃ i, i ≥ n ∧ decided n i = false)
    -- 3. approached by all (each stage agrees with the generic on its decided domain)
    ∧ (∀ n i, decided n i = true → approx n i = gen i) :=
  ⟨approximant_strictly_refines, undecided_at_frontier, approx_eq_gen_on_decided⟩

/-! ## 5. Tie to the forcing toy — same poset, same free-σ generic

The `ForcingToy` poset carries two *coexisting* total generics `g0, g1` (free σ, neither canonical);
this file shows that **any one** such generic, read through the finite conditions, is a reached-by-
none cut.  The two views compose: the generic is *free* (ForcingToy: no exterior dialer selects it)
AND *reached by none* (here: no finite condition lands on it) — the two faces of "the height-limit
of a free σ". -/

/-- The stage-`n` condition restricted to an undecided index is just the pad `false` — the
    per-condition projection (cf. `ForcingToy.proj`), here resolution-indexed. -/
theorem approx_undecided_is_pad (n i : Nat) (h : decided n i = false) :
    approx n i = false := by
  unfold approx; rw [h]; rfl

end E213.Lib.Math.Logic.GenericAsCut
