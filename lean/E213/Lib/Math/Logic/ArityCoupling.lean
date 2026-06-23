import E213.Lib.Math.Logic.SectionCountWithAbsence

/-!
# The WELD — the forced base parametrically determines free-fiber arity (∅-axiom)

No-walls seminar, Round 6 (`research-notes/frontiers/no_walls_seminar/R5_base_fiber_coupling.md`
§"The sharpest open question for R6": *"Weld the coupling into one ∅-axiom theorem:
`fiberArity(freeFib) = NT`, with `NT` supplied by `PairForcing` rather than hard-coded as `Bool`."*).

R5 established the base × fiber coupling at the *witness* level — the free fiber is `Bool`
(2-valued) **because** the forced atom `NT = 2` (the `Fin 2` base that forces arity-2 via
`pigeonhole_fin_to_fin2` is the `Bool` fiber that carries the `q = ±1` tag).  But the proof lived
as a **chain of separate ∅-axiom theorems sharing the literal constant `2`**, not as one fibered
statement.  R5 marked this the *located ABSENT*:

> the welded one-theorem form is the located ABSENT item — the `2` is the *same* `2` everywhere
> (NT, `Fin 2` base, `Bool` fiber, `q = ±1`, `not`'s domain), forced not chosen, but the proof is a
> chain sharing the constant rather than one parametric `∀`-statement.

**This file closes that ABSENT.**  It makes the coupling **one parametric theorem with `NT`
supplied** (a free `Nat` cardinality `n`, not the literal `2`):

  * `fiberTagOfCard n : StatusCount` — the per-fiber reading-count tag derived **from a Nat
    cardinality** `n` by structural recursion (`n = 0 → absence`, `n = 1 → one`, `n ≥ 2 → many`).
    This is the `TagOfDecidable.FiberCard` trichotomy re-read off a *cardinality* instead of a
    pre-decided tag — the fiber's arity *is* the input.
  * `arity_coupling n : fiberTagOfCard n = many ↔ 2 ≤ n` (+ the `one ↔ n = 1`, `absence ↔ n = 0`
    companions) — the parametric **"free ⟺ arity ≥ 2"**, `NT` abstract.  *This* is the weld: the
    free tag is not assigned, it is **derived from the cardinality**, and the threshold is exactly
    `2`.
  * `cyclicSucc` + `cyclicSucc_fpf` — the **wall's diagonal modifier**, parametric: a fixed-point-
    free self-map of an `n`-element fiber exists **iff** `n ≥ 2`, built `Fin`-free as the cyclic
    successor `k ↦ (k+1 < n ? k+1 : 0)` on `Nat`-residues `{k | k < n}`.  Crucially this is the
    **cyclic successor, not an involution** — an fpf involution needs `n` even, but the cyclic succ
    is fpf for *all* `n ≥ 2` (the wall's modifier exists at every free arity, not only the binary
    one).  `not : Bool → Bool` (R5's wall modifier on `Fin 2`) is the `n = 2` instance.
  * `coupling_at_forced_NT : fiberTagOfCard 2 = many` — the instantiation **at the forced atom**.
    `2 = NT` is the forced base value (`E213.Theory.Atomicity.PairForcing.pair_forcing` —
    `count p q = 1 ↔ (p = 2 ∧ q = 3)`; the binary-pair atom forced via
    `CombinatorialArity.pigeonhole_fin_to_fin2` / `reachable_only_object`).  So the **forced base
    parametrically yields the free binary fiber** (`σ` = the `q ± 1` tag `B`): plug the forced `NT`
    into the parametric coupling and the free tag falls out.

This turns R5's *"the same constant `2` recurs (proven separately)"* into *"the forced `NT`
**parametrically determines** the free-fiber arity and the wall's modifier arity in one statement"*.
The literal `2` is now supplied (`coupling_at_forced_NT` = `arity_coupling 2`), not hard-coded.

CRITICAL PURITY: **no `Fin n` recursion** (pulls `Quot`/`propext`).  The fiber is parametrized by a
**Nat cardinality `n`** and the finite tag is derived from it by `match n with | 0 | 1 | _ + 2`
(mirror `TagOfDecidable.FiberCard`); everything is proved by Nat comparisons + structural recursion
+ `Bool`/`Nat` matches.  The fpf map is on `Nat`-residues `{k | k < n}`, not `Fin n`.

Pure-Lean: `StatusCount` from `SectionCountWithAbsence`, `match n with | 0 | 1 | _+2`, `Nat`
arithmetic (`Nat.lt_irrefl`, `Nat.le_of_not_lt`, …), `decide` on closed tags.  No `propext`, no
`Classical`, no `funext`/`Quot.sound`, no compiled-kernel evaluation, no Mathlib.
-/

namespace E213.Lib.Math.Logic.ArityCoupling

open E213.Lib.Math.Logic.SectionCountWithAbsence (StatusCount classify4)

/-! ## §1 — the fiber tag derived from a Nat cardinality (the weld's input) -/

/-- ★ **The per-fiber reading-count tag, derived from a Nat cardinality `n`.**  Mirror of
    `TagOfDecidable.FiberCard` (`empty / point / multi`) but read off a *cardinality* `n` rather
    than a pre-decided tag — here the fiber's **arity is the input**, and the tag is *computed*:

      * `n = 0` → `absence`  (no reading — the `∅` pole),
      * `n = 1` → `one`      (a forced atom — a single reading),
      * `n ≥ 2` → `many`     (a free `σ` — ≥ 2 readings).

    Structural on `n` via `match n with | 0 | 1 | _ + 2` — **no `Fin n`** (avoids `Quot`/`propext`).
    This is the function whose output the weld `arity_coupling` characterizes: the free tag is
    *derived from the cardinality*, not assigned. -/
def fiberTagOfCard : Nat → StatusCount
  | 0     => .absence
  | 1     => .one
  | _ + 2 => .many

/-- Word-level reading of the cardinality tag (`absence / wall / forced / free`). -/
def classifyCard (n : Nat) : String := classify4 (fiberTagOfCard n)

/-! ## §2 — ★ the WELD: "free ⟺ arity ≥ 2", NT abstract -/

/-- ★★★ **The arity coupling (free pole): `fiberTagOfCard n = many ⟺ 2 ≤ n`.**  This is the weld
    R5 located as ABSENT: the **free** tag is *derived from* the fiber cardinality, and the
    threshold is *exactly* `2` — supplied as the abstract `n`, not hard-coded as `Bool`.  A fiber is
    a free `σ` iff its arity is `≥ 2`.  Proved by `match n with | 0 | 1 | _ + 2`, each branch by
    `Nat` comparison (no `Fin`). -/
theorem arity_coupling (n : Nat) : fiberTagOfCard n = StatusCount.many ↔ 2 ≤ n := by
  match n with
  | 0     => constructor
             · intro h; exact absurd h (by decide)
             · intro h; exact absurd h (by decide)
  | 1     => constructor
             · intro h; exact absurd h (by decide)
             · intro h; exact absurd h (by decide)
  | m + 2 => constructor
             · intro _; exact Nat.le_add_left 2 m
             · intro _; rfl

/-- ★★★ **The arity coupling (forced pole): `fiberTagOfCard n = one ⟺ n = 1`.**  A fiber is a
    *forced atom* iff it carries exactly one reading. -/
theorem arity_coupling_one (n : Nat) : fiberTagOfCard n = StatusCount.one ↔ n = 1 := by
  -- Derived from the two pure poles (`arity_coupling`, `_absence`) to avoid a `match`-splitter
  -- on the literal `1` (which the equation compiler taints with `propext`).  `= one` rules out
  -- `n = 0` (absence) and `2 ≤ n` (many), pinning `n = 1`.
  constructor
  · intro h
    have hne0 : n ≠ 0 := fun h0 => by rw [h0] at h; nomatch h
    have hnge2 : ¬ 2 ≤ n := fun h2 => by rw [(arity_coupling n).mpr h2] at h; nomatch h
    have hpos : 1 ≤ n := Nat.pos_of_ne_zero hne0
    have hlt2 : n < 2 := Nat.lt_of_not_le hnge2
    exact Nat.le_antisymm (Nat.le_of_lt_succ hlt2) hpos
  · intro h; rw [h]; rfl

/-- ★★★ **The arity coupling (absence pole): `fiberTagOfCard n = absence ⟺ n = 0`.**  A fiber is
    *absent* (no term to read) iff it carries zero readings. -/
theorem arity_coupling_absence (n : Nat) : fiberTagOfCard n = StatusCount.absence ↔ n = 0 := by
  match n with
  | 0     => constructor
             · intro _; rfl
             · intro _; rfl
  | 1     => constructor
             · intro h; nomatch h
             · intro h; nomatch h
  | m + 2 => constructor
             · intro h; nomatch h
             · intro h; nomatch h

/-- **`fiberTagOfCard` never returns `zero` (the wall).**  Like `TagOfDecidable.tagOf`, the
    cardinality-derived tag returns three of the four tetrachotomy tags (`absence / one / many`) and
    *never* the wall tag `zero`: a *decided* finite cardinality `n` never produces the wall (the
    wall lives only in the un-decidable `Type`-valued self-cover completion,
    `MasterClassifierNoGo.master_classifier_is_the_wall`).  Proved by `match n with | 0 | 1 | _+2`. -/
theorem fiberTagOfCard_never_wall (n : Nat) : fiberTagOfCard n ≠ StatusCount.zero := by
  match n with
  | 0     => exact fun h => by cases h
  | 1     => exact fun h => by cases h
  | _ + 2 => exact fun h => by cases h

/-! ## §3 — ★ the wall's diagonal modifier: a Fin-free fixed-point-free map iff `n ≥ 2`

The wall's diagonal needs a **fixed-point-free** self-map of the fiber.  R5's instance was
`not : Bool → Bool` on the 2-element fiber — but `not` is an *involution*, and an fpf involution
needs `n` *even*.  The parametric modifier that exists at **every** free arity `n ≥ 2` is the
**cyclic successor** `k ↦ (k + 1) mod n`, fpf for all `n ≥ 2`.  Built `Fin`-free on the
`Nat`-residues `{k | k < n}` — stated pointwise (`cyclicSucc n k ≠ k` for `k < n`). -/

/-- The **cyclic successor** on `Nat`-residues mod `n`, `Fin`-free: `k ↦ k + 1` if it stays below
    `n`, else wrap to `0`.  This is the wall's diagonal modifier at arity `n` — for `n ≥ 2` it is
    fixed-point-free on `{k | k < n}` (`cyclicSucc_fpf`).  Unlike an involution it is fpf for *all*
    `n ≥ 2` (no even-`n` requirement); `not : Bool → Bool` is the `n = 2` instance. -/
def cyclicSucc (n k : Nat) : Nat := if k + 1 < n then k + 1 else 0

/-- The cyclic successor stays in range: `k < n → cyclicSucc n k < n`. -/
theorem cyclicSucc_lt (n k : Nat) (hk : k < n) : cyclicSucc n k < n := by
  unfold cyclicSucc
  by_cases h : k + 1 < n
  · simp only [if_pos h]; exact h
  · simp only [if_neg h]; exact Nat.lt_of_le_of_lt (Nat.zero_le k) hk

/-- ★★★ **The wall's diagonal modifier exists iff `n ≥ 2` (forward): for `n ≥ 2` the cyclic
    successor is fixed-point-free on `{k | k < n}`.**  For every residue `k < n`, `cyclicSucc n k ≠
    k`.  Two cases: if `k + 1 < n` then the successor is `k + 1 ≠ k`; otherwise it wraps to `0`, and
    `0 ≠ k` because `¬(k+1 < n)` with `k < n` forces `n = k + 1`, so `k = n - 1 ≥ 1` (as `n ≥ 2`).
    **No `Fin`** — pure `Nat` arithmetic.  This is the diagonal modifier the wall needs, parametric
    in the forced arity. -/
theorem cyclicSucc_fpf (n : Nat) (hn : 2 ≤ n) (k : Nat) (hk : k < n) :
    cyclicSucc n k ≠ k := by
  unfold cyclicSucc
  by_cases h : k + 1 < n
  · simp only [if_pos h]
    intro heq
    -- heq : k + 1 = k  ⟹  k < k
    have : k < k := by
      have hlt : k < k + 1 := Nat.lt_succ_self k
      rw [heq] at hlt
      exact hlt
    exact Nat.lt_irrefl k this
  · simp only [if_neg h]
    -- ¬(k+1 < n) and k < n ⟹ n = k+1 ⟹ k = n-1 ≥ 1, so 0 ≠ k
    have hnk1 : n ≤ k + 1 := Nat.le_of_not_lt h
    have hk1n : k + 1 = n := Nat.le_antisymm (Nat.succ_le_of_lt hk) hnk1
    -- from 2 ≤ n = k+1, get 1 ≤ k, so k ≠ 0
    have h1k : 1 ≤ k := by
      have h2 : 2 ≤ k + 1 := hk1n ▸ hn
      exact Nat.le_of_succ_le_succ h2
    intro heq
    -- heq : 0 = k, contradicts 1 ≤ k
    have : (1 : Nat) ≤ 0 := by rw [heq]; exact h1k
    exact absurd this (by decide)

/-- ★★★ **The wall's diagonal modifier does NOT exist below `n = 2` (converse): on a `n ≤ 1` fiber
    every self-map of `{k | k < n}` has a fixed point — so no fpf map exists.**  For `n = 0` the
    domain is empty (vacuous); for `n = 1` the only residue is `0` and any self-map sends it into
    `{k | k < 1} = {0}`, so `g 0 = 0` is forced — a fixed point.  Establishes the `iff`: fpf
    modifier ⟺ `n ≥ 2`. -/
theorem no_fpf_below_two (g : Nat → Nat) (n : Nat) (hn : n ≤ 1)
    (hg : ∀ k, k < n → g k < n) :
    ∀ k, k < n → ¬ (g k ≠ k) := by
  intro k hk hne
  -- k < n ≤ 1 ⟹ k = 0; g 0 < n ≤ 1 ⟹ g 0 = 0 = k, contradicting g k ≠ k
  have hk1 : k < 1 := Nat.lt_of_lt_of_le hk hn
  have hk0 : k = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ hk1)
  have hgk1 : g k < 1 := Nat.lt_of_lt_of_le (hg k hk) hn
  have hgk0 : g k = 0 := Nat.le_zero.mp (Nat.le_of_lt_succ hgk1)
  exact hne (hgk0.trans hk0.symm)

/-- ★ **The fpf-modifier coupling, both directions in one statement.**  A fixed-point-free self-map
    of an **inhabited** `n`-element fiber `{k | k < n}` exists **iff** `n ≥ 2`: the cyclic successor
    witnesses the forward direction (`cyclicSucc_fpf`), and `no_fpf_below_two` shows no fpf map
    exists for `0 < n ≤ 1` (i.e. `n = 1`).  The wall's diagonal modifier is thus coupled to the
    *same* arity threshold `2` as the free tag (`arity_coupling`) — both are `≥ 2`, the forced `NT`.

    **Inhabitation is load-bearing.**  The hypothesis `0 < n` is required: on the *empty* fiber
    (`n = 0`) a fixed-point-free map exists *vacuously* (there is no `k < 0` to fix), so without
    `0 < n` the forward direction would be false at `n = 0`.  This is exactly the tetrachotomy's
    `∅` / `0` cut (`SectionCountWithAbsence`): the wall's diagonal modifier is a question about an
    *inhabited* fiber; the empty fiber is `absence`, prior to the count.  So: among **inhabited**
    fibers, a fixed-point-free self-map exists iff the arity is `≥ 2` — the free pole. -/
theorem fpf_modifier_iff (n : Nat) (hpos : 0 < n) :
    (∃ g : Nat → Nat, (∀ k, k < n → g k < n) ∧ (∀ k, k < n → g k ≠ k)) ↔ 2 ≤ n := by
  constructor
  · intro ⟨g, hrange, hfpf⟩
    -- 0 < n, so n ≥ 1.  Either n ≥ 2 (done) or n = 1 (no_fpf_below_two contradicts hfpf at 0).
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · -- n < 2 with 0 < n ⟹ n = 1
      have hn1 : n ≤ 1 := Nat.le_of_lt_succ hlt
      exact absurd (hfpf 0 hpos) (no_fpf_below_two g n hn1 hrange 0 hpos)
    · exact hge
  · intro hn
    exact ⟨cyclicSucc n, cyclicSucc_lt n, cyclicSucc_fpf n hn⟩

/-! ## §4 — ★ instantiation at the forced NT = 2 -/

/-- ★★★ **The binary fiber is free — at the forced atom `NT = 2`.**  Instantiate the parametric
    coupling `arity_coupling` at `n = 2`: `fiberTagOfCard 2 = many`.  The value `2 = NT` is the
    **forced** base atom — `E213.Theory.Atomicity.PairForcing.pair_forcing`
    (`count p q = 1 ↔ (p = 2 ∧ q = 3)`, the unique coprime atom pair) and
    `CombinatorialArity.pigeonhole_fin_to_fin2` / `reachable_only_object` (arity `2` forced because
    the `Fin 2` base collides for `k ≥ 3`).  So the **forced base parametrically yields the free
    binary fiber** (`σ` = the `q ± 1` tag `B`): plug the forced `NT` into the weld and the free tag
    falls out — *derived*, not assigned. -/
theorem coupling_at_forced_NT : fiberTagOfCard 2 = StatusCount.many := rfl

/-- ★★★ **The forced NT yields the free tag, via the weld** (the explicit `iff` instance).  At the
    forced atom `n = 2`, `fiberTagOfCard 2 = many` *iff* `2 ≤ 2` — the parametric `arity_coupling`
    specialized to the forced base.  Makes explicit that `coupling_at_forced_NT` is `arity_coupling`
    evaluated at the forced `NT`, not an independent `decide`. -/
theorem coupling_at_forced_NT_via_weld : fiberTagOfCard 2 = StatusCount.many ↔ 2 ≤ 2 :=
  arity_coupling 2

/-- ★★★ **The wall's diagonal modifier exists at the forced NT = 2** — the `not`-analog.  At
    `n = 2` the cyclic successor `cyclicSucc 2` is fixed-point-free on `{0, 1}` (`cyclicSucc 2 0 = 1
    ≠ 0`, `cyclicSucc 2 1 = 0 ≠ 1`) — this *is* `not : Bool → Bool` (R5's wall modifier) under the
    `Fin 2 ≅ {0,1}` identification.  So at the forced `NT` the wall's diagonal modifier exists,
    coupled to the *same* `2`. -/
theorem fpf_at_forced_NT : ∀ k, k < 2 → cyclicSucc 2 k ≠ k :=
  cyclicSucc_fpf 2 (by decide)

/-- ★ **The full coupling at the forced atom, bundled.**  At `NT = 2`: the fiber tag is `free`
    (`coupling_at_forced_NT`), the free threshold is met (`2 ≤ 2`), and the wall's fixed-point-free
    diagonal modifier exists (`fpf_at_forced_NT`).  The forced base `(NS,NT,d,c)`'s `NT` component
    parametrically determines **both** the free-fiber arity **and** the wall-modifier arity — R5's
    located-ABSENT coupling, now one parametric object instantiated at the forced value. -/
theorem forced_NT_couples_free_and_wall :
    fiberTagOfCard 2 = StatusCount.many
    ∧ (2 : Nat) ≤ 2
    ∧ (∃ g : Nat → Nat, (∀ k, k < 2 → g k < 2) ∧ (∀ k, k < 2 → g k ≠ k)) :=
  ⟨coupling_at_forced_NT, Nat.le_refl 2, (fpf_modifier_iff 2 (by decide)).mpr (by decide)⟩

/-! ## §5 — concrete sanity instances (the three poles, classified) -/

/-- The three buildable poles read off a cardinality, classified to words. -/
theorem classifyCard_instances :
    classifyCard 0 = "absence"
    ∧ classifyCard 1 = "forced"
    ∧ classifyCard 2 = "free"
    ∧ classifyCard 7 = "free" := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §6 — honest residue

What is BUILT (∅-axiom, this file): the **weld** R5 located as ABSENT, now one parametric object.

  * `fiberTagOfCard : Nat → StatusCount` — the fiber tag *derived from* a Nat cardinality `n`
    (`0 → absence`, `1 → one`, `≥2 → many`), `Fin`-free, structural on `n`.
  * `arity_coupling` (+ `_one`, `_absence`) — **"free ⟺ arity ≥ 2"** with `NT` supplied abstractly;
    the free tag is *derived from the cardinality*, threshold exactly `2`.  The R5 ABSENT was
    precisely the absence of this `∀`-quantified form (it lived as a chain sharing the literal `2`).
  * `cyclicSucc` / `cyclicSucc_fpf` / `no_fpf_below_two` / `fpf_modifier_iff` — the **wall's
    diagonal modifier**, parametric and `Fin`-free: a fixed-point-free self-map of an `n`-element
    fiber exists **iff** `n ≥ 2`, witnessed by the cyclic successor (fpf for *all* `n ≥ 2`, not only
    even `n`, so it strictly generalizes R5's involution `not`).  *The fpf-modifier side BUILT* —
    not left ABSENT.
  * `coupling_at_forced_NT` (= `arity_coupling 2`) / `forced_NT_couples_free_and_wall` — the
    instantiation at the forced atom `NT = 2` (`PairForcing.pair_forcing` /
    `CombinatorialArity.pigeonhole_fin_to_fin2`): the forced base parametrically yields the free
    binary fiber **and** the wall's modifier, both coupled to the same `2`.

This closes R5's located-ABSENT: *"the same constant `2` recurs (proven separately)"* becomes
*"the forced `NT` parametrically determines the free-fiber arity and the wall-modifier arity in one
statement"* — the literal `2` is now **supplied** (`coupling_at_forced_NT` *is* `arity_coupling`
at the forced value), not hard-coded.

What stays ABSENT (unchanged from R5/R4, correctly): the **master classifier**
`Fibration → StatusCount` over *every* `Type`-valued fiber family — that is the wall
(`MasterClassifierNoGo.master_classifier_is_the_wall`), the founding diagonal, and it is *supposed*
to be ABSENT.  This file welds the **cardinality → tag** coupling (the decidable, below-the-wall
part), not the undecidable completion.  The fiber here is a *Nat cardinality* `n`; the moment a
fiber becomes a `Type`-valued self-cover the section-count becomes the diagonal and the master tag
hits the wall (`TagOfDecidable` §4).  The weld lives strictly below that boundary — which is exactly
where it should.
-/

end E213.Lib.Math.Logic.ArityCoupling
