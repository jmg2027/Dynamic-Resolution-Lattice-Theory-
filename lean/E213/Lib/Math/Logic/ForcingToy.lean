import E213.Lib.Math.Logic.ChoiceLens

/-!
# ForcingToy — the minimal ∅-axiom independence toy: σ free ⟹ two distinct models

No-walls seminar Round 2, agenda item 1 (the `R1_synthesis` frontier
§"What Round 2 builds", spec in `B_forcing_as_adjunction.md` §3).

**Thesis (the toy of Cohen independence as a Lens-parameter adjunction).**
Cohen forcing builds two models of ZF disagreeing on AC/CH by adjoining a *generic* selection σ
that the construction does not fix; independence is the statement that **σ is free** — no exterior
dialer (`seed/AXIOM/05_no_exterior.md` §5.1) selects it, so distinct generics coexist and the
global readout disagrees between them, **with neither canonical**.

This file is the minimal ∅-axiom witness of *that* shape:

  * a **2-point forcing poset** `P := Fin 2` — the index of available σ-values (one bit "decided"),
    the smallest non-degenerate forcing poset;
  * two **generics** `g0 g1 : ∀ i:Nat, Bool` — mirroring `ChoiceLens.sigmaL := fun _ => false`,
    `ChoiceLens.sigmaR := fun _ => true`: two explicit, total, computable sections of the inhabited
    family `i ↦ Bool`, each ∅-axiom (no choice axiom);
  * a **global section / readout** `glob : (∀ i, Bool) → Nat` — the prefix-count over the first three
    indices (mirroring `ChoiceLens.readOp`), the "value of the chosen bit, read globally";
  * the **independence-toy theorem** `forcing_toy_independence : glob g0 ≠ glob g1` — the *same*
    construction `glob` yields DIFFERENT global sections under the two generics, with **neither
    canonical**: the toy model of "AC/CH independent = σ free, both adjunctions give distinct models".

The bundling leg (`carryBoth`/`proj`) carries **both** generics at once as ONE name over `P` and
recovers each by the per-condition projection — the funext-free, ∅-axiom counterpart of
"name = `P`-indexed family, glued; restrict to a stage to read it" (sheaf-over-poset semantics).
We use a direct `P → (∀ i, Bool)` bundle rather than the `iProdLens` Σ-type engine; see the note at
`carryBoth` for why the `iProdLens` route is the wrong layer for this toy.

Pure-Lean: `decide` on closed Bool/Nat goals, `rfl` on the 2-point projection; no `propext`, no
`Classical`, no kernel-trusting reduction tactic.
-/

namespace E213.Lib.Math.Logic.ForcingToy

open E213.Lib.Math.Logic.ChoiceLens (sigmaL sigmaR)

/-- **The 2-point forcing poset.**  `P` indexes the available σ-values: two conditions
    `false`, `true`, each "deciding" one bit.  The smallest non-degenerate forcing poset.  We use
    `Bool` rather than `Fin 2` so the per-condition match stays ∅-axiom: matching on `Fin 2` routes
    through `Nat.rec`/`Fin`'s `Quot`-backed recursor and pulls `propext, Quot.sound`, whereas `Bool`
    matches by its primitive recursor with no axioms. -/
abbrev P : Type := Bool

/-- **Generic `g0`** — the section picking `false` everywhere (reusing `ChoiceLens.sigmaL`).  One of
    the two coexisting generics; total, explicit, no choice axiom. -/
def g0 : ∀ _ : Nat, Bool := sigmaL

/-- **Generic `g1`** — the section picking `true` everywhere (reusing `ChoiceLens.sigmaR`).  The
    other coexisting generic; total, explicit, no choice axiom. -/
def g1 : ∀ _ : Nat, Bool := sigmaR

/-- **Global section / readout.**  Number of indices `i < n` with `g i = true`, read at the fixed
    horizon `n = 3` — the construction's single "global element", mirroring `ChoiceLens.readOp`.  A
    finite fold over the generic: the value the *whole* model assigns to "the chosen bit". -/
def glob (g : ∀ _ : Nat, Bool) : Nat :=
  (if g 0 = true then 1 else 0)
    + (if g 1 = true then 1 else 0)
    + (if g 2 = true then 1 else 0)

/-- Under generic `g0` the global readout is `0`. -/
theorem glob_g0 : glob g0 = 0 := by decide

/-- Under generic `g1` the global readout is `3`. -/
theorem glob_g1 : glob g1 = 3 := by decide

/-- The two generics are distinct (pointwise at `0`). -/
theorem g0_ne_g1_at_0 : g0 0 ≠ g1 0 := by decide

/-- ★★ **The independence toy: σ free ⟹ two distinct models.**  The *same* global construction
    `glob` produces DIFFERENT global sections under the two generics `g0`, `g1`, with **neither
    canonical** (no exterior dialer fixes σ, §5.1).  This is the minimal ∅-axiom model of Cohen
    independence read as a Lens-parameter adjunction: the value of "the chosen bit" is not fixed by
    the construction, so both σ=0 and σ=1 extensions exist and disagree. -/
theorem forcing_toy_independence : glob g0 ≠ glob g1 := by decide

/-! ## Bundling: carry both generics at once over `P`, project per condition

"Carry all σ at once, glue; restrict to a stage to read" — the sheaf-over-poset move.  We bundle the
two generics into ONE name `carryBoth : P → (∀ i, Bool)` and recover each by the per-condition
projection.  This is the direct, funext-free realization of the bundling the seminar agenda calls
for.

**Why not `iProdLens`?**  `IndexedJoin.iProdLens {ι} (F : ι → Σα, Lens α) : Lens ((i:ι)→(F i).1)`
lives at the *Lens-over-`Raw`* layer: its fibers are `Lens` structures whose `view`s fold `Raw`
trees, and its per-σ projection `iProdLens_view` reads a `Raw` argument, not a `Nat`-indexed
`Bool`-section.  Bundling the *generics* `g0 g1 : ∀ i:Nat, Bool` is one layer below that — the
generics are sections of the inhabited fiber `Bool`, not Lenses on `Raw`.  Routing them through the
Σ-type `iProdLens` would force an artificial `Raw`-encoding of each `Bool`-section and pull `funext`
on the dependent function space (exactly what `iProdLens_view`/`iProdLens_is_greatest_pw` are
*stated pointwise to avoid*).  The direct `P`-indexed bundle below carries the same "name = family
over the poset, project per condition" content at the correct layer, ∅-axiom and funext-free. -/

/-- **The bundled name.**  Carry both generics at once as ONE family over the poset `P`:
    condition `false ↦ g0`, condition `true ↦ g1`.  The 213-native "name = `P`-indexed family". -/
def carryBoth : P → (∀ _ : Nat, Bool)
  | false => g0
  | true  => g1

/-- **Per-condition projection.**  Restrict the bundled name to condition `p` — the sheaf
    restriction `F(X) → F(p)`.  Definitionally just `carryBoth p`. -/
def proj (p : P) : ∀ _ : Nat, Bool := carryBoth p

/-- Projecting the bundle at condition `false` recovers generic `g0`. -/
theorem proj_false : proj false = g0 := rfl

/-- Projecting the bundle at condition `true` recovers generic `g1`. -/
theorem proj_true : proj true = g1 := rfl

/-- ★ **Bundling recovers each generic, and the per-condition global readouts disagree.**
    Carrying both σ at once over `P` and projecting per condition recovers `g0` at `false` and `g1`
    at `true`; reading the global section through each projection reproduces the independence toy
    (`glob (proj false) = 0 ≠ 3 = glob (proj true)`).  "Carry both σ, project per σ" =
    sheaf-over-poset semantics, with the σ-dependence surviving the bundle. -/
theorem bundle_recovers_independence :
    proj false = g0 ∧ proj true = g1 ∧ glob (proj false) ≠ glob (proj true) :=
  ⟨proj_false, proj_true, by decide⟩

end E213.Lib.Math.Logic.ForcingToy
