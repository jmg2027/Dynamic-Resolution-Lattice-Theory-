import E213.Theory.Raw.Congruence
import E213.Lens.LensCore

/-!
# Lens.Congruence — bridge between `Eqv` (internal) and `Lens.equiv` (external)

Per `research-notes/2026-05-18_lens_emergence_path.md` §2.6.  Each
lens `L : Lens α` induces an *external* equivalence
`L.equiv x y := L.view x = L.view y`.  Each generator set
`gens : Raw → Raw → Prop` induces an *internal* equivalence
`Eqv gens x y` via the equivalence closure
(`Theory.Raw.Congruence`).

The two are connected as follows:

  - **Internal → External**: if every generator pair preserves
    `L.view`, then so does the whole `Eqv gens` closure.
  - **External → Internal**: choosing `gens := L.equiv` makes
    `Eqv L.equiv` trivially equal to `L.equiv` at the `gens`-step
    (and the closure adds nothing because `L.equiv` is already an
    equivalence).

This file proves the first direction (the non-trivial one) and
provides the second as a one-liner.  Together they realise §2.6's
"external α-value agreement ⟺ internal `Eqv` equivalence" claim
*relative to a fixed lens* `L`.

∅-axiom standard; no Mathlib / Classical / propext / Quot.sound /
omega.
-/

namespace E213.Lens

open E213.Theory

/-- If a lens's `view` is constant on every generator pair, it is
    constant on every `Eqv gens`-equivalent pair. -/
theorem view_eq_of_Eqv {α} {L : Lens α} {gens : Raw → Raw → Prop}
    (h_gens : ∀ {x y}, gens x y → L.view x = L.view y)
    {x y : Raw} (h : Eqv gens x y) : L.view x = L.view y :=
  Eqv.induction' (fun a b => L.view a = L.view b)
    (fun hgen => h_gens hgen)
    (fun _ => rfl)
    (fun ih => ih.symm)
    (fun ih₁ ih₂ => ih₁.trans ih₂) h

/-- Choosing the generator set to be `L.equiv` recovers `L.equiv`
    on the generator step: the equivalence closure of an
    equivalence relation contains the original at the `of` step. -/
theorem Eqv_of_view_eq {α} {L : Lens α} {x y : Raw}
    (h : L.view x = L.view y) :
    Eqv (fun a b => L.view a = L.view b) x y :=
  Eqv.of h

end E213.Lens
