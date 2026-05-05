import E213.Firmware.Raw
import E213.Hypervisor.Lens

/-!
# Lens.view is slash-arg-swap invariant — for *every* Lens

The companion theorem to Path.lean's pathLens witness.  Path.lean
proves that an asymmetric `combine` (e.g. `List.append`) is
permissible at the Lens-data level, but observes (in prose only,
lines 26-30) that "no Lens can recover a notional ordering."

This file states that observation as a *named theorem* with no
symmetry hypothesis: for **any** `L : Lens α`, even one whose
`L.combine` is genuinely non-commutative,

  L.view (Raw.slash x y h) = L.view (Raw.slash y x (Ne.symm h))

holds — because `Raw.slash` itself is the symmetric primitive
(`Raw.slash_comm`).  The asymmetry of `L.combine`, if any, never
manifests at the Raw level.

## Closing the asymmetric-framework gap to Initiality

`raw_initial` (`SemanticAtom.lean`) covers `HasDistinguishing`
instances, which require `combine_sym`.  Asymmetric frameworks
(directed graphs, causal sets, ordered structures with
fundamental directionality) do not satisfy `combine_sym` and
hence formally fall outside the universal-property statement.

`view_slash_swap` closes this gap structurally: the asymmetry
of any candidate framework α with non-commutative combine is
invisible to *every* Lens-view of Raw, because Raw.slash is
literally symmetric.  Therefore framework-fundamental asymmetry
cannot be Raw-recovered — it is necessarily a Lens-imposed
artifact (cmp-canonical ordering of `Tree`).  Initiality's
reach is thus complete: any framework whose distinguishability
claims do not require asymmetry factors through Raw, and any
framework whose distinguishability claims *do* require
asymmetry is asking for something Raw structurally does not
have.

## Strict ∅-axiom

The proof is `congrArg L.view Raw.slash_comm` — no axiom
introduced.  Verifies via `#print axioms`.
-/

namespace E213.Hypervisor.Lens.Morphism.SlashSwap

open E213.Firmware E213.Hypervisor

/-- **Slash arg-swap invariance of every Lens.view.**
    No commutativity hypothesis on `L.combine` — the invariance
    comes entirely from `Raw.slash_comm`. -/
theorem Lens.view_slash_swap {α : Type} (L : Lens α)
    (x y : Raw) (h : x ≠ y) :
    L.view (Raw.slash x y h)
      = L.view (Raw.slash y x (Ne.symm h)) :=
  congrArg L.view (Raw.slash_comm x y h)

/-- **Slash arg-swap is in every Lens-equivalence kernel.**
    The downstream-useful form: regardless of which Lens you pick,
    the kernel relation `L.equiv` always identifies
    `slash x y` with `slash y x`.  So any "Raw quotient" obtained
    by Lens-pulling identifies slash-arg-swap pairs *for free*. -/
theorem Lens.equiv_slash_swap {α : Type} (L : Lens α)
    (x y : Raw) (h : x ≠ y) :
    L.equiv (Raw.slash x y h) (Raw.slash y x (Ne.symm h)) :=
  Lens.view_slash_swap L x y h

end E213.Hypervisor.Lens.Morphism.SlashSwap
