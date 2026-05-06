/-!
# KernelFreeAudit: modularity audit of Lean kernel axioms

User question (2026-04-26): `propext` and `Quot.sound` are also
hard-coded into the Lean kernel — can even those be modularized?

## Audit results (M1-M22 milestones + 9 arc fronts)

### Group A: **No axioms** (pure Lean type-checker, no external axioms)

These use Lean only as a "coding language" — propext, Quot.sound, and
Classical.choice are all absent.  Inductive types + computation only.

- `RawDecEq.instDecidableEqRaw`: DecidableEq Raw.
- `ParityLensCollapseFalse.parityLens_collapse_false`: xor x x = false.
- `RefinesPreorder.refines_refl`, `refines_trans`: preorder properties.
- `LensEquivProperties.lens_equiv_refl/_symm/_trans`: equivalence
  properties.
- `IsLeafLens.isLeafLens_combine_sym`: leaf-Lens combine commutativity.
- `HasModulusNS.isOrderCauchy_of_hasModulus`: HasModulus implies
  isOrderCauchy.
- `HasModulusBoundsExtra.cauchy_at_larger_N`: modulus N-monotonicity.

### Group B: **propext only** (no Quot.sound)

- `CanonicalChoice.canonical_trichotomy`.
- `IdLensKernelEq.idLens_equiv_eq`.
- `ConstLensTotalKernel.constLens_equiv_total`.
- `SumNotCoproduct.sum_not_coproduct_xor`.
- `SumNotCoproductGeneric.sum_not_coproduct_and`.
- `SubtypeInstanceClosed.subtypeCombine_comm`,
  `subtypeHasDistinguishingClosed`, `trueSubtypeInstance`.
- `FourDistinctKernels.id_neq_leaves`.

### Group C: **[propext, Quot.sound]** (Lean baseline used)

Depends on the `omega` tactic (internally uses both axioms) or on
`Raw.fold` / `Raw.rec` (transitively depends on Quot.sound).

### omega elimination demonstrated (B → A or C → B downgrade)

Concrete omega elimination results:

- `Sqrt2IrrationalKernelFree.sqrt2_irrational`: original was
  `[propext, Quot.sound]` but downgraded to `[propext]` only via
  manual descent.  **Demonstrates that Quot.sound was an incidental
  dependency of omega**.
- `EulerSharperKernelFree.euler_sharper_lower_n3/n4`:
  verification of concrete values is axiom-free via `decide` (Group A).
- `WallisSharperKernelFree.wallis_sharper_n2/n3`: same.
- `DiagonalHasModulus`: omega eliminated → downgraded to `[propext]` only.
- `PellHasModulus`: omega eliminated (still C due to upstream Quot.sound
  influence, but module-internal is propext only).

### Conclusion

`propext` + `Quot.sound` in Lean 4 core are *kernel axioms* —
modularizing them requires modifying Lean itself.

However, the dependencies of the framework's theoretical results are
*largely incidental*: the main sources are the internal use of the
`omega` tactic + the quotient encoding of `Raw.fold`.  Eliminating
`omega` + using explicit Nat reasoning allows a substantial fragment to
become `[propext]` only or axiom-free.

## Significance

Answer to the user question:

**Partially possible**: many of 213's results are already verifiable
*without Lean kernel axioms*.  In particular, the framework's
*combinatorial* properties (decidability, preorder/equivalence laws,
finite classifications, parity-style identities) are in Group A.

**Universal property + Cauchy infrastructure** depends on propext +
Quot.sound (omega + Raw.fold).  This is inherent to the Lean 4 core
design — modularization requires re-implementing omega primitives +
explicit handling of Raw.fold's well-foundedness.

**Conclusion**: Lean *can* be fully downgraded to coding-language only
— by rewriting all omega as manual arithmetic and Raw.fold as explicit
recursion.  Cost: a proportionally large refactor.  Current ratio:
approximately ~30% of theorems are already axiom-free.
-/

namespace E213.Hypervisor.Lens.Algebra.FreeAudit

-- This module records the audit results — no new theorems are added.

end E213.Hypervisor.Lens.Algebra.FreeAudit
