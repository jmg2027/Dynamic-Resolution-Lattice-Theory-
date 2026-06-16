# Order theory: Galois connections, Boolean algebra, fixed points (∅-axiom)

Mirror of `lean/E213/Lib/Math/Order/`. Every theorem named here is PURE
(`#print axioms → "does not depend on any axioms"`); the Lean files are the
source of truth.

The cluster is **parametrized order theory** done without typeclasses or any
Mathlib: an order is a relation `le : α → α → Prop` with `refl`/`trans`/
`antisymm` supplied as explicit hypotheses, and each structure (adjunction,
Boolean algebra, complete lattice) is a bundle of such hypotheses passed
per-theorem. The proofs are pure order-chases and equational rewriting; no
`funext` is used anywhere (function-level facts are stated pointwise), keeping
the cluster `Quot.sound`-free.

## 1. Galois connections

`GaloisConnection`: a pair `f : α → β`, `g : β → α` with the adjunction
`gc : ∀ a b, leB (f a) b ↔ leA a (g b)` (used only via `.mp`/`.mpr`, never
`rw`).

- `gc_unit`/`gc_counit`: `a ≤ g(f a)`, `f(g b) ≤ b`.
- `gc_monotone_f`/`gc_monotone_g`: both adjoints are monotone.
- `gc_fgf`/`gc_gfg`: the triangle identities `f∘g∘f = f`, `g∘f∘g = g`
  (pointwise, via antisymmetry).
- The induced **closure operator** `clo a = g (f a)`: `clo_extensive`,
  `clo_monotone`, `clo_idempotent`.
- `gc_unique_right`: a right adjoint is determined by its left adjoint.

Concrete witness: the multiply/divide adjunction `(·*p) ⊣ (·/p)` on `Nat`
(`mulDiv_gc = AddMod213.le_div_iff_mul_le`).

`GaloisConnectionComposition` caps it:

- `gc_comp`: Galois connections **compose** — `(f'∘f, g∘g')` is a connection
  `A ⊣ C` (pure adjunction transitivity, `Iff.trans`).
- `closed_iff_image`: the closure's fixed points are exactly the image of the
  right adjoint, `clo a = a ↔ ∃ b, a = g b`.
- `gc_le_closed`: the universal property `a ≤ g b ↔ clo a ≤ g b`.

## 2. Boolean algebra

`BooleanAlgebra`: the Huntington/lattice axioms (`inf`, `sup`, `cmpl`, `bot`,
`top` with comm/assoc/absorption/distributivity/identity/complement) supplied
as hypotheses.

- `idem_inf`/`idem_sup`, `inf_bot`/`sup_top`: idempotence and boundedness,
  derived from absorption + identities.
- `cmpl_unique`: the complement is unique (`sup a b = top → inf a b = bot →
  b = cmpl a`) — the key lemma, both candidates shown equal to `inf (cmpl a) b`.
- `cmpl_cmpl`: double complement `cmpl (cmpl a) = a`.
- `de_morgan_inf`/`de_morgan_sup`: both **De Morgan laws**, via `cmpl_unique`.
- `cmpl_bot`/`cmpl_top`.

Concrete witness: `Bool` (`and`/`or`/`not`/`false`/`true`), all twelve axioms
discharged by `decide`; the abstract laws specialize to `bool_de_morgan_*` and
`bool_cmpl_cmpl`.

## 3. The fixed-point theorem (Knaster–Tarski)

`KnasterTarski`: a complete lattice as `le` + a set-indexed infimum
`glb : (α → Prop) → α` with `glb_lb` (lower bound) and `glb_glb` (greatest),
and a monotone `f`. The least fixed point is the glb of the pre-fixed points:

- `lfp = glb (fun x => le (f x) x)`.
- `lfp_fixed`: `f lfp = lfp` — `lfp` is a fixed point.
- `lfp_least`: `f a = a → le lfp a` — `lfp` is the **least** fixed point.
- `lfp_least_prefixed`: `le (f a) a → le lfp a`.
- Dually, via a `lub` parameter, the greatest fixed point `gfp` (`gfp_fixed`,
  `gfp_greatest`).

The proof is the standard two-step order-chase: `f lfp` is a lower bound of the
pre-fixed points (so `f lfp ≤ lfp`), hence itself pre-fixed (so `lfp ≤ f lfp`);
antisymmetry closes it. This is the foundation of domain theory / denotational
semantics, here with the cardinal/typeclass packaging stripped to the bare
order hypotheses.

## Methodology

The whole cluster reads one way: a structure is its axioms-as-hypotheses, an
"abstract theorem" is a derivation that uses only those hypotheses, and a
"model" (Nat division, Bool, Unit) discharges the hypotheses to inhabit it.
The `Iff` in an adjunction is eliminated, never rewritten (rewriting `Iff`
imports `propext`); function-level equalities are kept pointwise (rewriting
functions imports `Quot.sound`). What remains is the order content itself,
∅-axiom.
