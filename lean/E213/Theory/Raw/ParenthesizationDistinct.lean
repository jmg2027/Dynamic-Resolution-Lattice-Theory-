import E213.Theory.Raw.Slash
import E213.Theory.Raw.Levels
import E213.Theory.Raw.Congruence

/-!
# Theory.Raw.ParenthesizationDistinct — different parenthesisations are different Raws

In a Raw expression like `slash (slash x y) z` versus
`slash x (slash y z)`, the *parenthesisation* (i.e. the binary
tree shape) is **part of the Raw**, not a meta-notational artifact.
Same multiset of leaves, different Raws.

This file makes that distinction concrete with a kernel-evaluated
counter-example.

## Why this is *positive*, not a defect

`Raw.slash` is the free commutative magma operation.  Canonical-form
symmetry (`Raw.slash_comm`) is built in; *associativity is
deliberately absent*.  The 213 axiom set commits to no equational
law beyond what's intrinsic to the canonical-form quotient.

If we wanted "(x/y)/z = x/(y/z)" as a Raw-level identity, we would
be **adding** an axiom — discarding structural information about how
the Raw tree was built.  That contradicts the minimum-commitment
discipline (`seed/AXIOM/04_falsifiability.md` §5.2.1: axiom-addition
is falsification, not strengthening).

The two trees with leaves `{x, y, z}`:

```
  (x/y)/z              x/(y/z)
   slash                slash
   /   \                /   \
 slash   z             x   slash
 /   \                     /   \
 x     y                   y     z
```

are **legitimately distinct** Raws.  The parenthesisation = tree
shape = a structural feature of the Raw, not a chart artifact.

(Note: even the *source-text parens* `(`, `)` are themselves
Raw-encodable per §2.7 syntactic internalisation.  At the deepest
reading, the meta-language symbols and the Raw structure are one.)

## Implication for ℕ₊

The research note's §2.6 candidate
"ℕ₊ = Raw / (a ≡ b ∧ slash_assoc)" — quotienting Raw by atomic
identification plus associativity — was treating two different
projects as the same thing.  The correct realisation is:

  - ℕ₊ is the **image** of `Lens.leaves.view : Raw → Nat`.
  - The lens projection is **many-to-one** — different Raws map to
    the same Nat.  *That is the structure of leaves count.*
  - No quotient on Raw is needed; the Nat-side carries the abstract
    number, the Raw-side carries the chart representative.

This is exactly what the Option C refactor realised (commit
`9efd8263`).  The "slash_assoc as generator" idea from §2.6 should
be abandoned — not because it's hard to prove, but because it asks
the wrong question.  ℕ₊ is a *projection*, not a *quotient*.

∅-axiom standard; `decide`-based.
-/

namespace E213.Theory.Raw.ParenthesizationDistinct

open E213.Theory

/-! ### Three pairwise-distinct Raws -/

private def x : Raw := Raw.a
private def y : Raw := Raw.b
/-- `z := slash b (slash a b)` — two-level slash, distinct from
    every one-level form involving `a` and `b`. -/
private def z : Raw :=
  Raw.slash Raw.b (Raw.slash Raw.a Raw.b (by decide)) (by decide)

/-! ### The four `≠` preconditions -/

private theorem xy_ne : x ≠ y := by decide
private theorem yz_ne : y ≠ z := by decide
private theorem xyz_ne : Raw.slash x y xy_ne ≠ z := by decide
private theorem x_yz_ne : x ≠ Raw.slash y z yz_ne := by decide

/-! ### The two associated forms -/

/-- Left-associated `(x/y)/z`. -/
private def lhs : Raw := Raw.slash (Raw.slash x y xy_ne) z xyz_ne
/-- Right-associated `x/(y/z)`. -/
private def rhs : Raw := Raw.slash x (Raw.slash y z yz_ne) x_yz_ne

/-- **Structural distinction**: the two parenthesisations produce
    distinct Raws.  Same leaves multiset, different tree shape.
    Verified by kernel evaluation. -/
theorem parenthesisation_distinct : lhs ≠ rhs := by decide

/-! ### Public-facing conclusion -/

/-- **No universal `slash_assoc`** can hold over `Raw` — the
    structural distinction above contradicts the universal claim.
    This is **as it should be**: associativity would erase
    parenthesisation structure that is genuinely Raw-internal. -/
theorem no_universal_slash_assoc :
    ¬ ∀ (x y z : Raw) (h₁ : x ≠ y) (h₂ : Raw.slash x y h₁ ≠ z)
        (h₃ : y ≠ z) (h₄ : x ≠ Raw.slash y z h₃),
      Raw.slash (Raw.slash x y h₁) z h₂
        = Raw.slash x (Raw.slash y z h₃) h₄ := by
  intro h
  exact parenthesisation_distinct
    (h x y z xy_ne xyz_ne yz_ne x_yz_ne)

/-! ### Same leaves count, different Raws (added 2026-05-18)

The two parenthesisations have IDENTICAL leaves multisets — same
atoms, same total count — yet are distinct Raws.  This is the
"projection, not quotient" thesis (`seed/AXIOM/09 §9.1` companion):
the Raw side carries strictly more information than its leaves
projection. -/

/-- **Same leaves, distinct Raws**: `lhs` and `rhs` have identical
    leaves counts (both = 5: one a, one b, plus the 3 atoms of z)
    yet are distinct Raws.  The leaves Lens is many-to-one. -/
theorem same_leaves_distinct_parenthesisation :
    Raw.leaves lhs = Raw.leaves rhs ∧ lhs ≠ rhs := by
  refine ⟨?_, parenthesisation_distinct⟩
  decide

/-- **Concrete witness of leaves-projection many-to-oneness**:
    the leaves projection collapses two structurally distinct
    Raws to the same Nat (= 5). -/
theorem leaves_view_collapses : Raw.leaves lhs = 5 ∧ Raw.leaves rhs = 5 := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ### Internal-Eqv view of the collapse (added 2026-05-18)

`lhs` and `rhs` are concretely `Eqv`-equivalent under the leaves-
induced generator: the generator pair `Raw.leaves lhs = Raw.leaves rhs`
sits in the closure by `Eqv.of`.  Combined with `lhs ≠ rhs`, this is
a concrete non-trivial witness that `Eqv (Raw.leaves ·= Raw.leaves ·)`
is strictly coarser than structural equality on `Raw`. -/

/-- **`lhs` and `rhs` are leaves-Eqv equivalent**: the equivalence
    closure of "same Raw.leaves count" relates the two
    parenthesisations.  Direct consequence of
    `same_leaves_distinct_parenthesisation` via `Eqv.of`. -/
theorem lhs_rhs_leaves_eqv :
    E213.Theory.Eqv
      (fun a b => Raw.leaves a = Raw.leaves b) lhs rhs := by
  apply E213.Theory.Eqv.of
  exact same_leaves_distinct_parenthesisation.1

/-- **Strict-coarsening witness**: there exist two distinct Raws
    related by `Eqv` under the leaves-induced generator.  This is a
    concrete proof that `Eqv (Raw.leaves ·= Raw.leaves ·)` is
    *strictly coarser* than `=` on `Raw`. -/
theorem exists_distinct_leaves_eqv :
    ∃ x y : Raw, x ≠ y ∧
      E213.Theory.Eqv (fun a b => Raw.leaves a = Raw.leaves b) x y :=
  ⟨lhs, rhs, parenthesisation_distinct, lhs_rhs_leaves_eqv⟩

end E213.Theory.Raw.ParenthesizationDistinct
