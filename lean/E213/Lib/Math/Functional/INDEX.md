# Functional Analysis 213 — Module Index

Blueprint: `blueprints/math/08_functional_213.md` (retired).

## Modules

| File | Topic | Status |
|---|---|---|
| `Norm.lean` | `lInfNorm`, `l1Norm` over finite grid; constant-fn closed forms | ∅-axiom |
| `InnerProduct.lean` | `innerNum n f g`; symmetry + left bilinearity | ∅-axiom |
| `LinearOperator.lean` | `LinOp := (Nat → Nat) → (Nat → Nat)`; id/zero/scale/compose | ∅-axiom |
| `Spectrum.lean` | `IsEigenpair`; id-eig-1, scale-eig-c, zero-eig-0, compose-scale | ∅-axiom |
| `Capstone.lean` | 5 cluster witnesses + `total_witness` | ∅-axiom |
| `Functional.lean` | umbrella | — |

## 213-native paradigm

  * **Banach completion bypassed**: at the finite-grid resolution
    every `Nat → Nat` is "complete" — there is no Cauchy chase
    because the iterate is exact.
  * **Hahn-Banach / open-mapping rejected**: both depend on
    Choice; 213 admits only directly-constructible extensions.
    This is a *feature*, not a restriction (matches the
    Measure 213 σ-algebra rejection).
  * **Spectrum = pointwise eigenvalue identity**: no
    Banach-algebra completion required.
  * **Inner product = Σ pointwise product over finite grid**.
    L²-norm-squared is `innerNum n f f`; no measure-completion
    chase.

## Honest scope

  * Cauchy-Schwarz `⟨f,g⟩² ≤ ⟨f,f⟩·⟨g,g⟩` deferred — same
    `(a-b)²` Nat-arithmetic issue as in Measure 213's Hölder.
  * `‖·‖_p` for general `p` not built; `lInf` and `l1` are the
    atomic anchors; `p=2` enters via the inner product.
