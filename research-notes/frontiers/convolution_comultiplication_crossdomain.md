# Cross-domain: ℕ's two comultiplications — the structural home of "+ and × are two faces of one count"

**Status: a cross-relation between this branch's convolution clusters and main's
count-Lens essays. The fusion observation is recorded; one genuinely-open frontier
(the bialgebra/distributivity compatibility) is flagged.**

## The two arcs that meet

- **This branch** built two convolutions on ℕ-indexed sequences, each computed by an
  *explicit comultiplication* (a co-operation that cuts `n` into ordered pairs):
  - **Cauchy / additive cut** `natSplits n = [(i,j) : i+j=n]`
    (`Meta/Nat/Convolution213.lean`), product `conv f g n = Σ_{i+j=n} f i·g j`
    — generating-function multiplication, closed as a commutative semiring with the
    coassociativity `conv_assoc`.
  - **Dirichlet / multiplicative cut** `[(d,e) : d·e=n]`
    (`Lib/Math/NumberTheory/DirichletIdentities.lean`), product
    `dconv f g n = Σ_{d∣n} f d·g(n/d)` — the divisor convolution, in which `μ∗1=ε`,
    `φ=μ∗id`, `σ_k=id^k∗1`, the Jordan totient `J_k=μ∗id^k`.

- **Main** essayed the *function-level* reading of the same split:
  - `theory/essays/synthesis/addition_and_multiplication_are_two_faces_of_one_count.md`
    — `vp` is one count-Lens with two behaviours (`vp_mul`: × adds; `vp_add_eq_min`:
    + minimizes).
  - `theory/essays/synthesis/multiplicativity_is_the_x_count_lens.md` — multiplicativity
    = the ×-count-Lens reading through its prime axes, faithful by `vp_separation`.

## The fusion (what the juxtaposition exposes)

ℕ carries **two comultiplications** — the additive cut `Δ_+ : n ↦ Σ_{i+j=n} i⊗j` and the
multiplicative cut `Δ_× : n ↦ Σ_{d·e=n} d⊗e`. Cauchy convolution is the product **dual to
`Δ_+`**; Dirichlet convolution is the product **dual to `Δ_×`**. Main's two essays are
precisely the *function-level shadow* of this object-level fact:

- "multiplicativity = ×-count-Lens" is the statement that a function is a **`Δ_×`-coalgebra
  morphism** — it respects the multiplicative cut on coprime parts (coprimality = the
  disjoint-support condition that makes `Δ_×` a *tensor* cut, `dconv_mul`).
- "+ and × are two faces of one count" is the statement that the **same** ℕ supports both
  cuts, and `vp` is the homomorphism intertwining them (`vp_mul` carries `Δ_×` to addition
  of exponent-vectors; this is why Dirichlet-multiplicative functions factor through `vp`).

So this branch supplies the two **co-operations** whose function-level morphisms main
named. The slot-programme doctrine "comm/assoc are shadows of a comultiplication swap
symmetry" now has both rungs explicit on ℕ: `conv_comm`/`conv_assoc` from `Δ_+`'s
swap/coassoc, and the Dirichlet-ring commutativity/associativity from `Δ_×`'s
(divisor-pair swap `d↔n/d`, divisor-triple reglue).

## The genuinely-open frontier

The two comultiplications do not live in isolation — `×` distributes over `+` in ℕ, so
`Δ_+` and `Δ_×` should satisfy a **compatibility** (the bialgebra/Hopf-style relation that
turns the pair into one structure on ℕ). Concretely:

- **F1 — distributivity as a comultiplication identity.** State and close ∅-axiom the
  ℕ-native compatibility between `Δ_+` and `Δ_×` induced by `a·(b+c)=a·b+a·c`: how the
  multiplicative cut of a `conv`-product relates to the additive cut of a `dconv`-product.
  This is the object-level form of "`vp` intertwines the two faces" — currently only the
  *function-level* intertwining (`vp_mul`/`vp_add_eq_min`) is closed.
- **F2 — the unit/counit pairing.** `δ` (Cauchy unit `[1,0,…]`) and `ε` (Dirichlet unit
  `[n=1]`) are *the same sequence* read against the two products. Whether the antipode
  (Möbius `μ` for `Δ_×`; the `(−1)`-alternation / formal inverse for `Δ_+`) is **one
  construction** read through the two cuts is open — Möbius inversion and binomial
  inversion (`A n g = Σ(−1)^k C(n,k) g(k)`, already in `inclusion_exclusion_set_partitions`)
  would then be the two faces of one antipode.

F2 is the sharper target: **binomial inversion (additive) and Möbius inversion
(multiplicative) as one antipode under the two cuts** — a clean ∅-axiom cross-relation, both
sides already closed in the corpus, only the unifying statement unwritten.

## Provenance / pointers

- Additive cut: `Meta/Nat/Convolution213.lean` (`natSplits`, `conv`, `conv_assoc`),
  promoted `theory/math/combinatorics/convolution_generating_functions.md`.
- Multiplicative cut: `Lib/Math/NumberTheory/DirichletIdentities.lean` (`dconv`, the
  divisor identities), promoted `theory/math/numbertheory/multiplicative_divisor_theory.md`
  §9.
- Function-level shadow (main): the two synthesis essays above.
- Binomial inversion (the additive antipode candidate):
  `Combinatorics/BinomialInversion`, promoted
  `theory/math/combinatorics/inclusion_exclusion_set_partitions.md`.
