# Linalg213 Gap-fill — Module Index

Companion to the existing `Linalg213/` paper-1 chiral compression
capstone.  This sub-cluster fills out the elementary linear-algebra
operations (matrix multiplication, determinant, tensor product,
eigenvalue) that the paper-1 capstone leaves at the structure
level.

## Modules

| File | Topic | Status |
|---|---|---|
| `MatrixMul.lean` | `matrixMulNum n A B`; identity / zero matrices; zero · any = 0 | ∅-axiom |
| `Determinant.lean` | 2×2 magnitude form via positive/negative parts; identity / zero / diagonal closed forms | ∅-axiom |
| `TensorProduct.lean` | `tensorDim m n = m·n`; `5 ⊗ 5 = 25`; identity, comm; `5^25` N_U link | ∅-axiom |
| `Eigen.lean` | `IsMatEigenpair`; scalar `λ·I` eigenpair; identity eigenvalue | ∅-axiom |
| `Capstone.lean` | 5 cluster witnesses + `total_witness` | ∅-axiom |
| `Gap.lean` | umbrella | — |

## 213-native paradigm

  * **Matrix = `Nat → Nat → Nat`**: arithmetic only; no Choice; no
    abstract `Module` typeclass.
  * **Determinant = polynomial closed form**: 2×2 case is split
    into positive/negative magnitude parts — sign is a separate
    oracle layer (truncated Nat-subtraction here gives magnitude).
  * **Tensor = product on Nat**: `5 ⊗ 5 = 25` is the K_{3,2}^{(c=2)}
    channel count; `5^25` agrees with the N_U count-Lens readout.
  * **Eigen = pointwise identity**: matched to
    `Functional/Spectrum.lean`'s `IsEigenpair` paradigm.

## Honest scope

  * Permutation expansion of det for general `n×n`: needs
    inversion-counting parity at the oracle level.
  * Characteristic polynomial: requires `cutPow` chain at matrix
    level (Real213 polynomial bridge follow-up).
  * SVD / Jordan canonical: separate marathons.
