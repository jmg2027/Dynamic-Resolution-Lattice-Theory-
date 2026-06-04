/-!
# Octonion basis algebra — Fano plane multiplication (∅-axiom)

Concrete multiplication table for the octonion basis `e₀, e₁, …, e₇`,
with `e₀ = 1` and `e₁..e₇` imaginary units following the Fano-plane
oriented triples.

213-native paradigm: at level 3 (CD), the sign-tracking that
distinguishes `(a,b)·(c,d) = (ac−bd, ad+bc)` collapses on basis
elements into a **Fano plane lookup**.  Multiplication-rule choice
becomes orientation choice on the 7 Fano lines.

Atomic content: `OctSigned := Bool × Fin 8`, `octBasisMul` lookup
on the 8×8 table from one Fano orientation.
-/

namespace E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionBasisAlgebra

/-- Octonion basis element with sign: `(true, k) = +e_k`,
    `(false, k) = -e_k`. -/
abbrev OctSigned := Bool × Fin 8

/-- Sign multiplication. -/
def signMul (s t : Bool) : Bool := !(Bool.xor s t)

/-- Octonion basis multiplication via Fano plane lookup.
    Encodes `e_i · e_j → (sign, k)` for the 8×8 table.

    Key relations:
      * `e_0 = 1` is identity.
      * `e_i · e_i = -1` for `i ≥ 1`.
      * Oriented Fano lines (one convention):
        (1,2,3), (1,4,5), (2,4,6), (3,4,7).
      * `e_i · e_j = ±e_k` per orientation. -/
def octBasisMul (a b : OctSigned) : OctSigned :=
  let i := a.2.val
  let j := b.2.val
  let s := signMul a.1 b.1
  match i, j with
  | 0, _ => (s, b.2)
  | _, 0 => (s, a.2)
  | 1, 1 | 2, 2 | 3, 3 | 4, 4
  | 5, 5 | 6, 6 | 7, 7 => (!s, ⟨0, by decide⟩)
  | 1, 2 => (s, ⟨3, by decide⟩)
  | 2, 1 => (!s, ⟨3, by decide⟩)
  | 2, 3 => (s, ⟨1, by decide⟩)
  | 3, 2 => (!s, ⟨1, by decide⟩)
  | 3, 1 => (s, ⟨2, by decide⟩)
  | 1, 3 => (!s, ⟨2, by decide⟩)
  | 1, 4 => (s, ⟨5, by decide⟩)
  | 4, 1 => (!s, ⟨5, by decide⟩)
  | 4, 5 => (s, ⟨1, by decide⟩)
  | 5, 4 => (!s, ⟨1, by decide⟩)
  | 5, 1 => (s, ⟨4, by decide⟩)
  | 1, 5 => (!s, ⟨4, by decide⟩)
  | 2, 4 => (s, ⟨6, by decide⟩)
  | 4, 2 => (!s, ⟨6, by decide⟩)
  | 4, 6 => (s, ⟨2, by decide⟩)
  | 6, 4 => (!s, ⟨2, by decide⟩)
  | 6, 2 => (s, ⟨4, by decide⟩)
  | 2, 6 => (!s, ⟨4, by decide⟩)
  | 3, 4 => (s, ⟨7, by decide⟩)
  | 4, 3 => (!s, ⟨7, by decide⟩)
  | 4, 7 => (s, ⟨3, by decide⟩)
  | 7, 4 => (!s, ⟨3, by decide⟩)
  | 7, 3 => (s, ⟨4, by decide⟩)
  | 3, 7 => (!s, ⟨4, by decide⟩)
  | _, _ => (s, ⟨0, by decide⟩)

end E213.Lib.Math.NumberSystems.SignedCut.Octonion.OctonionBasisAlgebra
