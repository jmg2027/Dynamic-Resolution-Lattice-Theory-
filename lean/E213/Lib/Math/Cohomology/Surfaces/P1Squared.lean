/-!
# Minimal CW for ℙ¹ × ℙ¹ — 213-native form

The product `ℙ¹ × ℙ¹` (complex dim 2 = real dim 4) has minimal CW
decomposition by Künneth product of two ℙ¹ ≅ S² minimal complexes
(1 zero-cell + 1 two-cell each):

  | dim | count | basis                          |
  |-----|-------|--------------------------------|
  | 0   | 1     | pt × pt                        |
  | 2   | 2     | line × pt   (= H₁),  pt × line (= H₂) |
  | 4   | 1     | line × line  (= volume class)  |

(All odd dimensions empty.)  Cellular cohomology
`H⁰ = H⁴ = ℤ`, `H² = ℤ²`, all boundaries zero.

## Hodge structure comparison

  · Same **cup-pairing matrix** as T² on H²: `[[0, 1], [1, 0]]`.
  · Same **signature** (1, 1).
  · **Different Hodge diamond**: ℙ¹×ℙ¹ has `h^{2,0} = h^{0,2} = 0`,
    `h^{1,1} = 2`; T² has `h^{2,0} = h^{0,2} = 1`, `h^{1,1} = 1`.

So two **different Kähler 2-folds** with the same cup-pairing
signature (1, 1) — illustrating that the Hodge Index signature
is a *coarser* invariant than the Hodge diamond.

Used by `HodgeConjecture/Pairing/HodgeIndexP1Squared.lean` for
the Hodge Index capstone.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Surfaces.P1Squared

/-- 0-cells: `pt × pt`. -/
inductive Cell0 : Type
  | ptpt : Cell0
  deriving DecidableEq, Repr

/-- 2-cells: two horizontal/vertical hyperplane classes
    `H₁ = line × pt` (first ℙ¹'s line) and
    `H₂ = pt × line` (second ℙ¹'s line). -/
inductive Cell2 : Type
  | H1 : Cell2   -- line × pt
  | H2 : Cell2   -- pt × line
  deriving DecidableEq, Repr

/-- 4-cells: the volume class `line × line`. -/
inductive Cell4 : Type
  | vol : Cell4
  deriving DecidableEq, Repr

abbrev C0 : Type := Cell0 → Int
abbrev C2 : Type := Cell2 → Int
abbrev C4 : Type := Cell4 → Int

/-- Cup-pairing on H² × H² → H⁴.

    `H₁ ⌣ H₁ = (line·line) × (pt·pt)` — but `pt·pt` lives in
    `H⁴(ℙ¹) = 0`, so `H₁ ⌣ H₁ = 0`.

    Symmetrically `H₂ ⌣ H₂ = 0`.

    `H₁ ⌣ H₂ = (line·pt) × (pt·line) = (pt) × (pt) = volume`,
    coefficient `+1`.  And `H₂ ⌣ H₁ = +1` by graded comm of
    two 2-forms. -/
def cup (α β : C2) : C4 :=
  fun _ => α Cell2.H1 * β Cell2.H2 + α Cell2.H2 * β Cell2.H1

/-- The hyperplane class `H₁` (first factor's line). -/
def basis_H1 : C2 := fun
  | Cell2.H1 => 1 | Cell2.H2 => 0

/-- The hyperplane class `H₂` (second factor's line). -/
def basis_H2 : C2 := fun
  | Cell2.H1 => 0 | Cell2.H2 => 1

/-- Diagonalised positive class `H₁ + H₂` — analogue of α₊
    on T².  `cup = +2`. -/
def alpha_plus : C2 := fun
  | Cell2.H1 => 1 | Cell2.H2 => 1

/-- Diagonalised negative class `H₁ − H₂` — analogue of α₋
    on T².  `cup = −2`. -/
def alpha_minus : C2 := fun
  | Cell2.H1 => 1 | Cell2.H2 => -1

theorem cup_H1H1_zero : cup basis_H1 basis_H1 Cell4.vol = 0 := by decide
theorem cup_H2H2_zero : cup basis_H2 basis_H2 Cell4.vol = 0 := by decide
theorem cup_H1H2_one  : cup basis_H1 basis_H2 Cell4.vol = 1 := by decide
theorem cup_H2H1_one  : cup basis_H2 basis_H1 Cell4.vol = 1 := by decide

theorem cup_alpha_plus : cup alpha_plus alpha_plus Cell4.vol = 2 := by decide
theorem cup_alpha_minus : cup alpha_minus alpha_minus Cell4.vol = -2 := by decide
theorem cup_alpha_ortho : cup alpha_plus alpha_minus Cell4.vol = 0 := by decide


/-- α₊ ≠ α₋ (distinct in `C2`: they differ at `H₂`). -/
theorem alpha_plus_ne_minus : alpha_plus ≠ alpha_minus :=
  fun h => absurd (congrFun h Cell2.H2) (by decide)

/-- ★★★★★ **Signature `(1, 1)` of `H²(ℙ¹×ℙ¹; ℤ)`** — ∅-axiom.  The cup-pairing admits the
    ℤ-orthogonal classes `α₊ = H₁+H₂`, `α₋ = H₁−H₂` with `α₊⌣α₊ = +2`, `α₋⌣α₋ = −2`,
    `α₊⌣α₋ = 0`, `α₊ ≠ α₋`.  With `dim H² = 2` this forces signature `(1, 1)` (Sylvester) —
    the same hyperbolic intersection form `[[0,1],[1,0]]` as `T²`, on a *different* surface
    (`cup_H1H1 = cup_H2H2 = 0`, `cup_H1H2 = 1`).  The `decide`-witness analogue of
    `T2Minimal.Signature.signature_one_one_witness`. -/
theorem signature_one_one_witness :
    cup alpha_plus alpha_plus Cell4.vol = 2
    ∧ cup alpha_minus alpha_minus Cell4.vol = -2
    ∧ cup alpha_plus alpha_minus Cell4.vol = 0
    ∧ alpha_plus ≠ alpha_minus :=
  ⟨cup_alpha_plus, cup_alpha_minus, cup_alpha_ortho, alpha_plus_ne_minus⟩
end E213.Lib.Math.Cohomology.Surfaces.P1Squared
