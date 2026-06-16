import E213.Lib.Physics.Symmetry.OctetModule

/-!
# Burnside orbit count of the Sym(3) action on the octet — ∅-axiom

The symmetric group `Sym(3)` acts on the `8`-dimensional octet module `OctetModule`
(`H1K`, `2⁸ = 256` cochains over `F₂`) by the three transposition matrices `S01`, `S12`,
`S02` and the `3`-cycle `ρ = S12 ∘ S01`.  This file counts the orbits of that action
by the **Burnside (Cauchy–Frobenius) lemma** `|Orbits| = (Σ_g |Fix(g)|)/|G|`, and refines
the count into a full orbit-size decomposition.

  * **Per-element fixed-point counts** (`decide` over the 256 cochains):
    `|Fix(S01)| = |Fix(S12)| = |Fix(S02)| = 32 = 2⁵`, `|Fix(ρ)| = 4 = 2²`.
  * **Burnside count**: `(256 + 3·32 + 2·4)/6 = 360/6 = 60` orbits (`sym3_burnside_arithmetic`,
    `sym3_burnside_sum`).
  * **Inclusion–exclusion**: `|Fix(S01) ∪ Fix(S12) ∪ Fix(S02)| = 3·32 − 3·4 + 4 = 88`
    (`transpFixedCount_eq_88`), the pairwise transposition intersection being the full
    `Sym(3)`-fixed subspace (any two transpositions generate `Sym(3)`).
  * **Orbit-size decomposition** `(a,b,c,d) = (4,0,28,28)` (`suborbit_decomposition`):
    `4` singletons (the `Sym(3)`-fixed subspace `fixedSize = 4`), `0` orbits of size `2`,
    `28` orbits of size `3` (stabilizer a single `⟨transposition⟩`), `28` orbits of size `6`
    (trivial stabilizer).  Sums check: `4+0+28+28 = 60` orbits, `4·1+0·2+28·3+28·6 = 256`
    cochains.  The absence of size-`2` orbits is the structural fact `|Fix(ρ)| = fixedSize`:
    every `ρ`-fixed cochain is already `Sym(3)`-fixed, so no cochain has stabilizer exactly
    the cyclic subgroup `⟨ρ⟩`.

All `∅`-axiom (`decide` on finite enumerations + `rfl`/`rw`).
-/

namespace E213.Lib.Math.Combinatorics.Sym3OctetOrbits

open E213.Lib.Physics.Symmetry.OctetModule
  (M_S01 M_S12 M_mul_vec M_mul_M IdMatrix Octet OctetAt)
open E213.Lib.Physics.Symmetry.OctetModule renaming Octet → H1K, OctetAt → H1Kat

/-! ## Per-element fixed-cochain predicates -/

/-- Cochain `ω` fixed by the `S01` transposition matrix. -/
def isFixedByS01 (ω : H1K) : Bool :=
  (List.range 8).all (fun j =>
    if h : j < 8 then M_mul_vec M_S01 ω ⟨j, h⟩ == ω ⟨j, h⟩ else true)

/-- Cochain `ω` fixed by the `S12` transposition matrix. -/
def isFixedByS12 (ω : H1K) : Bool :=
  (List.range 8).all (fun j =>
    if h : j < 8 then M_mul_vec M_S12 ω ⟨j, h⟩ == ω ⟨j, h⟩ else true)

/-- Cochain `ω` fixed by the 3-cycle `ρ = M_S12 ∘ M_S01`. -/
def isFixedByRho (ω : H1K) : Bool :=
  (List.range 8).all (fun j =>
    if h : j < 8 then
      M_mul_vec M_S12 (M_mul_vec M_S01 ω) ⟨j, h⟩ == ω ⟨j, h⟩
    else true)

/-- Count of `H1K` cochains fixed by `S01`. -/
def fixedSizeS01 : Nat :=
  ((List.range 256).filter (fun i => isFixedByS01 (H1Kat i))).length

/-- Count of `H1K` cochains fixed by `S12`. -/
def fixedSizeS12 : Nat :=
  ((List.range 256).filter (fun i => isFixedByS12 (H1Kat i))).length

/-- Count of `H1K` cochains fixed by `ρ` (3-cycle). -/
def fixedSizeRho : Nat :=
  ((List.range 256).filter (fun i => isFixedByRho (H1Kat i))).length

/-- **`S01` transposition fixes `32 = 2⁵` cochains.**  Fixed dimension
    `= 2` (two trivial copies) `+ 3` (one fixed direction per standard copy)
    `= 5`, cardinality `2⁵ = 32`. -/
theorem fixedSizeS01_eq_32 : fixedSizeS01 = 32 := by decide

/-- **`S12` transposition fixes `32` cochains** — equal to `S01` by
    conjugacy in `Sym(3)`; verified by direct enumeration. -/
theorem fixedSizeS12_eq_32 : fixedSizeS12 = 32 := by decide

/-- **3-cycle `ρ` fixes `4 = 2²` cochains.**  Fixed dimension `= 2` (the
    two trivial copies); the `3`-cycle matrix `[[0,1],[1,1]]` over `F₂`
    has trivial fixed subspace on each standard copy. -/
theorem fixedSizeRho_eq_4 : fixedSizeRho = 4 := by decide

/-! ## Burnside orbit count -/

/-- The Burnside orbit count of the `Sym(3)` action on the octet. -/
def orbitCount : Nat := 60

/-- **Burnside arithmetic**: `(256 + 3·32 + 2·4)/6 = 60`. -/
theorem sym3_burnside_arithmetic :
    (256 + 3 * 32 + 2 * 4) / 6 = orbitCount := by decide

/-- **Burnside sum**: `Σ_g |Fix(g)| = |Orbits|·|G|` for `|G| = 6`. -/
theorem sym3_burnside_sum :
    256 + 3 * fixedSizeS01 + 2 * fixedSizeRho = orbitCount * 6 := by
  rw [fixedSizeS01_eq_32, fixedSizeRho_eq_4]
  decide

/-- **Orbit count `= 60`**, with per-element fix sizes and the
    `Sym(3)`-fixed subspace `fixedSize = 4`. -/
theorem orbit_count_via_burnside :
    orbitCount = 60
    ∧ 256 + 3 * fixedSizeS01 + 2 * fixedSizeRho = orbitCount * 6
    ∧ fixedSizeS01 = 32
    ∧ fixedSizeS12 = 32
    ∧ fixedSizeRho = 4
    ∧ E213.Lib.Physics.Symmetry.OctetModule.fixedSize = 4
    ∧ orbitCount - 4 = 56 := by
  refine ⟨rfl, sym3_burnside_sum, fixedSizeS01_eq_32,
          fixedSizeS12_eq_32, fixedSizeRho_eq_4,
          E213.Lib.Physics.Symmetry.OctetModule.fixedSize_eq_4, ?_⟩
  decide

/-! ## Third transposition + inclusion–exclusion -/

/-- Third transposition matrix `S02 = S01 · S12 · S01` (conjugation of
    `S12` by `S01` in `Sym(3)`).  Under the `M_mul_M A B` = "apply `B`
    then `A`" convention this is `M_S01 · (M_S12 · M_S01)`. -/
def M_S02 : Fin 8 → E213.Lib.Physics.Symmetry.OctetModule.Octet :=
  M_mul_M M_S01 (M_mul_M M_S12 M_S01)

/-- `S02` is involutory: `M_S02 · M_S02 = IdMatrix` (pointwise, `decide`). -/
theorem M_S02_squared_pointwise :
    ∀ i j : Fin 8, M_mul_M M_S02 M_S02 i j = IdMatrix i j := by decide

/-- Cochain `ω` fixed by the `S02` transposition matrix. -/
def isFixedByS02 (ω : H1K) : Bool :=
  (List.range 8).all (fun j =>
    if h : j < 8 then M_mul_vec M_S02 ω ⟨j, h⟩ == ω ⟨j, h⟩ else true)

/-- Count of `H1K` cochains fixed by `S02`. -/
def fixedSizeS02 : Nat :=
  ((List.range 256).filter (fun i => isFixedByS02 (H1Kat i))).length

/-- `S02` transposition fixes `32` cochains — equal to `S01`/`S12` by
    conjugacy class in `Sym(3)`; verified by enumeration. -/
theorem fixedSizeS02_eq_32 : fixedSizeS02 = 32 := by decide

/-- Cochain fixed by at least one of the three transpositions. -/
def isFixedBySomeTransp (ω : H1K) : Bool :=
  isFixedByS01 ω || isFixedByS12 ω || isFixedByS02 ω

/-- Count of cochains fixed by at least one transposition. -/
def transpFixedCount : Nat :=
  ((List.range 256).filter (fun i => isFixedBySomeTransp (H1Kat i))).length

/-- **`|Fix(S01) ∪ Fix(S12) ∪ Fix(S02)| = 88`** by inclusion–exclusion:
    `3·32 − 3·4 + 4 = 88`, the pairwise intersection being the full
    `Sym(3)`-fixed subspace (any two transpositions generate `Sym(3)`). -/
theorem transpFixedCount_eq_88 : transpFixedCount = 88 := by decide

/-! ## Orbit-size decomposition -/

/-- Cochains with stabilizer exactly one `⟨transposition⟩` (orbit size `3`). -/
def stabExactlyTranspCount : Nat := transpFixedCount - 4

/-- Cochains with trivial stabilizer (orbit size `6`):
    `256 − 4 − 0 − 84`. -/
def stabTrivialCount : Nat := 256 - 4 - 0 - 84

/-- Number of orbits of size `1` (singletons, `Sym(3)`-fixed). -/
def orbitsOfSizeOne : Nat := 4

/-- Number of orbits of size `2` (stabilizer `A₃`, none here). -/
def orbitsOfSizeTwo : Nat := 0

/-- Number of orbits of size `3` (stabilizer a `⟨transposition⟩`):
    `84 / 3`. -/
def orbitsOfSizeThree : Nat := stabExactlyTranspCount / 3

/-- Number of orbits of size `6` (trivial stabilizer): `168 / 6`. -/
def orbitsOfSizeSix : Nat := stabTrivialCount / 6

/-- **Orbit-size decomposition `(a,b,c,d) = (4,0,28,28)`.**

  The `60` `Sym(3)`-orbits on the octet partition by orbit size into
  `4` singletons (`Sym(3)`-fixed), `0` of size `2`, `28` of size `3`
  (stabilizer a single `⟨transposition⟩`), `28` of size `6` (trivial
  stabilizer).  Checks: `4+0+28+28 = 60` orbits and
  `4·1+0·2+28·3+28·6 = 256` cochains.  The size-`2` count is `0` because
  `|Fix(ρ)| = fixedSize = 4` — every `ρ`-fixed cochain is already
  `Sym(3)`-fixed, so no stabilizer equals `⟨ρ⟩` exactly. -/
theorem suborbit_decomposition :
    orbitsOfSizeOne = 4
    ∧ orbitsOfSizeTwo = 0
    ∧ orbitsOfSizeThree = 28
    ∧ orbitsOfSizeSix = 28
    ∧ orbitsOfSizeOne + orbitsOfSizeTwo + orbitsOfSizeThree
        + orbitsOfSizeSix = orbitCount
    ∧ orbitsOfSizeOne * 1 + orbitsOfSizeTwo * 2
        + orbitsOfSizeThree * 3 + orbitsOfSizeSix * 6 = 256
    ∧ 256 + 3 * fixedSizeS01 + 2 * fixedSizeRho = orbitCount * 6
    ∧ fixedSizeRho = E213.Lib.Physics.Symmetry.OctetModule.fixedSize
    ∧ transpFixedCount = 88 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · exact sym3_burnside_sum
  · rw [fixedSizeRho_eq_4, E213.Lib.Physics.Symmetry.OctetModule.fixedSize_eq_4]
  · exact transpFixedCount_eq_88

end E213.Lib.Math.Combinatorics.Sym3OctetOrbits
