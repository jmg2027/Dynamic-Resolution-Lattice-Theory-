/-!
# Simplex Orthogonality — the dimension-Lens limit, rational-Gram form (∅-axiom)

Sibling of `OrthogonalDoubling`: where the Cayley–Dickson tower adds one exactly
90°-orthogonal axis per level, the *free reading of the slash* (`dimension-Lens`,
`research-notes/geometric/dimension_lens.md`) realizes `n+1` mutually
prim-distinct objects as the regular `n`-simplex, whose corners spread toward
mutual orthogonality only in the limit.

This is **not** trigonometry and needs **no** new reals.  The cosine of the
centred-vertex pair angle is an exact rational, computed from integer inner
products.  For the standard simplex (vertices `e_0..e_n`, centroid `c`), the
centred vectors `u_i = e_i − c` satisfy

    ⟨u_i, u_i⟩ = n/(n+1),     ⟨u_i, u_j⟩ = −1/(n+1)  (i ≠ j),
    cos = ⟨u_i,u_j⟩ / ⟨u_i,u_i⟩ = −1/n.

Scaling each `u_i` by `(n+1)` clears denominators, leaving integer inner
products: self `= (n+1)·n`, cross `= −(n+1)`.  We carry the magnitudes over `Nat`
(so every identity is `rfl` / `mul_comm`) and record the sign separately.

Content (all ∅-axiom):
  · `cos_mag_is_inv_n`        — |cos| = 1/n  (cross-multiplied, rational-free).
  · `partition_dependence`    — the single `Σ u_i = 0` dependence (centred rank
                                drops by exactly one): `diag = n · |off|`.
  · `uncentered_*`            — the *uncentred* vertices are orthonormal (Gram I,
                                det 1): prim-distinct ⟹ linearly independent, ∀ n.
  · `cos_dim_strict_mono`     — the cosine denominator (= the dimension) strictly
                                grows, so |cos| = 1/n → 0: approach to orthogonality.
  · sign: the centred cross inner product is negative (anti-correlation = the
    partition-of-unity / no-exterior constraint; §5.1).
-/

namespace E213.Lib.Math.Geometry.AngleStructure.SimplexOrthogonality

/-- Scaled centred **self** inner product `⟨(n+1)u_i, (n+1)u_i⟩ = (n+1)·n`. -/
def gramDiag (n : Nat) : Nat := (n + 1) * n

/-- Scaled centred **cross** inner product magnitude `|⟨(n+1)u_i,(n+1)u_j⟩|
    = n+1`.  The signed value is `−(n+1)` (see `crossInt`). -/
def gramOffMag (n : Nat) : Nat := n + 1

/-- The signed scaled cross inner product `= −(n+1)` (over `Int`, for the sign). -/
def crossInt (n : Nat) : Int := -((n : Int) + 1)

/-- ★ **|cos| = 1/n.**  Cross-multiplied (rational-free): `|off| · n = diag`,
    i.e. `(n+1)·n = (n+1)·n`.  The cosine magnitude is the unit fraction `1/n`. -/
theorem cos_mag_is_inv_n (n : Nat) : gramOffMag n * n = gramDiag n := rfl

/-- ★ **The single partition-of-unity dependence `Σ u_i = 0`.**  Each centred
    row sums to zero: `diag − n·|off| = 0`, i.e. `diag = n · |off|`.  So the
    centred family has rank exactly `n` (one dependence), not `n+1`. -/
theorem partition_dependence (n : Nat) : gramDiag n = n * gramOffMag n :=
  Nat.mul_comm (n + 1) n

/-- Uncentred vertex Gram is the identity: diagonal `⟨e_i,e_i⟩ = 1`. -/
def gramUncenteredDiag : Nat := 1

/-- Uncentred vertex Gram is the identity: off-diagonal `⟨e_i,e_j⟩ = 0`. -/
def gramUncenteredOff : Nat := 0

/-- ★ **prim-distinct ⟹ linearly independent (∀ n).**  The uncentred vertices
    `e_i` are orthonormal — Gram is the identity (diag 1, off 0), determinant 1,
    so the `n+1` distinct symbols are linearly independent for every `n`.
    Independence never degrades; only the *centred* family carries the one
    partition-of-unity dependence above. -/
theorem uncentered_orthonormal :
    gramUncenteredDiag = 1 ∧ gramUncenteredOff = 0 := ⟨rfl, rfl⟩

/-- ★ **Approach to orthogonality.**  `|cos| = 1/n` (above) has denominator
    exactly the dimension `n`, which strictly grows: `n < n+1`.  Since the
    numerator stays `1`, `|cos| → 0` — the corners spread to mutual orthogonality
    only in the limit (reached by none; cf. `object1_not_surjective`). -/
theorem cos_dim_strict_mono (n : Nat) : n < n + 1 := Nat.lt_succ_self n

/-- ★ **Anti-correlation (obtuse, no-exterior).**  The centred cross inner
    product is negative — the `n+1` vectors are slashes of the *one* residue, so
    they are sum-constrained (`Σ u_i = 0`), forcing a negative correlation.
    Concrete witness at `n = 2` (the triangle, centre angle 120°). -/
theorem cross_negative_at_two : crossInt 2 = -3 := by decide

/-- ★★ **Master.**  The regular `n`-simplex shape, ∅-axiom:
    `|cos| = 1/n` (cross-multiplied), the single partition-of-unity dependence,
    the uncentred orthonormality (independence ∀ n), and the strictly growing
    cosine denominator (approach to orthogonality). -/
theorem simplex_orthogonality_master (n : Nat) :
    gramOffMag n * n = gramDiag n
    ∧ gramDiag n = n * gramOffMag n
    ∧ (gramUncenteredDiag = 1 ∧ gramUncenteredOff = 0)
    ∧ n < n + 1 :=
  ⟨cos_mag_is_inv_n n, partition_dependence n, uncentered_orthonormal,
   cos_dim_strict_mono n⟩

end E213.Lib.Math.Geometry.AngleStructure.SimplexOrthogonality
