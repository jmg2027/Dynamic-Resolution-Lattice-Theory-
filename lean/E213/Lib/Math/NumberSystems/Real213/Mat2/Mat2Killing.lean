import E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Bracket

/-!
# The adjoint representation and the Killing form on `sl₂` — the `d>1` trace character

`research-notes/decomposition/practice/representation.md` located its sharp open residue: the
**trace character** `χ(g) = tr ρ(g)` for `d > 1` is *not* a multiplicative character (`tr` is the
additive `×↦+` twin, `tr(MN) ≠ tr M · tr N`), so the `det`-homomorphism machinery does not turn
`tr` into a character.  This file closes that residue at the Lie level, where the additive trace
character finally lands **as a structure**:

  * the **adjoint map** `adMap X := [X,·] = bracket X` is the linear endomorphism of the matrix
    space `Mat2` (its restriction to traceless matrices `sl₂` is the adjoint *representation*);
  * on the 3-dimensional `sl₂` (basis `e = [[0,1],[0,0]]`, `f = [[0,0],[1,0]]`,
    `h = [[1,0],[0,-1]]`) the endomorphism `ad_X` is a genuine `3×3` matrix `adMat X`, certified
    to *be* the matrix of `ad_X` by `adMat_col_{e,f,h}` (its columns are the brackets `[X,e]`,
    `[X,f]`, `[X,h]` for traceless `X`);
  * the **Killing form** `K(X,Y) := tr(ad_X ∘ ad_Y) = tr(adMat X · adMat Y)` is a genuine
    symmetric bilinear form — the Lie algebra's intrinsic invariant metric;
  * the headline tie `killing_eq_trace_form`: for traceless `X, Y`,
    `K(X,Y) = 4 · tr(X·Y)`.  The `d>1` trace character `tr ρ` appears here not as a (non-existent)
    multiplicative character but as the **trace form**, the genuinely-additive symmetric bilinear
    invariant the adjoint representation carries.  This is where the `×↦+` additive trace character
    is grounded as a structure;
  * `adX_traceless`: `tr(ad_X) = 0` for all `X` — the adjoint action is unimodular (the additive
    character of the adjoint rep vanishes), and `ad_X ∈ sl₃` (the `3×3` traceless sector).

All entries are finite `Int213` identities on the matrix entries; everything closes by `ring_intZ`
(a bare `0` target reached through the pure `sub_self_zero`, never the `propext`-leaking core
`Int.zero_*`).  All ∅-axiom.

Residual (honest, per `representation.md`): the trace *form* `K` is grounded, and `K = 4·tr(XY)`
ties it to the matrix trace — but this is the **invariant bilinear form** reading of the trace, not
a multiplicative trace *character* (none exists — `tr(MN) ≠ tr M · tr N`).  Nondegeneracy of `K`
on `sl₂` (Cartan's semisimplicity criterion) is recorded as `killing_gram` (the Gram matrix on the
standard basis is invertible: `K(e,f)=4`, `K(h,h)=8`, all other standard pairings `0`); the general
`d×d` Killing form and `Rep(G)` decomposition stay open.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Killing

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.HyperbolicEllipticTrace (Mat2)
open E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Bracket (bracket sub)
open E213.Meta.Int213.Order (sub_self_zero)
open E213.Meta.Int213 (zero_mul zero_add)
open E213.Meta.Int213.PolyIntM (mul_zeroZ)

/-! ## §0 — the adjoint map `ad_X = [X,·]`

The adjoint map is the linear endomorphism `Y ↦ [X,Y]` of the matrix space.  Restricted to the
traceless sector `sl₂` it is the adjoint *representation* (`tr_bracket_zero` shows `[X,Y]` is
always traceless, so `ad_X` preserves `sl₂`). -/

/-- ★★★★ **The adjoint map** `ad_X : Mat2 → Mat2`, `ad_X(Y) = [X,Y]`.  The linear endomorphism of
    the matrix space whose restriction to traceless matrices (`sl₂`) is the adjoint representation.
    `tr_bracket_zero` certifies `ad_X` lands in the traceless sector, so `sl₂` is `ad`-stable. -/
def adMap (X : Mat2) : Mat2 → Mat2 := fun Y => bracket X Y

/-- `ad_X(Y)` is literally the bracket `[X,Y]` (definitional unfolding helper). -/
theorem adMap_eq (X Y : Mat2) : adMap X Y = bracket X Y := rfl

/-! ## §1 — `sl₂` coordinates and the standard basis `e, f, h`

A traceless matrix `[[p,q],[r,-p]] = p·h + q·e + r·f`.  We read its `(e,f,h)`-coordinates off the
entries: `xe = b = q`, `xf = c = r`, `xh = a = p` (with `d = -a` the traceless constraint). -/

/-- The standard `sl₂` basis vector `e = [[0,1],[0,0]]`. -/
def basisE : Mat2 := ⟨0, 1, 0, 0⟩
/-- The standard `sl₂` basis vector `f = [[0,0],[1,0]]`. -/
def basisF : Mat2 := ⟨0, 0, 1, 0⟩
/-- The standard `sl₂` basis vector `h = [[1,0],[0,-1]]`. -/
def basisH : Mat2 := ⟨1, 0, 0, -1⟩

/-- Reconstruct a traceless matrix from its `(e,f,h)`-coordinates:
    `ofCoord xe xf xh = xe·e + xf·f + xh·h = [[xh, xe],[xf, -xh]]`. -/
def ofCoord (xe xf xh : Int) : Mat2 := ⟨xh, xe, xf, -xh⟩

/-- `e`, `f`, `h` are the coordinate basis vectors. -/
theorem ofCoord_e : ofCoord 1 0 0 = basisE := by decide
theorem ofCoord_f : ofCoord 0 1 0 = basisF := by decide
theorem ofCoord_h : ofCoord 0 0 1 = basisH := by decide

/-! ## §2 — the `3×3` matrix of `ad_X` in the `(e,f,h)` basis

A minimal `3×3` integer matrix with product and trace, used only for the adjoint matrix.  Indices
`(1,2,3) ↔ (e,f,h)`.  For `X = xe·e + xf·f + xh·h` (i.e. `X.a = xh`, `X.b = xe`, `X.c = xf`,
`X.d = -xh`), using `[h,e] = 2e`, `[h,f] = -2f`, `[e,f] = h`:

```
ad_X(e) = 2·xh·e − xf·h        ad_X(f) = −2·xh·f + xe·h        ad_X(h) = −2·xe·e + 2·xf·f
```

so the matrix of `ad_X` (columns = images of `e, f, h`) is

```
        [  2·xh      0      −2·xe ]
adMat X = [   0     −2·xh    2·xf ]
        [ −xf      xe       0    ]
```
-/

/-- A minimal `3×3` integer matrix. -/
structure Mat3 where
  m11 : Int
  m12 : Int
  m13 : Int
  m21 : Int
  m22 : Int
  m23 : Int
  m31 : Int
  m32 : Int
  m33 : Int
deriving DecidableEq

namespace Mat3

/-- `3×3` matrix product. -/
def mul (A B : Mat3) : Mat3 :=
  ⟨A.m11*B.m11 + A.m12*B.m21 + A.m13*B.m31,
   A.m11*B.m12 + A.m12*B.m22 + A.m13*B.m32,
   A.m11*B.m13 + A.m12*B.m23 + A.m13*B.m33,
   A.m21*B.m11 + A.m22*B.m21 + A.m23*B.m31,
   A.m21*B.m12 + A.m22*B.m22 + A.m23*B.m32,
   A.m21*B.m13 + A.m22*B.m23 + A.m23*B.m33,
   A.m31*B.m11 + A.m32*B.m21 + A.m33*B.m31,
   A.m31*B.m12 + A.m32*B.m22 + A.m33*B.m32,
   A.m31*B.m13 + A.m32*B.m23 + A.m33*B.m33⟩

/-- `3×3` trace. -/
def tr (A : Mat3) : Int := A.m11 + A.m22 + A.m33

end Mat3

/-- ★★★★ **The matrix of `ad_X` in the `(e,f,h)` basis** (`X.a = xh`, `X.b = xe`, `X.c = xf`).
    For traceless `X` this *is* the matrix of the linear endomorphism `ad_X = [X,·]` on `sl₂`,
    certified by `adMat_col_{e,f,h}` (its columns are the brackets with the basis). -/
def adMat (X : Mat2) : Mat3 :=
  ⟨2 * X.a,   0,        -2 * X.b,
   0,        -2 * X.a,   2 * X.c,
   -X.c,      X.b,       0⟩

/-! ### The columns of `adMat X` are the brackets `[X, e/f/h]` (for traceless `X`)

This is the honesty anchor: it certifies `adMat X` genuinely is the matrix of the endomorphism
`ad_X` on `sl₂`, not a coincidental formula.  The hypothesis `X.d = -X.a` is the traceless
constraint (`X ∈ sl₂`) — without it the bracket has an `X.a - X.d` term that the matrix entry
`2·X.a` would not capture. -/

/-- Column `e`: `ad_X(e) = [X,e] = 2·xh·e − xf·h` for traceless `X`.  Equals
    `ofCoord adMat.m11 adMat.m21 adMat.m31`. -/
theorem adMat_col_e {X : Mat2} (hX : X.d = -X.a) :
    adMap X basisE = ofCoord (adMat X).m11 (adMat X).m21 (adMat X).m31 := by
  rcases X with ⟨a, b, c, d⟩
  simp only at hX; subst hX
  dsimp only [adMap, bracket, sub, basisE, ofCoord, adMat, Mat2.mul]
  rw [show (0 : Int) = a - a from (sub_self_zero a).symm]
  refine congr (congr (congr (congrArg Mat2.mk ?_) ?_) ?_) ?_ <;> ring_intZ

/-- Column `f`: `ad_X(f) = [X,f] = −2·xh·f + xe·h` for traceless `X`. -/
theorem adMat_col_f {X : Mat2} (hX : X.d = -X.a) :
    adMap X basisF = ofCoord (adMat X).m12 (adMat X).m22 (adMat X).m32 := by
  rcases X with ⟨a, b, c, d⟩
  simp only at hX; subst hX
  dsimp only [adMap, bracket, sub, basisF, ofCoord, adMat, Mat2.mul]
  rw [show (0 : Int) = a - a from (sub_self_zero a).symm]
  refine congr (congr (congr (congrArg Mat2.mk ?_) ?_) ?_) ?_ <;> ring_intZ

/-- Column `h`: `ad_X(h) = [X,h] = −2·xe·e + 2·xf·f` for traceless `X`. -/
theorem adMat_col_h {X : Mat2} (hX : X.d = -X.a) :
    adMap X basisH = ofCoord (adMat X).m13 (adMat X).m23 (adMat X).m33 := by
  rcases X with ⟨a, b, c, d⟩
  simp only at hX; subst hX
  dsimp only [adMap, bracket, sub, basisH, ofCoord, adMat, Mat2.mul]
  rw [show (0 : Int) = a - a from (sub_self_zero a).symm]
  refine congr (congr (congr (congrArg Mat2.mk ?_) ?_) ?_) ?_ <;> ring_intZ

/-! ## §3 — `ad_X` is traceless: the adjoint action is unimodular -/

/-- ★★★★ **The adjoint representation is traceless:** `tr(ad_X) = 0` for all `X`.  The additive
    character of the adjoint rep vanishes — `ad_X` lands in `sl₃` (the `3×3` traceless sector), the
    unimodularity of the adjoint action.  Immediate from the diagonal `2·xh + (−2·xh) + 0`. -/
theorem adX_traceless (X : Mat2) : (adMat X).tr = 0 := by
  show 2 * X.a + -2 * X.a + 0 = 0
  ring_intZ

/-! ## §4 — the Killing form `K(X,Y) = tr(ad_X ∘ ad_Y)` -/

/-- ★★★★ **The Killing form** `K(X,Y) := tr(ad_X ∘ ad_Y) = tr(adMat X · adMat Y)`.  The Lie
    algebra's intrinsic invariant symmetric bilinear form — the genuine *structure* the additive
    `×↦+` trace character lands as (`representation.md`'s `d>1` trace character). -/
def killing (X Y : Mat2) : Int := (Mat3.mul (adMat X) (adMat Y)).tr

/-- The Killing form expanded entrywise (the `tr(adMat X · adMat Y)` polynomial in the entries) —
    `rfl`, used to drive the bilinear-form identities below past the structure-projection layer. -/
theorem killing_unfold (X Y : Mat2) :
    killing X Y =
      ((2*X.a)*(2*Y.a) + 0*0 + (-2*X.b)*(-Y.c))
      + (0*0 + (-2*X.a)*(-2*Y.a) + (2*X.c)*Y.b)
      + ((-X.c)*(-2*Y.b) + X.b*(2*Y.c) + 0*0) := rfl

/-- ★★★★ **The Killing form is symmetric:** `K(X,Y) = K(Y,X)`.  From `tr(AB) = tr(BA)` on the
    `3×3` adjoint matrices (the `tr_bracket_zero` cousin, lifted to the adjoint rep) — a finite
    `Int213` identity per the trace polynomial. -/
theorem killing_symmetric (X Y : Mat2) : killing X Y = killing Y X := by
  rw [killing_unfold, killing_unfold]
  simp only [zero_mul, mul_zeroZ, zero_add, Int.add_zero]
  ring_intZ

/-- ★★★★★ **The headline tie — `sl₂`'s Killing form is `4·tr(XY)`:** for traceless `X, Y`
    (`X.d = -X.a`, `Y.d = -Y.a`),
    `K(X,Y) = 4 · tr(X·Y)`.  This is the `d>1` trace character of `representation.md` finally
    appearing **as a structure**: not a (non-existent) multiplicative trace character, but the
    adjoint representation's intrinsic **invariant symmetric bilinear form**, equal to the matrix
    trace form up to the constant `4` (`2·dim sl₂ / 3`, the dual-Coxeter flavour).  The genuinely
    additive `×↦+` trace finally hosted as a Lie-algebraic invariant.  A finite `Int213` identity:
    both sides are degree-2 in the entries and `ring_intZ` normalises them equal under the traceless
    substitution. -/
theorem killing_eq_trace_form {X Y : Mat2} (hX : X.d = -X.a) (hY : Y.d = -Y.a) :
    killing X Y = 4 * Mat2.tr (Mat2.mul X Y) := by
  rcases X with ⟨a1, b1, c1, d1⟩
  rcases Y with ⟨a2, b2, c2, d2⟩
  simp only at hX hY; subst hX; subst hY
  rw [killing_unfold]
  simp only [Mat2.tr, Mat2.mul, zero_mul, mul_zeroZ, zero_add, Int.add_zero]
  ring_intZ

/-! ## §5 — nondegeneracy flavour: the trace form on the `(e,f,h)` basis (Cartan's criterion)

The Killing form is nondegenerate ⟺ the algebra is semisimple (Cartan's criterion).  For `sl₂` we
record the Gram data on the standard basis: `K(e,f) = K(f,e) = 4`, `K(h,h) = 8`, and the
off-pairs `K(e,e) = K(f,f) = K(e,h) = K(f,h) = 0`.  The `2×2` block on `{e,f}` has determinant
`−16 ≠ 0` and the `h`-entry `8 ≠ 0` — the Gram matrix is invertible, so `K` is **nondegenerate**:
`sl₂` is semisimple. -/

/-- ★★★ **The Killing-form Gram matrix on the standard basis** — the nondegeneracy data
    (Cartan's semisimplicity criterion for `sl₂`).  `K(e,f) = 4`, `K(h,h) = 8`, all other standard
    pairings `0`; the Gram matrix `[[0,4,0],[4,0,0],[0,0,8]]` is invertible (`det = −128 ≠ 0`), so
    `K` is nondegenerate and `sl₂` is semisimple. -/
theorem killing_gram :
    killing basisE basisF = 4 ∧ killing basisF basisE = 4 ∧ killing basisH basisH = 8
    ∧ killing basisE basisE = 0 ∧ killing basisF basisF = 0
    ∧ killing basisE basisH = 0 ∧ killing basisF basisH = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [killing_unfold]; dsimp only [basisE, basisF, basisH]; decide

end E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Killing
