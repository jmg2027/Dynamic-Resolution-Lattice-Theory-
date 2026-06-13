import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI
import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega
import E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic
import E213.Lib.Math.Algebra.CassiniUnimodular
import E213.Meta.Int213.PolyIntMTactic

/-!
# UnitsToModular — the modular generators `S, U` are regular-representation images of the units

The genuine bridge between the **spiral-axis unit groups** (`ℤ[i]^×` order 4, `ℤ[ω]^×` order 6)
and the **modular elliptic generators** `S` (order 4) `U` (order 6) of `Real213.ModularElliptic`:
the *regular representation* `ℤ[i] → M₂(ℤ)` (multiplication-by-`u` in the basis `{1, i}`) is a ring
homomorphism, and it sends the Gaussian unit `i` to **`S` exactly**.  So `S⁴ = I` is *literally
the image of* `i⁴ = 1` under a real morphism — not two coincidental order-4 facts.

This is the honest unification (a structure-preserving map, not glyph-reuse): the two CM points
**disc −4 (`i`)** and **disc −3 (`ω`)** are the single source of the orders `4, 6` — they are the
unit-group orders, the modular elliptic fixed points (`S` fixes `i`, `U` fixes `ω`), and (via the
regular rep) literally the same matrices.  For the Gaussian side this is an *equality*
(`repI i = S`); for the Eisenstein side it is *up to conjugacy* (`repO (−ω)` has the same trace,
determinant and order `6` as `U` — the same `SL₂` conjugacy class `λ²−λ+1`), since the repo's
`ℤ[ω]` basis `{1, ω}` and `U`'s basis differ by orientation.

Honest scope: this connects the *units* to `S, U` by a genuine homomorphism.  It does **not**
formalise `PSL₂(ℤ) ≅ ℤ/2 * ℤ/3` (cited classical), and makes no claim about the Cayley–Dickson
*dimension* tower `1,2,4,8` (which diverges from the axis `{2,4,6}` at `6 ≠ 8`).

**213-native caveat**: `ℤ[i]`, `ℤ[ω]`, `S`, `U` are *imported* substrate (bare `Int`-pair /
`Int`-matrix structures — no `NS/NT/d` in their definitions), and `repI i = S` holds by `rfl`
*because `S` is defined as `repI ⟨0,1⟩`* — a construction-tautology, not a 213 primitive at work.
The genuinely 213-native content this gestures at is only: the **period-2 swap** (the
difference-Lens sign, `seed/AXIOM/06_lens_readings.md §6.7`) is the one un-adjoined automorphism,
and `det = NS − NT = 1` is the glue.  Orders `4, 6` are *adjoined-and-derived* from the two
non-square residues `−1, −NS`, not native; the unit→generator bridge is structure-preserving-map
theory about imported objects.  `∅`-axiom-correct ≠ 213-native.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.UnitsToModular

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI (ZI)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic (Mat2 S U I2 negI2 mul)
open E213.Lib.Math.Algebra.CassiniUnimodular (det det_step)

/-! ## §1 — Gaussian `ℤ[i]`: the regular representation sends `i` to `S` (literally) -/

/-- The regular representation `ℤ[i] → M₂(ℤ)`: multiplication by `re + im·i` in the basis
    `{1, i}` is the matrix `[[re, −im], [im, re]]`. -/
def repI (u : ZI) : Mat2 := ⟨u.re, -u.im, u.im, u.re⟩

/-- ★★★ **The regular representation is a ring homomorphism** (multiplicative): `repI (u·v) =
    repI u · repI v`.  (Both sides are `M₂(ℤ)`; the four entries are the Gaussian product law.) -/
theorem repI_hom (u v : ZI) : repI (u * v) = mul (repI u) (repI v) := by
  cases u with | mk ure uim =>
  cases v with | mk vre vim =>
  show (⟨ure * vre - uim * vim, -(ure * vim + uim * vre),
          ure * vim + uim * vre, ure * vre - uim * vim⟩ : Mat2)
      = ⟨ure * vre + (-uim) * vim, ure * (-vim) + (-uim) * vre,
          uim * vre + ure * vim, uim * (-vim) + ure * vre⟩
  congr 1 <;> ring_intZ

/-- ★★★ **The Gaussian unit `i` maps to the modular generator `S`** — *literally* `repI i = S`. -/
theorem repI_I : repI ZI.I = S := rfl

/-- The unit `1` maps to the identity matrix. -/
theorem repI_one : repI ⟨1, 0⟩ = I2 := rfl

/-- ★★★ **`S` is the regular-representation image of the Gaussian unit `i`, and `S⁴ = I` is the
    image of `i⁴ = 1`.**  Bundles the honest unification of the order-4 axis with the modular
    generator `S`: `repI` is a homomorphism, `repI i = S`, and `i⁴ = 1` in `ℤ[i]` — so the
    order-4 of `S` *is* the order-4 of the Gaussian unit, under a real morphism. -/
theorem gaussian_unit_realizes_S :
    repI ZI.I = S
    ∧ (∀ u v : ZI, repI (u * v) = mul (repI u) (repI v))
    ∧ ZI.I * ZI.I * ZI.I * ZI.I = ⟨1, 0⟩ :=
  ⟨repI_I, repI_hom, by decide⟩

/-! ## §2 — Eisenstein `ℤ[ω]`: the regular representation realises the order-6 `U`-class -/

/-- The regular representation `ℤ[ω] → M₂(ℤ)`: multiplication by `re + im·ω` in the basis
    `{1, ω}` (with `ω² = −1 − ω`) is `[[re, −im], [im, re − im]]`. -/
def repO (u : ZOmega) : Mat2 := ⟨u.re, -u.im, u.im, u.re - u.im⟩

/-- ★★★ **The Eisenstein regular representation is a ring homomorphism.** -/
theorem repO_hom (u v : ZOmega) : repO (u * v) = mul (repO u) (repO v) := by
  cases u with | mk ure uim =>
  cases v with | mk vre vim =>
  show (⟨ure * vre - uim * vim, -(ure * vim + uim * vre - uim * vim),
          ure * vim + uim * vre - uim * vim,
          (ure * vre - uim * vim) - (ure * vim + uim * vre - uim * vim)⟩ : Mat2)
      = ⟨ure * vre + (-uim) * vim, ure * (-vim) + (-uim) * (vre - vim),
          uim * vre + (ure - uim) * vim, uim * (-vim) + (ure - uim) * (vre - vim)⟩
  congr 1 <;> ring_intZ

/-- ★★ **The order-6 Eisenstein unit `−ω` realises the `U`-conjugacy class.**  `repO (−ω)` has the
    *same trace* (`1`), *determinant* (`1`) and *order* (`6`) as the modular generator `U` — the
    same `SL₂` conjugacy class (char. poly `λ² − λ + 1`).  (Equality up to conjugacy, not on the
    nose: the repo's `ℤ[ω]` basis `{1, ω}` differs from `U`'s by orientation.) -/
theorem eisenstein_unit_realizes_U_class :
    -- repO(−ω) and U share trace and determinant (same characteristic polynomial)
    ((repO ⟨0, -1⟩).a + (repO ⟨0, -1⟩).d = U.a + U.d)
    ∧ ((repO ⟨0, -1⟩).a * (repO ⟨0, -1⟩).d - (repO ⟨0, -1⟩).b * (repO ⟨0, -1⟩).c
        = U.a * U.d - U.b * U.c)
    -- and −ω has order 6 in ℤ[ω]
    ∧ ((⟨0, -1⟩ : ZOmega) * ⟨0, -1⟩ * ⟨0, -1⟩ * ⟨0, -1⟩ * ⟨0, -1⟩ * ⟨0, -1⟩ = ⟨1, 0⟩) :=
  ⟨by decide, by decide, by decide⟩

/-! ## §3 — the two CM points are the single source of the orders `4, 6` -/

/-- ★★★ **The orders `4` and `6` come from one source: the CM points disc −4 (`i`) and disc −3
    (`ω`).**  Via the regular representation: the Gaussian unit `i` (disc −4) *is* `S` (order 4,
    fixes `i`), and the Eisenstein order-6 unit (disc −3) realises `U` (order 6, fixes `ω`).  The
    unit-group orders `{4, 6}`, the modular elliptic generators `{S, U}`, and these matrices are
    one structure, joined by the homomorphisms `repI, repO` — the honest unifier of the
    `{2,4,6} = 2·{1,2,3}` spiral axis with the modular elliptic generators. -/
theorem orders_four_six_from_two_cm_points :
    (repI ZI.I = S ∧ mul (mul (mul S S) S) S = I2)
    ∧ ((repO ⟨0, -1⟩).a + (repO ⟨0, -1⟩).d = U.a + U.d
        ∧ mul (mul (mul (mul (mul U U) U) U) U) U = I2) :=
  ⟨⟨repI_I, by decide⟩, ⟨by decide, by decide⟩⟩

/-! ## §4 — the modular generators sit on the q=1 Cassini floor (bridge to `det_step`) -/

/-- ★★★ **The modular elliptic generators are on the q=1 Cassini floor.**  `S, U ∈ SL₂` (`det = 1`),
    so their *characteristic recurrence* `s(n+2) = tr(M)·s(n+1) − det(M)·s(n)` has multiplier
    `q = det(M) = 1` — hence every solution is a **conserved-Cassini** (`det_step` with `q=1`)
    orbit, the same `q=1` floor as the golden orbit (`CassiniUnimodular`).  `S` gives
    `tr=0, det=1` (`s(n+2) = 0·s(n+1) − 1·s(n)`); `U` gives `tr=1, det=1`
    (`s(n+2) = 1·s(n+1) − 1·s(n)`).  This bridges the modular generators (`ModularElliptic`) to the
    Cassini multiplier law: being in `SL₂` *is* being on the `q=1` floor.  (Complements the
    regular-representation Bridge B — units↔generators — with generators↔Cassini-floor.) -/
theorem modular_generators_on_q1_floor :
    (S.a * S.d - S.b * S.c = 1 ∧ U.a * U.d - U.b * U.c = 1)
    ∧ (∀ s : Nat → Int, (∀ n, s (n + 2) = 0 * s (n + 1) - 1 * s n) →
        ∀ n, det s (n + 1) = det s n)
    ∧ (∀ s : Nat → Int, (∀ n, s (n + 2) = 1 * s (n + 1) - 1 * s n) →
        ∀ n, det s (n + 1) = det s n) :=
  ⟨⟨by decide, by decide⟩,
   fun s hrec n => (det_step 0 1 s hrec n).trans (Int.one_mul _),
   fun s hrec n => (det_step 1 1 s hrec n).trans (Int.one_mul _)⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.UnitsToModular
