import E213.Lib.Math.Foundations.ResidueTag

/-!
# Cohomology — a NONZERO H¹: the cycle graph S¹ (the q=−1 obstruction surfaced)

the `homological_algebra` decomposition names a buildable
witness (the "Suggested buildable witness", §"Conceptual-only / absent legs"):

> a small concrete `Ext¹` … exhibiting a nonzero `q=−1` residue where
> `reduced_betti_d4_contractible` exhibits the zero (`q=+1`/exact) one.

`Examples/BettiKernel.lean` gives the **contractible / exact** case on the full
simplex Δ⁴ (`reduced_betti_d4_contractible`: `ker δ = im δ`, the residue is empty,
`q=+1`).  A full simplex is contractible *because* it is the complete graph with
all higher faces filled, so it can never carry a nonzero `H^{>0}`.

This file builds the COMPLEMENTARY case: a cochain complex with a genuinely
NONZERO `H¹`.  The simplest such space is the circle `S¹`, realised as the
**cycle graph** `C₃ = ∂Δ²` — 3 vertices `{0,1,2}`, 3 edges
`{0,1}, {1,2}, {2,0}`, and **no 2-cell** (the triangle is *hollow*).  The single
loop around the cycle is a 1-cocycle that is not a 1-coboundary — a nonzero
element of `ker δ¹ / im δ⁰`, the `q=−1` obstruction residue that `de_rham.md`'s
`H*_dR` / `sheaf_theory.md`'s `H^{>0}` / a nonzero `Ext¹` all name.

We work mod 2 (Bool / XOR), the same coefficients as `Cochain.add` and `delta`.

## Why the cycle is NOT contractible (the obstruction)

  * `C⁰ = Fin 3 → Bool` (vertices), `C¹ = Fin 3 → Bool` (edges).
  * `δ⁰σ(edge i) = σ(tail i) XOR σ(head i)` with edges `0:{0,1}, 1:{1,2}, 2:{2,0}`.
  * **No 2-cell** ⇒ `δ¹ ≡ 0` ⇒ `ker δ¹ = C¹` (all 8 edge-cochains are closed).
  * The cycle is connected ⇒ `ker δ⁰ = {const} = {000, 111}` (size 2, dim 1)
    ⇒ `dim im δ⁰ = 3 − 1 = 2` ⇒ `|im δ⁰| = 4`.
  * `H¹ = ker δ¹ / im δ⁰` has dim `3 − 2 = 1` ⇒ `|H¹| = 2 > 1` ⇒ `b₁ = 1`.

The witnessing cocycle: the **all-true** edge cochain `111` — it is closed
(`δ¹ = 0`, vacuously, no 2-cell) but is NOT in `im δ⁰` (no vertex cochain has
its odd-cycle coboundary equal to `111`).  This is the loop class.

All ∅-axiom (`decide` on finite Bool enumerations + the `ResidueTag` re-export).
-/

namespace E213.Lib.Math.Cohomology.Examples.NonzeroBetti

open E213.Lib.Math.Foundations.ResidueTag (ResidueTag multiplier)

/-! ## §1 — the hollow-triangle cochain complex `C₃ = ∂Δ²` -/

/-- A `Bool`-cochain on the 3 cells (3 vertices, or 3 edges) of the triangle,
    indexed by the raw vertex/edge number `0,1,2` (a `Nat → Bool`, evaluated
    only at `0,1,2`).  Using `Nat` (not `Fin 3`) keeps every readout
    `Nat`-arithmetic decidable, so `decide` stays ∅-axiom (no `Fin`-literal
    pattern match, which would pull in `propext`). -/
def Tri := Nat → Bool

/-- The `c`-th cochain (`0 ≤ c < 8`) via 3-bit binary encoding:
    `cochainOf c i = (c >>> i) & 1`. -/
def cochainOf (c : Nat) : Tri := fun i => (c / 2^i) % 2 == 1

/-- The hollow-triangle coboundary `δ⁰ : C⁰ → C¹`.
    Edge `0 = {0,1}`, `1 = {1,2}`, `2 = {2,0}` (the cyclic boundary `∂Δ²`).
    `δ⁰σ(edge i) = σ(tail) XOR σ(head)`.  Indexed by the raw edge number. -/
def triDelta0 (σ : Tri) : Tri := fun i =>
  if i = 0 then xor (σ 0) (σ 1)
  else if i = 1 then xor (σ 1) (σ 2)
  else xor (σ 2) (σ 0)

/-- Bool check that two cochains agree on the 3 cells `0,1,2`. -/
def triEq (σ τ : Tri) : Bool :=
  (σ 0 == τ 0) && (σ 1 == τ 1) && (σ 2 == τ 2)

/-! ## §2 — kernel and image sizes by enumeration

`δ¹ ≡ 0` (no 2-cell), so `ker δ¹ = C¹` has size `2³ = 8`.  We compute `|im δ⁰|`
by enumerating the 8 vertex cochains and counting distinct coboundaries.  -/

/-- Size of `ker δ⁰` (vertex cochains with zero coboundary = the connected
    components = the constants `{000, 111}`). -/
def kerSize0 : Nat :=
  ((List.range 8).filter
    (fun c => triEq (triDelta0 (cochainOf c)) (fun _ => false))).length

/-- Number of edge cochains (`0 ≤ e < 8`) that ARE in `im δ⁰` (some vertex
    cochain maps onto them). -/
def imSize0 : Nat :=
  ((List.range 8).filter
    (fun e => (List.range 8).any
      (fun c => triEq (triDelta0 (cochainOf c)) (cochainOf e)))).length

/-- Size of `ker δ¹`.  There is no 2-cell, so `δ¹ ≡ 0` and every one of the
    `2³ = 8` edge cochains is closed. -/
def kerSize1 : Nat := 8

/-! ## §3 — the dimension count: `b₁ = 1` -/

/-- `ker δ⁰ = {000, 111}` (the constants; the triangle is connected): size 2. -/
theorem kerSize0_eq_2 : kerSize0 = 2 := by decide

/-- `im δ⁰` has size 4 (`= 2^(3−1)`, the coboundaries of an odd cycle):
    `dim im δ⁰ = 2`. -/
theorem imSize0_eq_4 : imSize0 = 4 := by decide

/-- `ker δ¹ = C¹` has size 8 (no 2-cell ⇒ `δ¹ ≡ 0`). -/
theorem kerSize1_eq_8 : kerSize1 = 8 := by decide

/-- ★★ **`H¹(S¹) ≠ 0` — the nonzero Betti number.**  `|H¹| = |ker δ¹| / |im δ⁰|
    = 8 / 4 = 2 > 1`, so `dim H¹ = 1 = b₁`.  Strictly: the kernel of `δ¹`
    properly contains the image of `δ⁰` (`8 > 4`), so a class survives — the
    `q=−1` obstruction residue is nonempty, in contrast to
    `reduced_betti_d4_contractible` (`ker δ = im δ`, residue empty).  -/
theorem betti_one_cycle :
    kerSize1 = 8 ∧ imSize0 = 4 ∧ imSize0 < kerSize1 := by decide

/-! ## §4 — the witnessed nonzero cohomology class (the loop)

The all-true edge cochain `e = 111` (`cochainOf 7`) is a 1-cocycle (`ker δ¹`,
vacuously — no 2-cell) that is NOT a 1-coboundary: no vertex cochain `σ` has
`triDelta0 σ = 111`.  It is the generator of `H¹(S¹)`. -/

/-- The loop class: the all-true edge cochain. -/
def loopClass : Tri := cochainOf 7

/-- `loopClass` is closed: it lies in `ker δ¹`.  Vacuously true — there is no
    2-cell, so `δ¹ ≡ 0`; we record it as membership in the (full) kernel `C¹`.
    Concretely, `loopClass` is one of the 8 enumerated edge cochains. -/
theorem loopClass_is_cocycle :
    triEq loopClass (cochainOf 7) = true := by decide

/-- ★★★ **`loopClass` is NOT a coboundary** — no vertex cochain maps onto it.
    Enumerating all 8 vertex cochains, none has `triDelta0 σ = 111`: the odd
    cycle's coboundary always flips an even number of edge-bits, so `111`
    (odd weight) is unreachable.  This is the genuine nonzero cohomology class —
    a closed-not-exact 1-cocycle = a nonzero `Ext¹` / `H¹` witness. -/
theorem loopClass_not_coboundary :
    (List.range 8).all
      (fun c => !(triEq (triDelta0 (cochainOf c)) loopClass)) = true := by decide

/-- ★★★ **The nonzero cohomology class, witnessed.**  `loopClass` is a 1-cocycle
    (closed, `ker δ¹`) that is not a 1-coboundary (not in `im δ⁰`) — a nonzero
    element of `ker δ¹ / im δ⁰ = H¹(S¹)`.  This is the `q=−1` obstruction
    residue SURFACING, the complement of the contractible (`q=+1`, empty-residue)
    case `reduced_betti_d4_contractible`. -/
theorem nonzero_cohomology_class :
    -- closed (a cocycle): it is an edge cochain, hence in ker δ¹ = C¹
    triEq loopClass (cochainOf 7) = true
    -- not exact (not a coboundary): no vertex cochain maps onto it
    ∧ (List.range 8).all
        (fun c => !(triEq (triDelta0 (cochainOf c)) loopClass)) = true
    -- so the residue is nonempty: |ker δ¹| > |im δ⁰|
    ∧ imSize0 < kerSize1 := by decide

/-! ## §5 — the `q=±1` contrast with the contractible case

`reduced_betti_d4_contractible` is the `q=+1` (converge / exact) pole: `ker = im`,
residue empty — `homological_algebra.md`'s `Ext⁰`-only / contractible case.
The cycle is the `q=−1` (escape / obstruction) pole: `ker ⊋ im`, a class escapes.
We tag the two with the `ResidueTag` (`escape ↦ −1`, `converge ↦ +1`). -/

/-- The cycle's cohomological tag: `escape` (`q=−1`) — the obstruction residue is
    nonempty (`im δ⁰ ⊊ ker δ¹`). -/
def cycleTag : ResidueTag := .escape

/-- The contractible-Δ⁴ tag: `converge` (`q=+1`) — the residue is empty
    (`ker δ = im δ`, `reduced_betti_d4_contractible`). -/
def contractibleTag : ResidueTag := .converge

/-- ★★ **The `q=±1` contrast.**  The hollow cycle reads `escape` (`q=−1`, the
    obstruction surfaces, `im δ⁰ ⊊ ker δ¹`); the contractible Δ⁴ reads `converge`
    (`q=+1`, residue empty).  Their multipliers are the two unimodular Cassini
    poles `−1` and `+1`.  This is exactly `homological_algebra.md`'s
    `Ext⁰`(=`q=+1`, exact) versus `Ext^{>0}`(=`q=−1`, obstruction) split,
    witnessed by two concrete cochain complexes. -/
theorem cycle_vs_contractible_qpm :
    multiplier cycleTag = -1
    ∧ multiplier contractibleTag = 1
    ∧ cycleTag ≠ contractibleTag
    -- the cycle's nonempty residue
    ∧ imSize0 < kerSize1 := by
  refine ⟨rfl, rfl, ?_, by decide⟩
  intro h; exact absurd h (by decide)

end E213.Lib.Math.Cohomology.Examples.NonzeroBetti
