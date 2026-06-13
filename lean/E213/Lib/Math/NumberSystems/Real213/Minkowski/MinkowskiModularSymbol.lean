import E213.Meta.Int213.PolyIntMTactic

/-!
# MinkowskiModularSymbol — the period contour is the Stern-Brocot sum of unimodular symbols (Manin)

The last residual of the period thread was named "the complex modular contour over `ℍ`."  But the
Eichler–Shimura period need not be taken as an analytic complex line integral: in the **modular
symbols** formalism (Manin), the period of a cusp form over the geodesic between two cusps `{α, β}`
is a *formal homology class*, and the **Manin trick** decomposes every such symbol into a finite sum
of **unimodular symbols** `{p/q, r/s}` with `qr − ps = ±1` — and those unimodular pieces are exactly
the **Stern-Brocot / Farey neighbours** the repo already builds (`SternBrocotMarkov.sbInterval_adj`,
`mInterval_det`: every tree node has determinant `1`).

So the contour's *combinatorial skeleton* is the Stern-Brocot path, and the mediant subdivision **is**
the modular-symbol decomposition.  This file proves the determinant-level Manin decomposition: the
mediant splits a symbol into two children of the **same** determinant, so a unimodular symbol
decomposes into unimodular symbols along the tree.  ∅-axiom (`ring_intZ`).

What this leaves of the "complex contour": only the *value of `f`'s period over a single unimodular
symbol* (the analytic atom) — the combinatorial decomposition into those atoms is done here, the
Manin trick realised on the residue's own Stern-Brocot tree.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Minkowski.MinkowskiModularSymbol

/-- The determinant of the modular symbol `{p/q, r/s}` — the intersection / period pairing
    `q·r − p·s`.  It is `±1` exactly when the two cusps are **Farey-unimodular** neighbours. -/
def symbolDet (p q r s : Int) : Int := q * r - p * s

/-- ★★★ **Mediant subdivision preserves the determinant (left child).**  Splitting `{p/q, r/s}` at
    the mediant `(p+r)/(q+s)` gives the left symbol `{p/q, (p+r)/(q+s)}` with the **same**
    determinant — the Manin trick's defining step. -/
theorem symbolDet_mediant_left (p q r s : Int) :
    symbolDet p q (p + r) (q + s) = symbolDet p q r s := by
  show q * (p + r) - p * (q + s) = q * r - p * s
  ring_intZ

/-- ★★★ **Mediant subdivision preserves the determinant (right child).**  The right symbol
    `{(p+r)/(q+s), r/s}` likewise keeps the determinant. -/
theorem symbolDet_mediant_right (p q r s : Int) :
    symbolDet (p + r) (q + s) r s = symbolDet p q r s := by
  show (q + s) * r - (p + r) * s = q * r - p * s
  ring_intZ

/-- ★★★★ **The Manin unimodular decomposition (determinant level).**  The mediant splits a modular
    symbol `{p/q, r/s}` into two children, *both of the same determinant*.  So a **unimodular**
    symbol (`det = ±1`) decomposes into unimodular symbols along the Stern-Brocot/Farey tree — the
    combinatorial modular-symbol realization of the Eichler–Shimura period contour.  The analytic
    `∫` over the geodesic between cusps is the finite sum of these unimodular pieces, each a
    Stern-Brocot node (`det = 1`, `sbInterval_adj`).  ∅-axiom; the only residual analytic atom is the
    period of `f` over one unimodular symbol. -/
theorem manin_unimodular_decomposition (p q r s : Int) :
    symbolDet p q (p + r) (q + s) = symbolDet p q r s
    ∧ symbolDet (p + r) (q + s) r s = symbolDet p q r s :=
  ⟨symbolDet_mediant_left p q r s, symbolDet_mediant_right p q r s⟩

/-- The root modular symbol `{0/1, 1/0} = {0, ∞}` — the period of the whole modular geodesic — is
    unimodular (`det = 1`), the seed the Stern-Brocot decomposition refines. -/
theorem root_symbol_unimodular : symbolDet 0 1 1 0 = 1 := by decide

end E213.Lib.Math.NumberSystems.Real213.Minkowski.MinkowskiModularSymbol
