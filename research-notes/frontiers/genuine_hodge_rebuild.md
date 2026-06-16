# Genuine Hodge-conjecture rebuild (post-deletion of the bogus layer)

**Why the old programme was deleted.** A full honesty audit (committed) found
the `HodgeConjecture/` headline layer was stereotype-matching: the central
`hodge_conjecture_213*` family had `IsLensHodgeClass := True` and proofs
`⟨σ, fun _ => rfl⟩` on the `K_{3,2}^{(c=2)}` graph — a **1-complex**, where the
real `(p,p)` Hodge conjecture is *vacuous* (no `H^{p,p}` for `p ≥ 1`).  The
entire `MotivicBridge/`, the fake Hard-Lefschetz layer (`kahler_class` defined
but unused), the Refinement clone family, and the arithmetic-geometry Bridge
files were the same pattern — a famous name welded to a `binom` identity or a
`True`.  ~38 files deleted; the genuine surface intersection-form seam
(`Surfaces/`, the Hodge-Riemann files, the `⋆⋆=id` involution, the
statistical-physics bridges) was kept and decoupled from any "Hodge Conjecture"
framing.

**The real conjecture content** (what nothing in the old 75 files stated):
on a smooth projective / Kähler variety `X`, every rational `(p,p)` cohomology
class is a `ℚ`-combination of **algebraic cycle classes** (image of the
cycle-class map `CH^p(X)_ℚ → H^{2p}(X,ℚ) ∩ H^{p,p}`).  This is non-trivial only
on an object with `H^{p,p} ⊊ H^{2p}` — i.e. `h^{2,0} > 0`.

## Stage 1 — DONE: Lefschetz (1,1) / divisor case on the abelian surface `T⁴`

`lean/E213/Lib/Math/Cohomology/Surfaces/AbelianSurfaceHodge.lean` (9 PURE).
The object is the abelian surface `T⁴` (the kept `Surfaces/T2Squared` seam:
`H²` 6-dim, `h^{2,0}=1, h^{1,1}=4, h^{0,2}=1`, signature `(3,3)`) — a genuine
variety where Hodge has teeth.

  · `IsHodge11 F := F.c02 = F.c13 ∧ F.c12 = −F.c03` — the `(1,1)` type =
    `J`-invariance; a **real predicate** — `hodge11_nonvacuous` proves the
    `(2,0)` class `e02` fails it.
  · `IsAlgebraic F` — `F` is an integer combination of the four Néron–Severi
    divisor generators (cycle-class image).
  · `hodge11_implies_algebraic` (★): every integral `(1,1)` class is algebraic
    — the **Lefschetz (1,1) theorem**, the one Hodge case proven
    unconditionally in classical geometry.  Proof exhibits the divisor
    coefficients (no tautology).
  · `polarization` (`e01+e23`, an ample divisor) witnesses both predicates.

This is modest but honest: a genuine (p,p)-vs-algebraic distinction on a real
surface, with the implication proven by exhibiting cycles — the antithesis of
`:= ⟨σ, rfl⟩`.

## Open stages (the rest of the rebuild)

- **Stage 2 — generality of the (1,1) lattice.**  Lift the divisor case from
  the 6-coordinate `Form` model to a basis-free `H²(T⁴)` with the Hodge
  decomposition `H² = H^{2,0} ⊕ H^{1,1} ⊕ H^{0,2}` from the complex structure
  `J`, and prove `NS(X) = H^{1,1} ∩ H²(X,ℤ)` (integral (1,1) = algebraic) as a
  rank statement.
- **Stage 3 — a genuine cycle-class map.**  Define `CH¹(T⁴) → H²` (divisors →
  classes) intrinsically (not by listing generators) and prove surjectivity
  onto the integral `(1,1)` lattice.
- **Stage 4 — higher `(p,p)` / `(2,2)` on a 4-fold**, and the obstruction
  structure: where the conjecture stops being Lefschetz-(1,1)-easy (the actual
  open Hodge content begins at `(2,2)` on dimension-4 varieties).
- **Stage 5 — honest scope statement.**  The framework must NOT cite any of
  this as "the Hodge Conjecture proven"; Stage 1 is *Lefschetz (1,1) on `T⁴`*,
  a classical theorem, formalised ∅-axiom — and the general conjecture remains
  open here as it is in mathematics.

## Cross-references
- `lean/E213/Lib/Math/Cohomology/Surfaces/AbelianSurfaceHodge.lean` (Stage 1)
- `lean/E213/Lib/Math/Cohomology/Surfaces/T2Squared/HodgeIndex.lean` (the kept
  genuine `T⁴` intersection form, signature (3,3))
- `theory/math/cohomology/hodge.md` (the genuine surface seam narrative)
