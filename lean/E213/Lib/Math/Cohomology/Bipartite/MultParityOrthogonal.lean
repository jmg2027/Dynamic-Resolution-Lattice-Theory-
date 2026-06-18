import E213.Lib.Math.Cohomology.Bipartite.Parametric.CochSpaces

/-!
# Multiplicity parity ⊥ cup orientation on K_{3,2}^{(c=2)}

The "chirality forces `c = 2`" route (frontier P3′) would need the
sheet-swap involution — the multiplicity-bit flip `e ↦ e XOR 1`,
generator of the internal `C₂^(NS·NT)` of `Aut(K_{3,2}^{(c=2)})`
(`Lib/Physics/Symmetry/AutKChiral`) — to BE the cup-orientation sign
(`Cup/SignedCup.cup1_antisymmetric`, the `(−1)^inv` parity on
simplex-vertex order).  It is not.

The cup sign is a function of an edge's **endpoints** (its two simplex
vertices `src`, `tgt`); the sheet-swap **preserves the endpoints**
(`src`, `tgt` depend only on `e / 2`, unchanged by the low-bit flip)
and flips only the multiplicity bit `e % 2`.  So the two ℤ/2's act on
orthogonal data and cannot be identified: the multiplicity parity
carries information no endpoint-function — the cup orientation — can
see.  This refutes the frontier's P3′ (the chirality identification of
`c = 2`); the repo's cup chirality is the `NS ≠ NT` endpoint asymmetry,
a different ℤ/2 from the multiplicity.

The edge-endpoint extractors are the parametric `CochSpaces.srcOf` /
`CochSpaces.tgtOf` at `(c, NT) = (2, 2)` (the K_{3,2}^{(c=2)}
specialisation), i.e. `srcOf 2 2 e = (e/2)/2`, `tgtOf 2 2 e = (e/2)%2`
— no concrete graph carrier.

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.MultParityOrthogonal

open E213.Lib.Math.Cohomology.Bipartite.Parametric.CochSpaces (srcOf tgtOf)

/-- Each sheet-pair `(2k, 2k+1)` of K_{3,2}^{(c=2)} shares its endpoints
    `(src, tgt)` — both depend only on `e / 2` — but differs in the
    multiplicity bit `e % 2`. -/
def sheet_swap_orthogonality_check : Bool :=
  (List.range 6).all (fun k =>
    (srcOf 2 2 (2*k) == srcOf 2 2 (2*k+1))
    && (tgtOf 2 2 (2*k) == tgtOf 2 2 (2*k+1))
    && ((2*k) % 2 != (2*k+1) % 2))

/-- ★ The sheet-swap ℤ/2 (multiplicity parity) is provably NOT a function
    of an edge's endpoints, hence not the cup-orientation ℤ/2 (which
    depends only on endpoints): every sheet-pair shares `(src, tgt)` yet
    differs in `e % 2`.  Refutes "chirality identifies `c = 2`"
    (frontier P3′).  PURE. -/
theorem mult_parity_orthogonal_to_cup_orientation :
    sheet_swap_orthogonality_check = true := by decide

end E213.Lib.Math.Cohomology.Bipartite.MultParityOrthogonal
