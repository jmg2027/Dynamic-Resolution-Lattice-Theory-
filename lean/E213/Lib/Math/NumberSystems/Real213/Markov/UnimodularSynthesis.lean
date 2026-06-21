import E213.Lib.Math.NumberSystems.Real213.Markov.SternBrocotMarkov

/-!
# The unimodular invariant — one `det = 1` drives the Stern-Brocot tree and the Markov recurrence

The Farey / Stern-Brocot mediant tree (continued-fraction approximation) and the Markov
triple recurrence (the Markov/Hurwitz Diophantine spectrum) are two different domains. This
file proves they are driven by **one** invariant: `det₂ = 1` (the `SL₂(ℤ)` unimodularity),
propagated by the single multiplicative law `det2_mul` (`det(MN) = det M · det N`, a pure
`ℤ` polynomial identity, not `decide`).

  · the invariant **propagates over the whole tree**: every node matrix `M_t = M_l·M_r` is
    unimodular (`mNode_det1`, from `det2_mul` and the det-1 generators);
  · the invariant **forces the Markov structure** at every node: `det M = 1` is exactly the
    hypothesis of Frobenius's cross-determinant identity (the slope-monotonicity /
    residue-injectivity engine) and of the Cayley–Hamilton Vieta recurrence (the Markov jump
    `m' = 3m₁m₂ − m₃`).

So the capstone below is not a coincidence of two facts: both readings are *consequences of
the same `det₂ = 1`*, which is itself the `det2_mul` law applied to the unimodular
generators. This is the operational content of "one residue, many readings"
(`seed/AXIOM/05_no_exterior.md` §5.1) for the unimodular invariant — a proven shared engine,
not a value-coincidence (cf. the retracted byte-identity entries in
`catalogs/cross-domain-identifications.md`).

Companion essay: `theory/essays/synthesis/unimodular_invariant.md`.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Markov.UnimodularSynthesis

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic (Mat2 mul)
open E213.Lib.Math.NumberSystems.Real213.Markov.SternBrocotMarkov
  (det2 mInterval mNode mInterval_det mNode_det1 markoff_frobenius markoff_vieta)

/-- ★★★ **One unimodular invariant, two domains.**  At every Stern-Brocot path the node
    matrix carries the *same* `det₂ = 1`, and that invariant simultaneously drives the
    Farey/Stern-Brocot tree and the Markov recurrence:

      1. **unimodularity** — `det₂(M_t) = 1` (the Farey-interval det-1 invariant, propagated
         over the whole tree by `det2_mul`);
      2. **Frobenius monotonicity** — the cross-determinant of the node against its left bound
         is the right bound's `c`-entry `m_s` (Zhang's Lemma 2 / slope strictly monotone /
         residue injectivity), forced by `det M_l = 1`;
      3. **Vieta jump** — the left-child mediant's `c`-entry satisfies the Cayley–Hamilton
         recurrence `tr(M_l)·(M_t)_c − (M_r)_c` (the Markov equation jump `m' = 3m₁m₂ − m₃`),
         forced by `det M_l = 1`.

    All three are consequences of one `det₂ = 1`; the invariant is the engine, the two
    domains its readings. ∅-axiom. -/
theorem unimodular_drives_tree_and_markov (path : List Bool) :
    det2 (mNode path) = 1
    ∧ (mInterval path).1.a * (mNode path).c - (mInterval path).1.c * (mNode path).a
        = (mInterval path).2.c
    ∧ (mul (mInterval path).1 (mNode path)).c
        = ((mInterval path).1.a + (mInterval path).1.d) * (mNode path).c
            - (mInterval path).2.c :=
  ⟨mNode_det1 path,
   markoff_frobenius (mInterval path).1 (mInterval path).2 (mInterval_det path).1,
   markoff_vieta (mInterval path).1 (mInterval path).2 (mInterval_det path).1⟩

end E213.Lib.Math.NumberSystems.Real213.Markov.UnimodularSynthesis
