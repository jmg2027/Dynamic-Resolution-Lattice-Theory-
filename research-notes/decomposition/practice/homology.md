# Decomposition: the boundary operator ∂ / δ, and ∂² = 0 (homology)

*213-decomposition per `../README.md` (model v3). Tests the hypothesis: **∂ is a
height-LOWERING reading, dual to the height-RAISING distinguishing of
`dimension.md`; its sign IS the direction-axis of `C`; and `∂²=0` is a
residue/character fact — distinguishing the boundary twice cancels because the
orientation bits cancel in pairs.** Homology = ker∂/im∂ = the residue of the
boundary-reading.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **simplex** = the same nesting `dimension.md` reads for
  height: an `n`-cell is `n+1` distinguished vertices, the build-tree of
  iterated distinguishing. Its faces are the *sub-builds* — the `(k+1)`-subsets
  that are one distinguishing shallower. In Lean a `k`-cochain is the indicator
  on `k`-subsets, `Cochain n k` (`Cochain/Core.lean`), and the face structure is
  the binomial face table `binom d k` (`Physics/Simplex/FaceTerms.lean :
  simplex_face_counts` = `1,5,10,10,5,1` on Δ⁴). `C` carries **both** of the
  README's read-off axes here: a **fold-height** (the cell dimension `k`) and a
  **direction / orientation bit** (the vertex ordering — which face was removed,
  with what sign).

- **Reading `L↓` (the boundary-reading)** — project a cell to **its faces with
  alternating orientation**: `∂σ(τ) = Σ_i (−1)^i σ(τ \ {τ[i]})`. This is the
  *mirror* of `dimension.md`'s height-raising distinguishing: one distinguishing
  *adds* a unit of height (`Raw.depth_slash`); the boundary-reading *peels* one
  unit, sending `Cᵏ → Cᵏ⁺¹` along the face-removal that drops cell-dimension by
  one. Lean shadow: `delta : Cochain n k → Cochain n (k+1)`
  (`Delta/Core.lean : delta`, `deltaAt`), the XOR-fold over the `k+1` faces
  `τ.eraseIdx i`. The **orientation/sign** is the explicit `(−1)^i`: in mod-2
  it collapses to XOR (Bool), and the *genuine* signed form lives in
  `Cup/SignedCup.lean`'s `negPow (inv S T) = (−1)^{inv}` — the README's
  **direction sub-readout** of `C`, restored as an honest `ℤ` sign.

- **Residue** — `L↓` is many-to-one *and* has a kernel/image gap, and **that gap
  IS homology**: `H = ker ∂ / im ∂` = the part of `ker ∂` the reading forces
  (closed) but cannot fill from one level down (exact). Lean shadow:
  `Examples/BettiKernel.lean : kerSizeDelta` (size of `ker δ`),
  `reduced_betti_d4_contractible` (`|ker δ₀|=1`, `|ker δ₁|=2` ⇒ reduced Betti
  `b̃₀=b̃₁=0` on the contractible Δ⁴: ker = im, residue empty). Homology is
  precisely the boundary-reading's surplus — exactly the README's "what `L`
  forces but cannot capture," here at the cochain level.

## Re-seeing (⟨C | L⟩)

```
   ∂ / δ            =  ⟨ simplex (a nesting) | L↓ = the alternating face-reading ⟩
   "drops dimension by one"  =  L↓ is the MIRROR of dimension.md's L↑ (one peel = −1 to height)
   "the sign (−1)^i"         =  the orientation bit of C, read out by ∂  (SignedCup.negPow = (−1)^inv)
   "∂² = 0"                  =  each codim-2 face is removed by TWO orders → its two signs cancel
   "homology = ker∂/im∂"     =  Residue(L↓, C):  closed-not-exact = the boundary-reading's surplus
```

Set side-by-side with `dimension.md` and `determinant.md`, the three are one
triangle on `C`'s two read-off axes:

| reading | axis of `C` consumed | readout |
|---|---|---|
| `L↑` dimension (`dimension.md`) | **height** (raise +1) | dimension / degree / pole-order |
| `det` (`determinant.md`) | **direction** (sign) | orientation scalar `±1`/`ℤ` |
| **`L↓` boundary (here)** | **height (lower −1) ⊗ direction (sign)** | faces with orientation; residue = homology |

∂ is the *only* one of the three that consumes **both** axes at once — height to
move between levels, direction to sign the faces. That is why its residue
(homology) is richer than either alone.

## Revelation (∂²=0 as sign-cancellation / homology = the boundary-reading's residue)

**Forcing — `∂²=0` is the orientation bits cancelling in pairs, not an axiom.**
Apply `L↓` twice: `∂²σ(ρ)` for a codim-2 face `ρ` collects each codim-2 sub-face
*exactly twice* — once by removing vertex `i` then `j`, once by removing `j` then
`i` — with **opposite orientation signs**. The two equal magnitudes with
opposite direction-bits annihilate, so `∂²=0` *for every* cochain. This is
`determinant.md`'s `q=±1` orientation cancellation acting at the level of the
complex: the swap of removal-order is the same pair-swap that flips `det`'s sign
and produces ℤ's `−`. In mod-2 the cancellation is visible as XOR of two equal
Bool values = `false` — verified universally on Δ⁴ at every interior stratum:
`Delta/V4Capstone.lean : dsq_zero_universal_delta4` (`∀ σ, ∀ i, δ(δσ) i = false`
at `(5,1),(5,2),(5,3)`), backed by `Universal.Prop5{1,2,3}.dsq_zero_prop_5_k`.
The signed ℤ version of *why* it cancels is `Cup/SignedCup.lean :
cup1_antisymmetric` / `mergeSign = (−1)^inv`: swapping order flips the sign, so
the double-count sums to zero. **`∂²=0` is the README's `q=±1` direction-bit
cancelling — the same residue-sign that gives Cassini's period-2 alternation and
det's sign.** The companion alternating-sum-cancels fact is
`FaceTerms.simplex_face_euler_zero` (`Σ (−1)^k binom d k = 0`): the Euler
characteristic vanishes by the *same* sign pairing, one dimension up.

**Residue surfaced — homology IS `Residue(L↓, C)`.** ker∂ (closed cochains) is
what the boundary-reading *forces*; im∂ (exact cochains) is what it can *fill*
from one level down; the quotient `H = ker/im` is exactly "forced but not
captured" — the README's residue, now at the cochain level rather than the
number level. `BettiKernel.reduced_betti_d4_contractible` makes this concrete:
on the contractible Δ⁴, `ker = im` and the residue is empty (`b̃ = 0`) — no
homology because the simplex has no un-fillable closed cycle. The same `L↓` on a
non-contractible build would leave a nonzero residue; that nonzero surplus is
the homology class. So "homology group" stops being a separate object and
becomes *the surplus of one reading*, exactly as "irrational"/"infinite" became
shapes of a reading's surplus in earlier batches.

**Collapse — `∂` (drop), `det` (sign), `dimension` (raise) are one structure read
on `C`'s two axes.** The boundary-reading is the height-axis run *downward* with
the direction-axis switched *on*; dimension is the height-axis read as a count;
det is the direction-axis read as a scalar. `∂²=0` is what forces these to be one
family rather than three: it is *both* a height fact (peel twice = go down two,
through every intermediate face twice) *and* a direction fact (the two passages
carry opposite signs). The Hodge involution `⋆⋆ = id`
(`Hodge/InvolutionLifts.lean : hodge_involution_5strata_capstone`,
`hodge_involution_universal_delta4`) is the same direction-bit applied to the
*complementary* face `e_{compᵢ}` with sign `(−1)^i` — `⋆` is `q=−1` applied once
(an involution: `q² = +1`), the dual partner of `∂`'s pairwise `q=−1`
cancellation. Graded-commutativity of the cup (`CupPairing.cup_symm`,
`cup_symm_pointwise`) and the Leibniz rule `δ(α⌣β) = δα⌣β ⊕ α⌣δβ`
(`V4Capstone.leibniz_universal_delta4`) are the *same* orientation sign threading
the product — one direction-bit, three operators (∂, ⋆, ⌣).

## Note for the technique

- **Does ∂ confirm a HEIGHT-LOWERING reading dual to the distinguishing? YES —
  and it is the *mirror*, not a new axis.** `dimension.md` established
  height-raising (`+1` per distinguishing, `Raw.depth_slash`); ∂ is that same
  height-axis traversed **down one rung** (`Cᵏ → Cᵏ⁺¹` peels a face = drops cell
  dimension by one). No new primitive: the height axis was already in `C`
  (`isPart_wf`, the well-founded measure); ∂ just reads it in the descending
  direction. This *closes* a symmetry the README only half-stated — the
  height axis is **bidirectional**, exactly as the README found character-mode to
  be bidirectional (valuation ↔ exp). So: **fold-height is bidirectional**, and
  ∂/δ is its downward reading.

- **Does ∂²=0 tie to the q=±1 / direction bit? YES — it is the cleanest instance
  yet.** `∂²=0` holds *because* the order-swap of two face-removals is the README's
  swap-bit, contributing opposite signs `q=−1` that cancel in pairs. This is
  literally `determinant.md`'s `q=±1` orientation residue and `integers.md`'s
  pair-swap sign, now operating on the complex. The Lean witness in mod-2
  (`dsq_zero_universal_delta4`) shows the cancellation as XOR-of-equals; the
  signed-ℤ *reason* is `SignedCup.cup1_antisymmetric`/`negPow`. So `∂²=0` is **not
  a fourth thing** — it is the direction-bit's pairwise cancellation, the `q=−1`
  pole of the residue tag.

- **Is "nilpotent reading" a new pattern, or character + direction?** It is
  **character + direction, not new.** A nilpotent reading (`∂²=0`, and dually the
  involution `⋆²=+id`) is exactly a *height-traversing* reading whose
  direction-bit sign forces the two-step composite to annihilate (`q=−1`,
  nilpotent) or to return (`q=+1`, involutive). Nilpotency and involution are the
  **two poles of the README's `q=±1` residue tag applied to a two-step
  composite**: `q=−1` per swap ⇒ `(q)·(q) = +1` returns for ⋆ (one swap, squared)
  but the *pair-cancellation* across two distinct removal-orders gives `0` for ∂.
  So the calculus needs no "nilpotent" primitive; ∂²=0 and ⋆⋆=id are one
  direction-bit read at a two-step composite. Suggested sharpening to the map:
  **height is a bidirectional axis (∂ = down, distinguishing = up); the direction
  bit governs how two-step composites close — `0` (nilpotent, pair-cancel) or
  `id` (involutive)**.

---

### Verified Lean anchors (file : theorem)

- `Lib/Math/Cohomology/Delta/Core.lean` : `delta`, `deltaAt`, `subsetIdx`
  (the boundary/coboundary reading `Cᵏ → Cᵏ⁺¹`)
- `Lib/Math/Cohomology/Delta/SqZero.lean` : `phase_CA_delta_sq_zero`,
  `delta_sq_vertex0_n5`, `delta_sq_edge01_n5` (∂²=0 at concrete cochains)
- `Lib/Math/Cohomology/Delta/V4Capstone.lean` : `dsq_zero_universal_delta4`
  (**universal** ∂²=0 on Δ⁴, `∀ σ`), `delta4_cohomology_capstone`,
  `hodge_involution_universal_delta4`, `leibniz_universal_delta4`
- `Lib/Math/Cohomology/Cup/SignedCup.lean` : `mergeSign` = `(−1)^inv`, `negPow`,
  `cup1_antisymmetric`, `signed_cup_capstone` (the orientation sign `∂` carries —
  the direction bit; antisymmetry = order-swap flips sign)
- `Lib/Math/Cohomology/Examples/BettiKernel.lean` : `kerSizeDelta`,
  `kerSize_5_0`, `kerSize_5_1`, `reduced_betti_d4_contractible`
  (homology = ker∂/im∂ as the reading's residue; Δ⁴ contractible ⇒ residue empty)
- `Lib/Math/Cohomology/Hodge/InvolutionLifts.lean` :
  `hodge_involution_5strata_capstone` (⋆⋆ = id — the direction-bit's involutive
  pole, dual to ∂'s nilpotent pole)
- `Lib/Math/Cohomology/Surfaces/T2Minimal/CupPairing.lean` : `cup_symm`,
  `cup_symm_pointwise` (graded-commutativity = the same orientation sign on ⌣)
- `Lib/Physics/Simplex/FaceTerms.lean` : `simplex_face_counts` (the face/height
  table ∂ traverses), `simplex_face_euler_zero` (`Σ(−1)^k binom = 0`, the
  one-up sign cancellation)
- cross-frame: `determinant.md` (`q=±1`, `det_step`/`cassini_law...`),
  `dimension.md` (height-raising `L↑`, `Raw.depth_slash`, `isPart_wf`)
