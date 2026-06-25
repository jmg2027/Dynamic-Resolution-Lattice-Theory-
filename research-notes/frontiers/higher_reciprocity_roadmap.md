# Higher-reciprocity tower — roadmap (L2 of the number-theory rebuild)

> Milestone plan.  This is the *open-frontier* map for the higher-reciprocity branch of the
> ∅-axiom number-theory rebuild (CLAUDE.md §7.1: primacy = breadth of derivation; rebuilding a
> discipline *is* the work).  Status markers are kept live here; closed pieces migrate to the
> module docstrings / `theory/`.

## Where this sits in the giant roadmap

```
L0  distinguishing / residue (∅-axiom)
     └ number systems ℕ, ℤ, ℚ, ℝ, ℤ[ω], ℤ[i]  as ⟨C|L⟩ ⊕ Residue reconstructions
L1  elementary number theory per carrier
     └ Nat213: Fermat · Euler · Wilson · QUADRATIC reciprocity        [DONE]
L2  higher-reciprocity tower            ← we are here
     ├ quadratic          (Nat213)                                    [DONE]
     ├ CUBIC              (ℤ[ω])   character substrate DONE; law open  ← current frontier
     ├ QUARTIC/biquadratic (ℤ[i])  parallel sibling of cubic
     └ … → general / Artin reciprocity                                [far end]
L3  endgame: the whole reciprocity tower as ONE ⟨C|L⟩ ⊕ Residue pattern
     = "number theory rebuilt from the residue" = primacy demonstration
```

Cubic and quartic are two **rungs of the same `(·/π)_n` pattern** — character → Jacobi sum → law —
differing only in the value group `μ_n` and the carrier (`ℤ[ω]` vs `ℤ[i]`).  The physics branch
(DRLT) consumes these via the carrier-readout; the laws themselves are pure breadth.

## Dependency analysis — what gates what

| piece | cubic | quartic | shared? |
|---|---|---|---|
| character substrate (`μ_n`, residue prime, Euler criterion) | **DONE** | cheap replay | ✗ parallel |
| **character *function* on `𝔽_p` + Jacobi sum `N(J)=p`** | open | open | ✅ **same engine** |
| law proper (`J = π` primary + transfer) | open | open | ✅ same argument |

- The **quartic substrate does not depend on the cubic law** — independent sibling, no new ideas.
- The real bottleneck both laws share is the **Jacobi-sum engine**.
- Correction to an earlier pessimism: `N(J)=p` does **not** need the cyclotomic field `ℤ[ζ_p]`.
  `J = Σ_t χ(t)χ(1−t)` lives in `ℤ[ω]`, and `J·J̄ = p` follows from a `𝔽_p` double-sum collapsed by
  **character orthogonality** (already built: `EisensteinCubicCharFunction.chiExp_sum`,
  `chiExp_sum_shift`, the Schur relations).  A big cyclotomic field may be needed only at the
  **final transfer step** of the law (Gauss-sum Galois action) — decide on arrival.

## Execution order:  A → B → C

### Phase A — the shared Jacobi-sum core (built on the cubic side)
- **A1.** the cubic character as a **function on `𝔽_p`**.  **[DONE — the `t^m` + residue-field-iso
  route, chosen over the dlog-index route since `dlog` is only existential.]**
  - `ModArith/CubicCharFp.lean` — `χ(t) := t^m % p`: cube-root-valued (`cubicChar_cube_one`,
    `χ(t)³≡1` by Fermat), multiplicative (`cubicChar_mul`), unit-valued (`cubicChar_unit`), trivial
    ⟺ cubic residue (`cubicChar_one_iff_cube`), and **`μ₃`-valued** (`cubicChar_trichotomy`:
    `χ(t) ∈ {1, x%p, (x·x)%p}`).
  - `ModArith/CubeRootsUnityModP.lean` — the field fact `cube_root_trichotomy`: for `p ∣ x²+x+1`,
    every `y³≡1 mod p` is in `{1, x, x²}` (cubic factorisation + Euclid `int_dvd_prime_mul`).
  - `…/Integer/EisensteinResidueFieldCubeRoots.lean` — the lift into `ℤ[ω]`: `cube_roots_rational`
    (`{1,ω,ω²} ≡ {1,x,x²} mod d`), `ofInt_natMod_modEq` (`% p` invisible mod `d`),
    `natMod_value_omega_power` (`ofInt ↑χ(t) ≡` one of `{1,ω,ω²}` mod `d`).
  - `…/Integer/EisensteinCubicCharFp.lean` — the **computable `χ_ω : ℕ → ℤ[ω]`** (the if-`{0,1,ω,ω²}`
    selector): `chiOmega_value` / `chiOmega_unit_value` (`μ₃`-valued), `chiOmega_lift`
    (`ofInt↑χ(t) ≡ χ_ω(t) mod d`), `chiOmega_mul_conj` (`χ_ω·conj χ_ω = 1`, the `|χ|=1` unit-norm).
  - `…/Integer/EisensteinCubicCharFpMul.lean` — **`χ_ω` multiplicativity** `chiOmega_mul`
    (`χ_ω(s)·χ_ω(t) = χ_ω(st)`, the keystone), via `mu3_mul_closed` (μ₃ closed under ·) + `mu3_inj`
    (`root_unique`, μ₃ distinct mod d for `p>3`); plus `mu3_sum_zero` (`1+ω+ω²=0`).
  - **A1 is COMPLETE** — `χ_ω` is a genuine multiplicative `μ₃`-valued character on `𝔽_p`.
- **A2.** the Jacobi sum `J(χ,χ) = Σ_t χ_ω(t)·χ_ω(1−t)` as a concrete finite `sumRange` over `ℤ[ω]`.
  **[DONE — `…/Integer/EisensteinJacobiSum.lean`]** `jacobiSum` indexed over `𝔽_p` (`(1−t)` written
  `(1+(p−t))%p`); `chiOmega_zero_of_dvd`, boundary terms `t=0,1` vanish (`jacobi_term_zero/one`).
- **A3.** `N(J) = J·J̄ = p` — the double sum collapsed by orthogonality / translation invariance.
  ← **current frontier.**  **Character-orthogonality engine COMPLETE** (this session):
  - **`Σ_t χ_ω(t) = 0` DONE, unconditional** — `EisensteinCharSumZero.chiListSum_totatives_zero`.  The
    `sumRange`-permutation problem was solved by routing through the existing **`LPerm`** list-permutation
    infra (`EulerTheorem.lperm_image` — the unit-multiplication map permutes `totativeList p`) with a
    `ZOmega` list-sum `chiListSum` proved `LPerm`-invariant (`chiListSum_lperm`), scaling-factored
    (`chiListSum_map_factor` via `chiOmega_mul`), and a primitive-root non-residue (`chiOmega_ne_one`).
  - **Endgame cancellation DONE** — `EisensteinScaleCancel.scale_fixed_eq_zero` (`w·S=S, w≠1 ⟹ S=0`
    via `ZOmegaDomain.no_zero_div` + `ext`/`ring_intZ` right-distributivity `sub_mul_zomega`).
  - **Remaining: the `J·J̄ = p` double sum.**  Substrate **DONE** — `EisensteinListSum` (generic
    `listSum f L`, `listSum_mul_distrib`: `(Σ_L f)(Σ_M g) = Σ_s Σ_t f s·g t`, plus perm/linearity/map).
    Concrete sub-plan (the next builds):
    1. **`jacobiList` DONE** (`EisensteinJacobiNorm`) — `J = listSum (χ_ω(a)·χ_ω((1−a)%p)) (List.range p)`.
    2. **`jacobiList_conj` DONE** — `conj J = Σ χ̄_ω(a)·χ̄_ω(1−a)` (`conj_listSum` homomorphism + `conj_mul`).
    3. **`jacobiList_norm_double` DONE** — `J·J̄ = Σ_a Σ_b (χ_ω(a)χ_ω(1−a))·(χ̄_ω(b)χ̄_ω(1−b))`
       (`listSum_mul_distrib`).
    4. **reindex + collapse** (the hard core, NEXT) — for each fixed unit `b`, reindex the inner `a`-sum
       by `a = (b·c) mod p` (a unit-permutation of `List.range`, `lperm_image`-style); termwise
       `χ_ω(a)χ̄_ω(b) = χ_ω(c)` (`chiOmega_mul` + `chiOmega_mul_conj`).  The inner `Σ_c χ_ω(c)·χ_ω(1−bc)
       χ̄_ω(1−b)` splits into the `c` with `bc = 1` (diagonal, contributes the `p` count) and the rest,
       killed by `Σ_c χ_ω(c) = 0` (`chiListSum_totatives_zero`).  The `a,b ∈ {0,1}` boundary terms
       (where `χ_ω = 0`) are isolated first (`jacobi_term_zero/one`-style).  **This is the major
       remaining build** — comparable in size to the whole orthogonality engine.
    5. **`N(J) = p`** — assemble.  Then `J` primary ⟹ `J = π` (A4).
- **A4.** `J` primary normalisation → `J = π`.

### Phase B — the cubic law
- `(π/π')₃ = (π'/π)₃` from `J = π` + the transfer (determine here whether Gauss sums / `ℤ[ζ_p]`
  are genuinely required for the last step).

### Phase C — quartic / biquadratic (`ℤ[i]`)
- replay the substrate (`μ₄ = {1,i,−1,−i}`, residue prime, character, Euler criterion — fast, the
  Gaussian infrastructure `ZI`/`ZIUnits`/`ZIDomain` exists), then reuse the Phase-A/B engine with
  `μ₄` → the quartic law.  The cheap substrate part may be done early for breadth.

## Current status (this branch)
- Cubic **character substrate COMPLETE** (`Integer/Eisenstein*` cubic cluster, ~60 PURE theorems +
  2 allowed-`propext`; see `Integer/INDEX.md` "Cubic / Eisenstein reciprocity").
- Jacobi-sum substrate seeded: finite sums, `Σ_{j<3k} ωʲ = 0`, the character homomorphism `χ̂(i)=ωⁱ`,
  Schur relations, well-definedness in `μ₃`.
- **A1 DONE** — the cubic character on `𝔽_p`: `μ₃`-valued, **multiplicative** (`chiOmega_mul`), lifted
  into `ℤ[ω]/(d)` (`CubicCharFp`, `CubeRootsUnityModP`, `EisensteinResidueFieldCubeRoots`,
  `EisensteinCubicCharFp`, `EisensteinCubicCharFpMul`).
- **A2 DONE** — the Jacobi sum `jacobiSum` as a concrete `sumRange` over `ℤ[ω]`
  (`EisensteinJacobiSum`).
- **Next concrete step: A3** — `N(J)=p`, blocked on a `sumRange` permutation-reindexing lemma (the
  `𝔽_p` character-sum `Σχ_ω=0`) + the domain cancellation.  See the A3 entry above.
