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
  - **Remaining A1 polish (optional):** package a single computable `χ_ω : ℕ → ℤ[ω]` (the if-`{0,1,ω,ω²}`
    selector) with multiplicativity transferred from `cubicChar_mul` via residue-field injectivity
    (`EisensteinCubicCharWelldef.root_unique`, `p>3`).  Not blocking A2/A3.
- **A2.** the Jacobi sum `J(χ,χ) = Σ_t χ(t)χ(1−t)` as a concrete finite `sumRange` over `ℤ[ω]`.
  Indexed over `𝔽_p` residues (with `χ_ω(0)=0`), built on `EisensteinFiniteSum.sumRange`.  ← **next.**
- **A3.** `N(J) = J·J̄ = p` — the double sum collapsed by orthogonality / translation invariance.
  The hard analytic core.  Components in hand: `EisensteinCubicCharFunction.chiExp_sum` /
  `chiExp_sum_shift` (exponent-side `Σχ=0`), `CyclicCharacterOrthogonality.cyclic_orthogonality_modp`
  (`Σ_{k<n} ωᵏ ≡ 0` in `ℤ/p`).  Gap: the **`𝔽_p`-residue-indexed** `Σ_{t} χ(t) = 0` (scaling-
  invariance `Σχ(t)=Σχ(at)=χ(a)Σχ(t)` over the unit-permutation `t↦at`), then the `J·J̄` double-sum.
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
- **A1 DONE** — the cubic character as a function on `𝔽_p`, `μ₃`-valued, multiplicative, lifted into
  `ℤ[ω]/(d)` (`CubicCharFp`, `CubeRootsUnityModP`, `EisensteinResidueFieldCubeRoots`).
- **Next concrete step: A2** — the Jacobi sum `Σ_t χ(t)χ(1−t)` as a concrete `sumRange` over `ℤ[ω]`.
