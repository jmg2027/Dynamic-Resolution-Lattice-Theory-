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
- **A1.** the cubic character as a **function on `𝔽_p`**: `χ(t) = ω^{ind_g(t)}` via the discrete log
  (reuse `ModArith` primitive-root + `dlog`).  ← the hard core; the ZOmega-`decide` decidability
  choice is made here (index-function route vs `t^m` + residue-field iso).
- **A2.** the Jacobi sum `J(χ,χ) = Σ_t χ(t)χ(1−t)` as a concrete finite `sumRange`.
- **A3.** `N(J) = J·J̄ = p` — the double sum collapsed by orthogonality / translation invariance.
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
- **Next concrete step: A1** — the character function on `𝔽_p`.
