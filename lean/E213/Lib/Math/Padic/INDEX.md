# Padic — sub-tree INDEX

Real213-p-adic construction: ∅-axiom p-adic integers `ℤ_p` (`ZpSeq p`)
and p-adic numbers `ℚ_p` (`QpSeq`) via carry-propagation FSM.

**Status**: CLOSED — 26 files, ~462 PURE declarations.
All phases (1–6) complete.  Promoted chapter: `theory/math/padic_real213.md`.

## File map

| File | Phase | Decls | Content |
|---|---|---|---|
| `Foundation.lean` | 1 | 41 | `ZpDigit`, `ZpSeq`, `trunc`, `zero`/`one`/`neg_one`, `eq_mod_pn`, `trunc_lt_p_pow`, `digits_of_nat` |
| `Arith.lean` | 2 | 104 | `Zp.add`/`mul`/`neg` via carry FSM, ring axioms at trunc (comm/assoc/distrib/add-inverse), `shiftLeft` |
| `Pow.lean` | 2+ | 18 | `Zp.pow`, `pow_trunc`, Fermat at digit 0, `teichmuller_iter` |
| `Norm.lean` | 3 | 21 | `valAtLeast`/`valEq`, strong ultrametric (`valEq_add_of_lt`, `valEq_mul`, `valEq_neg`) |
| `Valuation.lean` | 3 | 11 | `vAt` bounded valuation + characterization lemmas |
| `Hensel.lean` | 4 | 71 | Inverse (`invFull`) + square root (`sqrtFull`) + uniqueness; concrete `i_5`, `i_13`, `√2 ∈ ℤ_7` |
| `HenselBridge.lean` | 4 | 8 | Bridge lemmas connecting Hensel to ring arithmetic |
| `HenselResidual.lean` | 4 | 6 | Residual digit-level Hensel refinements |
| `NegInvolution.lean` | 4 | 5 | `neg (neg x) = x` at trunc level |
| `NegInvolutionDigit1.lean` | 4 | 11 | Negation involution at digit 1 |
| `NegInvolutionFull.lean` | 4 | 5 | Full negation involution |
| `NegInvolutionPreserve.lean` | 4 | 4 | Negation preservation lemmas |
| `SetoidFramework.lean` | 4 | 12 | `ZpSeqEquiv` setoid + reflexivity/symmetry/transitivity |
| `SetoidAssoc.lean` | 4 | 8 | Ring operation associativity under setoid |
| `SetoidAlgebra.lean` | 4 | 8 | Algebraic structure under setoid equivalence |
| `Teichmuller.lean` | 4 | 7 | Frobenius lift, `teichmuller_iter_cauchy`, geometric sum |
| `Field.lean` | 5 | 40 | `QpSeq` (ℚ_p): add/sub/mul/neg/inv/div/sqrt |
| `DRLT.lean` | 6 | 4 | `canonical_5adic_p` (= 5), digit smokes |
| `DRLTIntegration.lean` | 6 | 6 | 5-adic ↔ configCount: `trunc_25_lt_config2` + bridge bundle |
| `ZpSqrtD.lean` | ext | 13 | `ℤ_p[√d]` quadratic extension |
| `ZpSqrtDRing.lean` | ext | 8 | Ring structure on `ℤ_p[√d]` |
| `ZpSqrtDSetoid.lean` | ext | 11 | Setoid on `ℤ_p[√d]` |
| `ZpSqrtDFrob.lean` | ext | 8 | Frobenius on quadratic extension |
| `ZpSqrtDFrobRigor.lean` | ext | 6 | Rigorous Frobenius bounds |
| `ZpSqrtDRigor.lean` | ext | 8 | Rigorous quadratic extension lemmas |
| `ZpSeqMobiusBridge.lean` | bridge | 9 | Möbius-pair ↔ pointwise equality (Stern-Brocot tight) |

## Dependency chain (core)

```
Foundation
   ├── Arith ─── Pow ─── Teichmuller
   │     └── NegInvolution{,Digit1,Full,Preserve}
   │     └── SetoidFramework ─── SetoidAssoc ─── SetoidAlgebra
   ├── Norm ─── Valuation
   ├── Hensel{,Bridge,Residual}
   ├── Field (= ℚ_p)
   ├── DRLT ─── DRLTIntegration
   ├── ZpSqrtD{,Ring,Setoid,Frob,FrobRigor,Rigor}
   └── ZpSeqMobiusBridge (+ SternBrocot)
```

All under namespace `E213.Lib.Math.Padic.*`.

## Cross-references

  · Theory chapter: `theory/math/padic_real213.md` (308 PURE as counted
    for the chapter; 462 total including extensions and bridge)
  · Möbius bridge: `theory/math/mobius213_p_orbit_closure.md` §"p-adic
    Lens family as mod-p arena"
  · Lean bridge file: `ZpSeqMobiusBridge.lean` — Möbius-pair agreement ↔
    `ZpSeqEquiv` bidirectional

## Open frontier

  · Teichmüller representative as concrete `ZpSeq` (diagonal
    stabilization, analog of `sqrtFull`)
  · `ℤ_p^× ≃ μ_{p−1} × (1 + p·ℤ_p)` structural isomorphism
  · Lift DRLT precision-bounded results to 5-adic analogues
