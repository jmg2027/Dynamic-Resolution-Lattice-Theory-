# Padic — sub-tree INDEX

Real213-p-adic construction: ∅-axiom p-adic integers `ℤ_p` (`ZpSeq p`)
and p-adic numbers `ℚ_p` (`QpSeq`) via carry-propagation FSM.

**Status**: CLOSED — 27 files, ~500 PURE declarations.
All phases (1–6) complete.  Promoted chapter: `theory/math/padic_real213.md`.

## File map

| File | Phase | Decls | Content |
|---|---|---|---|
| `Foundation.lean` | 1 | 41 | `ZpDigit`, `ZpSeq`, `trunc`, `zero`/`one`/`neg_one`, `eq_mod_pn`, `trunc_lt_p_pow`, `digits_of_nat` |
| `Arith.lean` | 2 | 110 | `Zp.add`/`mul`/`neg` via carry FSM, ring axioms at trunc (comm/assoc/distrib/add-inverse), `neg_one_sq_trunc` (`(−1)²≡1`); `shiftLeft`/`shiftRight` + factorisation exactness `shiftLeft_shiftRight_trunc_of_low_zero` |
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
| `Teichmuller.lean` | 4 | 13 | Frobenius lift, `teichmuller_iter_cauchy`, geometric sum; explicit representative `teichmuller` (`ω(x)`, diagonal limit), Frobenius fix `teichmuller_pow_p_trunc` (`ω^p ≡ ω`) |
| `TeichmullerUnit.lean` | 4 | 7 | `ω(x)` as `(p−1)`-th root of unity (`teichmuller_pow_pred_trunc`); principal-unit decomposition `x = ω·u` (`teichmullerCofactor`, `u ≡ 1 mod p`) — the `ℤ_p^× ≃ μ_{p−1} × (1+p·ℤ_p)` split; concrete `i₅ ∈ μ₄` (`i_5_pow_four_trunc`) |
| `Field.lean` | 5 | 48 | `QpSeq` (ℚ_p): add/sub/mul/neg/inv/div/sqrt; general division `invGeneral`/`divGeneral` (non-unit denominator via valuation shift, reduces to `inv`/`div` at v=0) |
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
   ├── Arith ─── Pow ─── Teichmuller ─── TeichmullerUnit (+ Hensel)
   │     └── NegInvolution{,Digit1,Full,Preserve}
   │     └── SetoidFramework ─── SetoidAssoc ─── SetoidAlgebra
   ├── Norm ─── Valuation
   ├── Hensel{,Bridge,Residual}
   ├── Field (= ℚ_p)
   ├── DRLT ─── DRLTIntegration
   ├── ZpSqrtD{,Ring,Setoid,Frob,FrobRigor,Rigor}
   └── ZpSeqMobiusBridge (+ SternBrocot)
```

All under namespace `E213.Lib.Math.NumberSystems.Padic.*`.

## Cross-references

  · Theory chapter: `theory/math/padic_real213.md` (308 PURE as counted
    for the chapter; 462 total including extensions and bridge)
  · Möbius bridge: `theory/math/mobius213_p_orbit_closure.md` §"p-adic
    Lens family as mod-p arena"
  · Lean bridge file: `ZpSeqMobiusBridge.lean` — Möbius-pair agreement ↔
    `ZpSeqEquiv` bidirectional

## Open frontier

  · ~~Teichmüller representative as concrete `ZpSeq`~~ — **closed**
    (`Teichmuller.teichmuller`, diagonal limit)
  · ~~`ℤ_p^× ≃ μ_{p−1} × (1 + p·ℤ_p)`~~ — **closed at trunc level**
    (`TeichmullerUnit`: `teichmuller_pow_pred_trunc` + `teichmullerCofactor`).
    Remaining: the full sequence-level group isomorphism (uniqueness of
    the `ω·u` factorisation as `ZpSeq`).
  · ~~General division (non-unit denominator) → `QpSeq`~~ — **closed**
    (`Field.invGeneral`/`divGeneral`; `Arith.shiftRight` + factorisation
    exactness `shiftLeft_shiftRight_digit_of_low_zero`)
  · DRLT-specific 5-adic content (H) — terrain mapped: `5²⁵`-resolution
    removed, `i₅`/L-value physics readings have no internal handle (no
    forcible map); pure-math `i₅ ∈ μ₄` closed.  Any future H is
    arithmetic-first; tracked in `research-notes/frontiers/`.
