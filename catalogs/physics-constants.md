# Physics Constants Catalog

213 atomic chain of standard physical constants.

> **Reading this catalog honestly** (per `research-notes/frontiers/headline_precision_scope.md`
> + `README.md` headline table): the precision tags below (`0.000%`, `ppb`, `%`)
> are **central-value agreements**, often computed in the Lean *docstring*; the
> corresponding **PURE theorem** typically proves a coarser *bracket* (0.1%–ppm)
> or the clean dimensionless ratio. **Dimensionless ratios** (Koide `NT/NS`,
> `m_H/v_H = 1/c`, `m_μ/m_e`, `α_em`) are parameter-free DRLT content;
> **absolute** masses/energies (`m_p` via `Λ_QCD≈308 MeV`, `m_H` via `v_H`,
> `IE(H)` via CODATA `m_e`) rest on an **input scale**, as any theory does. The
> ratio is the prediction; the absolute = ratio × measured scale.

## Coupling

  α_em ≈ 1/137.036  (Phase 1, ppm)
  α_GUT = 6/(d²·π²) = 6/(25·π²) atomic
  α_3 = 1/(NS²-1) = 1/8 atomic-locked
  α_2 = 1/30 = 1/(NS·NT·d) atomic
  α_1 (Y) = atomic chain

## Mass

  m_e        Phase 1 chain via m_p
  m_p = 938.27 MeV  (NS·Λ_QCD·P, 0.000%)
  m_μ/m_e = 206.768  (NS·137/NT, 0.48 ppb)
  m_τ/m_μ ≈ 17 = NS²+(NS²-1)
  m_H = 125.28 GeV  (1/c · v_H, +0.02%)
  m_t/m_c ≈ 137  (atomic match)

## Lifetime / decay

  Muon lifetime prefactor 192 = (NS²-1)(d²-1)
  Z partial widths = 2·NS·NT = 12

## Cosmology

  Ω_Λ = 0.685  ((1-1/π)(1+α/d), 0.0008%)
  η_B ≈ 6×10⁻¹⁰  (atomic chain, 0.5%)
  e-folds N ≈ 60 = d²·NT + d·NT atomic

## Other

  R∞ = 13.605693 eV  (Phase 4 H 4.3 ppb)
  v_H ≈ 245.6 GeV  (electroweak)
  M_Pl/v_H = d^(d²)/(d+1) atomic
  log₁₀(E_Pl) ≈ 19 = NS³ - NT³

## Mixing

  Cabibbo λ = 5/22 = d/(d²-NS) atomic
  PMNS θ_12 leading = 1/NS
  PMNS θ_23 leading = 1/NT
  δ_CP = 195° = 180 + 360/24

## Usage

```lean
import E213.Lib.Physics.Library.CouplingLibrary
import E213.Lib.Physics.Library.PMNSLibrary
import E213.Lib.Physics.Library.CKMLibrary
```

## Quantum-info atomic readouts (Phase 3, blueprint 12)

```lean
import E213.Lib.Physics.Quantum.Qubit       -- NT = 2 state count
import E213.Lib.Physics.Quantum.Bell        -- CHSH ≤ 2·NS·NT = 12
import E213.Lib.Physics.Quantum.Bekenstein  -- S_BH ∝ 1/(d-1) = 1/4
```

Closes the previously 0% Lean coverage of blueprint 12.  All
PURE.  The integers 4 = NS+1 = d-1 (Bekenstein), 6 = NS·NT
(qubit pairs), 12 = 2·NS·NT (Bell, α_1, α_2) are cross-referenced
in `catalogs/atomic-integers.md`.

## DRLT Validation Standard — paired observables (Phase 6)

All 23 observables in this file now have BOTH a PURE precision
theorem AND a PURE falsifier bracket.  The previous 6 "remaining"
constants have been closed:

| Observable | Falsifier theorem | File |
|---|---|---|
| Koide Q = 2/3 | `koide_falsifier` (F21) | `KoideFormula.lean` |
| m_p/m_e ≈ 6π⁵ | `proton_electron_falsifier` (F22) | `ProtonElectronRatio.lean` |
| M_Pl/v_H | `hierarchy_falsifier` (F23) | `HierarchyTowers.lean` + `Vacuum.lean` |
| Muon prefactor 192 | `muon_prefactor_falsifier` (F24) | `AtomicSuperCatalog.lean` |
| m_t/m_c ≈ 137 | `quark_hierarchy_capstone` (F25) | `QuarkHierarchy.lean` |
| η_B ≈ 6×10⁻¹⁰ | `eta_B_falsifier_bracket` (F26) | `EtaBFalsifier.lean` |

See `catalogs/falsifiers.md` F1–F26 for the complete falsifier
registry.  23/23 paired — **100% coverage**.
