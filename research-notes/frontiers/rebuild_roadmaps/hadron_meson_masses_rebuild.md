# Genuine hadron / meson mass rebuild — dimensionless ratios, honest scale

**Status**: OPEN (rebuild roadmap). **Domain**: physics (DRLT branch).
**Template**: `research-notes/frontiers/genuine_hodge_rebuild.md` (honesty tone).
Covers `m_p` (the `93827=93827` deletion), `m_π`, `m_ρ`, `m_ω`, `m_J/ψ`, Δ-N.

## 1 — What was deflated, and the bogus mechanism

The deleted `m_p` headline typed the PDG proton mass as a `def` and matched it
against itself:

> `(93827 : Nat) = 93827` → "0.000% match m_p" / "1.56 ppm"

i.e. the "prediction" `938.27 MeV` was a **hand-typed literal compared to the
same literal** (`93827` in 0.01 MeV units), then `decide`d.  No scale, no chain,
no π entered.  The audit removed it; `ProtonMass.lean` now proves only genuine
integer atomic readings and says so:

> "the all-literal m_p brackets and the '0.000%' claim were removed (they
> bracketed a hand-typed literal 93827 against literal bounds, not a measured
> input)."

The meson masses (`Masses.lean`) carried the same shape in their docstrings —
"DRLT 137.6 MeV vs PDG 137.3 MeV" (m_π), "DRLT 782.1 vs 782.7" (m_ρ), "DRLT
3081.6 vs 3096.9" (m_J/ψ) — all **informal off-Lean estimates**; the file's
theorem (`hadron_simplicial_pattern`) proves only `decide`d integer identities
(`NS²=9`, `d/NT=5/2`, the cross-mults).  The absolute MeV numbers never appear
as Lean terms.

## 2 — The genuine targets

- **Absolute masses** (PDG): `m_p = 938.272 MeV`, `m_π± = 139.570 MeV`,
  `m_ρ = 775.26 MeV`, `m_ω = 782.66 MeV`, `m_J/ψ = 3096.9 MeV`.
- **213 forms** (from `ProtonMass.lean` / `Masses.lean` docstrings):
  - `m_p = NS·Λ_QCD·P(α_GUT·NS/d)`, `P(x)=(1+2x)/(1+x)` — Dyson-resummed.
  - GMOR `m_PS² = NS²·(m_q1+m_q2)·Λ_QCD`, prefactor `n_eff = NS² = 9`.
  - hyperfine `Δ = d·Λ_QCD/NT`, ratio `d/NT = 5/2`.
- **The honest dimensionless content**: every absolute mass = (atom-derived
  dimensionless factor) × (a QCD scale `Λ_QCD`).  213 can compute the
  *dimensionless factor*; `Λ_QCD` is a **scale input** (`headline_precision_scope.md`
  notes `308.32 MeV` appears only in docstring prose — no Lean derives it).

## 3 — Why the current Lean fails to DERIVE them

- **`m_p`**: the chain `m_p = NS·Λ_QCD·P(x)` needs `Λ_QCD`, which is **not
  derived anywhere** (prose-referenced "QCD-scale chain", never located).  So
  the absolute `938.27` is unreachable from pure atoms — *as for any theory, you
  cannot get MeV from integers*.  What the Lean honestly has: `NS=3`, `d³=125`,
  `NS/d=3/5`, `NT²=4` — the dimensionless skeleton, plus `P(x)` factors `(2,1)`.
- **Mesons**: `m_π/m_ρ`, `m_ρ` etc. never computed; only `NS²=9`, `d/NT=5/2`
  proven.  The "137.6 vs 137.3" comparison is docstring arithmetic.
- π is absent throughout; no ζ bracket is applied; the Dyson `P(x)` is a `def`
  of integer factors `(2,1)`, never evaluated at a computed `x`.

## 4 — Staged plan: compute dimensionless ratios in a falsifier window

The honest move is to **drop the absolute-MeV claims** and compute
*dimensionless* ratios that need no scale, using the Dyson `P(x)` evaluated on a
ζ/α_GUT bracket.  `α_GUT = 6/(25·ζ(2))` is constructible from Basel
(`Physics/Basel/Bound.lean`); `P(x) = (1+2x)/(1+x)` is exact rational arithmetic.

### Stage 1 (reachable now) — `m_p/Λ_QCD` computed in a window

`m_p/Λ_QCD = NS·P(α_GUT·NS/d) = 3·P(x)`, `x = α_GUT·3/5`.  Compute:
1. `α_GUT` bracket from Basel: `α_GUT = 6/(25·ζ(2))`, so
   `α_GUT ∈ (6/(25·upper(N)), 6/(25·S(N)))` — exact rationals, `decide`-checkable.
2. `x = α_GUT·NS/d` as a rational bracket; `P(x) = (1+2x)/(1+x)` evaluated on
   the endpoints (P monotone, so endpoints give a P-bracket).
3. **Target theorem** — `m_p/Λ_QCD` in a measurable window:
   ```
   theorem mp_over_lambda_in_3_3_1 :
       3 * P_lower.1 * /*…*/ ⟶  3·P(x) ∈ (3.03, 3.05)   -- excludes 3.0 and 3.1
   ```
   i.e. `m_p/Λ_QCD ≈ 3.04`, computed from `(NS,NT,d)` + the Basel ζ(2) bracket,
   π/literal-free.  This is the honest DRLT content: a **dimensionless** ratio
   in a falsifier window (PDG `m_p/Λ_QCD` with `Λ_QCD≈308` gives ≈3.04).

### Stage 1′ — a clean dimensionless meson ratio

`m_J/ψ` / (charm scale) or the hyperfine ratio `Δ/Λ_QCD = d/NT = 5/2`: the
ratio `d/NT = 5/2` is already exact and atom-forced — promote it from "integer
identity" to "the hyperfine-splitting-to-scale ratio is exactly 5/2", a clean
zero-parameter dimensionless prediction (cf. the genuinely-clean Koide `NT/NS`).

### Stage 2 — the scale `Λ_QCD` (honest: needs an input, or a ratio of scales)

Absolute `m_p = 938 MeV` requires `Λ_QCD`.  Either (a) accept `Λ_QCD` as the one
input scale and report all hadron masses as `(atom factor)·Λ_QCD` — honest, and
standard practice — or (b) seek a *ratio of scales* (e.g. `Λ_QCD/m_e` or
`Λ_QCD/v_H`) that might be atom-expressible, removing the dimensionful input.
**Do not** type `93827` and match it to itself.

## 5 — Honest scope (keep vs replace)

- **Replace (must)**: the deleted `93827=93827` pattern is gone; keep it gone.
  Any "DRLT 782.1 vs PDG 782.7 MeV" meson claim must be downgraded to docstring
  estimate (it already is) and never promoted to a theorem.
- **Keep / strengthen**: a Stage-1 `m_p/Λ_QCD ∈ (3.03,3.05)` computed from atoms
  + Basel ζ(2) is a legitimate dimensionless falsifier bracket.  The hyperfine
  `d/NT = 5/2` is a clean zero-parameter ratio.
- **Be honest (flag explicitly)**: **absolute masses are not atom-derivable** —
  they need a scale input (`Λ_QCD`), exactly as `headline_precision_scope.md`
  §Synthesis states ("you cannot get MeV from pure integers").  Report the
  dimensionless factor as the prediction; the absolute carries the scale caveat.

## 6 — Cross-references

- `lean/E213/Lib/Physics/Hadron/ProtonMass.lean` — post-deletion `m_p` (genuine
  integer readings; `Λ_QCD` is prose-only).
- `lean/E213/Lib/Physics/Hadron/Masses.lean` — GMOR `NS²=9`, hyperfine `d/NT=5/2`.
- `lean/E213/Lib/Physics/Couplings/AlphaGUT.lean` — `α_GUT = 6/(25·ζ(2))`.
- `lean/E213/Lib/Physics/Basel/Bound.lean` — ζ(2) bracket (the α_GUT/P(x) input).
- `lean/E213/Lib/Physics/Foundations/KoideFormula.lean` — the clean zero-param
  ratio model (`NT/NS`) to emulate for dimensionless predictions.
- `lean/E213/Lib/Physics/AlphaEM/GramStructuralCapstone.lean` — the compute-it
  spine.
- `research-notes/frontiers/headline_precision_scope.md` — §m_p (the scale-input
  finding).
