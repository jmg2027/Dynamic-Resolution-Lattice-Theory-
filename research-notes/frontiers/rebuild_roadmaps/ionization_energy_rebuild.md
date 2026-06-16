# Genuine ionization-energy rebuild — derive the IE *ratio*, scale the Rydberg

**Status**: OPEN (rebuild roadmap). **Domain**: physics (DRLT branch).
**Template**: `research-notes/frontiers/genuine_hodge_rebuild.md` (honesty tone).
Covers IE(H), IE(He⁺), the hydrogenic `Z²` series, and `R_∞` consistency.

## 1 — What was deflated, and the bogus mechanism

The "4.3 ppb" IE(H) headline rests on an **arithmetic consistency check among
typed measured constants**, not a derivation.  `Atomic/IE/HydrogenPPM.lean`:

```lean
def m_e_centi   : Nat := 51099895     -- CODATA m_e c², typed
def IE_H_micro  : Nat := 13605693     -- measured IE(H), typed
def inv_alpha_milli : Nat := 137036   -- 1/α, typed
theorem IE_formula_sub_ppm :
    2 * IE_H_micro * inv_alpha_milli^2 - m_e_centi*10^10 = 2211460256 := …
```

The file is honest in-text:

> "This is an arithmetic consistency check **among inputs**, not a derivation of
> any of them."

So the "4.3 ppb" is the residual of plugging three *measured* numbers
(`m_e`, IE, `1/α`) into the textbook `IE = m_e α²/2` and checking they agree —
`R_∞` is never computed from atoms; it is `R_infinity_mEV := 13605693` typed in
`Hydrogenic.lean`.  Per `headline_precision_scope.md`: the only PURE-proven
content is a **~0.1%-wide bracket** `[13.5993, 13.6131]` from the α ∈
[137.00,137.07] window — and even that uses **CODATA m_e** as a measured input.
The hydrogenic series `hydrogenic_atomic_chain` proves `Z²` integers (`NT²=4`,
`NS²=9`, `d²=25`, `10²=100`) plus residual gaps against the typed `R_∞`.

## 2 — The genuine targets

- **Observables**: `IE(H) = 13.598434 eV`, `R_∞ = 13.605693 eV` (Rydberg as
  energy), hydrogenic `IE(Z) = R_∞·Z²` for `He⁺=54.418`, `Li²⁺=122.454`, …
- **The atom-derivable part** — *ratios and structure*, not absolutes:
  - `IE = m_e c²·α²/NT`, with the denominator `NT = 2` **atom-forced** (the
    "mysterious Bohr 2" = temporal sector dim; `Atomic/Hydrogen.lean`).
  - hydrogenic scaling `IE(Z)/IE(Z') = Z²/Z'²` — a pure dimensionless law whose
    `Z²` values read as atom integers (`NT²,NS²,(NS+1)²,d²`).
  - the He⁺/H ratio `≈ 4` (= `NT²`) up to mass/QED corrections.
- **The scale**: absolute `R_∞ = m_e c²·α²/2` needs `m_e c²` (a measured energy
  scale) — *not* atom-derivable, like `Λ_QCD` for hadrons.

## 3 — Why the current Lean fails to DERIVE it

- `R_∞` is **typed** (`13605693`), never built from `m_e·α²/2` with a *computed*
  α.  The "4.3 ppb" is a self-consistency residual among three typed measured
  inputs, so it certifies *measurement consistency*, not a 213 prediction.
- The hydrogenic series proves `Z²` integers and then computes **residual gaps**
  (`NT²·R − IE_He = 5012 mEV`) against the typed `R_∞` — i.e. the comparison
  baseline is itself an input, so the "92 ppm / 26 ppm" gaps are input-vs-input.
- α appears only as the typed `inv_alpha_milli = 137036`, not the genuine α_em
  spine (`GramStructuralCapstone`, which *computes* `137035999111`).  The IE
  chain never imports the real α derivation.

## 4 — Staged plan: derive the IE *ratio*, then scale

### Stage 1 (reachable now) — the hydrogenic `Z²` ratio law, computed

The cleanest atom-content is the *ratio* `IE(Z)/IE(Z') = Z²/Z'²`, which needs no
scale and no measured `R_∞`.  Stage 1:
1. Define the hydrogenic prediction `IE_pred Z := Zsq Z · R` *as a ratio* and
   prove `IE_pred(2)/IE_pred(1) = NT² = 4` exactly (atom-forced), then check the
   **measured** `IE(He⁺)/IE(H) = 54.418/13.598 = 4.002` lands in `(4, 4.01)` — a
   measurable window the `Z²=4` law must hit:
   ```
   theorem he_h_ratio_in_4_window :
       4 * 13598434 < 54417760           -- ratio > 4
     ∧ 54417760 < 401 * 13598434 / 100   -- ratio < 4.01  (mass/QED corr band)
   ```
   This is a genuine falsifier: the `Z²` law predicts exactly `NT²=4`; the small
   excess (4.002 vs 4) is the known reduced-mass/QED correction band, *not* a
   tuned constant.  All `decide`, no `R_∞` input needed.
2. Promote the Bohr-denominator result: `IE = m_e α²/NT` with `NT = 2`
   atom-forced (`Hydrogen.lean` `bohr_denom = NT`) — the one genuinely 213-native
   structural fact (textbook `2` *explained* as `NT`).

### Stage 1′ — compute the α-bracket from the genuine spine

Replace `inv_alpha_milli := 137036` (typed) with the **proven** α_em bracket
(`AlphaEM/Brackets.inv_full_lower`, the ppm window the spine certifies).  Then
the IE(H) bracket `[13.5993, 13.6131]` becomes "computed-α in, bracket out"
instead of "typed-α in" — the same 0.1% width, but now sourced from the real
derivation chain, not a literal.

### Stage 2 — the Rydberg structure (honest: `R_∞` needs a scale)

`R_∞ = m_e c²·α²/2`.  213 supplies `α` (proven bracket) and the `/2 = /NT`
(atom-forced).  `m_e c²` is a **measured energy scale** — not atom-derivable.
So the honest end state: `R_∞ = (m_e c²)·(computed α²)/NT`, a *prediction up to
the one scale `m_e c²`*.  The dimensionless ratio `R_∞/(m_e c²) = α²/2`, with α
the spine's bracket, IS atom-derivable and should be the headline; the absolute
`13.6057 eV` carries the `m_e c²` caveat.

## 5 — Honest scope (keep vs replace)

- **Replace (must)**: the "4.3 ppb" headline as a *213 prediction* — it is a
  consistency residual among typed measured inputs.  The typed `R_∞` baseline
  for the hydrogenic gap theorems should be replaced by the `Z²` ratio law,
  which needs no `R_∞`.
- **Keep / strengthen**: (a) `Z²` ratio law `IE(Z)/IE(Z') = Z²/Z'²` with `Z²` as
  atom integers — a clean dimensionless prediction; (b) Bohr `denom = NT = 2`
  structural fact; (c) the IE(H) 0.1% bracket *once α is the proven spine
  bracket*, not a literal.  A ratio-in-a-window IS a legitimate DRLT falsifier.
- **Be honest (flag explicitly)**: **absolute `R_∞` / IE energies need a scale
  input** (`m_e c²`), like `Λ_QCD` for hadrons — `headline_precision_scope.md`
  §IE(H) already records this.  Do NOT claim ppb; the dimensionless ratio
  stands, the absolute carries the scale caveat.

## 6 — Cross-references

- `lean/E213/Lib/Physics/Atomic/IE/HydrogenPPM.lean` — the "4.3 ppb"
  among-inputs consistency check (typed `m_e`, `IE`, `1/α`).
- `lean/E213/Lib/Physics/Atomic/IE/Hydrogenic.lean` — typed `R_infinity_mEV`;
  `Z²` integers + input-vs-input residual gaps.
- `lean/E213/Lib/Physics/Atomic/Hydrogen.lean` — `bohr_denom = NT` (the genuine
  structural fact: Bohr "2" = atomic `NT`).
- `lean/E213/Lib/Physics/AlphaEM/Brackets.lean` — `inv_full_lower` (the proven α
  bracket to replace the typed `137036`).
- `lean/E213/Lib/Physics/AlphaEM/GramStructuralCapstone.lean` — the spine that
  *computes* α (`137035999111`); the model for sourcing α, not typing it.
- `research-notes/frontiers/headline_precision_scope.md` — §IE(H) (the
  measured-input / 0.1%-bracket finding).
