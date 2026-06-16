# Genuine quark/lepton mass-ratio rebuild — compute the chains, drop the welds

**Status**: OPEN (rebuild roadmap). **Domain**: physics (DRLT branch).
**Template**: `research-notes/frontiers/genuine_hodge_rebuild.md` (honesty tone).
Covers `m_t/m_c`, `m_b/m_c`, `m_t/m_b`, `m_τ/m_μ`, `m_μ/m_e`.

## 1 — What was deflated, and the bogus mechanism

The deleted welds had the shape: take a genuine atomic chain sum, then **add a
hand-chosen constant** so the integer hits a known measured number.  The
canonical case (now removed) was the `m_t/m_c` "`+50 → 137`" weld: the honest
chain summed to

```
mt_mc_chain_sum = NS·d² + NS·NT² = 75 + 12 = 87        (MtOverMc.lean)
```

and the deleted layer added `+50` to force `87 → 137 = 1/α_em(IR)`, then matched
that against the (also typed) measured `m_t/m_c`.  The honest file now states it
plainly:

> "The chain skeleton 87 is the *bare* integer sum; it is **not** 1/α_em(IR) =
> 137, and **no underived constant is added** here to force the two together."

That is the correct post-audit state for `m_t/m_c`: the `+50` weld is gone and
87 stands as a bare combinatorial sum.  The remaining work is to turn 87 (or a
corrected chain) into a *computed ratio* with a real comparison, instead of a
`decide`d integer identity (`mt_mc_chain_sum = 87 := by decide`).

The other ratios live in `QuarkHierarchy.lean` and `Mass/MuOverE.lean` as
`decide`d integer skeletons + **docstring numerics** ("0.4% match", "−1 ppb")
that the theorems do not prove (see `headline_precision_scope.md`).

## 2 — The genuine targets (PDG/CODATA + proposed atom-formula)

| ratio | measured | proposed 213 form | atom reading | honest status |
|---|---|---|---|---|
| `m_t/m_c` | ≈ 136.0 (MS̄ 172.76/1.27) | chain `NS·d²+NS·NT² = 87`, ×(ζ(2)/α_GUT tail?) | `75 = NS·d²`, `12 = NS·NT²` | **87 ≠ 136; NO derivation of the ratio yet** |
| `m_t/m_b` | ≈ 41.3 | `1/α_GUT = d²·ζ(2) = 25·ζ(2)` | `25 = d²` | bare `25` proven; ζ(2) factor not assembled |
| `m_b/m_c` | ≈ 3.27 | "Beyond NS=3" `NT²=4` corrected | `4 = NT² = d−1 = NS+1` | only the integer `4` proven |
| `m_τ/m_μ` | ≈ 16.82 | `NT⁴ = 16` base ×(1+correction) | `16 = NT⁴ = 2⁴` | only `16` proven |
| `m_μ/m_e` | 206.7683 | `(NS/NT)·(1/α_em)·P·(1+Σδ)` | `3/2 = NS/NT`, leading `205` | leading bracket `205∈[197,206]`; full value NOT proven |

## 3 — Why the current Lean fails to DERIVE them

- **`m_t/m_c`**: `87` is computed honestly, but `87 ≠ 136` and there is no
  formula taking 87 to the ratio.  The ratio is never computed; only `87=87` is.
  This one is honest *about not deriving* — the rebuild is to actually find a
  chain producing ~136 from atoms, or to state plainly that none exists.
- **`m_t/m_b`**: `mt_mb_ratio = d*d = 25` is proven, but the `ζ(2)` factor that
  turns `25` into `41.3` (`25·ζ(2) = 25·1.6449 = 41.12`) is **not applied** —
  ζ(2) appears only in the docstring "= d²·ζ(2)".  `41.12` is never computed.
- **`m_b/m_c`, `m_τ/m_μ`**: only the integers `4` and `16` are `decide`d; the
  ratios `3.27`, `16.82` never appear as terms.  These currently have **NO
  derivation** of the actual ratio — be honest.
- **`m_μ/m_e`**: the leading `r₀ = NS/(NT·α_em)` is genuinely bracketed via the
  α_em ppm bracket (`Brackets.inv_full_lower`), so this one *does* compute its
  leading term — but `P` (+0.6%) and `δ₁δ₂δ₃` are docstring-only; `206.768` is
  not proven (see `headline_precision_scope.md`).

## 4 — Staged plan to actually COMPUTE each ratio

The shared tool: ζ(2) via the Basel partial sum `Physics/Basel/Bound.lean`
(`S N`, `upper N`, `lower_tight N` — exact rational `(num,den)` brackets,
∅-axiom by `decide`), and ζ(3) via `Real213/Zeta3Cut.lean` (`ζ(3) ∈
(601/500, 1203/1000]`).  α_em enters as the proven ppm bracket
(`AlphaEM/Brackets.inv_full_lower`), the same input `m_μ/m_e` already uses.

### Stage 1 — one genuinely computed ratio bracket each (replace the `decide` skeletons)

- **`m_t/m_b`** (most reachable): define `mt_mb := d² · S(N)` as a rational and
  prove `41 · den < num < 42 · den` for a concrete `N` — i.e. compute `25·ζ(2)`
  through the Basel bracket and show it lands in `(41,42)`, a **measurable
  window excluding neighbors** (PDG ≈ 41.3).  π absent; ζ(2) is the Basel cut,
  not a literal.  Target:
  ```
  theorem mt_mb_in_41_42 :
      41 * (d*d * (Basel.S N).2) < d*d * (Basel.S N).1   -- > 41 via lower bracket
    ∧ d*d * (Basel.upper N).1 < 42 * (d*d * (Basel.upper N).2) := by decide
  ```
- **`m_μ/m_e`**: keep the genuine leading-bracket (`205∈[197,206]` from the α_em
  ppm bracket) — that IS a computed value, the honest content.  Stage 1 = state
  it as "leading term, bracket width = α_em's", not "206.768 ppb".
- **`m_t/m_c`**, **`m_b/m_c`**, **`m_τ/m_μ`**: Stage 1 is *honesty*, not a proof —
  record that `87`, `4`, `16` are bare integer skeletons with **no ratio
  derivation**, and that turning them into `136`, `3.27`, `16.82` would require
  a correction-chain not yet found.  Do **not** weld a constant.

### Stage 2 — the correction tails (look for missing physics, don't tune)

For `m_t/m_b`, after `25·ζ(2) ∈ (41,42)`, tighten `N` until the bracket reaches
PDG's ~0.4% (the docstring's current claim) — then the 0.4% becomes a *proven*
bracket, not a docstring number.  For `m_t/m_c`, the open question is whether
`87` carries a ζ(2)/α_GUT tail to ~136; this is genuine missing-physics hunting
per CLAUDE.md "Algebraic priority" — search the discrete structure (the
`QuarkHierarchy` chain steps) before positing a continuous correction.

## 5 — Honest scope (keep vs replace)

- **Replace (must)**: any presentation of `m_t/m_c=136`, `m_b/m_c=3.27`,
  `m_τ/m_μ=16.82` as *derived* — the Lean proves only `87`, `4`, `16`.  The
  removed `+50→137` weld must never return; a chain sum that doesn't reach the
  measured value should *say so*, as `MtOverMc.lean` now does.
- **Keep / strengthen**: a Stage-1 `m_t/m_b ∈ (41,42)` computed via the Basel
  ζ(2) bracket is a legitimate measurable falsifier; the `m_μ/m_e` leading
  bracket (inheriting α_em's ppm window) is genuinely computed.
- **Do NOT claim**: "0.4%" / "ppb" until the bracket *proves* that width.  Bare
  integers (`87`, `4`, `16`) are skeletons, not ratios.

## 6 — Cross-references

- `lean/E213/Lib/Physics/Hadron/MtOverMc.lean` — the honest `87` (post-`+50`).
- `lean/E213/Lib/Physics/Hadron/QuarkHierarchy.lean` — `25 = d²`, the chain
  skeletons, and the docstring ζ(2)/α_GUT claims to be cashed out.
- `lean/E213/Lib/Physics/Mass/MuOverE.lean` — the `m_μ/m_e` capstone (genuine
  leading bracket).
- `lean/E213/Lib/Physics/Basel/Bound.lean` — `S`, `upper`, `lower_tight` ζ(2)
  brackets (the Stage-1 construction tool).
- `lean/E213/Lib/Physics/AlphaEM/Brackets.lean` — `inv_full_lower` (α_em ppm
  bracket, the leading-term input).
- `lean/E213/Lib/Physics/AlphaEM/GramStructuralCapstone.lean` — the spine that
  *computes* its number (the standard to match).
- `research-notes/frontiers/headline_precision_scope.md` — the m_μ/m_e audit.
