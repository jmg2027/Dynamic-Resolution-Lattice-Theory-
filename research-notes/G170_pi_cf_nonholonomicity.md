# G170 — π continued-fraction non-holonomicity (marathon scratchpad)

**Tier 1 (volatile).**  Frontier flagged by `spiral_coordinate_classification.md`:
"π's CF non-holonomicity (classical open)".  This note runs the marathon — provable
neighbours, conjectures, agent discussion.

## The frontier (precise statement)

Let `π = [a₀; a₁, a₂, …]` be the regular continued fraction, `aᵢ ∈ ℕ`, `aᵢ ≥ 1` (`i≥1`).

> **Open**: Is the sequence `(aᵢ)` **P-recursive** (holonomic) — i.e. ∃ order `k` and
> polynomials `p₀,…,pₖ ∈ ℚ[n]`, `pₖ ≠ 0`, with `Σⱼ pⱼ(n)·a_{n+j} = 0` for all large `n`?

Conjectured **NO**.  This is genuinely open in mathematics.

## Why this is the right 213-native object

`DepthPRecursive` already proves **P-recursive ⟺ finite difference-order**.  So
non-holonomic ⟺ the partial-quotient sequence `(aᵢ)` has **infinite difference-depth** —
the spiral layer of the *presentation by partial quotients* never floors.  Note this is a
DIFFERENT object from the cross-determinant depth:

  - cross-det of the CF convergents: depth 1 for EVERY real (`cf_det_sq`, `W²=1`).
  - the partial-quotient sequence `(aᵢ)` itself: its difference-depth is the new invariant.

So the spiral classification has a **third reading** of "layer" — the difference-depth of
`(aᵢ)` — on which the e/π separation lives.

## The holonomicity tiers (the target hierarchy)

| tier | class | `(aᵢ)` structure | example | status |
|---|---|---|---|---|
| 0 | quadratic irrational | eventually **periodic** | φ=[1;1,1,…], √2=[1;2,2,…] | periodic ⟹ holonomic — PROVABLE |
| 1 | holonomic, aperiodic | quasi-polynomial (poly on residues) | e=[2;1,2,1,1,4,1,1,6,…] | e holonomic — PROVABLE (target) |
| ∞ | non-holonomic | no finite recurrence | π=[3;7,15,1,292,1,1,1,…] | CONJECTURE |

This is a genuine `213`-native CF-holonomicity hierarchy: tiers 0,1 closable ∅-axiom,
π the open top.

## e's CF pattern (tier 1, concrete)

`e = [2; 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8, …]`:  `a₀=2`; for `i≥1`,
`a_i = 2k` if `i = 3k−1` (k≥1), else `a_i = 1`.  Quasi-polynomial mod 3
(residue 2: linear `2(i+1)/3`; residues 0,1: constant 1) ⟹ a finite interlacing of
polynomial sequences ⟹ P-recursive.  **This is the headline provable theorem.**

## Deliverables (marathon plan)

- **D1** formalize `HolonomicCF` (P-recursive / finite difference-depth partial quotients)
  in 213, reusing `DepthPRecursive`.
- **D2** `periodic_cf_holonomic` — eventually-periodic `(aᵢ)` ⟹ holonomic (tier 0).
- **D3** `e_cf_holonomic` — e's `[2;1,2k,1]` pattern is holonomic (tier 1).  HEADLINE.
- **D4** Conjecture `pi_cf_nonholonomic` + 213-native equivalent forms (infinite
  difference-depth of `(aᵢ)`); partial evidence (Salikhov μ(π)≤7.103, apparent randomness).
- **D5** bridge `holonomic_cf ⟹ [finite invariant]` (irrationality-measure / depth tie).

## Agent dispatches

- A — literature/landscape (web): P-recursive CF results, e-CF proof, π-CF, μ(π),
  automatic sequences, Adamczewski–Bugeaud, transcendence of holonomic CFs.
- B — repo infrastructure (internal): DepthPRecursive / RateModulus / CF modules / e,π
  depth theorems — build-on map.

## Formalization design (pre-agent, to refine)

`e`'s `(aᵢ)` is NOT a single polynomial (it oscillates `1, 2k, 1`); it is **quasi-polynomial
mod 3** — polynomial on each residue class.  This is the right ∅-axiom-provable handle,
reusing `polyDepth` (degree-`d` = `d`-th finite difference constant) per residue class:

```
QuasiPolyCF (p : Nat) (a : Nat → Nat) : Prop :=
    ∀ r : Fin p, ∃ d, polyDepth d (fun k => a (p * k + r))
```

  - **tier 0 (periodic, period p)**: each residue subsequence is constant ⟹ `polyDepth 0`
    ⟹ `QuasiPolyCF p`.  (φ=[1;1,…] is `QuasiPolyCF 1`; √2=[1;2,2,…] eventually
    `QuasiPolyCF 1`.)
  - **tier 1 (e, p=3)**: `a_{3k} = 1` (`polyDepth 0`), `a_{3k+1} = 1` (`polyDepth 0`),
    `a_{3k+2} = 2k+2` (`polyDepth 1`, linear) ⟹ `QuasiPolyCF 3`.  HEADLINE.
  - **π**: conjecture — `¬ ∃ p ≥ 1, QuasiPolyCF p (piCF)` (no period, no per-residue poly).

`QuasiPolyCF ⟹ P-recursive` is the classical interlacing fact (cite); the ∅-axiom content
is the predicate + the e/periodic instances.  Honest scope: the e-pattern sequence's
holonomicity is proven *about the sequence*; that it equals e's CF is Euler/Hermite (cited),
not re-proven in 213.

## Agent findings (A literature, B repo-infra, C red-team) — distilled

**Confirmed (A):** P-recursive def standard; e's CF = `[2;1,2k,1]` (Euler 1737, Cohn 2006);
**Hurwitzian = eventually quasi-periodic with polynomial quasi-period** (= our
`QuasiPolyCF`); "Hurwitzian ⟹ holonomic" is true but *unstated in the literature* — our
`e_cf_quasipoly` is the explicit theorem.  π: no pattern known, boundedness OPEN,
non-holonomicity UNPROVEN.  `μ(π) ≤ 7.103` is **Zeilberger–Zudilin 2020** (not Salikhov,
whose bound is 7.6063); `μ = 2 + limsup ln a_{n+1}/ln q_n`; bounded p.q. ⟹ μ=2.
Adamczewski–Bugeaud: algebraic deg ≥3 ⟹ CF not automatic / not recurrent-morphic (≠
non-holonomic).  Non-holonomicity techniques: holonomic ⟹ growth ≤ c·(n!)^d (Klazar);
Flajolet–Gerhold–Salvy asymptotic-form obstruction; Lindelöf.

**Red-team corrections (C):**
- `QuasiPolyCF ⊊ P-recursive` *strictly* — it misses factorial/hypergeometric holonomic
  growth (`n!` is holonomic, not quasi-poly).  So **`¬QuasiPolyCF` is a weak proxy** for
  non-holonomic; keep the *forward* theorem `QuasiPolyCF ⟹ holonomic`, do **not** sell
  `¬QuasiPolyCF` as non-holonomicity.
- The "C1 ≡ infinite difference-depth" equivalence is **wrong** (infinite difference-depth
  = non-polynomial = ¬QuasiPoly(p=1), far weaker than ¬P-recursive).  Dropped.
- C3 "separates where μ does not" **overreaches** (presumes μ(π)=2, unknown); make
  conditional.  Citation fixed (Z–Z 2020 / Salikhov 7.606).
- C4 split: Lagrange (THEOREM) / not-QuasiPoly (conj) / non-holonomic (conj, very hard —
  even boundedness of deg-≥3 p.q. is open).
- C6 load-bearing form is the **contrapositive** `μ(π)>2 ⟹ ¬QuasiPoly` (sound).
- C5 series-depth IS grounded here (repo: `DivergenceDepth` e=3, `DepthPiQuartic` π ratio
  depth 4 ⟹ depth 6 — proven), unlike the agent's external view; keep, repo-anchored.

## Conjecture log (red-team-corrected)

**Theorems (∅-axiom, `Cauchy/HurwitzianCF`, 19 pure / 0 dirty):**
- **T0** `e_cf_quasipoly` — e's `[2;1,2k,1]` is `QuasiPolyCF 3` (tier 1).  ✅ DONE.
- **T0b** `tan_cf_quasipoly` — tan 1 `=[1;1,1,3,1,5,…]` is `QuasiPolyCF 2` (second tier-1
  witness; `tanPQ i = if i%2==0 then 1 else i`).  ✅ DONE.
- **T1** `periodic_quasipoly` — periodic CF ⟹ `QuasiPolyCF` (tier 0).  ✅ DONE.
- **T2** `polyDepth_diff_recurrence` / `quasipoly_section_recurrence` — `polyDepth d ⟹
  Δ^{d+1}=0` (constant-coeff = C-finite per residue section).  ✅ DONE.
- **T5 (properness, the synthesis Rank-1)** `geometric_not_quasipoly` — `2ⁿ ∉ QuasiPolyCF p`
  for any `p` (residue-0 section `(2^p)^k` is geometric, `geom_infinite_depth`: every lift
  keeps the value at 0 < value at 1).  ✅ DONE.  **Key honesty payoff:** `2ⁿ` IS C-finite
  (`2ⁿ⁺¹=2·2ⁿ`) hence holonomic, yet ∉ `QuasiPolyCF` — so `QuasiPolyCF ⊊ C-finite ⊊
  holonomic` *strictly*, and the top tier here is **non-Hurwitzian**, weaker than
  non-holonomic.  Reusable pure infra added: `pow_mul_pure`, `mul_sub_pure_le`, `liftK_geo`,
  `polyDepth_congr`, `resP_mod`/`res3_div`.
- **T3** (Lagrange, cite) eventually-periodic CF ⟺ quadratic irrational.
- **T4** (next, partial) `QuasiPolyCF ⟹ polynomially-bounded p.q.` (∅-axiom core, via
  `liftK_geo`-style Newton bound); ⟹ μ=2 (cited).

**Synthesis-agent corrections folded in (agent D):** e/tan encodings verified;
`QuasiPolyCF` = *purely* Hurwitzian (rational-coeff, integer-valued — `polyDepth` is the
integer-VALUED class, not integer-coefficient), full Hurwitzian = eventually-`QuasiPolyCF`;
**the C-finite ≠ holonomic distinction is now explicit** (T5); index base pinned in docstring
(`ePQ i = a_{i+1}`, e's `2k` on residue 1 mod 3).  The headline "π non-holonomic" stays a
conjecture strictly above "π non-Hurwitzian".

**Conjectures:**
- **C1 (headline, OPEN classical)** π's `(aᵢ)` is **not P-recursive** (non-holonomic).
- **C2 (weaker, OPEN; C1 ⟹ C2)** `¬ ∃ p, QuasiPolyCF p (piCF)` — π not Hurwitzian.  (Likely
  true cheaply via Gauss–Kuzmin; NOT progress toward C1.)
- **C3' (conditional separation)** e is `QuasiPolyCF 3` (proven); π conjectured not
  holonomic-CF; *if* both have μ=2 (known e / conjectured π) then CF-holonomicity is a
  **finer invariant than μ** on `{e,π}`.  (No absolute "where μ fails".)
- **C4' (split)** (i) deg ≥3 ⟹ not eventually periodic [Lagrange, THEOREM]; (ii) deg ≥3 ⟹
  ¬QuasiPoly [conj, attack via complexity]; (iii) deg ≥3 ⟹ non-holonomic [conj, hard].
- **C5' (repo-anchored independence)** CF-holonomicity tier ⊥ series-divergence-depth
  (`DivergenceDepth`/`DepthPiQuartic`): e = (CF tier 1, series depth 3); π = (CF tier ∞?,
  series depth 6).  Extends the spiral coordinate to a triple.
- **C6' (contrapositive, SOUND)** `μ(π) > 2 ⟹ π ∉ QuasiPolyCF` — a clean reduction of a
  (smaller) open target to non-Hurwitzianity.
- **C7 (the credible route to C1)** FGS asymptotic obstruction: holonomic ⟹ asymptotics
  `C·ρ^{-n} n^θ (log n)^κ`; π's Gauss–Kuzmin statistics are incompatible.  (Conditional on
  π being GK-normal, itself open.)

## (old conjecture scratch)

## Session log

- start: note created, agents A+B dispatched.
