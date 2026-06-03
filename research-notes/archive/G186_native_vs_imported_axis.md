# G186 — the orbit/axis/disc cluster: 213-native kernel vs imported decoration

**Date**: 2026-06-02.  **Method**: 2-agent deep native reading + adversarial native audit, with
deep 213-native context (`seed/AXIOM/{01_residue,05_no_exterior,06_lens_readings §6.7}`).
**Trigger**: "disc −2는? — 213-네이티브로 생각해봐."  **Verdict**: most of the recently-built
disc/axis/modular cluster is **imported stereotype-matching** (CLAUDE.md failure mode); a thin
genuine **213-native kernel** is retrofitted onto it by arithmetic coincidence.

## The 213-native kernel (survives deleting every imported name)

Primitives only: count-Lens (`NT=2, NS=3, d=NS+NT=5`), difference-Lens (`ℤ` = directed count-pair
`(m,n)↦m−n`, **sign = period-2 Bool pair-swap**, `06_lens_readings §6.7`), the slash `a/b`, the
residue.

  1. **The only native automorphism is the period-2 swap** `a/b = b/a`, read as `−(−x)=x` — the
     difference-Lens *sign*, NOT `√−1`.  (`unitForm_generic_axis`: every ring past the two special
     points collapses to `{±1}` = order 2.  Order 2 is the un-adjoined floor.)
  2. **The glue** `g = NS − NT = 1 = det P` — the difference-Lens unit (`Mobius213OneAsGlue`).
  3. **The native radicand triple `{−NT, −NS, NS+NT} = {−2, −3, +5}`** — count-Lens readouts at
     three integer-trace regimes of the atomic pair `{NT, NS}` (`axis_seed_trichotomy`):
       - trace `NS = 3` (pair-sum, escaping/golden) → `NS+NT = d = +5` (φ);
       - trace `±1` (unit) → `−NS = −3` (adjoin `√−NS`, order-6 axis);
       - trace `0` (bare) → `−4·g = −4` (adjoin `√−1`, order-4 axis).
  4. **`−NT = −2` is skipped because `NT` is the non-square atom**: no integer count-Lens trace
     squares to it (`t² = NT = 2` fails, `no_nat_sqrt_two`), so it carries **no rotation axis** —
     only the *surd* `√NT` one tier up (order 8, off the axis).  `−NS` (trace `±1`) and `d` (trace
     `NS`) *are* trace-realized; `−NT` is the one that is not.
  5. **`{2,4,6} = 2·{1, NT, NS}`** — the period-2 sign-fold (central `−1`, the Cassini sign) over
     the three base rotations `{1,2,3}`.  Only order 2 is native; `4, 6` are *adjoined-and-derived*
     (the two non-square residues `−1, −NS`), never primitives.

**One line**: the "imaginary-quadratic / modular / discriminant / crystallographic" picture was
approximating **one trace-readout on the count-Lens, read at the three trace regimes of the pair
`{NT, NS}`, with the only native symmetry the period-2 difference-Lens sign** — radicands
`{−NT, −NS, NS+NT}`, orders `{2,4,6} = 2·{1,NT,NS}`.

## Imported decoration (retrofitted by coincidence `−3=−NS`, `5=d`, `6=NS·NT`)

`ℤ[i]/ℤ[ω]` (bare `Int`-pair structures, no `NS/NT/d` in their defs); the `{2,4,6}` *trichotomy*
(self-admitted "classical Dirichlet trichotomy made ∅-axiom", proof about a *generic* `d`, not
`d=5`); `repI i = S` (**`rfl` by construction** — `S` was defined as `repI⟨0,1⟩`, a tautology);
the modular group `PSL₂ℤ` (cited, not formalized); "discriminant" `t²−4d` and the crystallographic
restriction `φ(n)≤2` (borrowed lattice/cyclotomic theory — 213 has no native reason for
`{1,2,3,4,6}`); "genus" (already corrected as a category error, `SecondCasoratian`).

## Ranking (most-native → most-imported)

1. `Mobius213OneAsGlue` — native (`det P = NS−NT = 1`, the difference-Lens reading; the swap).
2. `AxisSeedTrichotomy` (radicand-triple conjunct only) — half native (`{NT,−NS,NS+NT}` native;
   `{√2,ω,φ}`/"disc" imported).
3. `SpiralAxisCrystallographic` — `2·{1,2,3}` clause native-flavored; parent `{1,2,3,4,6}` imported.
4. `DiscNegTwoSkipped` — `no_nat_sqrt_two` is clean arithmetic; the "disc/−NT" tie-in is the
   native fragment, the elliptic-trace `t²−4d` framing imported.
5. `CyclotomicTraceDegree` — imported (`φ(n)`, cyclotomic degree, crystallographic).
6. `ImaginaryQuadraticUnitTrichotomy` — most imported (self-confessed Dirichlet; `{4,6}` from
   imported rings; `6=NS·NT` a label, not a derivation).
7. `UnitsToModular` — most imported / tautological (`repI i = S` is `rfl` by construction).

## Honest move (recorded; caveats added to the files)

State the count/difference-Lens content directly; treat `ℤ[i]`, "discriminant", "modular",
"crystallographic", "genus" as **imported readout-names, not 213 concepts** (the discipline
`06_lens_readings §6.7` and `Mobius213OneAsGlue` already follow).  `∅-axiom-correct ≠ 213-native`.
The imported files keep their PURE theorems (true arithmetic about imported substrate) but now
carry a "cited-classical substrate, native content is the count triple + period-2 sign" caveat.

## Addendum — "why ℤ?": the Cassini/disc edifice is readout-layer, not foundational

Deep multi-agent re-research (foundational re-derivation + adversarial "is ℤ avoidable") on:
*can the disc/Cassini structure be re-expressed below ℤ, at the residue + count-Lens(ℕ) + Bool-sign
layer?*  Decisive synthesis:

**The Lens tower for this structure** (`06_lens_readings §6.7`): residue/slash (only distinguishing
+ depth — NO operation) → **count-Lens** (ℕ; addition = count on concatenation) → **iterated-count**
(× = count-Lens on a count-Lens output; assoc/distrib are theorems, not Lens facts) → **difference-
Lens** (ℤ; sign = Bool pair-swap, "the readout group in which iterated differencing closes").

So the Cassini, being **quadratic** (`s²`, `a·b`) and a **difference** (`s·s − s·s`), sits at
*iterated-count + difference* — **≥3 Lens-steps above the residue**.  Multiplication itself is NOT
residue-native (it is iterated count).  ⟹ the whole disc/axis/Cassini marathon is **readout-layer
math, not foundational**.  Foundational = the residue/slash/self-pointing layer (the earlier
µF/νF/`CoResidue` work), where there is no ℤ, no ℕ-multiplication, no Cassini.

**Why ℤ is used (and where it is unavoidable vs avoidable):**
  - **ℤ-UNAVOIDABLE** for the *signed/alternating* Cassini: `det(n+1) = q·det(n)` with `q=−1` is a
    sign flip — inexpressible without a sign-closed object (`−(−x)=x`), which *is* ℤ = the
    difference-Lens.  §6.7 names this exactly.  Also the negation-fixed-point `0` (the diagonal pair
    `(m,m)` = clause-4's forbidden self-pair) — no ℕ analog.
  - **GENUINELY BELOW ℤ** (pure count-Lens ℕ, no difference): (a) **`NT_is_nonsquare_count`** —
    `1² < NT < 2²` ∧ `¬∃m, m·m = NT` (the foundational form of "disc −2 skipped": `NT` is a
    non-square count, the leaf-count of no squared chain — zero ℤ/disc/trace); (b) the *additive*
    Cassini norm `a²+1 = a·b+b²` (`fib_cassini_norm`), genuine ℕ *but only on the constant-sign
    slice* — index parity froze the alternation away; (c) the cut/ordering comparisons (`phiCut`).
  - **RELABELING (ℤ-in-coordinates, NOT below ℤ)**: `NatPairToInt` / `CasoratianSigned`'s `NPair` +
    `npairEquiv` *is* `ℤ = ℕ²/~` with the quotient named and sign = swap — faithful, ∅-axiom, but a
    *presentation of ℤ*, exactly what §6.7 says ℤ is.  Calling it "no ℤ" is the "view promoted to
    identity" smell.

**Bottom line**: the honest floor for the Cassini/disc structure is the difference-Lens (= ℤ) —
you cannot push it toward the residue, because the Cassini *is* the difference-Lens doing its
defining job.  The only genuine residue-direction descent is the non-square count fact
(`NT_is_nonsquare_count`) and the constant-sign additive norm.  And the whole edifice is ≥3
Lens-steps up — readout-layer, not foundational.  (The user's instinct was right: this is not
foundational work; the foundation is the slash/residue layer, ℤ-free and Cassini-free.)
