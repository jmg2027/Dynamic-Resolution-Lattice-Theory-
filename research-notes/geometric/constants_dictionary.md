# The constants dictionary — why φ is forced, the three frames, the multiplier principle

*Deep-research result (number theory / dynamics).  Classical scaffolding: Siegel
1944, Hurwitz 1891, Feigenbaum 1978 / Lanford 1982, Bombieri–Taylor 1986.
Grounded in the repo's `Mobius213/Px` and `OneAsGlue`.*

## 1. Why φ is forced (not tuned)

The binary slash (arity 2, `03_form.md` §3.2) selects the **quadratic tier**, and
within it the **minimal unimodular generator** `N_1 = Q = [[1,1],[1,0]]`
(`MetallicGeneratorTower`).  Its Perron eigenvalue is **φ**, the **smallest
quadratic Pisot number** and the **smallest limit point of the Pisot set** (the
real quadratic field of minimal discriminant, `ℚ(√5)`).  Among the integer
metallic generators `N_k` the discriminant `k²+4` is minimized at `k=1`, giving
`disc = 5 = N_S + N_T = d` (`discNk_golden`, `golden_minimal`: `5<8<13`).

Two-tier minimality (Siegel 1944): the **plastic number ρ ≈ 1.3247** (root of
`x³=x+1`, Padovan/Perrin) is the smallest Pisot number *overall* — what the
*cubic* analogue of the slash would carry; **φ** is the smallest *quadratic*
Pisot and the smallest Pisot *limit point*.  The slash is binary ⇒ quadratic tier
⇒ **φ, not ρ**.  ρ appears in the atlas only via the explicitly cubic reading.

Precise algebra (the repo encodes this correctly): `P = [[2,1],[1,1]] = Q²`, char
poly `x²−3x+1`, eigenvalues `φ², φ⁻²`, and **φ is the Möbius fixed point** of
`x ↦ (2x+1)/(x+1)` (`x²−x−1=0`).  `§3.5` states exactly this (eigenvalues `φ²,
1/φ²`, φ the fixed point); the `det=−1` of `Q` squares to `det=+1` of `P`, and the
Cassini defect stabilizes at the discriminant `d=5` (`CharPolySelf.cassini_general:
L(n)L(n+2) − L(n+1)² = 5 ∀n`).  Unimodularity is the conserved invariant; without
`det=±1` the map is rank-deficient (the `a=1` collapse) or leaves `SL(2,ℤ)`.

## 2. The three φ-frames are one fact

The hinge is `φ = [1;1,1,1,…]` (all partial quotients 1, the slowest CF):

1. **Algebraic ⟹ worst-approximable.**  Hurwitz (1891): the best constant is
   `√5 = √disc`, attained only by the golden class; φ is the **minimum of the
   Lagrange spectrum**.  The metallic discriminants `5,8,13` (`golden_minimal`)
   are the bottom of the Markov/Lagrange spectrum — the framework's tower is that
   spectrum's start.  The `5` in Hurwitz *is* the `d` of the framework.
2. **Worst-approximable ⟹ best-equidistributed.**  The golden-angle rotation has
   the **lowest discrepancy** of any irrational rotation (three-gap/Steinhaus +
   Weyl); convergent denominators are the Fibonacci numbers; all-1 partial
   quotients avoid all clustering (sunflower phyllotaxis is the optimal packing).
3. **⟹ canonical quasicrystal.**  The Fibonacci substitution `a↦ab, b↦a` has
   incidence matrix `Q = N_1` (the framework's golden generator); its fixed-point
   word is the canonical 1-D quasicrystal (cut-and-project on slope `1/φ`), the
   2-D analogue Penrose (inflation `φ`, `det = φ²`, i.e. `P`).

So `φ=[1̄]` ⟺ Hurwitz/Lagrange-extremal ⟺ lowest-discrepancy rotation ⟺
`Q`-substitution quasicrystal — **one `GL(2,ℤ)` datum `Q` read through three
functors** (= §3.5's "same Lens result across domains").

## 3. The multiplier principle (each reading its own constant) — and its break

> Each reading's carried constant is the **multiplier of its renormalization
> self-map at its fixed point.**

| reading | self-map | fixed point | constant = multiplier |
|---|---|---|---|
| Möbius (slash, arity 2) | `x ↦ (2x+1)/(x+1)` | φ | growth `φ` (eigenvalue ratio of `P`) |
| cubic recurrence | `x³ = x+1` | ρ | Perron eigenvalue (smallest Pisot) |
| period-doubling (logistic) | the **renormalization operator** `R` on *maps* | the Feigenbaum map `g` | `δ ≈ 4.669` = unstable eigenvalue of `DR` at `g` |

For φ, ρ the self-map is a finite companion matrix and the multiplier is an
**algebraic Pisot unit** (∅-axiom-expressible: `ℤ[√5]`, `ℤ[ρ]`).  For δ the
self-map is the **infinite-dimensional** doubling operator (Feigenbaum 1978;
Lanford 1982 rigorous, computer-assisted) and δ is its functional eigenvalue.

**The break (sharp):** φ, ρ are algebraic / finite-dimensional / explicit and
**Pisot**; δ is transcendental / infinite-dimensional / numeric and **not Pisot
(not even algebraic)**.  So the φ, ρ readings inherit Pisot–quasicrystal rigidity
(below); the δ reading inherits **universality** (same δ for all smooth unimodal
maps) instead.  The clean "multiplier" principle covers the *algebraic* (Pisot)
readings; δ shares only the abstract "multiplier at a renormalization fixed
point" form.  Consequence for 213: φ (and ρ) can be carried as strict ∅-axiom
objects; **δ cannot** — no finite presentation, outside the algebraic-priority
gate.

## 4. Pisot ⟺ quasicrystal (Bombieri–Taylor) — the mechanism

Bombieri–Taylor (1986): a self-similar inflation point set has **pure-point
(Bragg) diffraction iff the inflation factor is Pisot** (conjugates inside the
unit disk ⇒ bounded internal-space window ⇒ a Meyer set).  So the minimal reading
produces a genuine quasicrystal **automatically**, because its inflation factor
`φ` is a *unit* Pisot.  Minimality of the *reading* (smallest generator, lowest
discriminant, all-1 CF) maps to minimality of the *diffraction data* (sharpest,
lowest-Lagrange Bragg spectrum):

`minimal unimodular generator N_1 →(Perron) φ (min. quadratic Pisot) →(Bombieri–
Taylor) canonical Meyer/quasicrystal.`

This is the *mechanism*, not an analogy, and it is the same equivalence as §2 with
the Pisot property as the explicit hinge.  δ's non-Pisot nature is exactly why the
period-doubling reading gives universality rather than a quasicrystal.

## Takeaway

φ is forced because the slash is binary ⇒ the minimal *quadratic* Pisot unit, the
`disc = d = 5` rung of the metallic tower; its three faces (worst-approximable,
best-equidistributed, canonical quasicrystal) are one `GL(2,ℤ)` datum `Q`; each
reading carries the multiplier of its renormalization fixed point (algebraic
Pisot for φ/ρ, transcendental functional for δ); and Bombieri–Taylor is the
mechanism by which minimal readings surface minimal-Pisot constants.

*Open*: the markov_lagrange link (the metallic tower = Lagrange spectrum start) is
a candidate ∅-axiom target (the discriminants `k²+4` are already in
`MetallicGeneratorTower`).  ρ as an explicit cubic-Pisot ∅-axiom object (Padovan
companion) is unbuilt.
