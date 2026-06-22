# Decomposition: synthetic differential geometry / dual numbers (D = {x : x²=0}, Kock–Lawvere, R[ε]/ε², automatic differentiation, tangent bundle M^D)

*213-decomposition per `../README.md` (model v7.1) + `SYNTHESIS.md` (two invariants — the character
arrow `×↦·`/`×↦+` and the `q=±1` residue tag — read across the resolution axis with its **scaling**
sub-parameter). The KEY datum is the precise **dual of `ito_calculus.md`**: SDG is `derivative.md`'s
difference-reading with the second-order residue **truncated to zero** (`ε²=0`, the nilpotent
infinitesimal), making the first-order part EXACT — where Itô **kept** the `√h` second-order residue,
SDG **kills** it. Cross-links: `derivative.md` (the difference-Lens `L₋` + the resolution parameter;
the dropped `O(h²)`), `ito_calculus.md` (the Itô-dual choice — keep `√h` vs kill `ε²`),
`nonstandard_analysis.md` (infinitesimals, the calibrated boundary), `exponential.md` (the `^`-wall;
the value-derivative readout), `integers.md` (the difference-Lens pair = the slot structure).*

> **The thesis under test.** SDG is *not* a new analytic primitive. It is `derivative.md`'s resolution
> reading with one specific choice on the resolution axis's **scaling** sub-parameter: **truncate at
> `h²=0`**. The classical derivative reads `f(x+h) = f(x) + f'(x)·h + (residue, `O(h²)`)` and sends
> `h→0` via a modulus, discarding the `O(h²)` residue *below the resolution floor*. SDG instead works in
> the **dual numbers** `R[ε]/(ε²)`: it posits a nilpotent `ε` with `ε²=0` and the **Kock–Lawvere axiom**
> makes `f(d) = f(0) + f'(0)·d` **EXACT** (no limit) — because every term of order `≥2` is *algebraically
> zero*. So:
> 1. the **infinitesimal object `D = {x : x²=0}`** = the resolution `h` with the `q=±1` second-order
>    residue *truncated to zero* (the nilpotent relation `ε²=0`);
> 2. the **Kock–Lawvere axiom** (`f(d)=f(0)+f'(0)·d` uniquely) = the difference-reading `L₋` made
>    first-order-EXACT by that truncation — the derivative `f'(0)` *read off* as the `ε`-coefficient, no
>    modulus needed;
> 3. the **dual number `a + bε`** = a directed **(value, derivative) pair** — the SAME slot/pair
>    structure as `integers.md`'s difference-Lens pair `(m,n)↦m−n` and `Mat2`'s 2-component readout;
> 4. **automatic differentiation** = evaluating `f` in `R[ε]/(ε²)` (the derivative falls out as the
>    second slot, no symbolic limit);
> 5. the **tangent bundle `M^D`** = the space of infinitesimal arcs = the resolution-arc reading
>    (`T_e G`, the `lie_theory.md` open leg).
> So SDG = (`derivative.md`'s resolution reading) + (the nilpotent truncation `h²=0` = the dual number)
> + (the value-derivative pair = the slot structure) — **no new primitive; the Itô-dual choice.**

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the same two-layered point-construction as `derivative.md`/`ito_calculus.md`:
  a construction of points with a **value-construction hung at each**; a map `f` is a reading-over-`C`.
  SDG adds **no new construction of points**. What it adds is an *algebraic* operation on the
  value-construction: **adjoin a nilpotent slot** — the pair `a + bε` with `ε²=0`. This is the **dual
  number ring** `R[ε]/(ε²)`, and in the calculus it is the value-construction's *slot pair* (value in
  slot 0, derivative in slot 1) — the SAME two-slot pair structure as `integers.md`'s `(m,n)` (sign =
  swap-bit) and the `Mat2` 2-component readout. (Lean shadow — and this is the surprise of this note:
  the dual-number ring is **genuinely BUILT**, not merely conceptual — `F2CDTower.F2D = 𝔽₂[ε]/(ε²)`
  with `eps_sq_is_zero` PURE; only the *real-coefficient* `R[ε]/(ε²)` over `Real213` and the named
  SDG/Kock–Lawvere objects are absent.)

- **Reading `L`** — `derivative.md`'s difference-reading `L₋ = (m,n)↦m−n`, read at the resolution
  whose **scaling** is the nilpotent truncation `h²=0`. Three pieces, each already in the calculus:
  1. **the difference-reading as a slot pair.** `f(a+bε)` evaluated in `R[ε]/(ε²)` returns
     `f(a) + b·f'(a)·ε`: the value in slot 0, the derivative in slot 1. This is `L₋` *read as a directed
     pair* — exactly `integers.md`'s `npairToInt : (m,n) ↦ m − n` two-slot container, the derivative
     occupying the second slot the way the sign occupies it for ℤ. **No new reading.**
  2. **the truncation `ε²=0` — the load-bearing choice.** `derivative.md` reads `L₋` once and sends
     `h→0`, *dropping* the `O(h²)` residue below the floor. SDG instead imposes `ε²=0` **algebraically**:
     every order-`≥2` term is literally `0`, so the first-order expansion is **EXACT**, not a limit. The
     discrete shadow is the **second forward difference** `liftKZ 2` (`NewtonGregory.lean:57`): the
     genuine degree-2 structure (`obstruction_int_constant`, `liftKZ 2 = 2`) that the *first-order Lens
     cannot see* (`obstruction_nat`). SDG sets that structure to **zero by fiat** (`ε²=0`) — the dual,
     not the deletion-by-limit, of Itô's *promotion* of the same residue to a primary term.
  3. **the character/derivation readout.** The map `f ↦ f'(0)` (the `ε`-coefficient) is a **derivation**:
     `(fg)' = f'g + fg'` (the Leibniz rule), the calculus's recurring graded-product
     `leibniz_universal_delta4` shape — here truncated so the `f'g'·ε²` cross-term *vanishes*
     (`ε²=0`), leaving exactly the first-order Leibniz law. The derivative-readout is the additive/graded
     character on the value-slot.

- **Residue** — `q = ±1`, and the SDG choice is precisely the residue **truncated to the `q=+1`
  converging/closure pole**:
  1. *The second-order residue set to zero — `ε²=0`.* In `derivative.md` the difference-reading's
     residue at smooth resolution is the `O(h²)` term the `h→0` modulus discards (below the floor). SDG
     **truncates it algebraically**: `ε²=0` makes the surplus *identically zero*, so `f(d)=f(0)+f'(0)d` is
     exact with **no residue at all** at first order. This is the `q=+1` (converge/idempotent/closure)
     pole — the residue collapsed to nothing, the dual of Itô's `q=+1`-but-*kept* second moment
     `[B]_t=t`. The nilpotent reading is the `homology.md`/`ResidueTag` `q=±1` *nilpotent* iteration-
     character (`∂²=0`, `dsq_zero_universal_delta4`) read on the value-slot: `ε²=0` is the *same*
     two-step nilpotence the calculus already carries.
  2. *What the truncation forgets — higher derivatives.* `R[ε]/(ε²)` keeps only `f` and `f'`; `f''`,
     `f'''`, … are forgotten (they live in `R[ε]/(ε^{n+1})` — the higher Weil algebras, the *jets*).
     This is `L₋`'s many-to-one forgetting, exactly `derivative.md`'s "+C"/anti-diagonal residue, now
     graded by truncation order — a `dimension.md` fold-height residue: order-`n` truncation keeps the
     `n`-jet, forgets the rest.

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   value-construction R[ε]/(ε²)  =  ⟨ value-slot | adjoin a nilpotent slot, ε²=0 ⟩  (the dual number; the SAME 2-slot pair as integers.md's (m,n) / Mat2)
   the infinitesimal D={x:x²=0}  =  the resolution h with the q=±1 SECOND-ORDER residue TRUNCATED to 0  (ε²=0; the q=+1 collapse-to-nothing pole)
   Kock–Lawvere f(d)=f(0)+f'(0)d =  ⟨ value-pair (f(d),f(0)) | L₋ ⟩  made FIRST-ORDER-EXACT by ε²=0  (no modulus, no limit — the residue is gone)
   the derivative f'(0)          =  the ε-coefficient READ OFF the slot  =  L₋'s second slot (as ℤ's sign sits in the second slot of (m,n))
   the dual number a+bε          =  the directed (value, derivative) PAIR  =  integers.md's difference-Lens pair / Mat2's 2-component readout
   automatic differentiation     =  EVALUATE f in R[ε]/(ε²):  the derivative falls out of slot 1, no symbolic limit
   the Leibniz/derivation rule   =  leibniz_universal_delta4 shape with the f'g'·ε² cross-term KILLED (ε²=0) — first-order Leibniz exactly
   the tangent bundle M^D        =  the space of infinitesimal arcs = the resolution-arc reading (T_e G, lie_theory.md's open leg)
   higher jets R[ε]/(ε^{n+1})    =  the order-n truncation residue (dimension.md fold-height: keep the n-jet, forget the rest)
```

So SDG is **`derivative.md`'s difference-reading dialed to the `h²=0` truncation**, where the
second-order residue is set to *zero* — the SAME `L₋` reading, the SAME resolution parameter, the SAME
`q=±1` residue (here the `q=+1` collapse pole), with the one new ingredient being the **scaling choice**
(`ε²=0`, not `√h` and not `h→0`-by-modulus) that *removes* the second-order term instead of dropping it
below a floor or promoting it above one. It is not a new analytic primitive; it is `derivative.md` read
at the dial-position where its `O(h²)` residue is algebraically annihilated.

## VALIDATE — verdict: PREDICTION + PARTIAL (the dual-number ring is actually BUILT over 𝔽₂)

**Verdict: PREDICTION + PARTIAL, with one notable repo-first correction to the prior batch's "named
dual-number object likely ABSENT" prior.** The calculus *derives* SDG's shape from existing slots (the
difference-Lens, the resolution parameter + its scaling, the `q=±1` nilpotent residue, the value-slot
pair) and *predicts* that SDG is the Itô-dual choice. And — the surprise — **the dual-number ring
`R[ε]/(ε²)` is genuinely BUILT ∅-axiom**, with the defining nilpotent relation `ε²=0` proven PURE, in
`F2CDTower.lean` (over 𝔽₂, as the char-2 collapse of the Cayley–Dickson tower). The genuine absences
are (i) the *real-coefficient* `R[ε]/(ε²)` over `Real213`, (ii) the named Kock–Lawvere / SDG /
`tangentBundle` / `infinitesimalObject` objects, and (iii) the *first-order-exact* derivative-extraction
theorem `f(a+bε) = f(a) + b·f'(a)·ε` welded to a `Real213` derivative.

This is **PREDICTION** at the structural level (the calculus derives *which* residue SDG truncates and
*why* the first-order part becomes exact) **+ PARTIAL** on the build (the truncation algebra `ε²=0` is
PURE; the real-coefficient + SDG-named objects are the located missing leg). It is the precise **dual of
`ito_calculus.md`**: the two notes share `derivative.md`'s resolution axis and its `scaling`
sub-parameter, and split on the *one* second-order residue —

| | resolution scaling | the second-order term `(½f'')·(increment)²` | Lean shadow |
|---|---|---|---|
| `derivative.md` (smooth `d/dx`) | adjacency at `h`, `h→0` modulus | `O(h²)`, **dropped** below the floor | `diffZ`, modulus; `liftKZ 2` → nothing at the limit |
| `ito_calculus.md` (Itô) | adjacency at **`√h`** (increment `O(√h)`) | `(ΔB)²=O(h)` **first-order, KEPT** as `½f''dt` | `liftKZ 2`, `obstruction_int_constant` (2nd diff = 2) |
| **`synthetic_differential_geometry.md` (SDG)** | **`ε²=0`** (nilpotent truncation) | `f'(0)²·ε² = 0` **algebraically ANNIHILATED** | `F2D.eps_sq_is_zero` (`ε²=0`, PURE); the residue set to 0 |

The three notes are **one reading at three positions of the resolution-scaling dial**: drop it (smooth),
keep it (Itô, `q=+1`-promoted), kill it (SDG, `q=+1`-truncated). The re-skin guard is passed: the new
datum is *not* another resolution-axis re-description but the **exact Itô-complement** — Itô promotes the
second-order residue to a primary term, SDG annihilates it to make the first-order part exact, and both
are the *same* `q=±1` second-order residue `derivative.md` introduced.

## Revelation (collapse + forcing + spine)

**The infinitesimal object `D={x:x²=0}`, the Kock–Lawvere axiom, the dual number `a+bε`, automatic
differentiation, and the tangent bundle `M^D` are ONE `(C, L)` — `derivative.md`'s difference-reading
`L₋` read as a slot pair, with the second-order residue truncated to zero (`ε²=0`).** Collapse + forcing
+ residue-surfaced, three at once:

1. **Collapse onto `derivative.md`'s resolution axis — SDG is the derivative at the `ε²=0` dial.** The
   *infinitesimal object*, the *Kock–Lawvere axiom*, the *dual number*, *automatic differentiation*, and
   the *tangent bundle* are not five new primitives — they are `derivative.md`'s **one difference-reading
   `L₋`** read at the **`ε²=0` truncation**, returning the derivative as the second slot of a directed
   pair (the `integers.md`/`Mat2` slot structure). **And the deepest collapse of this note**: SDG and Itô
   are the *same* `(C, L)` at *opposite* settings of the resolution-scaling sub-parameter — Itô keeps the
   second-order residue (`√h` lifts it above the floor → `½f''dt`), SDG kills it (`ε²=0` annihilates it →
   first-order-exact). The "infinitesimal calculus" (SDG) and "stochastic calculus" (Itô) are
   `derivative.md` read at the two extreme scalings of the *same* residue.

2. **Forcing — `ε²=0` forces the first-order-exact Kock–Lawvere law and forces AD.** Whether the
   second-order residue survives (Itô), is dropped (smooth), or is *annihilated* (SDG) is **forced by the
   scaling choice alone**, not added by hand. Imposing `ε²=0` *forces* `f(a+bε) = f(a) + b·f'(a)·ε` to be
   exact (every order-`≥2` Taylor term carries an `ε^{≥2}=0` factor), which *forces* automatic
   differentiation: evaluating `f` in `R[ε]/(ε²)` *necessarily* yields `f'` in slot 1, with no symbolic
   limit. The derivation/Leibniz law `(fg)'=f'g+fg'` is then forced as the `leibniz_universal_delta4`
   graded-product shape with the `f'g'·ε²` cross-term *forced to vanish* — first-order Leibniz, exactly.

3. **Spine — SDG sits at the `q=+1` truncation pole of the second-order residue.** On the `SYNTHESIS.md`
   `q=±1` spine, the nilpotent truncation `ε²=0` is the **`q=+1`/nilpotent/closure** reading of the
   second-order residue (the `homology.md` `∂²=0` / `dsq_zero_universal_delta4` two-step nilpotence read
   on the value-slot): the residue collapsed to *nothing* (idempotent-to-zero), the dual of Itô's
   `q=+1`-but-*retained* converging second moment. The tangent bundle `M^D` is the resolution-arc reading
   = `lie_theory.md`'s open `T_e G` leg (the `Mat2Bracket.lean:32-34` located break — "no separate
   tangent space or `exp`"); SDG names that very arc-space, and the calculus locates it precisely at the
   `ε²=0` truncation of the value-slot's resolution reading.

**THE NEW DATUM (the re-skin guard): SDG is the exact COMPLEMENT of Itô on the resolution-scaling
sub-parameter, and the dual-number ring `R[ε]/(ε²)` is already BUILT ∅-axiom (over 𝔽₂, `ε²=0` PURE).**
`ito_calculus.md` showed the resolution axis carries a *scaling* and that Itô **revives** the dropped
second-order residue (`√h`). SDG is the complementary datum: the *same* scaling sub-parameter, set to
**annihilate** the residue (`ε²=0`), making the first-order reading exact — so "the infinitesimal" of
SDG and "the Brownian increment" of Itô are the two extreme treatments of `derivative.md`'s single
second-order residue. And unlike Itô's `BrownianMotion`/`ItoIntegral` (entirely absent), SDG's *core
algebra* — the nilpotent dual-number ring — is a **PURE Lean theorem already in the repo**
(`F2D.eps_sq_is_zero`), with only the real-coefficient version and the SDG-named objects open.

## Note for the technique — does SDG force a NEW construct?

**No new primitive — EXTEND, a resolution-scaling find that COMPLETES the Itô datum.** This decomposition
adds nothing to model v7.1's invariant set; it *uses* existing slots and sharpens the resolution axis's
**scaling** sub-parameter (the one `ito_calculus.md`/`padic.md` introduced) by exhibiting its *third*
position:
- *the infinitesimal object `D`* = `derivative.md`'s resolution `h` with the second-order residue
  truncated (`ε²=0`) — no new construction;
- *the Kock–Lawvere axiom* = the difference-reading `L₋` made first-order-exact by that truncation;
- *the dual number `a+bε`* = the directed (value, derivative) pair = the `integers.md`/`Mat2` slot
  structure — no new container;
- *automatic differentiation* = evaluating in `R[ε]/(ε²)` — the derivative read off slot 1;
- *the tangent bundle `M^D`* = the resolution-arc reading = `lie_theory.md`'s `T_e G` open leg.

The one sharpening for the technique: **the resolution axis's `scaling` sub-parameter has three
canonical positions on the second-order residue — drop (smooth `h→0`), keep/promote (Itô `√h`,
`½f''dt`), and truncate/annihilate (SDG `ε²=0`, first-order-exact).** SDG is the cleanest demonstration
that a residue the calculus normally drops below the floor can be **set to zero by an algebraic nilpotent
truncation**, making the first-order reading *exact* — the exact complement of Itô's promotion. This
*predicts* SDG's whole shape (the infinitesimal as a truncated residue, Kock–Lawvere as the exact
first-order reading, AD as evaluation-in-the-slot, the tangent bundle as the arc-reading) from the
model's slots, and — repo-first — corrects the prior "dual numbers likely ABSENT" with the BUILT
`F2CDTower` 𝔽₂[ε]/(ε²).

---

## Verified Lean anchors (file:line:theorem — all grep-confirmed; purity by `tools/scan_axioms.py` from repo root this session)

| Leg | Theorem (file:line : name) | Status |
|---|---|---|
| **★ the dual-number ring `R[ε]/(ε²)` is BUILT — the nilpotent relation `ε²=0`** (the SDG truncation algebra, over 𝔽₂) | `Lib/Math/Algebra/CayleyDickson/Tower/F2CDTower.lean : eps_sq_is_zero` (`:86`, `F2D.mul eps eps = zero`), `eps` (`:67`), `mul` (`:55`) | ∅-axiom ✓ (17/0) |
| the dual ring is commutative + has the zero-divisor `ε` + is NOT a field (its structural signature `= 𝔽₂[ε]/(ε²)`) | `…/F2CDTower.lean : mul_comm` (`:100`), `has_zero_divisors` (`:105`), `eps_has_no_inverse` (`:122`) | ∅-axiom ✓ (17/0) |
| **the SECOND difference-reading `liftKZ 2` — the second-order term SDG truncates to zero** (the discrete shadow) | `Lib/Math/Analysis/Cauchy/NewtonGregory.lean : liftKZ` (`:57`, `liftKZ(k+1)=diffZ∘liftKZ k`), `diffZ` (`:54`) | ∅-axiom ✓ (41/0) |
| **★ the second-order residue is genuinely non-trivial and invisible to the first-order Lens** (the very residue SDG sets to 0 / Itô keeps) | `…/NewtonGregory.lean : obstruction_int_constant` (`:404`, `liftKZ 2 ↑vObs = 2`), `obstruction_nat` (`:395`, `¬ polyDepth 2 vObs`) | ∅-axiom ✓ (PURE, by `decide`) |
| the value-derivative **slot pair** = `integers.md`'s difference-Lens directed pair (`a+bε` ≅ `(m,n)`) | `Lens/Number/Nat213/Tower/NatPairToInt.lean : npairToInt` (`:37`, `(p) ↦ Int.subNatNat p.1 p.2`) | ∅-axiom ✓ (19/0) |
| the nilpotent / graded-Leibniz two-step shape (`ε²=0` = the value-slot reading of `∂²=0`; the truncated derivation law) | `Lib/Math/Cohomology/Delta/V4Capstone.lean : dsq_zero_universal_delta4` (`:41`), `leibniz_universal_delta4` (`:62`) | ∅-axiom ✓ (5/0) |
| the `q=±1` residue tag — SDG = the `q=+1` truncate-to-zero pole (`converge`/nilpotent) | `Lib/Math/Foundations/ResidueTag.lean : golden_is_converge` (`:180`), `residue_tag_two_poles` (`:228`), `multiplier_unimodular` (`:86`) | ∅-axiom ✓ (55/0) |
| the tangent/infinitesimal `T_e G` arc-reading is the LOCATED OPEN leg (cross-link) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean` docstring `:32–35` ("no separate tangent space or `exp`") | located break, cited ✓ |
| the first-order term = `derivative.md`'s difference-Lens at residue resolution (prior) | `derivative.md` anchors (`diffZ`, `PolySumDerivativeModulus`) | cited, prior ✓ |

> **Axiom-purity note.** Re-run through `tools/scan_axioms.py` from repo root this session:
> **F2CDTower 17/0** (`eps_sq_is_zero`, `mul_comm`, `has_zero_divisors`, `eps_has_no_inverse` all PURE —
> the dual-number ring `𝔽₂[ε]/(ε²)` with `ε²=0` is genuinely ∅-axiom), **NewtonGregory 41/0**
> (`obstruction_int_constant`, `obstruction_nat`, `liftKZ`, `diffZ` PURE), **NatPairToInt 19/0**
> (`npairToInt` PURE), **ResidueTag 55/0**, **V4Capstone 5/0** (cross-cited, per `ito_calculus.md`'s
> scan this batch).

### Dropped / flagged (predicted-not-built — grep-confirmed ABSENT in `lean/E213`)

- **No `Real213`-coefficient dual numbers `R[ε]/(ε²)`** — the dual ring is built only over 𝔽₂
  (`F2CDTower`); the real-coefficient version (the actual SDG line ring `R`) over a `Real213` base is
  **not built**. The 𝔽₂ version proves the nilpotent *algebra* PURE but cannot host a real derivative
  `f'(a) ∈ R`. **Predicted-not-built (real coefficients).**
- **No `KockLawvere` / Kock–Lawvere axiom object and no first-order-exact extraction theorem** — grep
  (case-insensitive) for `Kock` / `KockLawvere` over `lean/E213` returns **0** hits; no
  `f(a+bε) = f(a) + b·f'(a)·ε` welded to a `Real213` derivative exists. The pieces are
  built (the dual algebra `ε²=0`, the difference-Lens `diffZ`, the modulus-derivative
  `PolySumDerivativeModulus`); the *substitution* "evaluate `f` in `R[ε]/(ε²)` and read `f'` off slot 1"
  is the conceptual weld. **Predicted-not-built.**
- **No `infinitesimalObject` / `D = {x : x²=0}` object** — grep for `infinitesimal` returns only
  `DyadicTrajectory`'s `InfinitesimalGap` (the *constructive 0⁺/1⁻ cut-gap*, a different object: the
  one-sided dyadic-cut infinitesimal, not the nilpotent `ε²=0` of SDG) and `Hyper213`'s
  ultrapower-infinitesimal (`nonstandard_analysis.md`, the cofinite-quotient horn — also not nilpotent).
  The SDG nilpotent infinitesimal object is **absent** as a named type. **Predicted-not-built.**
- **No `tangentBundle` / `M^D` object** — grep for `tangent` returns `golden_tangent` (a trig-tangent,
  unrelated), `FluxMVT` "tangent slopes" (prose), and `Mat2Bracket`'s `T_e G` *located-break* docstring.
  No space-of-infinitesimal-arcs `M^D` object exists. It is the SAME open leg `lie_theory.md` records
  (`Mat2Bracket.lean:32–35`). **Predicted-not-built (= `lie_theory.md`'s open `T_e G`).**
- **No automatic-differentiation theorem** — no `autodiff`/`forwardDiff`-in-`R[ε]` statement; it is
  exactly the Kock–Lawvere extraction theorem above, absent. **Predicted-not-built.**

### Verified buildable witness (genuinely true + terminating)

`F2CDTower.eps_sq_is_zero` (`:86`) is the existing ∅-axiom witness that **the dual-number nilpotent
relation `ε²=0` is real and PURE** (17/0) — the SDG truncation algebra, built. Together with
`NewtonGregory.obstruction_int_constant` (`:404`, the second-order residue `liftKZ 2 = 2` that SDG sets
to zero and Itô keeps), the structural shadow of "SDG annihilates `derivative.md`'s second-order residue"
is fully grounded ∅-axiom. **No new buildable witness is asserted here** — the genuine missing leg is the
*real-coefficient* `R[ε]/(ε²)` over `Real213` plus the Kock–Lawvere extraction theorem
`f(a+bε)=f(a)+b·f'(a)·ε` (the weld of the existing modulus-derivative `PolySumDerivativeModulus` to a
real dual slot), not a one-line `decide`. A buildable next step paralleling the 𝔽₂ build: a *truncated
polynomial* dual evaluation over `Int213` (`(a+bε)² = a² + 2abε`, `ε²=0` by the `F2CDTower` mechanism
lifted to `Int213`) exhibiting `f'` in slot 1 for concrete monomials — a promotion target, not asserted.
