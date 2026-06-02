# G181 — the atomic spiral structural adic (variable-base, carry = the residue unit)

**Tier 1 (volatile).**  Design note from a discussion session on the residue framework.
Companion synthesis: `theory/essays/the_form_of_the_residue.md`, `research-notes/G170`
(π non-holonomicity), the Markov/Lagrange arc (`theory/math/analysis/markov_spectrum.md`).
Vision is the user's (Mingu Jeong); this note pins it for investigation.

## The vision (residue-frame, standard math set aside)

Every codomain is a reading-out of the **Raw / ℕ initial algebra** (`raw_initial`).  At each
point the reading *spirals* outward via the point's **local unit-circle axis** (dyadic /
Eisenstein / …); the axis count per point is not one — it cascades `{2,3} → 5 → 10 → 20`
(unit / atomic-points NS+NT=5 / C(5,3) planes / ×NT two-sided), itself a binomial/Raw-native
shape.  Extending these bridges gives ordinals and diagonal (`ascent_unbounded`,
`diag_not_in_seq`); abstract codomains are quotients re-naming the extended shape
(`QuotLens.universalLens_kernel`).  Deep purpose: see this shape clearly and **substitute math
problems into it**.

## The proposed object: an *atomic spiral structural adic*

**Not** a fixed-base p-adic (that is the over-developed dyadic `2→2→2→…`).  Instead:

> a **variable-base** positional system where each place's base = the **local axis**, the
> **carry = the residue unit `+1`**, and the base sequence follows the **atomic spiral**
> `(NS,NT)=(3,2) → 2,3,5,…`.  `NS = NT+1` means a `2`-place that carries **promotes to a
> `3`-place** — "2의 결과가 3" is literally the carry.

State = state-transition: a digit is a *transition* (which axis → which axis), not a static
value — which is why the axis count reads as `{2}` or `{2,3}` depending on point-vs-transition
(a §5.4 Lens choice, not a fact).

## Cleanest realization — the golden / Zeckendorf adic (µF side)

Place values = **Fibonacci** `1,2,3,5,8,13,…` = the `P=[[2,1],[1,1]]` orbit = the spiral.
Digits `∈{0,1}`, **no two consecutive 1s**.  Two laws, both 213-native:

  - **carry `"11" → "100"`** = the recurrence `F_{n−1}+F_{n−2}=F_n` = the unit `+1` lifting
    one rung of the spiral.  `"2의 결과가 3"` visible: `10 (=2) + 1 (=1) = 11 (forbidden) →
    100 (=3)`, i.e. `F₂+F₁=F₃`.
  - **no-consecutive-1s** = `det P = 1` / Cassini `W=±1` (`cf_det_sq`, `FibCassiniNat`) as a
    *digit law*: the orbit can never stack two units; the gap collapses by carry.  The µF
    floor written in digits.

Worked: `1=1, 2=10, 3=100, 4=101, 5=1000, 6=1001, 7=1010`.

## Digit-patterns = the µF/νF / holonomicity tiers

In the spiral adic (Zeckendorf-style, or the CF/Ostrowski variable base below):

  - **φ** = balanced repeat (all-`1` CF / `1010…` golden) — the no-overshoot floor (µF).
  - **quadratic irrational** = eventually-**periodic** digits (tier 0).
  - **Hurwitzian (e, tan 1)** = **quasi-periodic** digits (tier 1, `e_cf_quasipoly`).
  - **π** = **no stable pattern** (νF escape) — π non-holonomic ⟺ the spiral-adic digits never
    settle ⟺ the carry forever demands new axes.

So `Cauchy/HurwitzianCF`'s tiers become **digit-pattern grades** — "rationals repeat,
irrationals don't" lifted onto the spiral.  Markov tree = the digit-branching tree.

## Classical anchor (to verify in investigation)

The CF-based variable-base numeration of a number α is classically the **Ostrowski numeration
system** (places = α's convergent denominators `qₙ`, digits bounded by the partial quotients);
**Zeckendorf = Ostrowski(φ)**.  So "atomic spiral adic of α" ≈ Ostrowski(α), and the
spiral-adic *of φ itself* is Zeckendorf.  This is the formal name for the variable-base side;
the "carry = +1, base = local axis" framing is the 213-native reading.

## Two variants (a §5.4 choice)

  - **golden (combined)**: `P` already fuses 2 and 3 (trace `NS=3 = NT+1`), one spiral —
    natural at the µF floor; Zeckendorf is its integer face.
  - **separated 2/3**: 2-axis = Gaussian base `(1+i)` (disc −4), 3-axis = Eisenstein base
    (disc −3), digits literally alternating axes — honours "3 is not 2's kind of 3"
    (different ramification), at the cost of complexity.

## Session synthesis this rests on (one residue, many views)

  - **µF/νF mirror** (`Theory/Raw/MuNuMirror`): descent terminates (µF=Raw), ascent escapes
    (νF=residue).  φ = the fixed-point image (algebraic, closes); π = the continuous-symmetry
    Lens image, its non-closure (diagonalization) = transcendence = the residue's
    non-surjectivity reflected in that Lens.  Bridge `φ = 2cos(π/5)`.
  - **cyclotomic vs binomial = the `+1` unit read ×(mult) vs +(add)** — q-Lens (q=ζ vs q=1);
    repo: `CassiniUnimodular` (oscillation `q=±1` and golden Cassini are one unimodular law).
    Two views meet at φ (5-fold `ζ₅` = golden Pascal).
  - **dense π formulas (Ramanujan/Chudnovsky) = Eisenstein `E₄,E₆` (weights {4,6} = the
    `|ℤ[i]^×|,|ℤ[ω]^×|` axis) on the modular group `ℤ₂*ℤ₃`** — i.e. the 2-3 spiral, not the
    dyadic Wallis (slow).  213's claim: the spiral adic *explains* why the order-6 base closes
    π fast and the 2-base (Wallis) crawls.

## Investigation targets

1. Repo: existing numeration infra (`Dyadic`, `FibCassiniNat`/Zeckendorf, `ContinuedFractionFloor`
   partial quotients, `rawTower`) — what a spiral-adic module would reuse.
2. Hand-expand φ, √2 in the golden adic and the separated 2/3 adic; confirm √2 (disc-8, 2-axis)
   is clean in the separated form, quasi-periodic in golden.
3. Is the "carry = +1 promotes 2→3" realizable as a clean mixed-radix (bases `2,3,5,…`), and is
   it the same as / different from Ostrowski(φ)?
4. Does the digit-pattern grade (periodic / quasi-periodic / patternless) coincide with the
   `HurwitzianCF` tier exactly?  (Likely yes — Ostrowski digits of α track α's CF.)

## FINDINGS (investigation: literature agent + hand-expansion)

**Honest verdict: the *mathematics* is known — this is Ostrowski numeration (1922).  213's
content is the *reading*, not a new numeration.**

- **The "atomic spiral adic" = Ostrowski numeration.**  Places = convergent denominators
  `qₙ` (`qₙ = aₙqₙ₋₁ + qₙ₋₂`), digits `0 ≤ bₙ ≤ aₙ`, admissibility "`bₙ = aₙ ⇒ bₙ₋₁ = 0`."
  The partial quotients `aₙ` *are* the per-place "local axis."  **Zeckendorf = Ostrowski(φ)**
  exactly (all `aₙ=1` ⟹ Fibonacci places ⟹ {0,1}, no-consecutive — a textbook identity, not
  new).  The `011→100` carry = `Fₙ₊₁=Fₙ+Fₙ₋₁`.
- **Two splits confirmed distinct (hand-finding correct).**  (a) golden/**Ostrowski(φ)** =
  additive (Fibonacci places).  (b) the "2,3,5… promoting-carry" = **mixed-radix**: bases =
  primes ⟹ the *primorial number system* (named); place-values = running products
  (factoradic/Cantor).  These are genuinely different systems; the "atomic spiral" intuition
  conflates them.  Unique representation in (b) needs Ostrowski-type admissibility (not free).
- **Digit-pattern grade = Ostrowski–Sturmian complexity (known).**  Eventually-periodic CF ⟺
  quadratic irrational ⟺ regular/automatic Ostrowski digits (Lagrange); Sturmian words of
  quadratic slope (Fibonacci word for `1/φ²`).  So `HurwitzianCF`'s tiers (periodic /
  quasi-periodic / patternless) = the classical Ostrowski–Sturmian dictionary — which this
  repo *formalized ∅-axiom*, but did not discover.
- **The genuine "adic" already exists: the Ostrowski G-odometer.**  The true adic/profinite
  object is the **odometer (the "+1" adding machine) on the profinite completion of the
  admissible digit space** (Bratteli–Vershik / Vershik adic; Grabner, Ferenczi–Talet).  A
  *single profinite group/odometer*, not a tower of fields like `ℚₚ`.

**What survives as 213-native (the reading, sharpened — not overclaim):**
- **The odometer's `+1` IS the residue unit / the act of pointing.**  Standard math has the
  odometer as a dynamical system; 213 says *why* its `+1` is fundamental — it is the
  self-pointing act, the carry is the spiral lift (one rung up the `qₙ` tower), the profinite
  completion is the **νF escape** (completed self-pointing).  This matches `rawTower`
  (`ascent_unbounded`) and the µF/νF mirror: the odometer = the act made an arithmetic
  dynamical system; `ℤₚ`-style "single self-similar group" = the residue's one self-cover.
- **Contribution = unifying interpretation + ∅-axiom formalization**, not a new numeration:
  Ostrowski(α) + odometer + CF/Sturmian complexity, read as one residue/act structure, with
  the tiers proven (`HurwitzianCF`).  The `+1` unit recurring (Cassini `W=±1`, glue, carry,
  odometer) is the residue's invariant — the cross-domain agreement that is "no exterior"'s
  operational signature.

**Direction**: if anything is to be *built*, the target is the **Ostrowski/Vershik odometer
as the arithmetic face of the pointing act** (`+1` = the act, carry = spiral lift, profinite
limit = νF) — connecting `rawTower` / `MuNuMirror` to Ostrowski numeration.  Not a new adic;
a native reading of the known one.  (Done elsewhere per branch policy.)
