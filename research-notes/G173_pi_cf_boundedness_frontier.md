# G173 — π's continued fraction: the boundedness frontier (marathon, cont. of G170)

**Tier 1 (volatile).**  Continues the π-non-holonomicity marathon (`G170`).  This session
adds the **positive-floor unboundedness theorem** (∅-axiom) and grounds a corrected
conjecture about *where the difficulty of π actually lives*.

Lean source (this session): `lean/E213/Lib/Math/Cauchy/PositiveFloorUnbounded.lean` (11 PURE).

## The new theorem (∅-axiom, constructive, explicit witness)

> **`positive_floor_unbounded`** — if the `(m+1)`-th iterated finite difference of `s : ℕ→ℕ`
> is a *constant* (`polyDepth (m+1) s`) with value `≥ 1`, then `s` is **unbounded**: for every
> `B` there is an *explicit* index `n` with `B < s n`.

Proof skeleton (no LPO/LEM): a positive constant top difference makes `Δᵐs` strictly
increasing *everywhere* (`hbase`); `evStrictMono_down` pushes "eventually strictly
increasing" through one anti-difference at a time; `evStrictMono_descend` lands it on `s`;
`evStrictMono_unbounded` telescopes `s(N+i) ≥ s N + i` to the explicit witness `n = N+(B+1)`.

Contrapositive, decidable on `ℕ`: **`bounded_floor_zero`** — a bounded depth-`(m+1)` sequence
has vanishing top difference `Δ^{m+1}s(0) = 0`.

CF instance: e's residue-`1 (mod 3)` section is the linear `2k+2`; positive top difference `2`
⟹ **e's partial quotients are unbounded** (`ePQ_unbounded`) *through the structural theorem* —
a genuine positive-degree section forces unbounded partial quotients.

## What this does NOT do (the honest scope — red-team item 5)

The theorem applies **only to positive-degree polynomial sections**.

  - The **periodic floor** (`φ=[1;1,…]`, `√2=[1;2,2,…]`): a non-constant periodic section is
    *not* of finite difference-depth at all (its finite differences stay periodic, never
    settling to a constant), so the hypothesis simply does not fire — consistent with `φ`,
    `√2` having bounded partial quotients.
  - The **geometric `2ⁿ` gap** (`HurwitzianCF.geometric_not_quasipoly`): `2ⁿ` is exponential,
    hence has **no** finite difference-depth, so this lemma cannot apply.  `2ⁿ` is unbounded
    by the separate (elementary) fact of geometric growth — *not* because of this theorem.

So the slogan "every tier above periodic needs unbounded p.q." is **NOT** proved.  The exact
content is: *a genuine positive-degree polynomial partial-quotient section forces unbounded
partial quotients.*

## Agent dispatches this session (3, in parallel)

  - **A — literature/landscape** (web): bounded-P-recursive periodicity; π p.q. boundedness;
    constructive (Bishop) status of monotone convergence; FGS / Klazar growth obstructions.
  - **B — red-team** (adversarial): attack the theorem, the contrapositive framing, and the
    conjecture C8.
  - **C — repo-infra** (internal): ∅-axiom-safe `Nat` lemmas, reusable `DivergenceLadder` /
    `DepthPRecursive` definitions, propext-landmine cross-check.

## Distilled agent findings

**A (literature) — confirmed:**
  - **π's partial quotients: BOUNDEDNESS IS OPEN.**  Not proven unbounded, not even a sharply
    formulated conjecture-with-program.  Unboundedness is a *heuristic expectation* from the
    Gauss–Kuzmin distribution `P(aₙ=k)=log₂(1+1/(k(k+2)))` (heavy tail `~1/(k²ln2)`; under it
    the `aₙ` are a.s. unbounded — Borel–Bernstein/Khinchin), and π is **not** known to be
    Gauss–Kuzmin normal (open, intractable).  **Correction to G170's wording:** drop
    "conjecturally unbounded (Gauss–Kuzmin)" as if a conjecture — it is open/heuristic.
  - **Constructive status (Q3): CONFIRMED.**  "Every bounded monotone sequence of naturals is
    eventually constant" = the Monotone Sequence Principle, **equivalent to LPO** over BISH
    (Mandelkern, *Limited Omniscience and the Bolzano–Weierstrass Principle*, Bull. LMS 1988;
    also Bishop–Bridges, Diener CRM).  So our refusal to prove "bounded ⟹ eventually constant"
    is forced; only the witnessed direction (`positive_floor_unbounded`) is ∅-axiom.  This is
    exactly the same boundary `MonotonicBounded.lean` already refuses to cross.
  - **Klazar growth bound (THEOREM):** holonomic ⟹ `|aₙ| ≤ cⁿ·(n!)^d`.  So *super-`(n!)^d`*
    growth ⟹ non-holonomic.  **FGS structure theorem (THEOREM):** holonomic ⟹ coefficient
    asymptotics in the template `C·ρⁿ·n^θ·(log n)^k`; a wrong-shape asymptotic (e.g. `log n`,
    `pₙ`, irrational `θ`) ⟹ non-holonomic.  These are the two complementary obstructions; π's
    CF is in neither's easy range (bounded-or-slowly-varying integer regime).

**A vs B — the one genuine conflict (adjudicated):**
  - "**bounded P-recursive integer sequence ⟹ eventually periodic**."  A says **TRUE**
    (folklore/known; mechanism: polynomial recurrence coefficients are *eventually periodic
    mod m*, so the state vector mod m evolves in a finite set under an eventually-periodic map
    ⟹ eventually periodic mod m; boundedness with `m>2B` lifts to ℤ; cf. Garrabrant–Pak,
    *P-Recursive Integer Sequences and Automata*).  B says **uncited / likely false for
    P-recursive (only C-finite)** and exhibited *no* counterexample.
  - **Adjudication:** A's mechanism is concrete, constructive in spirit, and correct (mod-m
    periodicity of `ℤ[n]` coefficients is elementary; the finite-state lift is standard).  B's
    objection asserted a counterexample without producing one and conflated P-recursive with
    C-finite.  **Verdict: A is right — the implication holds for integer P-recursive.**  But
    keep B's caution visible: it is a *classical* input (not ∅-axiom here; the mod-m+finite
    automaton argument is not formalised), and the cleanest indisputable sub-case is C-finite.

**B (red-team) — accepted corrections (folded into the Lean file):**
  1. `positive_floor_unbounded` is **SOUND, fully constructive** (explicit witness, no LPO).
  2. `bounded_floor_zero` is sound **because the codomain is ℕ** (`c<1 ⟺ c=0` decidable); it
     is proved **directly** (assume `c≥1`, derive a concrete value beating the bound), *not*
     by `¬¬`-elimination of an `∃`.  ✅ matches the Lean proof.
  3. **Dropped the word "dichotomy"** and any "collapse to constant" suggestion — constructively
     only the *top* coefficient vanishes; lower-coefficient collapse is the LPO step.  Renamed
     file `BoundedDepthDichotomy → PositiveFloorUnbounded`.
  4. **Scope fix (item 5):** removed the over-reaching "all higher tiers need unbounded p.q."
     The lemma's hypothesis class is positive-degree polynomial sections only; periodic and
     exponential sections are *outside* it.  The `2ⁿ` gap is **not** covered.
  5. C8 reframed as modest *methodological localization*, not an explanation (see below).

**C (repo-infra):** `Nat.lt_or_ge`, `Nat.eq_zero_or_pos`, `Nat.not_succ_le_zero`,
`Nat.lt_irrefl`, `Nat.lt_of_lt_of_le`, `Nat.le_add_left`, `Nat.add_assoc`, `Nat.sub_self`,
`Nat.sub_le_sub_right` all ∅-axiom-safe (last used inside pure NatHelper proofs).
**Landmine hit:** `Nat.sub_eq_zero_of_le` leaks `propext` — replaced by
`Nat.sub_le_sub_right hge b` + `Nat.sub_self` (`a−b ≤ b−b = 0`) in `lt_of_one_le_sub`.
Logged for HANDOFF's propext list.

## Conjecture log (this session — red-team-corrected)

**C8 (boundedness localization, MODEST).**  The elementary periodicity route to π's
non-holonomicity is **unavailable in the regime π is expected to inhabit**.  Precisely: *if*
π's partial quotients were bounded, then [bounded + holonomic ⟹ eventually periodic (A's
classical theorem, mod-m argument) ⟹ quadratic irrational (Lagrange) ⟹ contradiction with π
transcendental], so π would be non-holonomic by the elementary route.  Since π's p.q. are
*expected unbounded* (heuristic, OPEN), this conditional has an antecedent everyone expects is
false — it is **not an explanation of difficulty but a localization of it**: any proof of π's
non-holonomicity must engage the *unbounded growth* of the partial quotients directly, not
route through periodicity/quadraticity.  (Honest novelty: low — the steps are classical; the
content is the localization + its ∅-axiom partial witness `positive_floor_unbounded`.)
  - *Scope caveat (B):* "π non-holonomic" must mean "π's **partial-quotient sequence** is not
    P-recursive" — distinct from any holonomicity of π-as-a-number.  C8 constrains only the
    p.q. sequence.

**C9 (the ∅-axiom-provable nucleus, PROVEN).**  A continued fraction with a **genuine
positive-degree polynomial residue section** has **unbounded** partial quotients
(`positive_floor_unbounded` on the section; witnessed by `ePQ_unbounded` for e).  This is the
clean, scoped, fully-constructive content extracted from the (overclaiming) "dichotomy".

**C10 (Klazar route) — CLOSED ∅-axiom this session.**  `Cauchy/NonHolonomicWitness.lean`
(22 PURE).  The *elementary* form of Klazar's bound IS ∅-axiom-provable (the analytic D-finite
theory is **not** needed): define the eventual growth majorant `HolonomicGrowth` (the shadow
every ℕ-valued P-recursive sequence satisfies past the roots of its leading coefficient), prove
its Klazar envelope by subtraction-free **window-sum telescoping** (`holonomicGrowth_envelope`:
`W(n+1) ≤ (C+1)(n+1)^D·W(n)` ⟹ `W(N+m) ≤ W_N·(C+1)^m·((N+m)!)^D`), and exhibit the
super-factorial witness `superFact n = (n!)ⁿ` that beats every envelope (`envelope_exceeded`,
explicit `m = 2(W+C+D+2)²+2`).  Result: **`superFact_nonHolonomic : ¬ HolonomicGrowth ((n!)ⁿ)`**
— the first ∅-axiom certificate of **non-holonomicity proper**, the genuine top tier strictly
above the C-finite `2ⁿ`.

A 4th red-team agent validated the design and forced two corrections, both folded in:
- **`HolonomicGrowth` must be eventual (`∃N, ∀ n ≥ N`).**  A genuine P-recurrence's leading
  coefficient `p_k(n)` has finitely many integer roots; at a root the per-`n` majorant
  inequality can fail.  Without the `∃N` quantifier a singular-but-holonomic sequence would be
  *falsely* certified non-holonomic — the certificate's soundness rests on
  `P-recursive ⟹ HolonomicGrowth`, which only holds eventually.
- **The bridge is the triangle inequality, not "division rounds down".**  `|p_k(n)|·a_{n+k} =
  |Σ p_i(n) a_{n+i}| ≤ Σ |p_i(n)|·a_{n+i}`, then `|p_k(n)| ≥ 1` (non-root) drops the factor.
  ℕ-valuedness of `(aₙ)` is essential and explicit.  The certificate is **one-directional**
  (sufficient, not a characterisation): `HolonomicGrowth` is strictly weaker than P-recursive,
  so it cannot detect *every* non-holonomic sequence — only those whose growth beats the
  envelope.  (So `(n!)ⁿ` is certified; π — slowly-growing CF — is **not** reachable this way,
  which is exactly why π's CF non-holonomicity stays open.)

Tooling note: `omega`, Mathlib `set`/`conv` are all unavailable/axiom-dirty here; every
add/pow rearrangement is by hand (single-step `Nat.add_assoc`/`add_comm` calc + pure NatHelper).
New reusable pure helpers: `mul_lt_mul_left_pure`, `pow_mul_pure`, `pow_lt_pow_right_pure`,
`le_fact`, `windowSum`(+`windowSum_shift`, the subtraction-free identity), `four_comm`.

**Next (C11):** the genuine tier is now inhabited by `(n!)ⁿ`; π's CF remains *conjectured* at
tier 3 but is **provably not reachable by the Klazar/growth route** (π's partial quotients do
not grow super-factorially — they are conjecturally Gauss–Kuzmin, bounded-in-`log`-average).
So tier-3 membership of π needs a *different* obstruction (FGS asymptotic shape, not growth) —
the genuinely hard, still-open core.

## Session log

  - 3 agents dispatched in parallel (A literature, B red-team, C infra).
  - `PositiveFloorUnbounded.lean` written, built, 11 PURE / 0 dirty; one propext landmine
    (`Nat.sub_eq_zero_of_le`) caught and replaced.
  - Docstrings + filename corrected to the honest scope (B items 2–5).
  - Promoted: see `theory/math/analysis/cf_holonomicity_hierarchy.md` (frontier section
    updated with the positive-degree-section unboundedness result).
