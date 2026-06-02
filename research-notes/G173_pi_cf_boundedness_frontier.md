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

**C10 (Klazar route, classical, for the record).**  A constructed CF with **super-`(n!)^d`**
partial-quotient growth is **non-holonomic** (Klazar's bound, contrapositive) — a *genuinely
non-holonomic* witness, unlike `2ⁿ` (which is C-finite, only non-Hurwitzian).  This would
populate the true top tier (non-holonomic) above the current `2ⁿ` (non-Hurwitzian-but-
holonomic) witness.  Not ∅-axiom (Klazar's bound is analytic/D-finite theory), but a
candidate target if a ∅-axiom growth-vs-recurrence obstruction can be built over the repo's
`liftK` ladder.  **This is the most promising next provable increment.**

## Session log

  - 3 agents dispatched in parallel (A literature, B red-team, C infra).
  - `PositiveFloorUnbounded.lean` written, built, 11 PURE / 0 dirty; one propext landmine
    (`Nat.sub_eq_zero_of_le`) caught and replaced.
  - Docstrings + filename corrected to the honest scope (B items 2–5).
  - Promoted: see `theory/math/analysis/cf_holonomicity_hierarchy.md` (frontier section
    updated with the positive-degree-section unboundedness result).
