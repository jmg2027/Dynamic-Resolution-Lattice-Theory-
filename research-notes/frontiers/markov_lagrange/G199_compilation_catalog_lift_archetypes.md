# G199 — the compilation catalog: three solved theorems, three finite→uniform lift archetypes (action B)

`G196`/`G197` localized the open Markov kernel `H` to **one** irreducible instruction-residue — the
*uniform cross-word continuant-trace `SEPARATE`* — with its finite instances `decide`-verified
(`ContinuantMarkov.markovNum_injective_pathsUpTo_4`, `∅`-axiom).  The open content is a **finite→uniform
lift**: the `SEPARATE` holds on every finite path-sample; pointing at the *uniform* version is `H`.

Action B (`G198`): compile **already-solved** infinite-abstract theorems to the proof-ISA
(`seed/PROOF_ISA.md`, `lean/E213/Lens/ProofISA.lean`) and record *how each one's finite→uniform lift was
achieved*.  Payoff: a solved problem's lift mechanism is a **template** for `H`'s lift; a problem missing
the *same* residue ⟹ transfer.  Below are three solved, `∅`-axiom theorems whose lifts are **structurally
distinct** — three archetypes — and `H` localized against them.

Each entry separates the **hard fact** (the `∅`-axiom theorem + its lift mechanism) from the
**interpretation** (its ISA reading).  None of this solves `H`; it sharpens *where to look*.

---

## Archetype 1 — DIAGONAL / direct lift (the residue instruction self-supplies the uniform witness)

**Solved theorem.**  `E213.Lens.Cardinality.cantor_general` (`Lens/Cardinality/Cantor.lean`) /
`cantor_raw_bool` / `E213.Lens.FlatOntologyClosure.object1_not_surjective` — no map `X → (X → Bool)` is
surjective; no enumeration captures the residue.  **`∅`-axiom.**

**Finite vs uniform.**  *Local*: for a given candidate enumeration `f` and a given index, the diagonal
disagrees at that index.  *Uniform*: `f` is non-surjective (disagrees with *every* row).

**Lift mechanism.**  The anti-diagonal `d(n) = ¬ f(n)(n)` is built **uniformly as a function of the
enumeration**.  The local disagreement-at-index `n` *is already* the uniform witness — `d` differs from
`f(n)` at `n`, for the single uniformly-defined `d`.  **No separate lift step.**  The `DIAGONALIZE`
instruction (`isa_diagonalize`) **self-supplies** the uniform witness in one move; this is exactly "the
residue is the most-primitive proof technique for the infinite" made operational.

**ISA reading.**  `isa_diagonalize` alone.  Lift cost: **zero** (the instruction's whole content *is* the
lift).

---

## Archetype 2 — INDUCTIVE / LOOP lift (finite per-step identity + structural induction)

**Solved theorem.**  `flt_primary` (`NumberTheory/DyadicFSM/FLT/FLTPrimary.lean:44`):
`∀ a, a^(p) ≡ a (mod p)` (for `p = p'+1` with the middle binomials vanishing).  **`∅`-axiom.**

**Finite vs uniform.**  *Local*: the **freshman's dream** `freshman_dream`
(`FLT/FreshmanDream.lean:53`) — `(a+1)^p ≡ a^p + 1 (mod p)` — a single per-step identity.  *Uniform*:
the congruence for **all** `a`.

**Lift mechanism.**  Two ISA moves in sequence:
  1. `COMPILE-DOWN` (`isa_compile_down`-flavoured): the binomial theorem is reduced mod `p` — the middle
     coefficients `C(p,k) ≡ 0`, leaving `(a+1)^p ≡ a^p + 1`.  The infinite-looking binomial collapses to
     a two-term identity *at the finite step*.
  2. `LOOP` (`isa_loop`, µ-recursion): structural induction on `a` — base `0^p ≡ 0`, step uses the
     freshman dream + IH.  The finite per-step identity is **lifted to all `a` by induction**.

**ISA reading.**  `isa_compile_down ∘ isa_loop`.  Lift cost: **one induction**, available precisely
because the per-step relation closes a recurrence (`(a+1)`-case reduces to `a`-case).

---

## Archetype 3 — ORBIT / free-action lift (finite representatives + a free symmetry collapse) — *in `H`'s own family*

**Solved theorem.**  `markov_max_unique_of_orbit` (`NumberSystems/Real213/SternBrocotMarkov.lean:2135`)
+ its discharged composites `markov_max_unique_1325_via_orbit`, `markov_max_unique_985_via_orbit`
(`ω = 2` composite Markov numbers `1325 = 25·53`, `985 = 5·197`).  **`∅`-axiom.**

**Finite vs uniform.**  *Local*: at a composite `c`, the windowed `√(−1)`-roots are a **finite** set
(`{182, 507}` at `1325`; `{183, 408}` at `985`) — one `decide`.  *Uniform*: `MarkovMaxUnique c` — over
**all** triples with max `c`.

**Lift mechanism.**  The unit-root group acts **freely** on the roots; `root_orbit_inj`
(`SternBrocotMarkov.lean:2023`) — `e·u ≡ u (mod c) ⟹ e ≡ 1` — is the free-action cancellation.  The
`u₁ = u₂` coincidence then closes **structurally** (not by enumerating `b`): a nontrivial `e` fixing `u`
is forced to `e ≡ 1`, contradiction.  The finite root-window is lifted to the uniform statement by
collapsing the orbit to representatives + **one realizability check per phantom orbit** (§25–§26).

**ISA reading.**  `isa_separate` on orbit representatives, closed by the **free `ℤ/·`-action**
(structurally, the §24 cancellation), not by `DIAGONALIZE`/`decide`.  Lift cost: the orbit reduction is
`∅`-axiom; what it *leaves open* (`H` in `markov_max_unique_of_orbit`) is a **per-`c` realizability**
residue — see below.

---

## `H` localized against the three archetypes (the action-B finding)

`H` = the uniform cross-word continuant-trace `SEPARATE` (`markovNum` injective on all tree paths;
`G196`/`G197`).  Honest match:

| Archetype | Applies to `H`? | Why |
|---|---|---|
| 1 — DIAGONAL | **No** | Paths do not *anti-construct* a Markov number; there is no self-referential diagonal to read off `markovNum`.  The residue here is not a Cantor diagonal. |
| 2 — LOOP | **No (not directly)** | Trace-injectivity is **global cross-word**, not a single-step recurrence: no per-step IH closes "all *distinct* paths give distinct numbers" (the obstruction circles back to `H`, `G197`). |
| 3 — ORBIT | **Closest — and in `H`'s own family** | The orbit lift *already* lifts the finite root-window to uniform composite uniqueness; its open residue is a **per-`c` realizability** statement (`markov_max_unique_of_orbit`'s `H`). |

**The sharp two-coordinate reading.**  The repo now carries `H` in **two ISA-compiled forms of the same
open residue**:
  - the **continuant-trace `SEPARATE`** form (`G196`/`G197`, `ContinuantMarkov`) — path-injectivity of
    `markovNum`;
  - the **orbit-realizability** form (`SternBrocotMarkov` §24–§26, `markov_max_unique_of_orbit`) — "no
    nontrivial-unit-root image of a realized windowed root is itself realized," uniformly in `c`.

These are *different attack surfaces* on the one residue.  Archetype 3 is the only realized template that
lifts a finite Markov sample to a uniform Markov truth — and it does so by a **free group action**, the
`isa_loop`/µ-ν territory action A targets.

**What this arms (for A).**  A's question becomes concrete: *does the cross-word trace `SEPARATE` admit a
free-action / orbit reduction the way the composite root-window did?*  The orbit machinery
(`root_orbit_inj`, §24–26) is built and `∅`-axiom; the untried framing is whether path-level
trace-distinctness is the **fixed-point/orbit-coincidence** of some residue recursion whose finite-path
certification (`isa_loop`, `slashNu_final`) yields the uniform truth.  Neither the trace-`SEPARATE` form
nor the orbit-realizability form is closed — but they are now two coordinates, and archetype 3 says the
orbit one is the coordinate with a *realized lift precedent in the same family*.

---

## Catalog status (cumulative instrument)

Three solved archetypes recorded — DIAGONAL (cost 0), LOOP (cost: one induction), ORBIT (cost: free-action
collapse + per-case realizability).  `H` matches none cleanly; **closest = ORBIT**, same family, lift
precedent realized.  This is the action-B payoff: not a solve, but a *localized direction* — A should
probe the orbit/µ-ν lift of the trace-`SEPARATE`, the one archetype with a same-family precedent.

### Pointers (all `∅`-axiom)
- A1 DIAGONAL: `Lens.Cardinality.cantor_general`, `FlatOntologyClosure.object1_not_surjective`
- A2 LOOP: `NumberTheory.DyadicFSM.FLT.flt_primary`, `…FLT.freshman_dream`
- A3 ORBIT: `NumberSystems.Real213.SternBrocotMarkov.{markov_max_unique_of_orbit, root_orbit_inj,
  markov_max_unique_1325_via_orbit, markov_max_unique_985_via_orbit}`
- `H` forms: `ContinuantMarkov.markovNum_injective_pathsUpTo_4` (trace `SEPARATE`),
  `markov_max_unique_of_orbit`'s `H` (orbit realizability); `G196`, `G197`
- ISA: `seed/PROOF_ISA.md`, `lean/E213/Lens/ProofISA.lean`

(Scratchpad — promote to `theory/` if the catalog stabilizes into a method chapter; action C.)
