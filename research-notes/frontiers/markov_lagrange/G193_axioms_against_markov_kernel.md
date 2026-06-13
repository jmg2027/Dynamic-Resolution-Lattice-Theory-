# G193 — The 213 axioms read against the Markov kernel: a standing record and attack map

A deep reading of the 213 axiom corpus (`seed/AXIOM/01–08`) against the open Markov uniqueness
(Frobenius 1913) kernel, plus a consolidated ledger of every direction explored this branch.  Purpose
(per the operating stance: *an unproven target is probed by recording every direction and attacking*):
make the foundational resonances explicit, log what each yields, and rank the live directions.  Discipline
throughout (`CLAUDE.md` failure catalog): a *resonance* or *location* of `H` in 213's structures is not a
proof and not leverage; each item is confidence-labeled.

---

## Part 1 — The axioms, read against the kernel

### A. The recurring `5` is `d`; the Markov tree is rooted at the φ self-reference fixed point. [SOLID]

`seed/AXIOM/06_lens_readings.md` §6.8 + `05_no_exterior.md` §5.6.  The atomic shape is `(NS,NT,d)=(3,2,5)`.
The Markov objects are *literally* readings of this shape, confirmed in code:
  - the Markov equation `x²+y²+z² = 3xyz` has coefficient **`3 = NS`** (`MarkovTree.markovEq`);
  - the tree's **root node max is `markovNum [] = 5 = d`** (`SternBrocotMarkov`, §2 bundle);
  - the first composite worked case is **`1325 = 5²·53 = d²·53`**, realized triple `(13,34,1325)` with
    `13,34` Fibonacci (`markov_max_unique_1325`).
The all-one-direction spine is the **Fibonacci/golden spine** (`aPhi i = fib(2i+2)`, `dPhi i = fib(2i+1)`,
`CrossDetConstDenom`; convergents → φ²).  By §5.6, φ = (1+√5)/2 is *the algebraic embodiment of the
minimum fixed point of self-reference* (the Möbius iterator `P(x)=(2x+1)/(x+1) → φ`, ∅-axiom in
`Mobius213`).  So the user's recurring "5" is **not coincidence: it is `d`, and `√5` is the φ-discriminant
of the residue's self-reference fixed point**, on whose Fibonacci spine the Markov tree is rooted.  This
places the entire Markov frontier *inside* the atomic shape, not beside it.

### B. `H` is the compatibility of 213's two self-reference forms (Bool-oscillation vs Nat-convergence). [SUGGESTIVE — a location, not a theorem]

`05_no_exterior.md` §5.2 distinguishes two structurally distinct realisations of the residue's
self-reference, *co-present aspects of one event*:
  - **Bool-style** (liar): an involution `not`, *no fixed point*, oscillation (`not²=id`, `not x ≠ x`);
  - **Nat-style** (Lambek): a fold/iteration that *converges* and *stays* (a reached fixed point).

The Markov structure carries **both, concretely**:
  - the `√(−1)` residue mod `c` / the **Cohn matrix `C² ≡ −I (mod c)`** (`MarkovUniqueness` §9) is an
    **order-4** element — the `i`, a Bool-style oscillation with no fixed point (the frozen, Bool-adjacent
    reading of §5.7);
  - the **Vieta tree descent** `c ↦ 3ab−c` to the root is **Nat-style** convergence.

Then the kernel reads, 213-natively: **`H`/realizability = "which Bool-oscillatory mod-`c` residue lifts
to a Nat-convergent tree path"** — the compatibility of the two self-reference forms on the same residue.
This is exactly the repo's prose "which ℤ-lift survives the full Vieta descent" (`markov_uniqueness.md`),
re-seen in the axiom's own taxonomy.  §5.2 even pre-classifies the *failure modes*: a derivation of `H`
can fail only as (i) oscillation-that-never-settles or (ii) a fixed-point-not-yet-reached — both repaired
*internally*, never by an external axiom.  **Value**: it *locates* `H` in the foundational taxonomy and
tells us the attack is a Bool↔Nat compatibility, not a new structure.  **Not** a proof or constraint.

### C. `H` should be attacked as a *forced fixed point*, the signature 213 move (§4.3 shape). [METHODOLOGICAL STEER]

`04_uniqueness.md` §4.3 + `08_falsifiability.md` §8.4: with no exterior dialer (§5.1), the shape `(3,2,5)`
is fixed not by choice but as **"the only self-consistent fixed point under the constraints"**; physical
constants likewise "appear only as residue-internal fixed points."  The Markov realized suborbit is a
*point of a torsor* (`SqrtUnity` free action, `root_orbit_inj`), and a torsor has no canonical point — so
by no-exterior the selection **cannot be an external label; it must be a forced internal fixed point** of
the Vieta dynamics.  This steers the attack: rather than *searching* which suborbit realizes, seek a
**uniqueness-by-forcing** argument — show realizability is the unique self-consistent fixed point — mirroring
how §4.3 forces `(3,2,5)` and how `slope_path_inj` already forces the slope.  Consistent with B (the
forcing is the Bool↔Nat compatibility).  **Steer, not a lemma.**

### D. The whole frontier sits on three adjacent rungs of the §6.7 number-tower cascade. [SOLID]

`06_lens_readings.md` §6.7: ℕ→ℤ→ℚ→ℝ are successive Lens bundlings of one residue.  Mapping the Markov
readings (G192) onto the cascade:
  - **ℚ-Lens** (ratios of chain readings, *coprimality from `det P = 1`*) = the **slope** `p/q` =
    `mediantLens` (the geodesic projection).  The repo's `sbInterval_adj` (det-1 Farey adjacency) *is* the
    §6.7 coprimality condition.
  - **ℤ/difference-Lens** (count read on an ordered pair, `subNatNat`) = the **residue** `markovRes`
    (`d − c`) and the signed structure.
  - **ℕ/count-Lens** (`Lens.leaves`) = the **size** `markovNum`.
So the frontier is not foreign material — it is three canonical rungs of the residue's own number cascade,
with the geodesic (ℚ-rung) as the genuinely Raw-Lens reading (G192).  This grounds the "three readings" in
the axiom's number theory rather than in an imported analogy.

### E. The ∅-axiom contract and the "honest verdict" are the §8.2/§8.3 internal audit. [SOLID — discipline]

`08_falsifiability.md` §8.2–8.3: falsifiability = the ∅-axiom contract; "abandon on derivation failure" is
*not external refutation* but "a 213-internal confirmation that the chosen Lens fails to produce
something."  This *is* the stance taken throughout G189–G192: the §34 iff and the continuant lemmas pass
`#print axioms` clean; the repeated "necessary-not-sufficient / boundary / no-leverage / renaming"
verdicts are the internal audit recording exactly where a Lens does not yet produce `H` — not a concession
to an outside, but the framework auditing itself.  The restraint (G192 §D: no manufactured theorem) is
§8.3 in practice.

---

## Part 2 — Directions ledger (everything tried this branch, with status)

| # | Direction | Artifact | Status / verdict |
|---|---|---|---|
| 1 | Reduce composite-`c` uniqueness to phantom elimination (orbit tower) | `SternBrocotMarkov` §20–§29, `OrbitRealizabilityH`, `markovMaxUnique_iff_orbitRealizabilityH` | ✅ ∅-axiom.  Perimeter: `H` named + equated to Frobenius; kernel untouched. |
| 2 | Forward bridge: size-injective ⟹ uniqueness | §33 `markov_max_unique_of_markovNum_injective` | ✅ ∅-axiom. |
| 3 | **Reverse bridge: uniqueness ⟹ size-injective; the literal iff** | §34 `markovNum_injective_of_markovMaxUnique`, `markovMaxUnique_iff_markovNum_injective` | ✅ ∅-axiom.  **Sourced**: this iff *is* the modern Frobenius statement (map injectivity).  Perimeter (formulation-equivalence). |
| 4 | Casoratian / discrete-Wronskian as cross-node tool | `G189` (corrected) | ❌ within-recurrence only; wrong shape for two incomparable transfer products. |
| 5 | Continuant / Aigner-ordering program (classical core) | `G191`, **`Real213/ContinuedFraction/Continuant.lean`** (E1 ✅) | ✅ E1 ∅-axiom (continuant + monotonicity).  Aigner = necessary-not-sufficient; E2–E5 unbuilt; Frobenius continuant formula (E4) is the substantial bridge. |
| 6 | Raw/Lens-native reading; the geodesic-engine boundary | `G192` | ✅ analysis.  **Boundary result**: geodesic (`mediantLens`) closes the direction-free layer (slope injective) and *structurally stops* at the orientation (size not direction-free).  All hard 213 constraints fix structure, none selects realization. |
| 7 | Cluster algebra / snake graph / frieze (LLRS route) | survey | ❌ entirely absent in repo; from scratch; CF/continuant route cheaper. |
| 8 | Cohomological gluing (ℤ/2 sign-cochain over ω primes ↔ `H¹(torus)`) | `G192` §B, `Cohomology/{Delta,Cochain}` | ⚠ structural rhyme only; realizability-map-as-δ unbuilt; not yet a constraint. |
| 9 | Axiom-level resonances (this note) | `G193` A–E | ✅ recorded: A,D,E solid; B a location; C a steer. |

---

## Part 3 — Live directions, ranked (for the next attempts)

1. **E2 (concrete, cheap, on-path)**: `continuant K[a₁..aₙ] = (∏[[aᵢ,1],[1,0]]).(1,1)` — connect
   `Real213/ContinuedFraction/Continuant` to `Mat2`.  First rung of the oriented bridge `markovNum = K(CF-shape of slope)`.
   ∅-axiom, non-cross-node.  *Then* E3 (path → Christoffel run-lengths → CF quotients; genL/genR vs
   `[[a,1],[1,0]]` basis change), E4 (the Frobenius formula — substantial), E5 (one Aigner ordering = the
   first genuine cross-node ∅-axiom Markov ordering, necessary-not-sufficient).

2. **B/C made formal (ambitious, the real shot)**: attempt `H` as a *forced fixed point* via the Bool↔Nat
   compatibility — does the Nat-style Vieta descent uniquely pin the Bool-style `√(−1)` torsor point?
   Concretely: is there an ∅-axiom *forcing* argument (not a search) that the realized window-root is the
   unique fixed point of [the descent restricted mod `c`]?  This is the only direction aimed *at* the
   kernel rather than around it; high risk, possibly equivalent to the conjecture.

3. **Count theorem (clean, narrows precisely)**: "the number of windowed `√(−1)` roots mod `c` = `2^(ω−1)`"
   as a single ∅-axiom statement (CRT over the `SqrtUnity` free action).  Formalises the "narrowing" G192
   identified; classical number theory, substantial but bounded.

4. **Cohomological gluing (speculative)**: build the realizability sign-pattern as an explicit ℤ/2 cochain
   over the ω prime factors and test whether a `δ`/coboundary condition captures "realized by one global
   triple" — at `ω=2` (e.g. `c=1325`) the data is one bit (`507` realized vs `182` phantom), a concrete
   test case.  If the δ-framing is more than renaming, it would align with the classical `H¹(torus)` stable
   norm; if not, log as rhyme and drop.

**Standing honest position (unchanged across all of Part 1–3):** every analysis — classical (Aigner
necessary-not-sufficient), Raw/Lens-native (constraints fix structure, not selection), and axiom-level
(`H` = a forced-fixed-point / Bool↔Nat compatibility) — *converges* on the same map: the structure is
fully pinned, the **realizability selection is the sole open freedom**, and it is exactly `H`.  No
direction has crossed it; directions 1–4 are how we keep attacking.

### Pointers
- iff (= Frobenius): `Real213/Markov/SternBrocotMarkov` §34 `markovMaxUnique_iff_markovNum_injective`
- continuant tool: `Real213/ContinuedFraction/Continuant.lean`
- companions: `research-notes/G191_continuant_aigner_program.md` (classical), `research-notes/G192_markov_kernel_raw_lens_native.md` (Raw/Lens), `G189` (Casoratian correction)
- axioms read: `seed/AXIOM/{01_residue, 04_uniqueness §4.3, 05_no_exterior §5.2/§5.6, 06_lens_readings §6.7/§6.8, 08_falsifiability §8.2/§8.4}`
- φ engine: `Mobius213` (`P(x)=(2x+1)/(x+1)→φ`), `Real213/CrossDet/CrossDetConstDenom`/`FibCassiniNat` (Fibonacci spine)
