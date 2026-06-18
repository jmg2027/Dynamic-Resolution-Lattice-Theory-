# Publishability / literature-novelty audit — whole-repository sweep

**Date:** 2026-06-18. **Method:** six parallel adversarial deep-research audits
(web access), one per content cluster, each instructed to *hunt the prior art that
refutes novelty* — default prior "this is classical, find where it is known" — plus
cross-check searches. Each cluster report is preserved verbatim under `/tmp/audit/`
during the session; the citations below are lifted from them. This file is the
synthesis owed to the directive "do it for every content in the repository … show me."

**One-sentence verdict.** Across every mathematical cluster the *theorem content is
classical and already-known* (often already in Mathlib), with precise prior-art
citations below; the **single genuinely distinctive artifact in the whole repository
is the strict ∅-axiom Lean 4 formalization at ~2k-module scale, built without Mathlib,
against the grain of a classical-by-policy system** — a *formalization / experience*
contribution (ITP/CPP/JAR), **not new mathematics**. Reported honestly, that is a real
contribution; reported as "new theorems" or "new foundations," it is rejection-bait.

This is exactly what the repo's own discipline predicts. CLAUDE.md's primacy gate
(`07_primacy.md` §7.1) defines progress as *breadth of ∅-axiom re-derivation* — the
residue reproducing domain after domain — **not** as theorem-level novelty. The audit
confirms the breadth is real and the re-derivations are sound; it does *not* find new
mathematics, and the program never claimed to.

---

## Cluster verdicts (all six)

### 1. Number theory — `/tmp/audit/01_number_theory.md`
All seven results classical; all have Mathlib formalizations of the *statement*, so even
"first formal proof" is unavailable.

| Result | Status | Prior art |
|---|---|---|
| Generalized Wilson, group-free `+1` | classical theorem; technique is folklore | Gauss 1801 (*Disq. Arith.* art. 78); **G. A. Miller, *Ann. Math.* 4(4) 1903, 188–190** (product of all elements of a finite abelian group = the unique involution else identity); Mathlib `NumberTheory.Wilson` |
| Fermat two-square via Thue + pigeonhole | classical | Thue 1902; Mathlib `Nat.Prime.sq_add_sq` |
| `x⁴+y⁴=z²` by descent | classical | Fermat; Mathlib `FLT.Four` |
| FTA-uniqueness as `vₚ`-count | classical (and circular unless `vₚ`-additivity built from Euclid) | Mathlib `Nat.factorization` |
| Pisano period / rank of apparition | classical | Wall, *AMM* 67 (1960) 525 |
| Eisenstein `p=x²+xy+y²` via Thue (disc −3) | classical | Gauss binary-quadratic-form theory |
| Totient multiplicativity via CRT bijection | classical (THE textbook proof) | Mathlib `Nat.totient_mul` |

The **group-free Wilson `+1`** is the only piece with any expository angle, and only as a
short *Monthly/Math-Mag* pedagogy note — referees will cite Miller 1903 and the
elementary-abelian-2-group folklore (`P ≡ t^{|S|/2}` is that result de-grouped, not a new
idea). Realistic research-novelty: none.

### 2. Constructive reverse math — `/tmp/audit/02_constructive_reverse_math.md`
This was the prompt's *highest*-novelty hope. It fails the hardest: every calibration is a
named published result.

| Calibration | Status | Prior art |
|---|---|---|
| sign dichotomy `x≤0 ∨ 0≤x` ⟺ LLPO | the *definition* of analytic LLPO | Bishop 1967; nLab; Diener CRM arXiv:1804.05495 |
| real `=` ⟺ WLPO; apartness ⟺ MP; LPO⟺WLPO∧MP | standard table entries | nLab decidable-equality; Ishihara 2006; Diener |
| comparability ⟹ LLPO | classic Brouwerian | Bishop–Bridges 1985 |
| Heine–Cantor ⟺ fan theorem | classic (Brouwer) | Veldman; Julian–Richman 1984 |
| Dini ⟺ fan theorem (detachable bars) | **exact rung is published** | **Berger–Schuster, *NDJFL* 47(2) 2006** |
| binary BW: ⟹LPO; extraction Π⁰₂ above base | known — and a **sharper** version is published | **Mandelkern 1988** (BWP⟺LPO, *Bull. LMS* 20(4)); **Brattka–Gherardi–Marcone 2012** (binary BW = jump of LLPO = `LLPO′`, arXiv:1101.0792); **Kohlenbach–Safarik 2010** (Π⁰₂ content) |

The designated best candidate — binary Bolzano–Weierstrass "strictly above LPO, Π⁰₂" — is
not only known (Mandelkern's 1988 lower bound) but the corpus's "above LPO" is *coarser
and slightly mis-aimed* versus the sharp published degree `BW_{2^ℕ} = LLPO′`
(Brattka–Gherardi–Marcone). The corpus sits **behind** the frontier here, not at it.

### 3. Constructive analysis (moduli) — `/tmp/audit/03_constructive_analysis.md`
Results 1–6 are textbook Bishop / proof-mining staples (located-sup EVT; geometric Banach
rate; continuous⇒integrable; Cesàro/Leibniz/comparison moduli; uniform-limit 3ε modulus;
modulus-equipped metric space). Result 7 (omniscience cost as a denominator/precision
blow-up) is the one candidate: substance is the standard located-real separation fact +
LLPO's *deliberate non-uniformity* — so there is **no uniform bound to prove** (that's the
whole point); at most a fresh expository framing, not a theorem. Prior art: Bishop–Bridges
*Constructive Analysis*; Kohlenbach *Applied Proof Theory* (2008); Schwichtenberg
*Constructive Analysis with Witnesses*; O'Connor completion monad (arXiv:0805.2438). The
formalization niche is **already crowded** (C-CoRN, Minlog, Agda Bishop reals, Coq exact
reals) — only the ∅-axiom footprint differentiates, and it must out-position C-CoRN/Minlog.

### 4. Combinatorics — `/tmp/audit/04_combinatorics.md`
Six classical theorems (1934–1971), all with standard already-constructive proofs.
The two flagged hooks both fail:
- **Witness-returning finite pigeonhole** — trivial (finite PHP is decidable) and *already
  in Mathlib* (`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`,
  `Fintype.exists_ne_map_eq_of_card_lt`). "Returns the pair vs refutes injectivity" is a
  presentation choice (constructively equivalent over decidable-eq finite types).
- **"Non-constructivity sink"** — the *localization* idea is a real, named research theme
  (Oliva–Powell arXiv:1204.5631; Powell *JLC* 22(2) 2012; Escardó *InfinitePigeon*;
  Kohlenbach) **but only for the INFINITE pigeonhole**, which carries genuine non-computable
  content. Applied to the *finite* PHP the corpus uses, the "localized non-constructive step"
  is decidable, hence vacuous. The term "non-constructivity sink" is the corpus's own coinage.

Erdős–Szekeres and Rédei (path-existence) are apparently *not* in Mathlib → a modest
"first axiom-free Lean formalization" datapoint, nothing more. Hall (#6) is a partial (n≤2)
fragment of an already-merged general Mathlib theorem (Gusakov–Mehta–Miller arXiv:2101.00127).

### 5. Formalization methodology — `/tmp/audit/05_formalization.md`
**This is where the real contribution lives.** Closest prior art and why it caps the claim:
- **TypeTopology (Escardó), Agda `--safe --without-K`** — the single most damaging
  comparison: large, respected, *never postulates* funext/propext/EM (threads them as
  explicit hypotheses), embodying the same "math that needs no axiom doesn't use it" thesis.
- **C-CoRN / agda-unimath / UniMath** — constructive but axiom-*bearing* (setoids /
  postulated funext / univalence). So "constructive formalization in general" is well-trodden.

What no existing development matches — **the defensible novelty is the combination**:
strict `propext`/`Quot.sound`/`Classical.choice`/`funext`-free *mathematical content*, in
**Lean 4** (a system whose maintainers explicitly *declined* to compartmentalize axioms and
told constructive users to use Agda/Coq — Lean Zulip "Compartmentalization of axioms"
thread), **without Mathlib** (reimplementing Nat/Int/List/Real to escape Mathlib's hidden
axiom leakage), at **~2,196-module scale**, with a **scanner-enforced** purity discipline
(`scan_all_axioms.py`) and a **whole-corpus axiom scan**.

Two honesty corrections a reviewer would catch (and the paper must front-load):
1. **"Literally zero axioms" is overstated.** `STRICT_ZERO_AXIOM.md` carves out a
   *sealed-DIRTY-by-design* class using `propext` (Prop-encodings), `funext`/`Quot.sound`
   (Lens equality), `Classical.choice` (elaborator plumbing). The honest claim is *purity of
   mathematical content with an enumerated boundary*, not absolute axiom-freedom.
2. The "~19.6k decls, no math theorem needs an axiom" scan is a statement about *this
   reimplemented corpus*, corroborating Bishop/Ishihara — not a universal claim.

**forcing-vs-bookkeeping** is the freshest conceptual piece but is a *re-framing* of proof
mining / Kreisel unwinding (Kohlenbach) + constructive reverse math (vein-C is CRM almost
verbatim). Sell it as a *practical evidential discipline for axiom-purity projects*, not a
new theory.

### 6. 213/DRLT foundations framework — `/tmp/audit/06_foundations.md`
Each foundational piece maps to a named standard notion; once translated the novelty
evaporates:

| Component | Closest established idea | Verdict |
|---|---|---|
| `object1_not_surjective` / FlatOntologyClosure | Cantor's theorem = canonical **Lawvere fixed-point** instance (`not:Bool→Bool` fixed-point-free); the Lean is literally `cantorDiag e n = !(e n n)` | RE-SKIN |
| `Real213` `Nat→Nat→Bool` cuts + modulus | Bishop modulus reals + located/decidable Dedekind cut / comparison-oracle / locator (Bauer–Lumsdaine arXiv:1510.00641; Booij arXiv:1805.06781; Ciaffaglione–Di Gianantonio) | RE-SKIN (niche-formalization at most) |
| Lens / residue / pointing | catamorphism (`view = Raw.fold`, fold of initial F-algebra) + kernel/setoid refinement lattice | RE-SKIN (renamed) |
| "modulus programme" thesis | Bishop "computational content" + proof mining + computable analysis | RE-ARTICULATION of a known stance |

The private vocabulary is a **publication liability** (reviewers will demand translation;
the repo's own foundational docs don't cite Lawvere/Yanofsky/Bishop — the biggest reframing
gap). The zero-axiom discipline is the one unusual property, and it is *engineering*, not a
mathematical discovery.

---

## Synthesis — what (if anything) is publishable

**Genuinely new mathematics: none found, across all six clusters.** Every theorem is
classical (Gauss 1801, Miller 1903, Thue 1902, Fermat, Wall 1960, Bishop 1967, Brouwer,
Mandelkern 1988, Berger–Schuster 2006, Brattka–Gherardi–Marcone 2012, …), and the
"distinctive" constructive/witness framings are the standard constructive content the
literature already supplies. Several candidates (binary BW, the omniscience-cost modulus,
the non-constructivity sink) are not just known but **published sharper elsewhere** or
**misapplied** (sink → infinite PHP).

**The one publishable kernel — a formalization paper, framed honestly:**

> *Strict-∅-axiom mainstream mathematics in Lean 4 without Mathlib: a methodology and a
> ~2,000-module corpus* — certifying `propext`/`Quot.sound`/`Classical.choice`/`funext`-free
> *mathematical content* in a classical-by-policy system whose maintainers declined axiom
> compartmentalization, by reimplementing the numeric/collection basis to eliminate hidden
> Mathlib axiom leakage; with (a) the "pure-twin" technique + scanner-enforced discipline,
> (b) a whole-corpus axiom scan finding no mathematical theorem requires a non-constructive
> axiom, and (c) the forcing-vs-bookkeeping criterion for grading the evidential value of
> axiom-free re-derivations.

- **Venue:** ITP / CPP / JAR (experience + methodology track). Not a mathematics venue.
- **Lead with:** the Lean-specific, against-the-grain, no-Mathlib difficulty + the scan data
  (mechanically checkable `#print axioms` certificates — a CPP plus).
- **Concede up front:** the constructive-math lineage (cite TypeTopology, C-CoRN, Bishop,
  Diener CRM, Kohlenbach); the sealed-DIRTY carve-out; "purity of mathematical content,"
  not absolute.
- **Extract cleanly from the 213/DRLT metaphysics** — "the residue," Lens vocabulary, the
  physics motivation. ITP/CPP reviewers react badly to it, and it is not needed for the
  formalization claim.

**Honest bottom line for the program.** The audit is a *negative* result on theorem-novelty
and a *positive* result on what the program actually set out to do: reproduce discipline
after discipline from a zero-axiom basis, breadth-first (the §7.1 primacy gate). That breadth
— number theory, constructive analysis, constructive reverse math, combinatorics, reals — all
verified ∅-axiom in one Lean library, *is* the artifact. It is publishable as engineering and
as an empirical "how much mainstream math is genuinely axiom-free" data point. It is not, and
was never claimed to be, a source of new theorems.

---

## Cross-cutting prior-art index (for any future write-up)

- Gauss generalized Wilson: Miller, *Ann. Math.* 4(4) 1903; Sury survey; Mathlib `NumberTheory.Wilson`.
- Constructive reverse math base text: Diener, *Constructive Reverse Mathematics*, arXiv:1804.05495; Diener–Ishihara (Springer 2021).
- Dini = fan theorem (detachable bars): Berger–Schuster, *NDJFL* 47(2):253, 2006.
- Binary BW degree: Brattka–Gherardi–Marcone, *APAL* 163(6) 2012, arXiv:1101.0792; Mandelkern, *Bull. LMS* 20(4):319, 1988; Kohlenbach–Safarik, *MLQ* 56(5) 2010.
- Bishop analysis / moduli: Bishop–Bridges, *Constructive Analysis*; Schwichtenberg, *Constructive Analysis with Witnesses*; Kohlenbach, *Applied Proof Theory* (2008).
- Infinite-PHP localization: Oliva–Powell arXiv:1204.5631; Powell *JLC* 22(2) 2012; Escardó *InfinitePigeon*.
- Hall in Lean: Gusakov–Mehta–Miller, arXiv:2101.00127. Dilworth/Mirsky/E–S/Hall in Coq: arXiv:1703.06133.
- Axiom-free formalization prior art: TypeTopology (Escardó); C-CoRN; agda-unimath; UniMath; Tao's Lean4 Nat-from-scratch.
- Foundations mappings: Lawvere FPT (TAC reprint 15, 1969); Yanofsky self-reference; Bauer–Lumsdaine constructive Dedekind reals arXiv:1510.00641; Booij locators arXiv:1805.06781; Ciaffaglione–Di Gianantonio coinductive reals.
- Lean team declines axiom compartmentalization: leanprover-community Zulip "Compartmentalization of axioms in Lean 4".
