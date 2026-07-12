# The year horizon — a divergence pass over the open program

**What this is.** A single divergence pass over the whole corpus (2026-07-12),
compiled for successor sessions: roughly one year of research topics, each
grounded in a named repo anchor, with a first formalizable step, a size
estimate, and a triage class.  Tier-1 volatile.  When a topic is taken up,
open (or extend) its own frontier note; when it closes, promote per
`theory/PROMOTION_CRITERIA.md` and archive.  Nothing here is a promise —
each entry is a *pointing not yet performed* (§5.3: no automatic location).

**How to read the estimates.**  S = small (≤1 session), M = multi-session
arc, L = marathon (weeks), XL = program (quarter+).  Risk: low = the route
is visible; med = one unknown; high = the kernel may be a wall.

---

## 0. The triage doctrine — classify the kernel before attacking

The corpus has now produced enough wall post-mortems to extract a *method*
for choosing targets.  Before starting any topic below, classify its kernel:

| Class | Signature | Verdict | Precedents |
|---|---|---|---|
| **W1 unsigned monotone count** | the quantity is a count/`lcm`/`ψ`-like monotone with an elementary two-sided estimate | ∅-axiom bracketable — attack | Chebyshev both halves, `primeDensityToZero`, `chebyshev_constant_interval` |
| **W2 signed cancellation** | the content is cancellation in a signed sum; the size IS the hidden structure | no count-Lens witness — do not attack head-on; map the boundary from below | RH (`M(N)=Σμ(n)`), PNT constant `= 1` (Erdős–Selberg bilinear step) |
| **W3 uniform-residue pointing** | everything around the kernel closes; the remaining step *is* the conjecture | terminal — record, certify the localization, stop | Markov `H` (`G197`), the universal no-exterior `∀` (§5.1) |
| **W4 interface defect** | the "wall" lives in a too-strong interface, not the mathematics | re-specify the interface and the theorem falls | Banach wall (`banach_fixed_point_modulated`), colimit corner (quotient-as-Σ) |

The standing meta-topic: **each new failure should be filed into this table,
and each W2/W3 diagnosis should come with the *boundary mapped from below***
(the largest sub-family that is W1).  This turns walls into atlases.

---

## Track A — Foundations: the descent leg spine

The central verdict (`the_genesis_seam.md`): by the completion-engine
criterion, the act's own well-foundedness (`isPart_wf`) generates the
`Raw`/`Lens` layer and the additive semiring; **every deep discipline still
completes on the borrowed `Nat` engine**.  The year's foundational work is
to move that boundary, measurably.

**A1. FTA existence re-grounded on the Ω-descent** — re-elaborate the
multiplicative descent so the recursion completes through the additive
Ω-count (`Omega_descent`: the count drops by one per peel), not
`Nat.strongRecOn` over magnitude.  Anchors: `MulDescentRec`,
`FactorizationCarrier`, `Omega_mul`, `IsPartGroundedInduction.lean`.
First step: one theorem (`fta_exists_grounded`) whose `#print`-cone is
audited free of `Nat.strongRecOn`/`Nat.lt_wfRel`.  Size M–L, risk med.
Success = the genesis-seam boundary moves from "1 layer" to "1 layer + FTA".

**A2. Prime words as `Raw` objects** — encode the factorization word so
`Ω = Raw.leaves` literally and the `×`-peel *is* `IsPart`.  Known
obstruction: the canonicity gate `x≠y` forbids repeated-prime nested trees —
design the distinct-children multiplicity encoding first (this is a real
design problem, not a lemma).  Size L, risk high.  Anchor:
`the_genesis_seam.md` Round 2.10.

**A3. `DStr` existence leg, Route B** — the last open leg of the
distinguishing-schema program: `cata : Raw → N` and `cata_inj` by mutual
well-founded recursion on `depth`, target a *partial*-operation algebra,
keep D1–D6 only.  Closes `raw_initial = ⟨existence, dhom_unique_pointwise⟩`
for the partial-op category and discharges the rival-enumeration frame.
Anchors: `the_distinguishing_schema.md` §RESOLUTION,
`SemanticAtom.raw_initial`.  Size M, risk med.

**A4. The signed escape-pole census (a tool, then a theorem)** — the
proof-*term* invariant from `the_one_act.md`: traverse elaborated terms,
tag non-trivial `Eq.refl` nodes `+1` (defeq-converge) / `−1` (consumes a
`≠`, escape); falsifiable prediction: every TIER-B residue-cone theorem
carries exactly one `−1` node.  Precondition: route `object1_not_surjective`
through the generic `lawvere_fixed_point`.  Size M (tool) + S (audit),
risk low-med.  This is the first *quantitative* face of the residue.

**A5. Native νF — construct the never-closing ascent** — today "escape" is
witnessed only by finite shadows (`depth` cofinal, `diag`), because
Mathlib-free Lean has no coinduction.  Build a native final-coalgebra
fragment (a `Stream`-like codata via ℕ-indexed families with a bisimulation
Lens, no `Quot.sound`) sufficient to state `residue_reentry_never_closes`
as a constructed non-terminating object.  Size L, risk high (the encoding
may smuggle `funext`-shaped commitments — audit hard).  Anchor:
`the_form_of_the_residue.md` closing gap.

**A6. The two rival corners not yet built** — negation-first and
relation-first rival primitives as *formal* corners (the built corners are
subsingleton/unary/non-distinct/ternary).  Each corner is one Lean file:
define the rival signature, prove it either collapses to `HasDistinguishing`
or fails a named clause.  This does not close the §5.1 `∀` (nothing can) —
it widens the dichotomy's tested span.  Size S–M each, risk low.

**A7. The simplicial bridge — two roads to one simplex** — tie the
operation-tower simplicial cone (`monoCount_closed = C(n+k−1,k)`,
`UnitHyper`) to the physics branch's `(NS,NT,d)` simplex combinatorics by
an ∅-axiom bridge theorem.  This is the strongest available test of the
no-exterior signature: two independent constructions forced onto one
object.  Anchor: `simplicial_operation_tower.md` L5.  Size M, risk med.

**A8. Is `×` a resolution of `+`? — settle the recurring contest** — the
corpus derives the additive/multiplicative asymmetry independently in ≥4
places (atom (in)distinguishability, `two_three_unique`, `prodL_*`,
`Omega_mul`) and has not settled whether `×` is a second structure or `+`
at a different resolution.  Target: a single theorem-pair stating exactly
what reduces (`Omega` is additive over `×`) and exactly what does not (the
exponent *vector* needs distinguishable atoms) — one file, one verdict,
ending the re-derivation loop.  Size M, risk med.

**A9. Universe/large-elimination audit + checker diversity** — extend
`cic_footprint.py` with an exact-universe-levels column; test the
falsifiable claim "every Raw motive is `Prop` or `Raw`"; replay one Tier-A
cone through a λΠ second checker.  Size M, risk low.  Anchor:
`the_trusted_base.md`.

---

## Track B — Number theory: after cubic reciprocity

Cubic reciprocity (both cases) is closed and novel (no other
proof-assistant formalization known).  The scaffold is now a *reusable
engine*; the year's work is to industrialize it.

**B1. Quartic reciprocity over ℤ[i]** — the direct transfer: `μ₄` values,
primary Gaussian primes, `biquadratic residue symbol`, Jacobi sums over
`ℤ[i]` (disc −4 replaces −3).  The cubic file map
(`EisensteinMu3Lift → EisensteinConjModEq → …Split`) is the template.
Size L, risk med (the quartic supplementary structure is heavier).  Anchor:
`higher_reciprocity_roadmap.md`.

**B2. The generic `μ_k` engine** — factor the shared mechanism out before
B1 duplicates it: (i) `muK_eq_of_modEq` (a `μ_k` congruence mod a modulus
coprime to the difference-set discriminant is an equality — the general
form of `mu3_eq_of_modEq_pi`); (ii) the "symmetric pair of `μ_k` relations
⟹ equal symbols" closer (the general `mu3_reciprocity_algebra`, whose `3⁴`
`decide` becomes a `k^4` bound — keep `k` small or find the algebraic
proof).  Then cubic AND quartic are two instances.  Size M, risk low-med.

**B3. Cubic supplementary laws + hypothesis descent** — the units `ω`,
`1−ω` symbols; derive `split_cubic_reciprocity`'s explicit
primary/coprimality hypotheses from primality alone; one statement uniting
inert + split.  Size M, risk low.

**B4. Binary quadratic forms — Gauss reduction, ∅-axiom** — reduction of
`ax²+bxy+cy²` (positive definite) is a finite descent (W1: the monovariant
is `a+c`); build `reduced_form_exists`, `class_count` for small
discriminants, `form_represents_prime` links.  Strategic value: the Markov
residual (`G204`) is *class-number core*; this builds the class-number
object itself from counting, mapping the W3 boundary from below.  Also
reconnects `sums_of_squares_engines` (`x²+ny²` for small `n`).  Size L,
risk low (the math is genuinely elementary).  This is the strongest new
number-theory opening.

**B5. Dirichlet-from-below: the Euclid-witness atlas** — Dirichlet's AP
theorem is W2 in general (L-function cancellation), but the sub-family
with *Euclid-style polynomial witnesses* (classes `a` with `a² ≡ 1 mod m`,
by Schur; e.g. `4k+1`, `4k+3`, `3k+1`, `8k+5`, …) is W1.  Build the
witness schema once (`cyclotomic-polynomial prime divisor ⟹ residue
class`), instantiate the full catalog, and state the *boundary theorem*
(the known characterization of which `(a,m)` admit such proofs) as the
mapped wall.  Size M–L, risk low.  A perfect triage-doctrine showcase.

**B6. Jacobi's four-square count `r₄(n) = 8σ(n)`** — the *count* refinement
of the closed four-square existence: via Hurwitz quaternions the proof is
unique-factorization counting, and the CD tower (`hurwitz_tower_L1/L2`)
already carries the quaternion arithmetic.  Links `FourSquare`,
`SumOfDivisors`, and the CD algebra in one capstone — a genuine
shared-engine theorem (the `the_substance_test` standard).  Size L,
risk med.

**B7. Bernoulli numbers + von Staudt–Clausen** — `B_n` denominators as a
prime-counting statement (W1: divisibility bookkeeping over binomials, the
`prime_dvd_binom` engine again).  Payoff chain: Faulhaber sums (the
`+`-tower's polynomial shadow), Kummer congruences (the p-adic arc), and
the ζ(2) bracket input for Track E's `Zeta2Cut`.  Size M, risk low.

**B8. PNT bracket narrowing** — the honest W1 remainder of the PNT arc:
sharpen `chebyshev_constant_interval` (`log₂e ∈ [(m+1)/(2(m+2)), 6]`) —
each narrowing IS the math (residue-shape doctrine: the bracket is the
computable operand).  Do not attempt constant `= 1` (W2, Erdős–Selberg).
Size S–M per sharpening, risk low.

**B9. Pell / fundamental units program** — `PellNorm` exists; build the
fundamental-unit existence for small discriminants + the unit-group
structure `ℤ[√d]^× ≅ ±φᵏ`-style readouts.  Feeds B4 (class numbers), the
Markov boundary, and the spiral-axis `{2,4,6}` unit-group classification.
Size M, risk low-med.

---

## Track C — Analysis: moduli, brackets, and the two heavy cuts

**C1. ζ(3) numerator kernel** — the remaining half of Apéry: numerator
integrality `(n!)³ ∣ 2·lcm³·zeta3Num n`.  The WZ-certificate route hit the
certifiability wall (panel 2026-06-16) — so attack the *route*, not the
wall: (i) the non-WZ elementary integrality proofs (Beukers-style
double-integral bookkeeping has a discrete shadow — check whether the
binomial-sum form of the harmonic kernel admits the same
`cube_dvd_lcm_cube` treatment as the closed H₃-part); (ii) if not, file
the kernel recurrence as W3 with the localization certified.  Anchors:
`zeta3_wz/numerator_plan.md`, `harmonic_recurrence_lcm`.  Size L, risk high.

**C2. π effective `(C,s)` — formalize the Mahler bracket** — the sole
honest instantiation of the ∀-form is Mahler 1953 `(C,s)=(1,42)`
(`PiHalfMeasure`).  Formalizing a Mahler-type irrationality measure is
heavy; the scoped first step is the *conditional* capstone already named:
the uniform period-spectrum theorem `M^n = I ⟹ ord ∈ {1,2,3,4,6}` (~250
lines, W1) and the `PiMeasureModulus` plumbing so any future `(C,s)` slots
in.  Size M (conditional) / XL (unconditional), risk low / very high.

**C3. `μ(x)` as the limsup boundary cut** — the full irrationality measure
as the reached-by-none boundary of the discrete deficiency
(`BestApproximation`: `W=1` ⟹ the constructive `μ ≥ 2`).  Target the
*two-sided* statement for concrete families (quadratics: `μ = 2` with
explicit brackets — W1 via continued-fraction periodicity).  Size M,
risk med.

**C4. The bare-interface completeness question** — the modulated Banach
engine closed the wall; the honest residual is representation-dependence.
Either (i) resolve freeze-permanence for the un-modulated `limPoint`
diagonal, or (ii) build the `NameComplete` carrier (Route B) where `lim`
is honestly total.  Outcome either way is a theorem about *which*
completeness interfaces are ∅-axiom-inhabitable — file into the W4 atlas.
Size M, risk med.  Anchor: `wall_synthesis.md`.

**C5. Discrete PDE a-priori ladder** — extend `pde_estimates/` from the
ODE Picard closure: the discrete heat equation on the lattice (maximum
principle = a fold inequality, energy estimate = Abel summation — both
W1), then the discrete wave equation's finite propagation speed (a
counting statement!).  Feeds the physics branch's field-equation needs.
Size L, risk low-med.

**C6. Brick 8 — the fold-back iff** — `aˣ = b` folds ⟺ `exp(a) ∥ exp(b)`
over ℚ (⟹ proven; ⟸ IS the separation) plus the mod-`p` curvature half
(cyclic `(ℤ/p)^×` collinearizes all exponent vectors — `CoprimeOrder`,
`Teichmuller` ground it).  Closes the `^`-wall's two independent
proof-facts into one criterion.  Size M, risk med.  Anchor:
`numbersystem_square.md`.

**C7. The three-distance theorem** — Weyl equidistribution's finite face
(the gaps of `{iα mod 1 : i < n}` take ≤3 values): pure counting on
continued-fraction convergents (W1), no measure needed.  Connects the
Markov/Lagrange spectrum arc, the spiral axis, and the π
presentation-dependence doctrine (the theorem is *about* the pointing's
finite signature).  Size M, risk low.  A high-elegance, self-contained
opening for a new contributor.

**C8. Fourier on ℤ/n — the finite harmonic layer** — character
orthogonality (`CyclicCharacterOrthogonality`) is already closed; one step
away are the DFT inversion formula, finite Parseval/Plancherel, and the
finite Poisson summation (all finite sums, W1).  Payoffs everywhere: Gauss
sums (already present) become Fourier coefficients; the `K_p` Laplacian
spectrum bridge (`curvature_spectrum_crossdomain` bridge 1) gets its
natural home; physics gets its first honest harmonic-analysis object.
Size M, risk low.  **Recommended first topic of the year** — maximal
connectivity per unit effort.

---

## Track D — Algebra & cohomology: above the closed skeleta

**D1. Explicit Sq² + one Adem instance** — the K_{3,2} Steenrod ladder
beyond Sq¹ was claimed in prose, bounded as frontier by the Phase-8 audit.
Smallest closable: Sq² on the 4-skeleton classes + the first Adem relation
instance `Sq¹Sq¹ = 0` (already forced) → `Sq²Sq² = Sq³Sq¹` on the
available degrees.  Size M–L, risk med.  Anchor:
`cohomology_higher_structure.md`.

**D2. Massey products — H¹ triples on K_{3,2}** — the first secondary
operation: `⟨a,b,c⟩` for cup-trivial triples, well-definedness modulo
indeterminacy stated Σ-style (no quotient).  Size M, risk med.

**D3. The ∀(k,l) cup-Leibniz** — the parametric-in-bidegree closure above
the fixed-bidegree CupAW family (`cup_leibniz_general.md`).  Likely a
finite-schema induction over the lex order.  Size M, risk low-med.

**D4. The E_n operad reading of GRA** — formalize `grade n = E_n` with the
`trivial23` unit (`gra_operad_level.md`): define the 213-native operad
(finite, no topology), prove GRA's `⊗` realizes the composition.  Size L,
risk med-high (design-heavy).

**D5. Sedenion zero divisors as residue readout** — extend the CD tower to
L4 (sedenions) and prove the zero-divisor existence as the *count-Lens
reading of associativity loss* — the tower's own `object1_not_surjective`
moment (each doubling loses a law; at 16 the loss becomes visible as
zero-divisors).  Candidate essay + Lean pair.  Size M, risk med.

**D6. Representation theory, finite seed** — the corpus has group theory
and (number-theoretic) characters but *no representation theory* (verified
absence).  Seed: the character table of `S₃` (3 irreducibles, orthogonality
by `decide`-scale finite sums), Maschke for `ℚ[S₃]`-style finite cases,
and the regular-representation count `|G| = Σ dᵢ²` as a double-count
(the incidence-Fubini engine!).  Then the payoff theorem: the gluon octet's
`8` re-read as `dim(adjoint of SU(3))` — giving the physics identification
gap (Track E5) its first typed target from the math side.  Size L,
risk med.  **The highest-leverage new discipline.**

**D7. Galois theory, finite seed** — the second verified absence.  The
corpus already lives in `ℚ(√5)`, `ℚ(i)`, `ℚ(ζ₅)`, `𝔽_p²` (Frobenius is
formalized!).  Seed: splitting structure of `x²−x−1`, `x²+1`, `x⁴+x³+x²+x+1`
as Lens-arrows; the Galois correspondence for these fixed small cases
(subgroup lattice ↔ subfield lattice, both finite posets — the
`Order/GaloisConnection` machinery finally meets its namesake); Frobenius
as the generator over `𝔽_p`.  Cross-payoff: reciprocity laws restated as
Frobenius-splitting statements (the modern reading of Track B).  Size L,
risk med.

**D8. Knot/braid normal forms — cash the colimit verdict** — the
colimit-corner assessment says free-group and braid cases are buildable
now (coequalizer = kernel of a normal-form map, quotient-as-Σ).  Build:
free-group reduction (exists: `FreeReduction`) → braid monoid `B₃` with
the confluent Garside normal form → the braid-relation invariance of a
first knot invariant (writhe/linking shadow).  Size L, risk med.

---

## Track E — Physics: forcing the identifications

The audited state: the numbers/counting are ∅-axiom-forced; the physical
*identifications* ride on prose (verified universal across 6 observables,
`classical_input_gap_closure.md`), and the honest independent-falsifier
count is K ≈ 3–7, not 23 (`evidential_overdetermination_count.md`).  The
genuinely clean parameter-free wins today: Koide `NT/NS`, `m_H/v_H = 1/c`,
the coupling ratios, the CKM modulus `1/φ²`, and the fully-closed
Yang–Mills mass gap.  The year-scale program: convert identifications into
typed models one at a time, and keep the falsifier ledger honest.

**E0. Repair (or honestly demote) the θ_QCD falsifier** — *urgent
falsifiability maintenance*: `theta_QCD_precision_bracket` consumes the
un-derived Jarlskog J; with the honest `J = 8.18×10⁻⁵` (×2.66 over
observed) the central value leaves its own bracket.  Either re-state the
bracket conditional-on-J (typed hypothesis), or demote it in the catalog
until E4 lands.  A broken falsifier is worse than none (§8).  Size S,
risk low.  Do this first.

**E1. The Gram `d²` forcing theorem** — the named remaining premise of the
α_em arc: identify the Gram self-energy *as* the `k=1` self-pairing cup
term (promote `CupRingTrace`/`SelfPairingTrace` test → derivation).  The
cup-graduation "`1/d` per factor" leg is *proven not derivable* from the
current Bool/F₂ cup — it needs a normalised ℚ-valued cup that does not
exist yet; building that ℚ-cup is the real sub-project (and it serves
Track D1–D3 too).  Anchors:
`Lib/Physics/AlphaEM/{GramCubicReduction,GramD2Readings,GramD2Mechanism}`.
Size L, risk med.  The single highest-value physics step (it upgrades the
ppb headline's last prose joint, and `m_μ/m_e` inherits it).

**E2. `Zeta2Cut` — bracket a continuous value ∅-axiom** — the deepest open
layer of the identification program: can the discrete modulus bracket
ζ(2)?  Specified-not-built; the genuine lemma is the `Htel` telescoping
induction.  Track B7 (Bernoulli) supplies the arithmetic side; the payoff
propagates to α_em (whose formula consumes `60·ζ(2)`) and to the honest
`m_p/Λ_QCD` Stage-1 falsifier window.  Size M, risk med.

**E3. The octet via D6** — replace the `Unit`-model coker identification
with the representation-theoretic count from Track D6 (`8 = 3²−1` as the
regular/adjoint double-count), closing one of the six identification gaps
with mathematics instead of a model.  Also serves
`atomic_c_multiplicity_forcing`: derive `b₁ = NS²−1` structurally instead
of the `decide` that bakes in `c=2`.  Size M after D6, risk med.

**E4. The Yukawa assembly `Y_d(i,j)` — the CP phase's missing leg** — the
apex *modulus* `1/φ²` is forced and near-exact; the *phase* is a posit
(`α=90°` via `C₄`, fit ~1.5σ), and the golden-phase route is dead (Niven:
discrete phases are rational multiples of π; A₅/icosian/CD routes all
proven dead).  The cohomological principle ("cohomological coupling ⟹
maximal CP") and the generation-index bridge (`N_gen = dim Λ²(ℝ³) = 3`)
are settled; the explicit generation-indexed Yukawa assembly is not — and
`cp_yukawa_from_scratch.md` records the honest NEGATIVE (generic
J-carrying textures give ~0°, not 90°).  So the open problem is sharp:
*which structural ingredient, absent from generic textures, forces the
right angle?*  Candidate: the Hodge `⋆² = −1` on the signed-ℤ Δ⁴
(`c_is_three_distinct_twos.md`'s open `CPHodgeStructure` leg).  Size XL,
risk high (W2-adjacent: phases are signed).  Downstream: fixes E0
properly, and the Jarlskog ×2.66 over-prediction.

**E5. Yang–Mills confinement half — reformulate, don't force** — the
mass-gap half is closed (`mass_gap_master`, gap = 4, plus the colored SOS
certificate).  The area-law half hit an honest wall: the abstract
bipartite complex has no embedding, hence no enclosed "area" to even
*state* `⟨W⟩ ∼ exp(−σ·A)`.  The licensed move is not to import an
embedding (exterior ruler) but to find an embedding-free surrogate: (i) a
combinatorial "minimal spanning 2-chain" count for a loop (area as a
*count* of 2-cells, W1 if monotone), or (ii) accept the W3 filing with the
localization certified.  Size XL, risk high.  Anchor:
`yang_mills_confinement.md`.

**E6. Neutrino sector — the absolute rungs** — the *ratios* exist (PMNS
`θ₁₂, θ₂₃` Fibonacci-bracketed, `m₃/m₂ ≈ 5.71`, normal ordering, JUNO-era
falsifier F3).  Absent: Δm²₂₁/Δm²₃₁ as *dimensionless ratios of each
other* (reachable without an absolute scale — the ratio
`Δm²₃₁/Δm²₂₁ ≈ 33` is a falsifier-grade number nobody has attempted), and
the θ₁₃ reading.  Absolute masses stay structurally excluded (no exterior
scale).  Size M probe, risk high.

**E7. Raise the honest K** — the over-determination audit found K ≈ 3–7
genuinely independent pinned numbers vs the "23 observables" headline.
Program: for each headline observable, either exhibit independence (a new
measured number not re-reading `{3,6,8,12,24}`) or merge it in the
catalog; E6's `Δm²` ratio and E2's ζ(2) window are the two candidate
*new* independents.  Each independence proof is a small forcing theorem.
Size S per observable, risk low.  Falsifiability maintenance — it
protects the whole deployment.

**E8. Gravity — wire the proven Kähler skeleton first** — the two proven
bricks (Hermitian split `G = h + iQ` with `Re = metric`, `Im = symplectic`;
metric-`J` = holonomy-generator identity) are *not wired* to the gravity
narrative, and the old `GravityShadow.lean` was deleted as bogus.  First
brick (all-PURE buildable): assemble `G = h + iQ` explicitly and state the
gravity/gauge split as a theorem about the Gram object — no spacetime
claim attached.  Then ONE theorem tying hinge deficit-angle counts to
`DiscreteRicci` (the Regge brick).  `G_N` and absolute cosmology stay on
the excluded-scale ledger.  Size M + M, risk med.

**E9. Weinberg angle: state the running gap as a typed hypothesis** — the
bare `sin²θ_W = 1/(1+2ζ(2))` bracket `[0.2326, 0.2439]` excludes the
observed 0.2312 by ~0.8%; "running closes it" is asserted, not derived.
Either derive a leading-log correction inside the coupling calculus (the
skeleton `α_em/α_2` exists) or restate F5 conditional-on-running.  Same
hygiene class as E0.  Size M, risk med.

**E10. g−2 — an untouched opening** — no `(g−2)` file exists.  The
Schwinger term `a_e = α/2π` is a *clean ratio of already-derived objects*
— a PURE bracket for `a_e` at leading order is a small theorem away and
would be the first DRLT contact with the anomalous-moment sector; the
muon anomaly's BSM window is then a natural falsifier candidate (does the
atomic calculus produce a correction of the observed sign/size, or
honestly nothing?).  Size S (Schwinger bracket) / L (beyond), risk
low / high.

---

## Track F — New disciplines: the rebuild frontier

The corpus audit (2026-07-12) verified twelve structural absences.  Each
entry below is the 213-native *seed* — not "port the classical theory" but
"find the count-Lens reading and let the discipline regrow".  Primacy =
breadth (§7.1): these are the year's breadth engine.

**F1. Finite probability → de Moivre–Laplace bracket** — probability as
ratio-Lens on counts (`ProbabilityCut` exists, LLN closed).  The flagship:
a *bracketed* central limit statement for Bernoulli — explicit two-sided
bounds on `C(2n,n±k)/4ⁿ` against the discrete Gaussian kernel (W1: pure
binomial estimates; the corpus already has `central_binom` machinery from
the Chebyshev arc!).  No measure theory needed — the bracket IS the
theorem (residue-shape doctrine).  Then: entropy as modulus degree
(`MaxEntropy` exists — connect it), and Chernoff-type tail counts.
Size L, risk med.  The most 213-native of all the absences.

**F2. Fubini for dyadic measure** — extend `measureNum`/`lebesgueStepNum`
to product brackets: the dyadic Fubini (finite double-count exchange — the
incidence-Fubini engine at the measure layer).  Small, closes the "no
product measures" gap in its honest bracket form.  Size M, risk low.

**F3. The Lens 2-category, formalized** — the decomposition calculus's
model v7.1 ("readings form a 2-category", `two_cells` meta) is
prose-only.  Formalize: Lenses as 1-cells, reading-refinements as 2-cells,
`Lens.refines` as the vertical composition — a finite, concrete 2-category
with the corpus's own objects.  This is category theory grown from inside
(vs. the verified absence of imported CT).  Size L, risk med-high
(design-heavy; must not import a CT library's commitments).

**F4. Elliptic-curve seed — the group law as polynomial identity** — the
EC addition law's associativity over ℚ (or `𝔽_p`) is a decidable
polynomial identity (W1, `decide`/`ring`-scale after the right encoding);
point-counting `#E(𝔽_p)` for small `p` is a count.  The Hasse bound's
*content* is W2 (signed character sum) — state the boundary explicitly:
counts attackable, the square-root cancellation not.  Payoff: the
congruent-number problem's elementary face, and the first contact with
the modern arithmetic-geometry absence.  Size L, risk med.

**F5. Modular-forms shadow: theta counts** — do not build modular forms;
build their *count shadows*: `r₂(n)` (two-squares count, refining the
closed characterization), `r₄(n) = 8σ(n)` (Track B6), Jacobi triple
product as a partition-count identity (the `conv` generating-function
engine + `pentagonal numbers` already closed).  The Eichler/Selberg world
stays W2; the coefficient identities are W1.  Size M–L, risk med.

**F6. Reverse-math atlas as a product** — the Logic cluster
(LPO/WLPO/MP/LLPO, WKL⟺Heine-Borel, omniscience costs) is mature enough to
publish as the corpus's second external exposure (after the ∅-axiom
formalization paper): "the constructive cost ledger of classical
analysis, machine-checked, Mathlib-free."  Work: complete the ledger's
empty cells (Dini↔?, rearrangement↔?), write the survey chapter.  Size M,
risk low.  (Line B exposure — `the_substance_test`.)

**F7. Game/decision seed — Zermelo and Sprague-Grundy** — finite games as
`Raw`-shaped trees (the corpus IS a tree calculus); Zermelo determinacy by
structural induction (W1), Sprague-Grundy values as a fold — nim-value =
the mex-Lens, and nim-addition is XOR (the Bool-Lens meets the count-Lens).
Cheap, delightful, and genuinely new coverage.  Size M, risk low.

**F8. Information theory, finite** — Kolmogorov/Chaitin already appears as
the Lawvere diagonal (the one-act file); build the finite side: Kraft
inequality (counting!), Shannon entropy's subadditivity via the
log-sum inequality's discrete bracket, and the source-coding *bound* as a
count comparison.  Ties `MaxEntropy` + `Information` into theorems.
Size M, risk low-med.

---

## The small-brick queue (session warm-ups, S-size)

Named, bounded, low-risk items — each a good first hour of a session or a
first contribution.  Sources: the frontier INDEX's own residuals.

1. Limit-arithmetic product + squeeze (`analysis_modulus_pending.md`).
2. Order-embedding ↔ infinite-subset bijection, reverse direction
   (`order_embedding_subset_bijection.md`).
3. Wilson ±1 classification: formalize the written fixed-point-free
   involution `σ_t` argument (`wilson_plus_one_argument.md`).
4. Disc-`−8` congruence-iff via the quadratic character of 2
   (`sums_of_squares_engines.md`).
5. The `K_p` Laplacian = additive-character spectrum instantiation
   (`curvature_spectrum_crossdomain.md` bridge 1, the `m=p` case).
6. The unimodularity note + companion-cycle reading of the apex
   (`selfref_matrix_crossdomain.md`).
7. `ModArithReadout`: transport one native modular theorem to `Nat213`
   (`carrier_readout_crossdomain.md`).
8. p-adic `sqrt` via the `unique_of_lift_fixed` engine (G123 seeds).
9. The `Meta/` propext-trap catalog (`pure_lean_calibration_synthesis.md`)
   — earned infrastructure, unbuilt.
10. `async_growth_seeds.md` items (exact-membership converse, swap-class
    census, uniform dagSize bounds).
11. Comultiplication-symmetry higher rungs (`comultiplication_symmetry.md`).
12. E0 (the θ_QCD falsifier repair) and E9 (Weinberg typed hypothesis).

Medium bricks one notch up: Hall marriage general-`n`; rearrangement
general-`n`; the antipode unification (binomial + Möbius inversion as one
antipode under `Δ_+`/`Δ_×`, `convolution_comultiplication_crossdomain.md`
F2 — both sides already closed, only the unifying statement unwritten);
the `sinCut`/`cosCut` unlock (blocked at the signed-cut cross-sign stub —
the alternating-series case is the real target,
`transcendentals/transcendental_functions_ladder.md`); and **Bertrand's
postulate end-to-end** — verdict already in: fully ∅-axiom-reachable,
keystone `∏_{p≤N} p ≤ 4^N` closed, the remainder is Erdős's binomial
argument (`bertrand_postulate.md`).  Bertrand is the recommended *first
marathon* for a new contributor: real theorem, zero research risk.

---

## Suggested sequencing (four quarters)

**Q1 — hygiene + connectivity + engine factoring** (low-risk, high-payoff):
E0/E9 (falsifier hygiene) → C8 (finite Fourier) → B2 (generic `μ_k`
engine) → B5 (Euclid-witness atlas) → A4 (escape-pole census tool) →
E7 (honest K).  Rationale: each unblocks 2+ later topics; all W1/W4.

**Q2 — the two flagship rebuilds**: D6 (representation seed) + F1
(probability bracket), in parallel with B1 (quartic reciprocity, riding
the Q1 engine) and E1 (Gram forcing).

**Q3 — the descent-leg push**: A1 (FTA on Ω-descent) → A3 (`DStr` Route B)
→ A7 (simplicial bridge), with D7 (Galois seed) and B4 (quadratic forms)
as the discipline-side companions.

**Q4 — heavy cuts + exposure**: C1 (ζ(3) numerator — attack or certify
W3), C2 (π conditional capstone), F6 (reverse-math atlas exposure),
E8 (gravity brick), and the year's wall-atlas consolidation (§0 table
updated with every verdict).

---

## The do-not-attack list (standing walls, with their honest class)

- **RH / Mertens-type bounds** — W2 (signed cancellation; the size IS the
  zeros).  Only the from-below atlas (B5, B8) is licensed.
- **PNT constant `= 1`** — W2 (Erdős–Selberg bilinear step, no ∅-axiom
  shadow).  Bracket-narrowing only.
- **Markov `H` (Frobenius 1913)** — W3, terminally localized (`G197`).
  Only the class-number *object* (B4) may move the frame.
- **The universal no-exterior `∀`** — §5.1, not a type.  Only corners (A6)
  and the import-metric (genesis seam) are theorems.
- **Schanuel-territory fold-back ceilings** — conjecture-tagged only
  (`numbersystem_square.md` nonlinear ceiling).
- **"Δ⁴ = spacetime", "gravity = defect"** — identification gaps, not
  theorems; only typed-model closures (E5, E8) count as progress.

---

## Cross-cutting invariants to maintain all year

1. Every closure lands PURE (`#print axioms` empty) or it does not count.
2. Every wall verdict is filed in the §0 table with its from-below atlas.
3. Every new discipline seed gets its count-Lens statement *first*, its
   classical name second (failure-mode table: stereotype matching).
4. The falsifier ledger (E7) is updated whenever a physics number moves.
5. When narrative and Lean disagree, Lean wins.
