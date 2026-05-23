# G137 — Cross-corpus synthesis from G134 cardinality cut-off merge

**Status**: Synthesis note (Phase 7.6 of `ready-to-merge` skill).
Written after the G134 §7 marathon merged into `main`
(10 files / 291 PURE / 0 DIRTY; chapter
`theory/meta/cardinality_cutoff_applications.md` registering 4
closed chapters in `theory/meta/INDEX.md`).

## Anchor

G134 closed the §7 six-direction application family of the
cardinality cut-off principle established in G133.  Hunter
depth-1 asymptotic cut-off proved sharp at m = 3 (every value
> 3125 is outside depth-1 Hunter); applications extend across
Aurifeuillean L_m unboundedness, Pell / Lucas / Fibonacci /
Tribonacci sequences, complexity hierarchy {0, 1, 2, 3}, and
alternate primitive set {2, 3}.

Catalogue settled at `{2, 3, 5, 7, 13, 521}` (atoms 41 and 137
removed for being forced-fit non-integer constants).  Triple
coincidence at 29 (`Pell P_5 = Lucas L_7 = Aurifeuillean L_1`),
Lucas–Aurifeuillean at 521 (`L_13 = Φ_10(5)`).

## Patterns

### Pattern A — Cardinality ceiling beats enumeration

Recurrent move: when proving "every value above some bound is
NOT in set S," replace exhaustive enumeration of S with a
**uniform cardinality cap** on S, then a single comparison.
Examples now in the corpus:

- `theory/meta/cardinality_cutoff_principle.md`: depth-1 Hunter
  values bounded by 3125 (= max generator depth-1 evaluation);
  ★ "∀ v > 3125, v ∉ depth-1 Hunter" follows in one line.
- `theory/math/cohomology/cup_ladder_graduation.md` (G132 Phase 19):
  max α-power at K_{3,2}^{(c=2)} k-skeleton = top dim + 1.  At
  2-skeleton, ceiling is α³ — higher α-powers structurally
  unsupported, no enumeration needed.
- `theory/math/cohomology/aurifeuillean.md`: cardinality cut-off
  for L_m ∉ HunterValues_1 at fixed m, using L_m monotone above L_3.

These are NOT three independent facts; they share the schema
"compute the structural ceiling, then anything above it falls
out of the set."  Worth naming as a first-class technique in
`seed/THEOREM_METHODOLOGY_SUITE.md` if a future revision adds a
§TH-5 "structural ceiling over enumeration."

### Pattern B — Multi-reading convergence on a small integer

The α-power graduation at H^k = `k + 1` (G132) admits THREE
independent readings (loop-vertex count + 1, filtration depth +
1, Steenrod ladder depth + 2) that all collapse to the same
integer.  This is the same pattern as:

- `theory/math/cohomology/k32_higher_cohomology.md` `b_1 = 8`:
  four count-Lens readings (E − V + 1; cup channels + NT;
  NT·(NS + 1); NS² − 1) all = 8 only at (NS, NT, c) = (3, 2, 2).
- `theory/physics/foundations/atomic_constants.md` `(NS, NT, d)
  = (3, 2, 5)`: forced by three independent constraints
  (pairing closure, atomicity, sub-Newton bracket).

Naming candidate: **integer convergence under multi-reading** is
how 213 distinguishes a coincidence from a structural identity.
A single-reading numerical match is a fit; a 3+ reading match is
a constraint.  This is the structural form of falsifiability in
the integer regime.

### Pattern C — Sequence-coincidence as catalogue probe

The triple coincidence `Pell P_5 = Lucas L_7 = Aurifeuillean L_1
= 29` and the quintuple Lucas–catalogue hit at 521 are not
ornamental.  They are catalogue-membership probes: if an
external sequence (Pell, Lucas, Fibonacci, Tribonacci) hits
catalogue atoms at multiple indices, the catalogue is "natural"
under that sequence's generating dynamics.

- 29 hit by three sequences → catalogue atom (already in).
- 521 hit by Lucas at 5 indices → strongest external pull.

Open question this raises (now obvious post-G134): is there a
**catalogue-discovery** route — generate all sequences with
linear recurrence over `{2, 3, 5}` coefficients up to depth k,
take their hits in `[1, 521]`, and see if the catalogue ATOMS
emerge as fixed points?  The current catalogue was assembled
top-down (atomic primes + DRLT counts); a bottom-up
sequence-hit convergence would be independent evidence.

## New questions

### Q1 — Fourth reading of (k+1)?

The (k+1) graduation has three readings (Pattern B).  Does the
cardinality cut-off principle (Pattern A) supply a FOURTH?
Conjecture: at H^k on a complex with top skeleton dim n, the
maximum α-power IS the cardinality cut-off of the cup-i ladder
at degree (k + 1).  If yes, Patterns A and B unify at the
α-power layer.

### Q2 — Catalogue closure of {2, 3, 5, 7, 13, 521}

G134 dropped 41, 137 as forced fits.  The current catalogue
{2, 3, 5, 7, 13, 521} should be tested for closure under the
sequence-hit probe of Pattern C: do all linear-recurrence
sequences over {2, 3, 5} that hit the catalogue at multiple
indices have catalogue-internal characteristic roots?  This is
a finite check (bounded depth, bounded leaves) and would either
add atoms or confirm closure.

### Q3 — Steenrod-truncation ↔ cardinality cut-off

At K_{3,2}^{(c=2)} 3-skeleton, Adem `Sq^a·Sq^b = 0` is vacuous
for every (a, b) because the target degree exceeds C³.  This is
literally a cardinality cut-off (Pattern A) applied to the
Steenrod algebra.  The Adem universal theorem
(`AdemUniversal.lean`) and the Hunter depth-1 cut-off
(`AurifeuilleanFullCutoff.lean`) prove the same SHAPE of result
on different content.  Worth a META-theorem capturing the shared
proof skeleton (would live as a `theory/meta/` chapter).

### Q4 — Cup-ladder applications chapter

G134 has an "applications" chapter
(`theory/meta/cardinality_cutoff_applications.md`) that lists six
directions where the cardinality principle applies.  G132 has a
"framework" chapter (`theory/math/cohomology/cup_ladder_graduation.md`)
+ a math companion (`k32_higher_cohomology.md`) + a physics
applications chapter (`theory/physics/alpha_em/precision_derivation.md`).
The latter is a SINGLE application (α_em); there is no
"cup_ladder_applications" multi-direction chapter.  Is this a
genuine asymmetry (α_em is the only physical observable in the
(k+1) regime) or a missing chapter waiting to be written?
Candidates for additional applications: m_p (already at
ppm tier — does the cup-ladder push it to ppb?), m_μ/m_e
(currently no cohomology lift), Cabibbo λ (5/22 ± 1%).

## Cross-references

- Pattern A: `theory/meta/cardinality_cutoff_principle.md` (anchor)
  + `theory/meta/cardinality_cutoff_applications.md` (G134 §7 family)
  + `theory/math/cohomology/cup_ladder_graduation.md` §"max α-power"
  + `theory/math/cohomology/aurifeuillean.md` "cut-off line" section
- Pattern B: `theory/math/cohomology/k32_higher_cohomology.md` §`b_1 = 8`
  + `theory/physics/foundations/atomic_constants.md` §forced tuple
  + `theory/math/cohomology/cup_ladder_graduation.md` §3-reading
- Pattern C: `theory/math/cohomology/aurifeuillean.md` + chapter
  `theory/meta/cardinality_cutoff_applications.md` (Directions C
  Pell / Lucas / Fibonacci / Tribonacci)
- Q1, Q3: meta-level — no chapter exists yet
- Q2: `theory/meta/cardinality_cutoff_principle.md`
- Q4: `theory/physics/alpha_em/precision_derivation.md`

