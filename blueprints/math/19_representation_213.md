# Representation Theory 213 — Blueprint

**Priority**: ★★★ (verified structural absence; highest-leverage new
discipline per `research-notes/frontiers/research_program_year_horizon.md`
Track **D6**, payoff Track **E3**)

**Status**: SEED — nothing under `Lib/Math/` answers "what does this group
*do* to a linear space".  The corpus has groups (`Algebra/Group/`),
permutation signs (`Linalg213/PermSign`, `ModArith/Zolotarev`),
number-theoretic characters (`ModArith/CharacterOrthogonality`), and a
physics-side `Sym(3)`-module on the octet (`Physics/Symmetry/OctetModule`)
— but no math-tier representation theory connecting them.

---

## 1. Why This Field

Classical reference (tagged as reference): G → GL(V) homomorphisms;
characters χ(g) = tr ρ(g); Maschke, Schur, orthogonality; |G| = Σ dᵢ² via
the regular representation; the physics dictionary "adjoint of SU(3) has
dimension 8".

Natural emergence in 213:
- A **representation is a Lens**: a finite group (a closed system of
  distinguishings — `composePerm`, `Cyclic`) is *read through* the linear
  shadow of the distinguishing — matrices over ℚ or ℤ, already built
  ∅-axiom in `Linalg213` (DetMul, Gram, PermMatrixDet, CayleyHamilton).
  The group does not "have" a matrix form; a matrix form is one pointing,
  and different representations of one group are different Lenses on the
  same distinguishing-system.
- A **character is the trace count-Lens**: tr collapses a matrix Lens to
  one number per group element — the coarsest faithful-enough readout.
  Orthogonality of characters is then a *finite double-count*, exactly the
  `IncidenceFubini` engine's territory, not an inner-product-space import.
- The **sign representation already exists twice** in the corpus and does
  not know it: `Linalg213/PermSign.psign` (inversion-count parity) and
  `ModArith/Zolotarev.psign_mulPerm_hom` (Legendre symbol as permutation
  sign).  Naming it "the 1-dim sign representation of Sₙ" unifies them —
  one Lens, two argument-patterns, per the equivalence-unification rule.
- The **payoff is physical**: `8 = NS²−1` is currently identified with the
  SU(3) octet through a Unit-model cokernel + an 𝔽₂ Sym(3)-module
  (`classical_input_gap_closure.md` G1/G2).  The regular-minus-trivial
  count of a 3-object system gives that identification its first typed
  math target (Track E3).

## 2. 213-native Emergence

### 2.1 Representation = group Lens into the linear shadow

A finite group in the corpus is concrete: `Fin n` addition (`Cyclic`),
`Nat → Nat` composition (`Symmetric`), reduced words (`FreeReduction`).
A representation `ρ : G → Mat d ℚ` with `ρ(gh) = ρ(g)·ρ(h)` is a
Lens-arrow: it re-presents the group's distinguishing-composition as
matrix composition.  Kernel of the Lens = what this reading cannot
distinguish (trivial rep distinguishes nothing; faithful loses nothing).
No abstract `Group`/`Module` typeclass tower — concrete carriers, concrete
matrices, `decide`/`rfl`-scale proofs, the `Algebra/Group/` paradigm.

### 2.2 Character = trace count-Lens; orthogonality = double-count

χ(g) = tr ρ(g) reads each group element as one integer (in-scope values
land in ℤ).  The orthogonality sum `Σ_{g∈G} χᵢ(g)·χⱼ(g⁻¹) = |G|·δᵢⱼ` is a
finite sum over an enumerated group — for S₃, six terms, `decide`-scale.
The schema is already proven once:
`ModArith/CharacterOrthogonality.charSumExp_eq_zero` and
`quadratic_orthogonality` are character orthogonality for cyclic groups
wearing number-theory clothes.  One schema, two instances (Phase RD).

### 2.3 Why ℚ/ℤ and not ℂ — the honest wall stated up front

The classical theory works over ℂ (algebraically closed, characteristic
0).  213 has no ℂ-as-completed-field; `Real213` reals are cuts
(pointings), and importing "algebraically closed" wholesale would be an
exterior ruler.  What survives over ℚ, honestly:

| Survives over ℚ / ℤ | Needs cyclotomic values μₙ |
|---|---|
| **All of S₃**: its 3 irreducibles (trivial, sign, standard 2-dim) are rational — full character table, orthogonality, Maschke, Σ dᵢ² = 6 | Cₙ (n ≥ 3): the 1-dim characters take values in μₙ ⊂ ℤ[ζₙ]; over ℚ the "irreducibles" are the φ(d)-dim rational blocks |
| Sign representation of any Sₙ (values ±1) | Full Sₙ character theory for large n (still rational classically, but Young machinery is a later marathon) |
| Permutation representations (matrices are 0/1, `PermMatrixDet` exists) | Any character with genuinely irrational values (2-dim irreps of C₅ ⋊ …) |

Cyclotomic values are not an escape hatch to ℂ: ℤ[ζₙ] is a finite
ℤ-module, buildable the `CayleyDickson`/`ZSqrt` way (tuples with axes;
the tuple is the number).  Where μₙ is forced, the cyclotomic machinery
of **blueprint 18 (finite Fourier)**,
`blueprints/math/18_finite_fourier_213.md`, is the shared substrate —
not duplicated here.

### 2.4 |G| = Σ dᵢ² as incidence double-count

Classically the regular representation decomposing.  213-native: count
the pairs of one finite incidence structure two ways — the
`Combinatorics/IncidenceFubini.genSwap` / `incidence_fubini_one_engine`
pattern.  For S₃: `6 = 1² + 1² + 2²`, `decide`-scale.

### 2.5 8 = 3²−1: adjoint = regular minus trivial

For a 3-object system the 3×3 matrix space has dimension 9 = 3²; the
trace-Lens splits off 1 (the scalar line); the traceless remainder has
dimension 8.  A *count with a typed carrier* (traceless 3×3 over ℚ,
buildable in `Linalg213`), where today `8` is only number-matched: an 𝔽₂
count (`OctetModule`, `2·triv ⊕ 3·std`), a Betti number (`H1K`,
`b₁ = E−V+1 = 8`), a Unit-model cokernel
(`OctetCokernel.octet_is_cokernel_of_zero_map`).  Freezing line of
`classical_input_gap_closure.md`: close the math, don't ontologize the
physics.

## 3. Building Blocks (already ∅-axiom in the corpus)

| Tool | Location | Use |
|---|---|---|
| Perm = `Nat → Nat`, `swap01`, `cyc3`, `composePerm` | `Lib/Math/Algebra/Group/Symmetric.lean` | S₃ carrier |
| ℤ/nℤ as Nat mod | `Lib/Math/Algebra/Group/Cyclic.lean` | Cₙ carrier |
| `psign`, inversion parity, `perms n` enumeration | `Lib/Math/Algebra/Linalg213/{PermSign,PermGroup,Permutation}.lean` | sign representation |
| Zolotarev `psign_mulPerm_hom` (sign is multiplicative) | `Lib/Math/NumberTheory/ModArith/Zolotarev.lean` | sign rep = Legendre symbol instance |
| Matrix mult, `DetMul`, `PermMatrixDet`, `Gram`, `CayleyHamilton` | `Lib/Math/Algebra/Linalg213/` | the linear shadow |
| `charSumExp_eq_zero`, `quadratic_orthogonality`, `altSign` | `Lib/Math/NumberTheory/ModArith/CharacterOrthogonality.lean` | cyclic character orthogonality (existing instance) |
| `genSum`, `genSwap`, `incidence_fubini_one_engine` | `Lib/Math/Combinatorics/IncidenceFubini.lean` | Σ dᵢ² double-count |
| Octet `Sym(3)`-module, `2·triv ⊕ 3·std` over 𝔽₂, fixedSize 4 | `Lib/Physics/Symmetry/{OctetModule,C3ChainCapstone}.lean` | physics target to be re-grounded |
| `octet_is_cokernel_of_zero_map` (Unit-model coker) | `Lib/Math/Cohomology/Bipartite/OctetCokernel.lean` | the identification to upgrade |
| GroupAction orbits | `Lib/Math/Algebra/Group/GroupAction.lean` | permutation representations |

## 4. Phase Plan

### Phase RA — Character table of S₃ (3-5 commits)

1. `Rep` as concrete data: for each of the 6 elements of S₃ (enumerated,
   not abstract), a matrix over ℚ (or ℤ where entries permit); the
   homomorphism law as a finite conjunction, `decide`/`rfl`.
2. Three irreducibles: **trivial** (1), **sign** — *defined as* the
   corpus's `psign`, with `psign_mulPerm_hom`/`PermSign` cited as the
   homomorphism law already proven — and the **standard 2-dim** (integer
   matrices acting on the sum-zero plane of the natural 3-dim
   permutation representation).
3. Character table as a 3×3 integer array; row and column orthogonality
   as finite sums (18 products each), `decide`-scale.
4. Success criterion: `#print axioms s3_character_orthogonality` = ∅;
   sign-rep theorem *reuses* PermSign/Zolotarev rather than re-proving.

### Phase RB — Maschke for small ℚ[G] (3-4 commits)

1. Invariant-complement construction with the averaging map `(1/|G|)·Σ`,
   legitimate over ℚ because |G| ∈ {2, 3, 6} is invertible — state the
   characteristic-0 hypothesis as the theorem's visible hypothesis, not
   background.
2. Concrete cases first: the natural 3-dim permutation rep of S₃ splits
   as trivial ⊕ standard (explicit projection matrix, `decide` on
   entries).
3. General small-case schema only if the concrete instances reveal one
   (rule: one bundle, not `_at_level_n` enumeration).
4. Success criterion: `perm3_splits_trivial_plus_standard` ∅-axiom, with
   an explicit idempotent whose image/kernel are the two summands.

### Phase RC — |G| = Σ dᵢ² via incidence-Fubini (2-3 commits)

1. Regular representation of S₃ as 6×6 permutation matrices
   (`PermMatrixDet` infrastructure).
2. The double-count `6 = 1² + 1² + 2²` typed through
   `IncidenceFubini.genSwap` — the same engine, new instance; no new
   summation lemmas.
3. Success criterion: the statement mentions the actual irreducibles of
   Phase RA (their dimensions extracted, not hard-coded).

### Phase RD — Cyclic case unified with Dirichlet orthogonality (2-3 commits)

1. State the character-orthogonality schema once (finite sum over an
   enumerated group vanishes off the diagonal) and instantiate twice:
   (a) S₃ from Phase RA; (b) the existing
   `CharacterOrthogonality.quadratic_orthogonality` /
   `charSumExp_eq_zero` for cyclic groups.  One Lens-arrow, two
   readings — do not create parallel "group character" and "Dirichlet
   character" objects (equivalence-pluralism failure mode).
2. Honest wall, stated in the file: Cₙ's full set of n 1-dim characters
   needs μₙ; over ℚ only the ±1-valued (quadratic) characters and the
   φ(d)-block decomposition are available until blueprint 18's
   cyclotomic carrier lands.  Cite `18_finite_fourier_213.md`.
3. Success criterion: zero duplicated summation lemmas between
   `ModArith/CharacterOrthogonality` and the new files.

### Phase RE — The octet: 8 = 3²−1 typed (payoff; 3-5 commits)

1. `Traceless3` : the sum-zero-trace subspace of 3×3 matrices over ℚ;
   dimension 8 by explicit basis (8 matrices, linear independence via
   `Linalg213/Rank` machinery or direct `decide`).
2. `adjoint_dim_eq_regular_minus_trivial` : 9 = 8 + 1 with the 1 being
   the scalar line split off by the trace count-Lens — the "−1" as
   self-pointing axis, consistent with the promotion-essay reading of
   `b₁ = NS²−1` (`research-notes/promotion_essay_log.md` entry 1).
3. Bridge theorems, each a *number-match with typed endpoints*: dim
   `Traceless3` = `H1K` rank = `OctetModule` 𝔽₂-dimension = 8.  The
   physics reading ("= SU(3) gluon octet") stays a reading; what closes
   is that the math side now offers an adjoint-shaped *object*, not only
   the integer.  This serves Tracks **D6/E3** of
   `research-notes/frontiers/research_program_year_horizon.md` and the
   `c`-independence point of
   `research-notes/frontiers/atomic_c_multiplicity_forcing.md`
   (`dim su(NS) = NS²−1` is constant in `c`; cf.
   `k32_b1_32_crosses_adjoint_only_at_2`), and upgrades G1/G2 of
   `research-notes/frontiers/classical_input_gap_closure.md` and the
   Unit-model status recorded in
   `research-notes/frontiers/delta4_dual_defect_status.md`.
4. Success criterion: `#print axioms` ∅ on all bridge theorems; the
   Sym(3) action on `Traceless3` by conjugation of permutation matrices
   defined, with its fixed subspace computed (comparison point for
   `OctetModule.fixedSize = 4` over 𝔽₂ — expect and record the
   char-0/char-2 discrepancy honestly rather than forcing a match).

### Phase RF — Capstone

Cluster witnesses per `Algebra/Group/Capstone.lean` style: character
table + orthogonality + Maschke split + Σ dᵢ² + octet bridge in one
`total_witness`.  Then promotion per `theory/PROMOTION_CRITERIA.md`
(H1-H4 + S1-S3) to `theory/math/algebra/representation.md`.

## 5. Connections to Other Tracks

- **Blueprint 18 (finite Fourier)**: shares the cyclotomic carrier ℤ[ζₙ];
  DFT = character theory of Cₙ.  Division of labor: 18 owns μₙ and the
  transform; 19 owns non-abelian groups and the trace-Lens.
- **Cohomology 213** (`15_cohomology_213.md`): H¹(K) rank 8 and the
  Sym(3) module are the meeting point (Phase RE).
- **Physics/Symmetry**: `OctetModule`, `C3ChainCapstone`, `SU5Channels`
  (24 = 5²−1 traceless generators is the same regular-minus-trivial count
  at d = 5 — a free second instance of Phase RE's theorem).
- **Number Theory 213**: Zolotarev/Gauss-lemma cluster = the sign
  representation evaluated on multiplication permutations.

## 6. Open Problems (honest walls)

- **No ℂ, no algebraic closure**: irreducibility over ℚ ≠ absolute
  irreducibility.  In-scope groups (S₃, Cₙ quadratic sector, sign reps of
  Sₙ) dodge this; general Schur theory does not — record the wall.
- **Schur's lemma** in generality needs endomorphism-ring analysis over ℚ
  (division algebras can appear); out of seed scope.
- **Character values are algebraic integers**: needs ℤ[ζₙ] integrality —
  blueprint 18 territory.
- **Large Sₙ** (Young tableaux, hook lengths): a later marathon; the
  corpus's `perms n` enumeration is the entry point.

## 7. Key Insights (★)

★ **The sign representation already exists twice** (`PermSign.psign`,
Zolotarev `psign_mulPerm_hom`) — Phase RA names one Lens read at two
argument-patterns; no new object.

★ **Orthogonality is a double-count**, not an inner-product import:
`IncidenceFubini` + enumerated groups make it `decide`-scale.

★ **S₃ is entirely rational** — the full classical character theory of the
physics-relevant group survives over ℚ with no wall.

★ **8 = 3²−1 gets a typed carrier**: traceless 3×3 over ℚ, turning three
number-matches (Betti, 𝔽₂-module, coker) into object-level bridges while
keeping the physics identification a reading.

## 8. First Marathon Command

```
"Start Phase RA.  Enumerate S₃ from Symmetric.lean, define the three
irreducible matrix representations over ℚ/ℤ (sign := PermSign/Zolotarev
psign), prove the 3×3 character table + orthogonality by decide-scale
finite sums, #print axioms ∅."
```
