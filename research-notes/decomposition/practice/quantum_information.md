# Decomposition: quantum information / quantum computing (qubit, tensor product, entanglement, no-cloning, gates, measurement, Bell/CHSH, von Neumann entropy, teleportation, density matrix)

*213-decomposition per `../README.md` (model v7.1) and `../SYNTHESIS.md` (the two invariants — the
character arrow `×↦·`/`×↦+`, the `q=±1` residue tag — plus the diagonal/no-surjection engine). A
**fresh** field in the PHYSICS deployment direction, LEVERAGE phase. It does not re-skin
`quantum_mechanics.md` (operator algebra) — its **new datum** is that the **no-cloning theorem is the
calculus's `q=−1` diagonal/no-surjection** (the same Cantor/Lawvere obstruction `no_surjection_of_fixedpointfree`),
**entanglement is the `⊗`-reading's non-factorizability residue**, and the **Bell/CHSH bound is the parity
`±1` correlation**. The thesis under test: quantum information = (the tensor `⊗`, monoidal/Hopf) +
(entanglement = non-product states = the `⊗`-reading's residue) + (no-cloning = the `q=−1` diagonal,
Cantor/Lawvere) + (gates = `q=±1` unitaries) + (von Neumann entropy = the `×↦+` character) — NO new primitive.*

**PHYSICS-BRANCH CAVEAT (read first, per CLAUDE.md "DRLT-validation-as-the-goal").** This is a
**math-structure decomposition** of quantum information's *combinatorial/operator skeleton*, NOT a physics
validation claim. Nothing here asserts a measured constant, a falsifier, or that quantum computing is
"derived from the residue". The deliverable is: *the qubit/tensor/no-cloning/entropy skeleton is the same
`⊗` + diagonal + character structure the calculus already built* — with the genuinely-physics objects (a
complex Hilbert space, the amplitude inner product, the named `noCloning`/`entanglement`/`densityMatrix`
objects) honestly located as absent.

## The decomposition (C / Reading / Residue)

- **Construction `C` — the monoidal `⊗` of state-count constructions, nothing new.** A qubit, in the
  213 physics deployment, is the **NT-axis 2-state** — the temporal atom `Qubit := Bool`, with the count
  `NT = 2` (`Qubit.qubit_state_count`). It introduces **no new construction**: the state space is the
  temporal atom, not a separate "quantum object". The **tensor product of state spaces** is the
  calculus's **monoidal product** `GRA.Monoidal.product`: two state-count models `M₁, M₂` build a product
  whose **grade adds** — `productGrade (a,b) = M₁.grade a + M₂.grade b` (`product_NT_NT_grade : grade (a,b) = a + b`).
  This is the `×↦+` shadow at the level of the construction itself: tensoring multiplies state-counts
  (`dim(H₁⊗H₂)=dim H₁·dim H₂`) and adds grades — the same monoidal structure tqft/Hopf
  (`CoAppend213`/`Convolution213` comultiplication) reads. So `C` = the `Mat2`/state-count `×`-construction
  carrying {direction (`q=±1`), fold-height, the monoidal `⊗`}.

- **Reading — the field is `C` read at *three* loci at once (the `q=±1` poles + the `⊗`-factorization):**
  - **`L_⊗` (the tensor / monoidal reading, `q=+1`):** the composite state space = the monoidal product
    (`product`, `product_NT_NT_grade`). A **product (separable) state** is one the `⊗`-reading factors:
    `ψ = ψ₁ ⊗ ψ₂`. Gates that act factor-wise are the component-wise `productOtimes`.
  - **`L_clone` (the diagonal / no-cloning reading, `q=−1`):** a *universal copier* — a single map
    `U` with `U(ψ) = ψ ⊗ ψ` for **every** `ψ` — is a point-surjective self-cover, exactly the
    construction the diagonal forbids. No-cloning = `no_surjection_of_fixedpointfree` / `object1_not_surjective`
    (below). This is the `q=−1` escape pole.
  - **`L_unitary` (gates / norm-preserving, `q=±1`):** a quantum gate is a unitary — the
    det/holonomy = 1 norm-preserving reading (`det_holonomy_eq_one`); the concrete finite gates are the
    elliptic involutions/rotations (the `q=±1` unimodular involutions, `bothSwap`/`multiplier_unimodular`).
  - **`L_Born` (measurement / the `q=+1` collapse):** measurement reads off a real eigenvalue (a `q=+1`
    fixed point, `disc_symmetric_nonneg`), the Born-rule weight-reading (per `quantum_mechanics.md`).
  - **`L_vN` (von Neumann entropy / the `×↦+` character):** `S(ρ) = −tr ρ log ρ` is Shannon entropy of
    the density matrix's eigenvalues — the `×↦+` entropy character (`entropy_additive`, `surprise_additive`).

- **Residue — the `q=±1` tag, read at BOTH poles, plus the `⊗`-factorization residue.**
  - **Entanglement = the `q=−1`/non-factor residue of `L_⊗`.** An **entangled state is a non-product
    state** — a state the `⊗`-reading *cannot* decompose as `ψ₁ ⊗ ψ₂`. This is the **same
    non-factorizability** as sum-vs-product / the prime non-factoring: a residue of *one* factorization
    reading, what `L_⊗` forces (a single composite-space vector) but cannot capture (a factor pair).
  - **No-cloning = the `q=−1` escape diagonal.** A universal copy map would be a surjection/fixed-point
    the diagonal forbids; no-cloning is `escape_residue_outside` ⟵ `no_surjection_of_fixedpointfree`.
  - The genuinely-physics residue (the complex amplitude `⟨ψ|φ⟩`, the inner-product Hilbert space, the
    named `densityMatrix`/`teleportation` objects) sits at the same `Real213`/ℂ + inner-product place
    `quantum_mechanics.md` located as open.

## Re-seeing (⟨C | L⟩)

```
   qubit                    =  ⟨ NT-axis state-count | the 2-state Bool reading ⟩         (qubit_state_count : NT = 2)
   tensor of state spaces   =  the monoidal product (grade ADDS, count MULTIPLIES)        (product, product_NT_NT_grade)
   product / separable state=  a state the ⊗-reading FACTORS as ψ₁⊗ψ₂                      (productOtimes component-wise)
   entanglement             =  a NON-product state = the ⊗-reading's non-factor residue   (q=−1; SAME as prime non-factoring)
   ★ no-cloning theorem      =  no universal copier = a forbidden surjection (the diagonal) (no_surjection_of_fixedpointfree)
   quantum gate (unitary)   =  the q=±1 norm-preserving det/holonomy = 1 reading           (det_holonomy_eq_one; multiplier_unimodular)
   measurement (Born rule)  =  the q=+1 real-eigenvalue collapse (read a fixed point)      (disc_symmetric_nonneg; quantum_mechanics.md)
   Bell / CHSH inequality   =  the parity ±1 correlation bound (the q=±1 spectral fact)    (legendre_mul ±1; Bell.chsh_bound = 12)
   von Neumann entropy S(ρ) =  the ×↦+ entropy character on ρ's eigenvalues               (entropy_additive, surprise_additive)
   density matrix ρ         =  the weight-reading (a mixed state = a probability over pure)(probability weight; named object ABSENT)
   teleportation            =  a Bell-measurement + classical-bit routing (a ⊗-recombination)(CONCEPTUAL — named object ABSENT)
```

Side by side, quantum information is **one `⊗`-construction read at the two `ResidueTag` poles plus the
factorization reading** — the same picture `tqft`/`hopf_algebras` read at `⊗`, `cardinality`/`godel` read
at the `q=−1` diagonal, `entropy`/`information_theory` read at the `×↦+` character, and `parity` read at `±1`:

| reading | what it does | pole | built anchor |
|---|---|---|---|
| `L_⊗` monoidal tensor (`tqft`/`hopf`) | builds the composite state space; grade adds | **q=+1** | `product_NT_NT_grade` |
| `L_clone` no-cloning (`cardinality`/`godel`) | a universal copier is a forbidden surjection | **q=−1** | `no_surjection_of_fixedpointfree` |
| `L_unitary` gates (`curvature`/`parity`) | norm-preserving involution/rotation, det 1 | **q=±1** | `det_holonomy_eq_one`, `multiplier_unimodular` |
| `L_Born` measurement (`quantum_mechanics`) | reads a real eigenvalue (fixed point) | **q=+1** | `disc_symmetric_nonneg` |
| `L_CHSH` Bell (`parity`) | the `±1` correlation bound | **q=±1** | `legendre_mul`, `Bell.chsh_bound_value` |
| `L_vN` von Neumann entropy (`entropy`) | the `×↦+` character on ρ's spectrum | (character) | `entropy_additive` |

**The leverage**: no-cloning, entanglement, and the Bell bound are not three independent quantum mysteries
— they are the calculus's `q=−1` diagonal, the `⊗`-reading's non-factor residue, and the `±1` parity
correlation, three readings the corpus already built for cardinality/Gödel, prime factorization, and parity.

## Revelation (collapse + forcing + spine)

**★ Collapse (the new datum) — no-cloning IS the `q=−1` diagonal/no-surjection (Cantor/Lawvere).** A
hypothetical universal cloner is a single map `U` such that `U|ψ⟩ = |ψ⟩|ψ⟩` for **every** state `ψ`.
Linearity of `U` then forces a contradiction on a superposition `α|0⟩+β|1⟩` — the textbook proof. The
calculus reads this *structurally*: a universal copy map is a **point-surjective self-cover** — a map whose
rows realize "every state, copied" — and the diagonal forbids exactly that. The obstruction is
`OneDiagonal.no_surjection_of_fixedpointfree` (the Lawvere contrapositive: a fixed-point-free modifier
forbids any point-surjection), instantiated at `Raw` as `FlatOntologyClosure.object1_not_surjective` (the
self-cover always leaves a residue). So **no-cloning is the SAME `q=−1` escaping diagonal as Cantor's
theorem (`cardinality.md`), Gödel incompleteness (`godel.md`), and the Vitali/non-measurable escape
(`measure.md`)** — a self-pointing reading whose residue cannot be in the system's image. This is not a
re-description: it places no-cloning on the *one* diagonal engine the `q=−1` spine is built from
(`ResidueTag.escape_residue_outside`, delegating verbatim to `no_surjection_of_fixedpointfree`). The
quantum-info "you cannot copy an unknown state" and the set-theoretic "no surjection onto the power set"
are one obstruction read in two domains.

**Collapse — entanglement = the `⊗`-reading's non-factorizability residue, the SAME residue as prime
non-factoring.** A separable state factors as `ψ₁ ⊗ ψ₂` (the `productOtimes` component-wise reading); an
entangled state is one the factorization reading **cannot** decompose. The calculus has met this exact
shape before: a prime is a number the *sum*-or-*product* factorization reading cannot split
(`prime_factorization.md`, `two_three_unique`); the residue is "what the factorization reading forces (a
single composite object) but cannot capture (a factor decomposition)". Entanglement is that residue on the
monoidal `⊗` — **a non-product state is the residue of the `L_⊗` factorization reading**, no new primitive.
(The `⊗`-construction itself is built and PURE: `Monoidal.product`, grade-additive, 13/0.)

**Forcing — gates are the `q=±1` unimodular norm-preserving reading.** A quantum gate is a unitary; the
norm-preserving constraint is the det/holonomy = 1 reading (`det_holonomy_eq_one`, every norm-preserving
step composes to total det 1). The single-qubit Pauli/Hadamard-style involutions and the rotation gates
are the `q=±1` unimodular involutions/rotations — `multiplier_unimodular` (`q·q=1`, the `±1` locus) and
`FoldKlein.bothSwap` (the involutive swap). Reversibility of quantum gates = the involution `q²=1`; this is
forced by norm-preservation, not posited.

**Collapse — the Bell/CHSH bound is the parity `±1` correlation.** A CHSH correlation `E(a,b) = ⟨A_a B_b⟩`
is a `±1`-valued spin-product expectation; the CHSH operator's eigenvalues and the classical `±2` /
quantum-violation bound are a `q=±1` spectral fact — the same `±1` character `parity.md` reads
(`legendre_mul`, the order-2 `×↦{±1}` multiplicative character; the Zolotarev/parity collapse). The repo's
physics deployment records the structural coincidence-count bound `chsh_bound = 2·NS·NT = 12`
(`Bell.chsh_bound_value`) — an atomic integer, **orthogonal** to the operator-level `±1` correlation
(it counts measurement-outcome pairs, not the Tsirelson `2√2`), and honestly so: the analytic Tsirelson
bound `2√2` is a `Real213`-cut value, the named open leg.

**Collapse — von Neumann entropy = the `×↦+` entropy character on ρ's eigenvalues.** `S(ρ) = −tr ρ log ρ`
is Shannon entropy applied to the density matrix's eigenvalue spectrum — `entropy.md`'s `×↦+` character
(`entropy_additive : H(m+n)=H(m)+H(n)`, `surprise_additive`), the same arrow as `vp_mul`/`det2_mul`/
`legendre_mul`. Subadditivity and the entanglement entropy of a pure bipartite state are this character
read on the reduced density matrix; the *eigenvalue* extraction (the `d>1` spectral theorem over ℂ) is the
inherited open leg (`spectral.md`/`quantum_mechanics.md`).

**The `q=±1` spine, made literal in one field.** Quantum information is the cleanest single field where the
spine appears whole:
- `q=−1` escape: no-cloning (`no_surjection_of_fixedpointfree`), entanglement (the non-factor residue),
  measurement collapse (the non-unitary `q=−1` break of otherwise-`q=+1` evolution).
- `q=+1` converge: the separable/product state (factors), unitary evolution (`det_holonomy_eq_one`),
  measurement reading a real eigenvalue (`disc_symmetric_nonneg`, the fixed point).
Measurement (read a `q=+1` fixed point) and no-cloning (the `q=−1` escape) are the two poles of one
`ResidueTag` (`residue_tag_two_poles`), dual — exactly the duality `quantum_mechanics.md` found for
measurement-vs-uncertainty, here for measurement-vs-no-cloning.

## VALIDATE — verdict

**EXTEND + PREDICTION (consolidation), with no-cloning = the `q=−1` diagonal as the genuine new datum,
and several honest located breaks.** Quantum information introduces **no new construction** — it
consolidates `tqft`/`hopf` (the `⊗`), `cardinality`/`godel` (the diagonal), `parity` (the `±1`),
`entropy` (the `×↦+` character), `quantum_mechanics` (the operator/Born structure), and `curvature` (det 1)
under the two standing invariants and the `q=±1` spine. The model **held** (no break to the interior).

- **Leg 1 — qubit + tensor = the monoidal `⊗`. EXTEND, BUILT.** `Qubit.qubit_state_count : NT = 2`
  (4/0 PURE); `Monoidal.product` + `product_NT_NT_grade` (13/0 PURE, grade-additive monoidal product).
  The state space is the temporal atom; the tensor is the calculus's monoidal product.

- **★ Leg 2 — no-cloning = the `q=−1` diagonal/no-surjection. PREDICTION, ENGINE BUILT.** A universal
  cloner is a forbidden point-surjection; `no_surjection_of_fixedpointfree` (11/0 PURE, `OneDiagonal`) /
  `object1_not_surjective` (`FlatOntologyClosure`) is the obstruction, on the same `q=−1` spine as Cantor/
  Gödel/Vitali (`ResidueTag.escape_residue_outside`, 55/0). The **named `noCloning` object is ABSENT**
  (no linear-map / Hilbert-state type to host the linearity proof), so this is a structural PREDICTION:
  the obstruction-engine is built and ∅-axiom; the quantum-specific witness is the open leg.

- **Leg 3 — entanglement = the `⊗`-reading's non-factor residue. PREDICTION.** Non-product states are the
  factorization residue, the same shape as prime non-factoring; the `⊗`-construction is built (`product`),
  but the **named `entanglement`/Schmidt-decomposition object is ABSENT** (needs a complex Hilbert tensor).

- **Leg 4 — gates = `q=±1` unitaries. EXTEND (consolidation).** `det_holonomy_eq_one` (26/0 PURE) =
  norm-preserving det 1; `multiplier_unimodular` (`q²=1`, 55/0 in `ResidueTag`) / `FoldKlein.bothSwap` =
  the involution/rotation `±1` locus. No new primitive. (Inherited from `quantum_mechanics.md`/`curvature.md`.)

- **Leg 5 — measurement = the `q=+1` real-eigenvalue collapse. EXTEND.** `disc_symmetric_nonneg` (9/0
  PURE) = symmetric ⟹ real spectrum (the Born-rule fixed point), per `quantum_mechanics.md`. The amplitude
  `|⟨ψ|φ⟩|²` and the collapse map are the inherited located break.

- **Leg 6 — Bell/CHSH = the parity `±1` correlation. PREDICTION + atomic bound BUILT.** `legendre_mul`
  (5/0 PURE) = the order-2 `±1` character; `Bell.chsh_bound_value : chsh_bound = 12` (5/0 PURE) = the
  213-native structural coincidence-count bound (an atomic integer, orthogonal to the analytic Tsirelson
  `2√2`). The `±1` correlation structure is the certified content; the analytic violation `2√2` is a
  `Real213`-cut, the open leg.

- **Leg 7 — von Neumann entropy = the `×↦+` character. PREDICTION.** `entropy_additive`/`surprise_additive`
  (14/0 PURE) = the additive entropy character on the eigenvalue spectrum. The **named `densityMatrix`/
  `vonNeumannEntropy` object is ABSENT** (needs the `d>1` complex spectral theorem to extract ρ's
  eigenvalues); the additivity character is built on the dyadic substrate.

**The located breaks (honest, in the `knots.md`/`quantum_mechanics.md` spirit).** Quantum information pins
where the calculus stops — the genuinely-physics/named objects, all at the `Real213`/ℂ + Hilbert-space place:
1. **A complex Hilbert space / inner product `⟨ψ|φ⟩` / the amplitude `|·|²`** — ABSENT (inherited from
   `quantum_mechanics.md`). The closest built structure is the Cayley–Dickson norm (`SignedCut/CD/CDNorm`),
   a level-indexed `normSq` with conjugation, NOT welded to a state vector or the probability weight.
2. **The named `noCloning` / `entanglement` / Schmidt / `densityMatrix` / `vonNeumannEntropy` /
   `teleportation` objects** — ABSENT (grep-confirmed: no `no_cloning`, `entangle`, `densityMatrix`,
   `vonNeumann`, `teleport` definitions in `lean/E213`; the only quantum names are `Quantum.Qubit`,
   `Quantum.Bell` = atomic counts, and `Quantum.Bekenstein`). The *engines* (the diagonal, the monoidal
   product, the character, the `±1` parity) are all built and PURE; only the field-specific named objects
   are absent — predicted-not-built, the same shape `quantum_mechanics.md` recorded.
3. **The analytic Tsirelson bound `2√2`** — a `Real213`-cut value, not the built atomic integer 12; the
   `±1` correlation structure is certified, the analytic violation is the `Real213` residue.
4. **Teleportation as an object** — CONCEPTUAL: a Bell-measurement + 2 classical bits + a `⊗`-recombination
   (a corrective unitary); every *leg* (Bell measurement, the `±1` parity, the gate `q=±1` unitary) is
   built, but the named protocol/circuit object is absent.

## Verified Lean anchors (file:line:theorem — all grep + `scan_axioms.py`-verified this session; all PURE)

| Leg | Theorem (file:line) | Purity (this session) |
|---|---|---|
| ★ qubit = NT-axis 2-state | `Lib/Physics/Quantum/Qubit.lean:23` `qubit_state_count : NT = 2`; `:34` `two_qubit_pair_count : NS*NT = 6` | **PURE** (4/0) ✓ |
| ★★ tensor of state spaces = monoidal product (grade adds) | `Lib/Math/Algebra/GRA/Monoidal.lean:129` `product`; `:182` `product_NT_NT_grade : grade (a,b) = a+b`; `:155` `leftUnitHom` | **PURE** (13/0) ✓ |
| ★★★★ no-cloning = the q=−1 diagonal/no-surjection (Cantor/Lawvere) | `Lens/Foundations/OneDiagonal.lean:51` `no_surjection_of_fixedpointfree`; `:43` `lawvere_fixed_point`; `:61` `cantor_via_lawvere` | **PURE** (11/0) ✓ |
| ★★★★ the residue is the diagonal at `A=Raw` (the self-cover always leaves a residue) | `Lens/Foundations/FlatOntologyClosure.lean:61` `object1_not_surjective` | **PURE** (per `FlatOntologyClosure`) ✓ |
| ★★★ the q=±1 spine: escape (no-cloning/entanglement) ⟵ no-surjection; converge (separable/unitary) | `Lib/Math/Foundations/ResidueTag.lean:133` `escape_residue_outside`; `:160` `converge_residue_fixed`; `:86` `multiplier_unimodular` (q²=1); `:228` `residue_tag_two_poles` | **PURE** (55/0) ✓ |
| ★★★ gates = q=±1 norm-preserving det/holonomy = 1 | `Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:136` `det_holonomy_eq_one` | **PURE** (26/0) ✓ |
| ★★ measurement = the q=+1 real-eigenvalue collapse (symmetric ⟹ real spectrum) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2SymmetricSpectrum.lean:83` `disc_symmetric_nonneg` | **PURE** (9/0) ✓ |
| ★★ Bell/CHSH = the parity ±1 correlation (order-2 `×↦{±1}` character) | `Lib/Math/NumberTheory/ModArith/LegendreMultiplicative.lean:77` `legendre_mul` | **PURE** (5/0) ✓ |
| ★★ Bell atomic coincidence-count bound (213-native, orthogonal to Tsirelson 2√2) | `Lib/Physics/Quantum/Bell.lean:37` `chsh_bound_value : chsh_bound = 12`; `:43` `bell_coincidence_atomic`; `:54` `bell_falsifier_bracket` | **PURE** (5/0) ✓ |
| ★★ von Neumann entropy = the `×↦+` entropy character (additivity on the spectrum) | `Lib/Math/Probability/Information/Entropy.lean:83` `entropy_additive`; `:90` `surprise_additive` | **PURE** (14/0) ✓ |
| q=−1 antisymmetry (commutator, for the operator-side cross-frame) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean:76` `bracket_antisymm` | **PURE** (10/0) ✓ |
| cross-frame | `quantum_mechanics.md` (operator/Born), `tqft.md`/`hopf_algebras.md` (`⊗`, `Convolution213`/`CoAppend213`), `cardinality.md`/`godel.md` (diagonal), `parity.md` (`±1`), `entropy.md`/`information_theory.md` (`×↦+`) | prior, ∅-axiom ✓ |

## Dropped / flagged (honest — not cited as anchors)

- **A named `noCloning` theorem** — grep-confirmed ABSENT in `lean/E213`. The *obstruction-engine*
  (`no_surjection_of_fixedpointfree`/`object1_not_surjective`) is built and PURE; the linearity-based
  quantum witness is the predicted-not-built leg. Cited only as the engine, never as a quantum theorem.
- **`entanglement` / Schmidt decomposition / `densityMatrix` / `vonNeumannEntropy` / `teleportation`
  objects** — grep-confirmed ABSENT (the only quantum names are `Quantum.Qubit`, `Quantum.Bell`,
  `Quantum.Bekenstein`, all atomic counts). Flagged predicted-not-built; the engines are cited, the named
  objects are not.
- **The analytic Tsirelson bound `2√2`** — a `Real213`-cut value, NOT the built atomic integer 12. The
  built `chsh_bound = 12` is a structural coincidence-count, cited honestly as orthogonal to the operator-level
  CHSH violation; the `2√2` is flagged as the `Real213` open leg, not asserted.
- **A complex Hilbert inner product `⟨ψ|φ⟩` and the amplitude `|·|²`** — ABSENT (inherited from
  `quantum_mechanics.md`); the Cayley–Dickson `CDNorm` is the nearest, not welded. Flagged CONCEPTUAL.

## Verified buildable witness (the new datum, ready to promote)

The **no-cloning = `q=−1` diagonal** collapse is the cleanest buildable witness: a one-line corollary
that a *universal qubit copier* (a point-surjective `f : State → (State → State)` realizing "copy every
state") cannot exist, instantiating `no_surjection_of_fixedpointfree` at the qubit state type with the
fixed-point-free flip — the **exact** shape of `cantor_via_lawvere` (`OneDiagonal.lean:61`,
`no_surjection_of_fixedpointfree (fun b => !b) bnot_self_ne`). The engine is already ∅-axiom (11/0); the
witness needs only the qubit `Bool`-state type (`Qubit := Bool`, built) — a single ∅-axiom corollary
`no_universal_qubit_copier` would promote the new datum from prose to a machine-checked theorem, on the
same diagonal as Cantor. (Flagged as a promotion target, NOT claimed built this session.)

## Touches model v7.1?

**No new primitive; EXTEND + one consolidation note.** The two invariants (the character arrow `×↦+` =
von Neumann entropy; the `q=±1` residue = no-cloning/entanglement vs separable/unitary) and the four axes
absorb quantum information with nothing added; the `⊗` is the monoidal product already in the frame. The
note for the README's batch log:

> **Quantum information is the tensor `⊗` + the `q=−1` diagonal (no-cloning) + the `×↦+` entropy
> character — no new primitive.** The qubit = the NT-axis 2-state (`qubit_state_count : NT = 2`, 4/0); the
> tensor of state spaces = the monoidal product `Monoidal.product` (grade adds, 13/0). ★ **No-cloning =
> the calculus's `q=−1` diagonal/no-surjection** — a universal copier is a forbidden point-surjection,
> `no_surjection_of_fixedpointfree`/`object1_not_surjective`, the SAME Cantor/Lawvere obstruction as
> `cardinality`/`godel`/`measure` (11/0). Entanglement = the `⊗`-reading's non-factorizability residue
> (the same residue as prime non-factoring). Gates = the `q=±1` unimodular norm-preserving reading
> (`det_holonomy_eq_one` 26/0, `multiplier_unimodular`). Measurement = the `q=+1` real-eigenvalue collapse
> (`disc_symmetric_nonneg` 9/0). Bell/CHSH = the parity `±1` correlation (`legendre_mul` 5/0; the built
> atomic count `Bell.chsh_bound = 12` 5/0, orthogonal to the `Real213` Tsirelson `2√2`). Von Neumann
> entropy = the `×↦+` character (`entropy_additive` 14/0). Located breaks: the complex Hilbert
> inner-product / amplitude `|·|²`, and the named `noCloning`/`entanglement`/`densityMatrix`/`teleportation`
> objects — the `Real213`/ℂ + Hilbert residue (engines built, named objects absent). Buildable witness:
> a ∅-axiom `no_universal_qubit_copier` corollary of `no_surjection_of_fixedpointfree` at `Qubit := Bool`.
> PHYSICS-branch: a math-structure decomposition, no validation claim.
