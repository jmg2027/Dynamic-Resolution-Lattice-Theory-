# Decomposition: cluster algebras (seeds, mutation μ_k, the exchange relation, the Laurent phenomenon, finite-type/Dynkin classification, the Markov/Stern–Brocot link)

*213-decomposition per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕ Residue(L,C)`).*
*The combinatorial-mutation entry. It does NOT re-skin `continued_fractions.md` (the
Stern–Brocot/mediant tree, `manin_unimodular_decomposition`) or `arithmetic_dynamics.md`
(the Vieta-jump recurrence, `CassiniUnimodular`): the NEW datum is that **a cluster algebra
is the repo's `SternBrocotMarkov` — the rank-3 Markov cluster algebra, BUILT 130/0** — with
**mutation = the q=±1 involution**, the **exchange relation = the mediant/Markov-Vieta jump**
(`markoff_vieta`, `markov_vieta_int`), the **exchange matrix = the SL₂ det-1 antisymmetric
form** (`det2_mul`/`mNode_det1`, `bracket_antisymm`), the **Laurent phenomenon = a q=+1
normal-form/no-residue theorem** (`FreeReduction`'s `Quot`-free normal form), and **finite-type
(Dynkin) = the q=+1 finite-order orbit** (`finite_order_divides_twelve`) vs **infinite-type = the
q=−1 escape** (`golden_aperiodic`). No new primitive.*

## The decomposition (C / Reading / Residue q=±1)

- **Construction `C` — the SL₂(ℤ) mediant tree, `continued_fractions.md`'s `C` carrying a
  seed.** A cluster-algebra **seed** = (a cluster of variables + an exchange matrix `B`). On the
  rank-2/rank-3 carrier this is exactly the **Stern–Brocot/Markoff node**: a node of the det-1
  binary tree (`sbInterval : List Bool → …`, root `(0/1, 1/0)`), each step a **mediant** L/R
  move (`sbStep`). The seed's *cluster* is the node's pair/triple of entries
  (`mInterval`/`mNode`), the seed's *exchange matrix* is the SL₂ det-1 orientation
  (`adj`: `q·r = p·s + 1`, preserved by every step — `sbStep_preserves`/`sbInterval_adj`).
  This is the **same `C`** as `continued_fractions.md` (the 2-term continuant fold, the
  Stern–Brocot mediant) and `arithmetic_dynamics.md` (the self-applying iterator), now read with
  a *seed* attached. The repo builds it as the **proper (injective) tree** carrying the Markoff
  matrices `M_t ∈ SL₂(ℤ)` (`genL = ⟨2,1,1,1⟩`, `genR = ⟨3,4,2,3⟩`, node = mediant product
  `mNode = M_l·M_r`).

- **Reading `L_exchange` — the binary mutation/exchange read at residue resolution.** A
  **mutation μ_k** replaces one cluster variable `x_k` by `x_k'` through the **exchange
  relation** `x_k·x_k' = M₁ + M₂` (two monomials). On the Markov carrier this reading is the
  **Vieta jump** `(x,y,z) ↦ (x, z, 3xz − y)` — the cluster variable `y` is exchanged for
  `3xz − y`, a *binary* law (`3xz` and `−y`, two terms). It is built two ways: the **integer
  Vieta jump preserves the Markov form** (`markov_vieta_int`: the equation
  `x²+y²+z² = 3xyz` is invariant under the jump), and the **matrix Cayley–Hamilton recurrence**
  `m' = tr(M)·m₃ − m₂ = 3·m₁·m₂ − m₃` (`markoff_vieta`, with the entry-shape `tr = 3c`
  `mInterval_shape`). The exchange matrix `B` (skew-symmetric) is the SL₂ det-1 form, read out
  as the `q=−1` **antisymmetric** bit (`bracket_antisymm`, `cup1_antisymmetric`).

- **Residue, tagged `q = ±1`** — the **two poles of the mutation orbit**:
  - **q = +1 (converge / finite-type / Laurent normal form).** μ_k² = id is the q=+1 involution
    (`bothSwap_involutive`, `multiplier_unimodular` q²=1): a mutation undone by re-mutating in
    the same direction. **Finite-type** (Dynkin classification) = the orbit closes after finitely
    many seeds = the **finite-order mutation pole** (`finite_order_divides_twelve`/`no_order_five`,
    `crystallographic_spectrum` — disc<0 ⟹ periodic floor). The **Laurent phenomenon** (every
    cluster variable stays a Laurent polynomial in any seed — denominators stay monomial, no
    "residue beyond Laurent") = a **q=+1 NO-RESIDUE / normal-form theorem**: the mutation reading
    never leaves its canonical ring, the same "stays canonical / confluent normal form" as
    `FreeReduction`'s `Quot`-free `proj_val_eq_iff`. On the Markov carrier the no-blowup is
    *literal and integer*: the Vieta jump keeps the entries positive integers
    (`mInterval_pos`/`markovNum_pos`) and the residue/number stay coprime det-1
    (`mNode_det1`, `markovRes_recovery_dvd`) — no denominator residue arises.
  - **q = −1 (escape / infinite-type / unbounded orbit).** Infinite-type cluster algebras have
    infinitely many seeds = the **infinite mutation orbit** = the q=−1 escape pole
    (`golden_aperiodic`: disc>0 ⟹ the SL₂ boost has infinite order, never returns;
    `cassini_law_one_at_two_multipliers` is the one law at the two poles). The Markov tree itself
    is the infinite case: `markovNum_children_ne` (children distinct) ⟹ an unbounded orbit of
    distinct Markov numbers — the rank-3 cluster algebra is infinite-type.

## Re-seeing — ⟨C | L_exchange⟩ ⊕ Residue

```
   seed (cluster + exchange matrix B)  =  ⟨ Stern–Brocot/Markoff node | — ⟩       sbInterval / mNode  (C, with a seed)
   exchange matrix B (skew-symmetric)  =  the SL₂ det-1 antisymmetric form        adj / det2_mul / bracket_antisymm
   mutation μ_k (involution μ_k²=id)   =  the q=±1 swap/involution                bothSwap_involutive / multiplier_unimodular (q²=1)
   exchange relation x_k·x_k'=M₁+M₂    =  the mediant / Markov-Vieta binary jump   markoff_vieta / markov_vieta_int  (3xz − y)
   the cluster variables               =  the node's entries (cluster)            mInterval / markovNum
   Laurent phenomenon (no denom. residue) = the q=+1 NO-RESIDUE / normal form     FreeReduction.proj_val_eq_iff ; mInterval_pos / mNode_det1
   finite-type (Dynkin classification) = the q=+1 finite-order mutation orbit      finite_order_divides_twelve / crystallographic_spectrum
   infinite-type                       =  the q=−1 escape (infinite orbit)         golden_aperiodic / markovNum_children_ne
   Markov triples x²+y²+z²=3xyz        =  the rank-3 cluster algebra, BUILT        mInterval_markov  (SternBrocotMarkov 130/0)
   Stern–Brocot mediant tree           =  the seed-mutation graph                  manin_unimodular_decomposition / sbInterval_adj
   the q=±1 tag                        =  multiplier ∓1                            ResidueTag.multiplier_unimodular
```

The single move: a cluster algebra is **not** a new field — it is the **Stern–Brocot/Markov
mutation structure** (`continued_fractions.md`/`arithmetic_dynamics.md`'s `C`) with a **seed**
attached, mutation = the q=±1 involution, the exchange relation = the mediant/Markov-Vieta
binary jump, the Laurent phenomenon = a q=+1 no-residue normal-form theorem, and
finite-type/Dynkin = the q=+1 finite-order orbit. The repo's rank-3 Markov instance is **built
130/0**; the *named, general* `ClusterAlgebra`/`mutation`/`exchangeMatrix`/`Laurent` objects are
absent (predicted-not-built, grep-confirmed).

## Revelation (collapse + forcing + the q=±1 spine)

**Collapse 1 — the exchange relation IS the mediant/Markov-Vieta jump, BUILT.** The defining
cluster-algebra move `x_k·x_k' = M₁ + M₂` (a *binary* exchange) is, on the rank-3 carrier,
exactly the Vieta jump `(x,y,z) ↦ (x, z, 3xz − y)`. This is not asserted — `markov_vieta_int`
proves the Markov equation `x²+y²+z² = 3xyz` is *preserved* by the jump, and `markoff_vieta`
proves the matrix form `m' = 3·m₁·m₂ − m₃` (Cayley–Hamilton `M² = tr·M − I` with the entry-shape
`tr = 3c`, `mInterval_shape`). So the *exchange relation* of the Markov cluster algebra is a
machine-checked ∅-axiom theorem, and `mInterval_markov` proves the whole tree's nodes satisfy
the Markov equation — **the rank-3 cluster algebra is built**. "Cluster mutation" and "Markov
Vieta jump / Stern–Brocot mediant" collapse to one `(C, L)`.

**Collapse 2 — the exchange matrix IS the q=−1 antisymmetric SL₂ det-1 form, and mutation IS the
q=±1 involution.** A cluster algebra's exchange matrix `B` is skew-symmetric/symmetrizable; on
the Markov carrier the orientation is the SL₂ det-1 invariant (`adj`: `q·r = p·s + 1`,
`sbInterval_adj`), and `det2_mul`/`mNode_det1` keep every node in SL₂(ℤ) — the multiplicative
det-1 backbone, the *same* antisymmetric `q=−1` form as `Mat2Bracket.bracket_antisymm`
(`[A,B] = −[B,A]`) and `cup1_antisymmetric` (`e_i∧e_j = −(e_j∧e_i)`). Mutation's involutivity
μ_k² = id is the q=±1 swap (`bothSwap_involutive`, `multiplier_unimodular`: `q·q = 1` so
`q ∈ {±1}`). So the exchange matrix (antisymmetry) and mutation (involution) are the *two faces
of the same q=±1 bit* the calculus carries everywhere (`SYNTHESIS.md` §2, the direction/swap
axis).

**Forcing — the Laurent phenomenon is a q=+1 no-residue normal-form theorem, not a miracle.**
The "Laurent phenomenon" — every cluster variable, expressed in any other seed's cluster, is a
*Laurent* polynomial (denominators stay monomial, never blow up) — is the calculus's q=+1
**no-residue / confluent normal form**: the mutation reading *stays in its canonical ring*, the
same shape as `FreeReduction`'s `proj_val_eq_iff` (the free group as a `Quot`-free normal-form
Σ-quotient — `normalize` lands in the canonical subtype, no residue beyond it) and
`LensImage.proj_val_eq_iff`. On the rank-3 Markov instance the no-blowup is *literal and
integer*: the Vieta jump keeps the entries positive integers (`mInterval_pos`, `markovNum_pos`),
the node stays det-1 (`mNode_det1`) with coprime residue/number (`markovRes_recovery_dvd`,
`markovNum_dvd_res_sq_succ`) — the mutation never produces a denominator residue. So the
Laurent phenomenon is *forced* by the same q=+1 "stays canonical" mechanism the colimit corner's
Side-A normal form uses (`README.md` v7.1, `colimit_quotient_synthesis.md`), not a separate fact.

**The spine — finite-type/Dynkin is the q=+1 finite-order orbit; infinite-type is the q=−1
escape.** This is the q=±1 spine (`SYNTHESIS.md` §3) read on a mutation orbit:
- **q=+1 (finite-type / Dynkin):** finitely many seeds = the mutation orbit *terminates* = the
  finite-order pole `finite_order_divides_twelve` / `no_order_five` / `crystallographic_spectrum`
  (the disc<0 elliptic / crystallographic spectrum — the same finite-order spectrum that
  `continued_fractions.md` uses for periodicity). Fomin–Zelevinsky's finite-type = Dynkin
  diagrams (A/D/E) is the *terminating* mutation orbit, the converge pole.
- **q=−1 (infinite-type):** infinitely many seeds = the orbit *escapes* = `golden_aperiodic`
  (disc>0 ⟹ infinite order). The Markov tree is exactly this: `markovNum_children_ne` (distinct
  children) ⟹ an infinite orbit of distinct Markov numbers — the rank-3 Markov cluster algebra
  is infinite-type, the q=−1 pole. `cassini_law_one_at_two_multipliers` is the *one* law read at
  the two poles, exactly the finite-type/infinite-type split.

No new primitive: a cluster algebra = (the Stern–Brocot/Markov mediant `C` with a seed) +
(mutation = the q=±1 involution) + (the exchange relation = the mediant/Markov-Vieta binary jump,
BUILT) + (Laurent = the q=+1 no-residue normal form) + (finite-type/Dynkin = the q=+1
finite-order orbit, infinite-type = q=−1 escape). It is the `SternBrocotMarkov` corpus read as a
cluster algebra.

## VALIDATE verdict — **EXTEND** (the rank-3 Markov cluster algebra is BUILT 130/0; the general named objects predicted-not-built)

No new primitive, no break. The cluster algebra slots entirely into model v7.1: `C` = the
Stern–Brocot/Markoff mediant tree with a seed (= `continued_fractions.md`/`arithmetic_dynamics.md`'s
`C`), `L` = the mutation/exchange = the mediant/Markov-Vieta binary jump at residue resolution,
`Residue` = the orbit's finite-type/infinite-type dichotomy tagged `q=±1`. It is **EXTEND**
(consolidation, not a fresh prediction) because the load-bearing instance — the **rank-3 Markov
cluster algebra** — is *already built and PURE* (`SternBrocotMarkov` 130/0): the exchange relation
(`markoff_vieta`, `markov_vieta_int`), the cluster-variable Markov-equation invariance
(`mInterval_markov`), the SL₂ det-1 exchange-matrix backbone (`det2_mul`/`mNode_det1`), the
no-residue integer Laurent witness (`mInterval_pos`), and the infinite-orbit pole
(`markovNum_children_ne`) are all machine-checked. The calculus does not predict the shape from
parts here — it *recognizes its own built object* as a cluster algebra.

**The honest line: every NAMED cluster-algebra object is ABSENT.** Grep-confirmed (case-insensitive,
`lean/E213/`): **no `ClusterAlgebra` / `cluster_algebra` / `mutation` / `mutate` / `exchangeMatrix`
/ `exchange_matrix` / `exchangeRelation` / `laurentPhenomenon` / `Laurent` / `Dynkin` / `seedMutation`
theorem or definition** — the only `mutation` hit is a code comment
(`Analysis/CascadeCalculus/Core.lean:75`, "graph mutation; deferred"), and all `cluster` hits are
documentation organization jargon ("sub-cluster"). What is built is the **rank-3 Markov instance +
the q=±1 ties**: the mediant tree (`sbInterval`/`mNode`), the exchange relation
(`markoff_vieta`/`markov_vieta_int`), the SL₂ det-1 exchange form (`det2_mul`/`bracket_antisymm`),
the q=±1 involution (`bothSwap_involutive`/`multiplier_unimodular`), the finite/infinite-orbit poles
(`finite_order_divides_twelve`/`golden_aperiodic`), the Laurent-as-normal-form analogue
(`FreeReduction`), and the formal q=±1 tag (`ResidueTag`). The **welds** — a named `ClusterAlgebra`
structure, a general `mutation : Seed → Seed`, a `B`-matrix mutation rule, a general Laurent-phenomenon
theorem (rank ≥ 2, any seed), and the Fomin–Zelevinsky finite-type ⟺ Dynkin classification — are
unbuilt.

## Verified Lean anchors (file:line:theorem — all grep-confirmed; scans `python3 tools/scan_axioms.py <module>` from repo root, this session)

**★ The rank-3 Markov cluster algebra (exchange relation + cluster variables + exchange matrix)
— `SternBrocotMarkov` (130/0 PURE):**
- `lean/E213/Lib/Math/NumberSystems/Real213/Markov/SternBrocotMarkov.lean:104` `det2_mul`
  (`det(MN)=det M·det N` — the multiplicative SL₂ det-1 backbone = the exchange matrix's
  unimodular/antisymmetric form), `:145` `mNode_det1` (every node ∈ SL₂(ℤ)).
- `:37` `adj` (def, the det-1 Farey orientation `q·r=p·s+1`), `:53` `sbStep_preserves`,
  `:66` `sbInterval_adj` (the exchange-matrix orientation preserved by every mutation step).
- `:169` `markoff_vieta` (★ the **exchange relation** as the Cayley–Hamilton jump
  `(M_l²M_r)_c = tr(M_l)·(M_lM_r)_c − (M_r)_c = 3m₁m₂ − m₃`), `:265` `markov_vieta_int`
  (the Vieta jump `(x,y,z)↦(x,z,3xz−y)` preserves `x²+y²+z²=3xyz`).
- `:218` `mInterval_shape` (entry-shape `tr = 3c`, the keystone), `:277` `mInterval_markov`
  (★ the tree's nodes satisfy the **Markov equation** — the cluster algebra is generated),
  `:256` `markov_first_nodes` (`markovNum [] = 5, [true] = 13, [false] = 29`).
- `:402` `mInterval_pos`, `:419` `markovNum_pos` (★ entries stay positive integers — the
  **integer Laurent / no-denominator-residue** witness), `:435` `markovRes_sq` /
  `:453` `markovNum_dvd_res_sq_succ` (`u²≡−1 mod m`), `:503` `markovRes_recovery_dvd`.
- `:2702` `markovNum_children_ne` (★ distinct children ⟹ **infinite mutation orbit** =
  infinite-type = q=−1 escape).

**The exchange relation / Markov-Vieta orbit (the cluster recurrence as an orbit)
— `MarkovCassiniUnimodular` (6/0 PURE):**
- `lean/E213/Lib/Math/NumberSystems/Real213/Markov/MarkovCassiniUnimodular.lean:42` `cval_rec`,
  `:51` `markov_orbit_cassini_step`, `:59` `markov_orbit_cassini_const` (the orbit's Cassini
  invariant under the mutation/Vieta step).

**★ Mutation = the q=±1 involution (μ_k² = id) — `FoldKlein` (9/0) + `ResidueTag` (55/0):**
- `lean/E213/Lens/Number/FoldKlein.lean:50` `bothSwap_involutive` (`bothSwap (bothSwap x) = x`
  — the involution μ_k²=id).
- `lean/E213/Lib/Math/Foundations/ResidueTag.lean:81` `multiplier` (def, ∓1), `:86`
  `multiplier_unimodular` (`q·q = 1` ⟹ `q ∈ {±1}` — the involution's unimodular bit),
  `:180` `golden_is_converge` (q=+1 tied to φ), `:228` `residue_tag_two_poles`.

**★ The exchange matrix = the q=−1 antisymmetric form — `Mat2Bracket` (10/0) + `SignedCup` (14/0):**
- `lean/E213/Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean:76` `bracket_antisymm`
  (`[A,B] = −[B,A]` — the q=−1 pair-swap = skew-symmetric exchange matrix).
- `lean/E213/Lib/Math/Cohomology/Cup/SignedCup.lean:62` `cup1_antisymmetric`
  (`e_i∧e_j = −(e_j∧e_i)`).
- `lean/E213/Lib/Math/Algebra/CassiniUnimodular.lean:142` `det_closed`
  (`det s n = qⁿ·det s 0`), `:163` `cassini_law_one_at_two_multipliers` (★ one law at the two
  poles = finite-type ⟷ infinite-type), `:170` `qpow_one` (`qpow 1 n = 1`, q=+1 conserved).

**★ Laurent phenomenon = the q=+1 no-residue normal form — `FreeReduction` (26/0 PURE):**
- `lean/E213/Lib/Math/Algebra/Group/FreeReduction.lean:237` `proj_val_eq_iff` (the `Quot`-free
  normal form — the "stays canonical / no residue beyond the normal form" mechanism = Laurent
  no-blowup), `:191` `freeReduce_idempotent`, `:264` `free_group_quotient_no_quot`.

**★ Finite-type (Dynkin) = q=+1 finite-order orbit; infinite-type = q=−1 escape
— `FiniteOrderSpectrum` (29/0) + `GoldenAperiodic` (3/0):**
- `lean/E213/Lib/Math/NumberSystems/Real213/ModularGeometry/FiniteOrderSpectrum.lean:503`
  `finite_order_divides_twelve`, `:527` `no_order_five`, `:603` `crystallographic_spectrum`
  (disc<0 ⟹ finite/periodic orbit = finite-type/Dynkin pole).
- `lean/E213/Lib/Math/NumberSystems/Real213/Phi/GoldenAperiodic.lean:57` `golden_aperiodic`
  (`pow G (n+1) ≠ I` ∀n — disc>0 ⟹ infinite order = infinite-type/q=−1 escape).

**Stern–Brocot mediant = the seed-mutation graph — `Mediant` (11/0) + `MinkowskiModularSymbol`
(5/0):**
- `lean/E213/Lib/Math/NumberTheory/Mediant.lean` (the mediant subdivision; `Mediant` scans 11/0).
- `lean/E213/Lib/Math/NumberSystems/Real213/Minkowski/MinkowskiModularSymbol.lean:52`
  `manin_unimodular_decomposition` (a det-±1 symbol splits at the mediant into two det-±1
  children — the binary exchange on the tree), `:59` `root_symbol_unimodular`.

**The residue (reached by none) — `FlatOntologyClosure` (cited via neighbors):**
- `lean/E213/Lens/Foundations/FlatOntologyClosure.lean:61` `object1_not_surjective` (the
  infinite-orbit reached-by-none surplus, the q=−1 escape).

**Scan tallies (`python3 tools/scan_axioms.py <module>`, from repo root, this session):**
`SternBrocotMarkov` **130/0** · `MarkovCassiniUnimodular` **6/0** · `CassiniUnimodular` **13/0** ·
`ResidueTag` **55/0** · `Mat2Bracket` **10/0** · `FoldKlein` **9/0** · `FiniteOrderSpectrum`
**29/0** · `FreeReduction` **26/0** · `MinkowskiModularSymbol` **5/0** · `Mediant` **11/0** ·
`SignedCup` **14/0**. All PURE, 0 DIRTY.

## Dropped / flagged (honest)

- **Named `ClusterAlgebra` / `mutation` / `mutate` / `exchangeMatrix` / `exchangeRelation` /
  `Laurent` / `laurentPhenomenon` / `Dynkin` / `seedMutation` objects — ABSENT (grep-confirmed,
  case-insensitive over `lean/E213/`).** Zero theorem/definition hits; the single `mutation`
  string is a code comment (`Analysis/CascadeCalculus/Core.lean:75`, "graph mutation; deferred"),
  and every `cluster` hit is documentation jargon ("sub-cluster"). The general field objects are
  predicted-not-built; the **rank-3 Markov instance is built** (`SternBrocotMarkov` 130/0). Stated
  as the open weld, not asserted.
- **The "Laurent phenomenon" tie is a normal-form ANALOGUE, not a literal Laurent-polynomial
  theorem.** `FreeReduction.proj_val_eq_iff` is the q=+1 "stays-canonical / no-residue-beyond-the-
  normal-form" mechanism; on the Markov carrier the no-blowup is the *integer-positivity*
  `mInterval_pos` (entries never acquire a denominator residue). A genuine `Laurent`-ring object
  with a "every cluster variable is Laurent in any seed" theorem is **not built**. The claim is
  "Laurent = the q=+1 no-residue normal form", grounded by the shared `FreeReduction`/positivity
  mechanism — not a built `LaurentPolynomial` welded to a general mutation.
- **The exchange relation is the rank-3 Markov instance, not a general `x_k·x_k'=M₁+M₂`.**
  `markoff_vieta`/`markov_vieta_int` are the specific Vieta jump `(x,y,z)↦(x,z,3xz−y)` (the
  Markov/rank-3 case); a general exchange relation parametrized by an arbitrary skew-symmetric
  `B` and an arbitrary cluster is absent. The single concrete cluster algebra (Markov) is built;
  the general construction is the open weld.
- **Finite-type ⟺ Dynkin as a named classification — predicted-not-built.** The finite-order /
  aperiodic *dichotomy* is built (`finite_order_divides_twelve` vs `golden_aperiodic`,
  `cassini_law_one_at_two_multipliers`), and `crystallographic_spectrum` is the disc<0 finite
  spectrum; but a `ClusterFiniteType ⟺ Dynkin` theorem (the Fomin–Zelevinsky A/D/E classification)
  is absent. Grounded only at the q=±1 orbit-dichotomy altitude, as `continued_fractions.md`'s
  Lagrange leg is.
- **Buildable witness (verified PURE, in-repo): `SternBrocotMarkov.markov_vieta_int` (`:265`)** —
  `x²+y²+z²=3xyz → x²+z²+(3xz−y)²=3xz(3xz−y)`, the **exchange relation as a Lean theorem**: the
  cluster mutation `y ↦ 3xz−y` preserves the defining relation. This IS the rank-3 cluster
  algebra's mutation invariance, machine-checked PURE (in the `SternBrocotMarkov` 130/0 scan).
  No false witness is asserted; the named general cluster/mutation/Laurent/Dynkin objects are
  honestly marked absent.
