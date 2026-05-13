# G12 — Layered API Classification (Kernel / Firmware / Hypervisor)

**Date:** 2026-05-XX (continuing G6–G11)
**Author:** Mingu Jeong (architectural insights), Claude (rigorous classification)
**Status:** Historical research note.  Predates the 2026-05-12 layer
rename (Kernel → Term, Firmware → Theory, Hypervisor → Lens) and
the 2026-05-13 App/ dissolution.  The structural conclusions
remain valid; only the layer-name terminology is stale.  Cited from
`Lens/API.lean` for the layered-API split (HV1–HV6 → Tier 1/Tier 2).
For current canonical layer spec, see `lean/E213/ARCHITECTURE.md`.
Stale theorem names mentioned here (`pair_iff_two`,
`closure_iff_three`, `arity_iff_two`, `Sound.of_lt_b`,
`Sound.of_equivQ`, `Sound.of_leQ`) are placeholders that were
not adopted; current canonical names are in `Theory/API.lean` and
`Term/API.lean` respectively.

---

## 0. Why this document exists

This session series produced two findings that demand an explicit
architecture clarification:

1. **`tools/layer_audit.py` is incomplete.**  It computes only the
   *mechanical floor* (`layer(F) ≥ max(layer(I))`) of each file,
   missing the provider/consumer distinction.  A file at the same
   floor as its imports may be a *provider* of that layer (= belongs
   there) OR a *consumer* of that layer (= belongs one above).

2. **HC²¹³ + post-HC cluster (29 files) all show as "Firmware-floor"**
   under the current audit, but conceptually splits into Hypervisor-
   provider, OS-orchestrator, and App-consumer roles.  See G10/G11.

These are not tooling bugs — they reveal that **layers in 213 have
two complementary characterisations**: (a) mechanical depth (current
audit), (b) API surface vs internal (this document).

The classification below is the (b) view, applied rigorously to
Kernel/, Firmware/, and Hypervisor/ via reading every file in those
trees.

---

## 1. The provider/consumer rule (refinement of ARCHITECTURE §6)

ARCHITECTURE.md §6 currently states:
  > `layer(F) ≥ max(layer(I))` over all `E213.*` imports `I` of `F`

This is a *floor*, not a *placement*.  The corrected rule:

  > A file at layer N is either:
  >   (i) a **provider**: introduces new abstraction at level N.
  >       Imports are ≤ N.  Examples: `Hypervisor/Lens.lean`
  >       provides the Lens abstraction at level 2.
  >   (ii) a **consumer**: uses level-N abstraction without adding
  >        a new one.  Belongs at level N+1.  Example: HC²¹³ files
  >        consume Math/Cohomology infrastructure (HV-flavored)
  >        without providing new HV abstractions → App or OS.

The provider/consumer distinction is not mechanically detectable from
imports alone.  It requires inspecting *what the file's main content
provides*: a new `def Lens` (provider) vs. `theorem foo := Lens.X`
(consumer).

---

## 2. Kernel API surface

`Kernel/` (15 files at root + `Kernel/Tactic/` subdir).  Role per
ARCHITECTURE §1.1: *"Lean-side scaffolding to run 213 inside Lean 4.
Provides deep-embedded Term type + total functions so that 213 facts
can be checked by Lean's kernel reduction without using ANY of Lean's
axioms."*

Empirical inventory (all read):

| File | Public API content |
|---|---|
| `Term.lean` | `Term` AST + `eval, equiv` + atomic constants `nS, nT, d, c` |
| `Compare.lean` | `le_b, lt_b` Bool comparators |
| `Pair.lean` | `pair, offDiag` Lens-distinguishability primitive |
| `Rat.lean` | `equivQ, leQ` rational cross-multiplication |
| `Decide.lean` | `allBelow, existsBelow` bounded quantifiers |
| `Sound.lean` | `of_equiv, of_le_b, of_equivQ, of_leQ` Bool→Prop bridges |
| `MonomialAxioms.lean` | `ns_mul_nt_eq_six` etc. — concrete equalities |
| `Cap_*.lean` (×7) | sealed capability ledgers |
| `Demo.lean` | example/demo only |
| `Tactic/Omega213` etc. | 213-native tactics |

### 2.1 Public Kernel API (4 sub-categories)

**K1 — Data API**: 213 syntactic objects
```
Term, Term.eval
Term.{nS, nT, d, c}
```

**K2 — Computation API**: Bool-returning total functions (axiom-free)
```
Term.{equiv, le_b, lt_b}            -- comparisons
Term.{pair, offDiag}                -- Lens primitive
Term.{equivQ, leQ}                  -- rational cross-mul
Decide.{allBelow, existsBelow}      -- bounded quantifiers
```

**K3 — Soundness API**: Bool→Prop bridges (load-bearing for upstream)
```
Sound.of_equiv      : equiv a b = true → eval a = eval b
Sound.of_le_b       : le_b a b  = true → eval a ≤ eval b
Sound.of_lt_b       : lt_b a b  = true → eval a < eval b
Sound.of_equivQ     : equivQ p q r s = true → ...
Sound.of_leQ        : leQ p q r s    = true → ...
```

**K4 — Tactic API**: 213-native proof automation (cross-cutting)
```
omega213                         -- macro replacing core omega
Nat213.{add_*, sub_*, mul_*, le_*, cases_lt_*}
Mod213.{parity, parity_add, parity_pow_*, mod3, mod6}
Pow213.{pow_*, dvd_*}
Fin213.{absurd0, ...}
```

### 2.2 Sealed (NOT Kernel API)

  - **`Cap_*`** (7 files) — capability ledgers.  *End-of-pipeline*
    concrete bracket theorems ("π/α_em sits in [a, b]") that happen
    to be ∅-axiom because they reduce to ℕ arithmetic.  Mechanically
    Kernel-floor, semantically App.  *Should not be imported by
    upstream code* — they are summary artifacts, not API.
  - **`Demo.lean`** — examples only.
  - **`MonomialAxioms.lean`** — concrete monomial equalities.
    Borderline; could be K1 (atomic-constant facts).

### 2.3 Recommendations for Kernel

  R-K1. **Add `Kernel/API.lean`** — re-export shim for K1+K2+K3,
        analogous to `Firmware/Raw.lean`.  Single import.
  R-K2. **Move `Cap_*` to `Kernel/Capabilities/`** sub-folder to
        signal sealed-not-API status.  Optionally move to App/.
  R-K3. **Document Tactic/ as horizontal cross-cutting layer**
        (K4) — `omega213` is consumed at every layer above Kernel.
        Update ARCHITECTURE §1.1 to mark it explicitly.

---

## 3. Firmware API surface

`Firmware/` (3 root + `Raw/` 13 files + `Atomicity/` 8 files +
`Tools/`).  Role per ARCHITECTURE §1.2: *"the 213 axiom — Raw type +
4-clause definitional commitments + the proofs that this shape is
forced uniquely."*

### 3.1 Public Firmware API (2 sub-APIs)

**FW-A — Raw API** (already explicit in `Firmware/Raw.lean` shim):
```
Raw                     -- opaque type (axiom #1: things exist)
Raw.{a, b}              -- two base elements (axiom #2)
Raw.slash               -- distinction op (axiom #3): (x y : Raw) → x ≠ y → Raw
Raw.slash_comm          -- symmetry (axiom #4): x/y = y/x
Raw.{depth, leaves}     -- canonical observables
Raw.fold                -- catamorphism (with fold_a, fold_b, fold_slash)
Raw.{swap, swap_swap}   -- automorphism (with swap_a, swap_b)
Raw.{swap_depth, swap_leaves}
Raw.{fold_eq_depth, fold_eq_leaves}
Raw.{fold_signed_swap, fold_swap_hom}
Raw.rec                 -- custom eliminator
RawLevels, RawSwap      -- level-bounded variants
```

**FW-B — Atomicity API** (forced shape uniqueness):
```
Atomicity.Five.{atomic_iff_five, canonical_partition, IsAlive}
Atomicity.PairForcing.pair_iff_two
Atomicity.NonDecomposable.closure_iff_three
Atomicity.{ArityForcing, ArityForcingGeneral}.arity_iff_two
Atomicity.PrimitiveSizes.{pairSize, closureSize}
Atomicity.Alive.{alive_iff_*}
Atomicity.FiveHelpers.{add_two_ne_self, bezout_left, bezout_right}
```

### 3.2 Sealed (NOT Firmware API)

  - **`E213.Firmware.Internal.Tree`** (in `Firmware/Raw/Core.lean`) —
    the scaffolding tree implementation behind opaque `Raw`.
    Already explicitly forbidden to consumers (see Raw.lean
    docstring: *"Forbidden to consumers"*).
  - **`Firmware/Raw/{Cmp, CmpIndependence, ComplexityClass,
    DecEq, SwapSlashInjective, ...}`** — internal proofs supporting
    the public Raw API.  Re-exported through `Firmware/Raw.lean`.
  - **`Firmware/Tools/CertChecker.lean`** — verification utility,
    not part of the axiom commitment.

### 3.3 Recommendations for Firmware

  R-FW1. **Add `Firmware/Atomicity.lean`** — re-export shim for
         FW-B, analogous to `Firmware/Raw.lean` for FW-A.  Currently
         consumers must import individual files from `Atomicity/`.
  R-FW2. **Mark `Firmware/Tools/CertChecker.lean`** explicitly as
         non-API utility (or move to `Kernel/Tools/`).
  R-FW3. **Document the dual-character of FW-API in ARCHITECTURE §1.2**
         — Raw provides the axiom *data*, Atomicity provides the
         axiom's *spec compliance*.  Both are required for any
         Hypervisor consumer.

---

## 4. Hypervisor API surface

`Hypervisor/` (1 root file `Lens.lean` + `Lens/` subdir with 77
files in 10 sub-clusters).  Role per ARCHITECTURE §1.3: *"Lens
framework — the catamorphism mechanism that turns Raw into any
α-codomain via Lens.view = Raw.fold.  Provides the universal
viewing mechanism.  Different α = different VM of 213."*

Empirical inventory (all read):

| Sub-cluster | Files | Content |
|---|---|---|
| `Lens.lean` (root) | 1 | `Lens` type, `view`, `equiv`, `refines`, `leaves`, `depth` |
| `Lens/Initiality.lean` | 1 | `Lens.view_unique` — universal property |
| `Lens/SemanticAtom.lean` | 1 | "213 = atom of meaning" formal hub |
| `Lens/Lattice/` | 7 | join, meet, family, indexed |
| `Lens/Compose/` | 7 | factoring, image minimum, on-lens |
| `Lens/Properties/` | 10 | refines props, IsLeaf, CanonicalForm, EquivProperties |
| `Lens/Morphism/` | 7 | BoolProp, FoldStructured, Dist |
| `Lens/Leaves/` | 5 | Mod3, ModNat, depth-incomparability |
| `Lens/Refines/` | 2 | Chain, Preorder |
| `Lens/Kernel/` | 8 | Congruence, Corresp, FreeAudit, FourDistinct |
| `Lens/Universal/` | 2 | Flat, QuotLens (universal Lens construction) |
| `Lens/Instances/` | 25 | concrete catalog (Bool, Path, Max, Parity, ZMod6, Cauchy, ...) |
| `Lens/Characterisation/` | 2 | Catalog, Core |

### 4.1 Public Hypervisor API (8 sub-categories)

**HV1 — Type API**: the Lens type + catamorphism
```
Lens (α : Type)            -- structure {base_a, base_b, combine}
Lens.view : Lens α → Raw → α
Lens.{leaves, depth}       -- canonical Lenses (built into root)
```

**HV2 — Equivalence API**: Lens-induced equality + refinement
```
Lens.equiv     : Lens α → Raw → Raw → Prop
Lens.equiv_{refl, symm, trans}
Lens.refines   : Lens α → Lens β → Prop      -- preorder
Lens.refines_{refl, trans}
Refines.Chain, Refines.Preorder              -- structural facts
```

**HV3 — Initiality API**: universal property of Raw → α
```
Lens.view_unique           -- ∀ f homomorphism, f = Lens.view  (Initiality.lean)
SemanticAtom.{HasDistinguishing typeclass, Raw.instHasDistinguishing}
Universal.Flat.every_lens_factors_through_idLens
```

**HV4 — Lattice API**: refines preorder lattice structure
```
joinLens, prodLens                        -- join + meet
joinLens_{kernel, is_least}               -- universal property
Lattice.{FamilyJoin, FamilyMeet, IndexedJoin, JoinEquiv}
```

**HV5 — Composition API**: Lens factoring + image
```
Compose.Factoring.factors_through_implies_refines
Compose.{ImageMinimum, OnLens, OnLensImage, Morphism}
```

**HV6 — Canonical Form API**: universalLens construction
```
Universal.QuotLens.universalLens        -- canonical Lens via kernel
Properties.CanonicalForm.universalLens_recovers
Kernel.{Congruence, Corresp}            -- kernel-equivalence theorems
```

**HV7 — Concrete Lens catalog** (Instances/, 25 files):
```
Instances.{AB, Bool, CompoundBool, F9, Identity, Inv, ListMax,
            Max, MaxByLeaves, MinByLeaves, Mod, ModN, Or, Parity,
            Path, Sym, And, Xor, ZMod6, Cauchy, ...}
```
Each provides a concrete `Lens α` instance for a specific α.

**HV8 — Characterisation API**: refines-relationship catalog
```
Characterisation.Catalog        -- which catalog Lenses refine which
Characterisation.Core           -- abstract characterisation patterns
Properties.{ABRefines, EquivProperties, InjectiveClass}
```

### 4.2 Sealed (NOT Hypervisor API)

  - **`Lens/Kernel/{FreeAudit, CardinalityLB, FourDistinct,
    SwapInvariant, SyntaxKernel}.lean`** — internal proofs about
    Lens-kernel structure.  Supporting infra for HV3/HV6, not
    consumed directly by App/OS.
  - **`Lens/Morphism/{BoolSqClassification, DepthParityNotFold,
    NoDepthParity, Dist}.lean`** — technical morphism-theory
    investigations.  Mostly internal.
  - **`Lens/Leaves/{DepthIncomparable, DepthJoin, RefinesParity}`** —
    technical leaves-flavored facts.  Borderline; some used by HV4.

### 4.3 Recommendations for Hypervisor

  R-HV1. **Add `Hypervisor/API.lean`** — re-export shim grouping
         HV1 + HV2 + HV3 + HV4 + HV5 + HV6.  HV7 (Instances) and
         HV8 (Characterisation) as separate optional imports.
  R-HV2. **`Hypervisor/Lens.lean` already has API-shim docstring**
         marker (*"This module uses only the Firmware's public
         API"*) — extend this convention by writing similar
         "Provides: ..." docstring at sub-cluster INDEX.md files.
  R-HV3. **Document the dual role of Initiality**: it is both
         (a) a metatheorem about Lens (so Meta-flavored), and
         (b) the API guarantee consumers rely on (so HV-API
         essential).  Currently lives in `Hypervisor/Lens/`
         which is correct for the API role.
  R-HV4. **Sub-cluster Instances/ further** — 25 concrete Lenses
         in flat dir.  Could split by codomain (Bool-valued,
         Nat-valued, finite-valued, structure-valued).  Per
         CLAUDE.md guideline 5.

---

## 5. OS layer proposal (currently empty in 213)

ARCHITECTURE §3.Q5 + §7 history records: the previous `OS/` was a
*misnomer for what's now `Firmware/Atomicity/`* (forced-uniqueness
proofs).  After dissolution, the OS slot in 213's vertical layering
is **literally empty**.

This is **not** the right resting state.  Mingu's observation
(this session): OS in SW arch has a distinct role from Hypervisor —
*OS orchestrates multiple HV views into coherent subsystems and
provides stable APIs to apps*.

### 5.1 Conceptual definition of OS in 213

```
Kernel       — bare computation (Lean-internal substrate)
Firmware     — axiom + forced-uniqueness commitment
Hypervisor   — view/abstraction mechanism (Lens type + catamorphism)
Meta         — metatheorems ABOUT Hypervisor
OS  ★        — orchestration: stable API, subsystem composition,
               cross-domain interface adapters
App          — concrete instance (single observable, single theorem)
```

**OS vs Meta**: parallel, not sequential.
  - Meta: *propositions* about HV ("for all Lens, …")
  - OS: *compositions* of HV ("Cup-Lens × Hodge-Lens orchestrated")

**OS vs App**: API surface vs concrete use.
  - OS: stable interface (e.g., `HodgeConjecture/API.lean`,
    `Bridge/Tate.lean` as a public interface to ℓ-adic users)
  - App: specific result (e.g., `Foundation/Complete.lean` master
    theorem citing the API)

### 5.2 Candidate OS-flavored files in 213

After reading the tree, files exhibiting OS character:

  - **`HodgeConjecture/API.lean`** — already exists, OS-character
    (single-import entry point for HC²¹³ subsystem)
  - **`HodgeConjecture/Bridge/*`** (7 files) — cross-discipline
    interface adapters (ℓ-adic, motivic, K-theory, p-adic, ...)
  - **`HodgeConjecture/INDEX.md`** — subsystem documentation
  - **`Physics/Capstones/*`** — multi-observable orchestration
  - Any future `Real213/INDEX.md` + framework entry point
  - Any future `Math/Cohomology/INDEX.md` + Cohomology subsystem
    entry point

### 5.3 Recommended OS placement options

**(α) Semantic OS tag in-place** — keep all paths under Math/Physics,
add a "semantic layer = OS" annotation in INDEX/docstrings.  Lowest
disruption.  Like ARCHITECTURE §6.1's mechanical-vs-semantic dual.

**(β) New `OS/` directory** — physically move OS-flavored files.
Most disruptive.  Math/Physics topical placement broken.

**(γ) Hybrid: `OS/` directory absorbs only Bridge + API + Capstone
files** — Math/Cohomology/Cup (HV-provider) stays in Math/, but
`HodgeConjecture/Bridge/*` moves to `OS/HodgeConjecture/Bridges/`.
Math topical-ness preserved for definitions; OS captures
orchestration.  *Recommended.*

### 5.4 Updates to ARCHITECTURE.md if OS is added

  - **§1.5.5 OS layer** new section with definition + role
  - **§3.Q5** clarify: previous dissolution was correct (Atomicity
    misnomer), but new OS proposal is **different layer** (not
    revival of misnomer)
  - **§4 dependency graph** add OS branch parallel to Meta:
    ```
                Hypervisor
                  ↓     ↓
                Meta    OS
                        ↓
                       App
    ```
  - **§6 layer_audit.py rule** extend: provider/consumer
    distinction needed for accurate placement

---

## 6. Concrete recommendations for the next session

Ordered by ROI / safety:

### 6.1 Documentation-only (zero risk)

  D1. **Add `Kernel/API.lean`** — re-export shim K1+K2+K3 (cf. R-K1).
      Single `import E213.Kernel.API` for downstream.
  D2. **Add `Firmware/Atomicity.lean`** — re-export shim FW-B
      (cf. R-FW1).  Mirror `Firmware/Raw.lean` style.
  D3. **Add `Hypervisor/API.lean`** — re-export shim HV1–HV6
      (cf. R-HV1).  HV7/HV8 as separate optional imports.
  D4. **Update ARCHITECTURE.md** §1.1/§1.2/§1.3 with explicit
      "Public API surface" sub-sections matching this document's
      Sections 2.1, 3.1, 4.1.
  D5. **Add §1.5.5 OS layer** to ARCHITECTURE.md per §5.1 above.

### 6.2 Tooling (low risk)

  T1. **Extend `layer_audit.py`** with provider/consumer heuristic:
      a file is *provider* iff it introduces a `def`/`structure`/
      `class` declaration whose namespace matches the file's
      directory; otherwise *consumer*.  Refine the heuristic by
      iterating with manual review.
  T2. **Add INDEX.md to each `Lens/` sub-cluster** (Lattice/,
      Compose/, Properties/, Morphism/, Leaves/, Refines/,
      Kernel/, Universal/, Instances/, Characterisation/) per
      CLAUDE.md guideline 7.

### 6.3 Sub-clustering (moderate risk, requires builds)

  S1. **`Kernel/Capabilities/`** sub-folder for `Cap_*` (cf. R-K2)
  S2. **`Hypervisor/Lens/Instances/{Bool,Nat,Finite,Structure}/`**
      sub-clusters for the 25 catalog Lenses (cf. R-HV4)
  S3. **`Math/Cohomology/`** depth-band sub-clustering (per
      ARCHITECTURE §6.2 — currently 226 files, depth 44, WIDE)

### 6.4 OS layer realisation (high risk, substantial)

  O1. **Choose option (α)/(β)/(γ)** from §5.3 for OS placement.
      Recommended: (γ) — OS/ absorbs Bridge + API + Capstones only.
  O2. **Implement chosen option**:
      - Create `lean/E213/OS/` directory
      - Move `HodgeConjecture/Bridge/*` to `OS/HodgeConjecture/
        Bridges/` (or similar)
      - Move `Physics/Capstones/*` to `OS/Physics/Capstones/`
      - Update namespaces + imports via bulk sed
      - Verify build + ∅-axiom scan
  O3. **Update ARCHITECTURE.md** §4 dependency graph + §1 layer
      table.

---

## 7. Cross-references

### Files cited

  - `lean/E213/ARCHITECTURE.md` — canonical layer definitions
  - `lean/E213/Term/{Term, Compare, Pair, Rat, Decide, Sound,
    MonomialAxioms, Cap_*, Demo}.lean`
  - `lean/E213/Term/Tactic/{Omega213, Nat213, Mod213, Pow213,
    Fin213}.lean`
  - `lean/E213/Theory/{Raw, RawLevels, RawSwap}.lean`
  - `lean/E213/Theory/Raw/*.lean` (13 files)
  - `lean/E213/Theory/Atomicity/*.lean` (8 files)
  - `lean/E213/Theory/Tools/CertChecker.lean`
  - `lean/E213/Lens.lean`
  - `lean/E213/Lens/*.lean` (77 files in 10 sub-clusters)
  - `tools/layer_audit.py` — current mechanical-floor audit
  - `tools/sync_namespaces.py` — path↔namespace synchroniser

### Companion notes

  - `hodge/G6_hodge_213_translation.md` — standard ↔ 213 dictionary
  - `hodge/G7_lens_initiality_cup_blueprint.md` — uniform proof sketch
    (relevant to OS-layer Bridges)
  - `hodge/G8_hodge_213_bridge_to_standard_math.md` — bridge concept
  - `hodge/G9_hodge_conjecture_complete.md` — HC²¹³ closure
  - `hodge/G10_post_hodge_program.md` — 17 post-HC theorems programme
  - `hodge/G11_galois_at_eighty.md` — structural-foundations historical

### CLAUDE.md sections relevant

  - `## Repository Organization Philosophy` — 8 numbered guidelines
    informing this classification
  - `## Resolution limit is a structural invariant (not "finitism")`
    — N_U as four-domain convergent invariant (canonical:
    `seed/RESOLUTION_LIMIT_SPEC.md`)
  - `## DRLT Axiom Standard` — strict ∅-axiom requirement

---

## 8. Summary for the next agent session

If you are reading this cold:

  1. **`tools/layer_audit.py` reports a *floor*, not a *placement*.**
     Layers in 213 have a provider/consumer distinction the audit
     does not capture.  See §1.

  2. **API surface for each layer is given in §2.1 (Kernel),
     §3.1 (Firmware), §4.1 (Hypervisor).**  These are based on
     reading every file in those layers (not background knowledge).

  3. **OS layer is empty in 213's vertical hierarchy.**  Mingu
     proposes filling it with orchestration / API-adapter files
     (cf. HC²¹³'s Bridge sub-cluster).  See §5.

  4. **Concrete next-session actions** in §6, ordered by risk:
     D1–D5 (docs, zero risk), T1–T2 (tooling, low risk), S1–S3
     (sub-cluster, moderate risk), O1–O3 (OS realisation,
     substantial).

  5. **All HC²¹³ work** (this session series) is in
     `lean/E213/Lib/Math/Cohomology/HodgeConjecture/` — 6 functional
     sub-layers (Foundation/Toolkit/Structure/Refinement/Pairing/
     Bridge), 138+ strict ∅-axiom theorems, master citation:
     `HodgeConjecture.API.HC213`.

  6. **Decisions are deferred** — this document is *analysis and
     proposals only*.  No file moves, no API.lean shims, no
     ARCHITECTURE updates have been applied yet.  Author of next
     session should pick from §6 menu and execute with
     human-confirmed scope.