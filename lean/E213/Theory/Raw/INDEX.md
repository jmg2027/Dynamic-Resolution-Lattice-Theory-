# `Theory/Raw/` — Raw axiom + public surface

The 213 Raw axiom: type + 4-clause definitional commitments
(`a`, `b`, `slash`, `slash_comm`) + structural observables (depth,
leaves, fold, swap).  Public surface exposed via `API.lean`.

## Files (13)

### Public surface
  - `API.lean`        — the canonical re-export shim (downstream
                        code should `import E213.Theory.Raw.API`)

### Core type + axiom
  - `Core.lean`       — `Raw` type + atomic constructors + slash
                        + slash_comm

### Structural observables (per axiom-clause / operation)
  - `Slash.lean`      — slash operation properties
  - `Fold.lean`       — `Raw.fold` catamorphism
  - `Rec.lean`        — recursor + fold equivalence
  - `Swap.lean`       — `Raw.swap` automorphism
  - `SwapSlash.lean`  — swap ∘ slash compatibility
  - `Levels.lean`     — level / depth machinery
  - `Hom.lean`        — Raw-algebra homomorphisms
  - `Signed.lean`     — signed Raw / negation
  - `Endomorphic.lean` — endomorphic catamorphism + slashOrSelf
                         (numbering-system isomorphism machinery)

### Internal substrates (not in API.lean — generic constructs / demos)
  - `Congruence.lean`              — generic equivalence closure
                                     `Eqv (gens : Raw → Raw → Prop)` (Option E
                                     of the lens-emergence roadmap; substrate
                                     for `Lens.Congruence`)
  - `ParenthesizationDistinct.lean` — kernel-decided counter-example
                                     showing two parenthesisations of the
                                     same leaves produce structurally
                                     distinct Raws (no `slash_assoc`)

### Demo
  - `Demo.lean`       — illustrative examples (Raw axiom semantics)

## Public API discipline

Hook-enforced (`.claude/hooks/layer-import-guard.sh` Rule 2):
**outside the `Theory/Raw/` cluster, code must import via
`Theory.Raw.API`.**  Direct reach-in to specific submodules
(Slash, Swap, Fold, Rec, Levels, Hom, Signed, Endomorphic) is
blocked.  Sole canonical entry: `Theory.Raw.API`.

## Where to add new Raw-axiom theorems

  - About slash         → `Slash.lean`
  - About fold          → `Fold.lean` or `Rec.lean`
  - About swap          → `Swap.lean` or `SwapSlash.lean`
  - About level/depth   → `Levels.lean`
  - Homomorphism shape  → `Hom.lean`
  - Signed extension    → `Signed.lean`
  - Then re-export via `API.lean` if it's part of the public
    surface.
