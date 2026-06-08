# `Theory/Raw/` — Raw axiom + public surface

The 213 Raw axiom: type + 4-clause definitional commitments
(`a`, `b`, `slash`, `slash_comm`) + structural observables (depth,
leaves, fold, swap).  Public surface exposed via `API.lean`.

## Files (20)

### Public surface
  - `API.lean`        — the canonical re-export shim (downstream
                        code should `import E213.Theory.Raw.API`)

### Core type + axiom
  - `Core.lean`       — `Raw` type + atomic constructors + slash
                        + slash_comm

### Structural observables (per axiom-clause / operation)
  - `Slash.lean`      — slash operation properties
  - `Fold.lean`       — `Raw.fold` catamorphism
  - `FoldSwap.lean`   — fold ∘ swap compatibility
  - `Rec.lean`        — recursor + fold equivalence
  - `Swap.lean`       — `Raw.swap` automorphism
  - `SwapSlash.lean`  — swap ∘ slash compatibility
  - `Levels.lean`     — level / depth machinery
  - `Endomorphic.lean` — endomorphic catamorphism + slashOrSelf
                         (numbering-system isomorphism machinery)

### Residue extension — the µF/νF mirror + the unit's arithmetic
  - `PrimitiveTower.lean` — the self-pointing tower `rawTower` (the ascent)
  - `Lambek.lean`     — µF = Raw: the peel relation `IsPart`, well-founded,
                        terminal at atoms (`isPart_wf`, `terminal_iff_atom`)
  - `MuNuMirror.lean` — the µF/νF mirror: descent terminates, ascent escapes
                        (`ascent_unbounded`, `ascent_adds_unit`, `tower_no_cycle`)
  - `CoResidue.lean`  — νF = `SlashNu`: the exact slash final coalgebra,
                        the populated escape (spine family, bit-streams,
                        `coSwap`, shift dynamics); §20 the label-generic spine
                        `gspine : (Nat→L) → GCoShape L` — one νF carrier for
                        every alphabet (`boolSpine` = `L=Bool`; p-ary = `L=Fin p`;
                        rides ℤ_p `Padic/NuEscape`, ℝ `Real213/NuEscape`); §21 the
                        carrier is *dynamical* — `gspine_shift_dynamics` (Bernoulli
                        shift / period = self-similarity over any alphabet); narr.
                        `theory/essays/foundations/the_residue_as_primitive.md`
  - `StateMachine.lean` — the FSM/RTL reading (state = transition; reachable
                        vs trace; `the_residue_as_state_machine.md`)
  - `Odometer.lean`   — the residue unit's `+1` adding machine on the
                        bit-stream escapes: carry/escape, injective + invertible
                        (`ℤ`-action), reversibility asymmetry, `ℤ₂`-homeomorphism;
                        §7 the alphabet-independent carry (`runCarry`), §8 the
                        **p-ary odometer** (`pOdo`, ℤ_p's `+1`: `(-1)+1=0`,
                        injective — the arithmetic one-carrier, `Padic/NuEscape`)
  - `OdometerValue.lean` — the profinite value (`bval`): `odo = +1 mod 2ᵏ`
                        (`bval_odo`) + `ℤ`-action freeness (`odo_free`); narr.
                        `theory/essays/foundations/the_residue_unit_odometer.md`

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
(Slash, Swap, Fold, Rec, Levels, Endomorphic, CoResidue, …) is
blocked.  Sole canonical entry: `Theory.Raw.API`.

## Where to add new Raw-axiom theorems

  - About slash         → `Slash.lean`
  - About fold          → `Fold.lean` or `Rec.lean`
  - About swap          → `Swap.lean` / `SwapSlash.lean` / `FoldSwap.lean`
  - About level/depth   → `Levels.lean`
  - Endomorphic / numbering-system shape → `Endomorphic.lean`
  - µF/νF / residue-escape / the unit's arithmetic → `Lambek.lean`,
    `MuNuMirror.lean`, `CoResidue.lean`, `Odometer.lean`, `OdometerValue.lean`
  - Then re-export via `API.lean` if it's part of the public
    surface.
