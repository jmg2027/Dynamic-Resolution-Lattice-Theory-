# D2 — 3-tier hierarchy of Lens-algorithm complexity classes

## Statement (interpretive synthesis, 2026-04-26)

The *numbers* of the 213 framework are not "points in one basket"
like ZFC's ℝ, but are classified as **Lens-algorithm complexity
classes**.  Three tiers:

### Tier 1 — FSM (Finite State Machine)

**Objects**: rationals ℚ, algebraic irrationals (√2, √3, √5, etc.).

**Characteristics**: closed within a finite algebraic invariant
(modular periodicity, Pell equation).  The Lens determines all future
cuts with *one observation*.

**Framework modules** (all ≤ propext, most zero axioms):

| Module | Result |
|--------|--------|
| `Sqrt2IrrationalPure` | √2 irrational, 2-adic descent, zero axioms |
| `Sqrt3IrrationalPure` + `PureNatMod3` | √3, 3-adic, zero axioms |
| `Sqrt5IrrationalPure` + `PureNatMod5` | √5, 5-adic, zero axioms |
| `PellHasModulus` + `PellSeq` | Pell sequence, mod-N closure |
| `LeavesModNat` + `ModLensCRT` | modular Lens family, CRT |
| `PrimeDescentObservations` | sqrt4 rational (boundary) |

Closure pattern: the finite state (= residue) of `m mod p` determines
the *entire* future of the sequence.  Cut decision = single modular
evaluation.

### Tier 2 — ICT (Infinite Combinatorial Trajectory)

**Objects**: transcendentals (e, π/2, and other algorithmic
transcendentals).

**Characteristics**: no finite modular state.  Trajectory complexity
grows *unboundedly* as factorial / cumulative product.  Each individual
cut is decidable in finite steps (HasModulus), but *N for the cut*
grows to infinity with the target precision.

**Framework modules**:

| Module | Result |
|--------|--------|
| `EulerCombinatorialPure` | e ∈ (2, 3), zero axioms |
| `EulerSharperPure` | e > 8/3, e ≠ a/3 (partial), ≤ propext |
| `EulerGenericPure` | meta-algorithm: e ≠ a/b for arbitrary b |
| `WallisSharper` | π/2 > 64/45, similar pattern |
| `HasModulus` typeclass | constructive Cauchy modulus |

Closure pattern: the induction of `euler_lower_step` has N growing
together with b — the *trajectory* must be *fully unfolded*.  No
finite state machine.

### Tier 3 — Power-set dependent (outside the framework)

**Objects**: *non-computable* reals of ZFC ℝ (Specker sequences,
random reals, Dedekind cuts of non-r.e. predicates).

**Characteristics**: no finite-step decidability for cuts themselves.
Cut decision requires *power-set reification* (arbitrary subset of
𝒫(ℚ)).

**Framework boundary**:

- `notes/C1_kernel_cardinality_obstruction.md`: strong countable
  evidence for Lens-kernel cardinality, Cantor diagonal does not
  preserve slash-closure.
- `notes/D1_zfc_real_as_final_boss.md`: no *constructive substitute*
  for power-set dependence — the true final boss of the framework.

CLAUDE.md falsifiability: if this tier is captured within the
framework, framework is strengthened; if permanently uncaptured,
framework boundary is confirmed.  Adding axioms triggers framework
discard.

## Meaning of separation between tiers

The distinction of the three tiers restores the true structure that
ZFC *collapses* into "a single point of ℝ":

- ZFC: √2, e, and random real are all "elements of ℝ".
- 213: all three are *different complexity classes* — fundamentally
  different at the algorithmic substrate level.

This is the framework-internally formalizable part of the user's
insight ("the complexity classes themselves are different").

## 213-unique contribution (honest assessment)

### New parts

1. **Substrate is Lens** (not a Turing machine).  Both FSM and ICT
   are captured by the *same* abstraction (Lens) on the same Raw +
   slash axiom — substrate-uniform.
2. **0-axiom Lean verification**: Sqrt{2,3,5}IrrationalPure (FSM
   tier) + EulerGenericPure (ICT tier) all verified framework-internally.
   Actual implementability of the substrate confirmed.
3. **Explicit falsifiability boundary for power-set**: not merely
   "non-computable" but the framework discard condition of *no axiom
   addition* (CLAUDE.md §1.5).

### Parts echoing prior work (honest prior-art)

- **Computable analysis** (Weihrauch, Type-2 Effectivity): similar
  3-tier — computable / r.e. but non-computable / non-r.e.
- **Bishop constructive analysis**: explicit requirement of Cauchy
  modulus (prior to HasModulus).
- **Specker sequences** (1949): explicit example of non-computable reals.
- **Algebraic vs transcendental** (classical number theory): part of
  Tier 1 vs Tier 2 — but without the additional "computable vs not"
  separation within transcendental.
- **Chomsky hierarchy** (regular / context-free / recursive): similar
  ascending complexity class pattern.

### Honest conclusion

The *abstraction* of the 3-tier classification itself is not a new
discovery — it is a well-known structural distinction in computable
analysis literature.  213's contribution:

> *"0-axiom Lean verification on a Lens substrate + explicit
> falsifiability boundary for power-set."*

This is a 213-flavored formalization of an *existing* distinction.
Rather than a "discovery", it is "*reconstruction of an existing
distinction on a more fundamental substrate*".

## Lean-formal separation of tiers (attempt)

### Candidate formal definition of Tier 1 (FSM)

```
class HasFiniteStateMachine (xs : Nat → Raw) where
  state : Type
  finite : Fintype state
  transition : state → state
  init : state
  cut_decision : state → ℚ → Bool  -- or appropriate framework-internal target
  determines : ∀ n m k, ...  -- one-step decision property
```

Problem: what is the "framework-internal target" — Lens kernel or
ABLens orderProj.  The formal statement of Tier 1's *closure* itself
is nontrivial.

### Candidate formal definition of Tier 2 (ICT)

```
HasModulus xs ∧ ¬ HasFiniteStateMachine xs
```

= "Cauchy but no finite state".  The formal statement of the negative
part is harder (absence of all possible state machines).

### Formal definition of Tier 3

= no capture by any module within the framework.  Negative
existential — requires reference outside the framework (currently
not directly formalizable in Lean).

## Next steps

- (a) Attempt `ComplexityClass.lean` Lean module — partial formal
  definition of Tier 1 (state machine + transition + cut decision).
- (b) Formalize an *explicit example* of the negative half of Tier 2
  (¬ FSM) — a statement that all specific descent attempts for e fail.
- (c) Write `HasFiniteStateMachine` instances: Pell sequence + each
  prime descent.  Sqrt2/3/5 instances follow automatically.

## Cross-references

- `notes/B1_pure_descent_method.md`: 5-step descent template (Tier 1).
- `notes/B2_hermite_direction.md`: Hermite formalization (Tier 2).
- `notes/C1_kernel_cardinality_obstruction.md`: power-set obstruction.
- `notes/D1_zfc_real_as_final_boss.md`: framework boundary of Tier 3.
- `framework/E213/Research/Sqrt{2,3,5}IrrationalPure.lean`: Tier 1
  modules.
- `framework/E213/Research/EulerGenericPure.lean`: Tier 2 modules.
