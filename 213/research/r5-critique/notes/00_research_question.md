# 00 — The research question

## The setup (Paper 1, §3–§4)

Paper 1 proves: R1–R5 uniquely determine the self-recognising
Lens codomain as `ℂ` (up to ℝ-algebra isomorphism).

The derivation in §4.1 **begins with** the assumption "α is an
ℝ-algebra" and then classifies finite-dim cases. The paper
attributes the ℝ-algebra assumption to R5:

> "R5 requires the codomain to receive every non-terminating
> structural branch of R with a uniquely determined state.
> … The minimal such codomain is `ℝ`."

## The suspicion

R5 phrased this way imports classical set-theoretic machinery:
- "every non-terminating branch" — universal quantifier over an
  actually-completed infinite totality;
- "Cauchy-complete" — completion of a metric space, again
  presupposing a classical ambient.

Neither is supplied by 213's axiom. Both are standard ZFC
scaffolding dressed up as structural requirements.

**Claim.** If we drop R5 and keep only R1–R4, then every
quadratic Galois extension whose Galois group is `ℤ/2`
satisfies R1–R4 (with the appropriate `combine`/base-value
choice). In particular, `ℤ[i]` and `ℚ[i]`, both countable,
qualify. Hence ℂ is not uniquely determined by R1–R4.

## Minimal statement to test

**Proposition (E1).** There exists a Lens `L` with codomain
`ℤ[i]` (Gaussian integers) such that:

1. `L.combine` is binary (R1);
2. `view` is a catamorphism of the free commutative magma on
   two generators (R2);
3. `L.combine` has no zero divisors: for `u, v : ZI`, if
   `L.combine u v = 0` then `u = 0` or `v = 0` (R3);
4. There exists a unique nontrivial involution
   `conj : ZI → ZI` satisfying
   `L.view (Raw.swap r) = conj (L.view r)` for every `r : Raw`
   (R4).

We propose `L = (ZI, i, -i, ZI.mul)` with `conj = ZI.conj`.

If the proposition is Lean-provable, R1–R4 do not force ℂ.

## Why this matters

- **Mathematically:** pinpoints where classical infinity enters
  the paper's chain. Isolates R5 as the smuggling channel.
- **Philosophically:** supports the 213 programme's claim that
  mainstream foundations rely on infinitary assumptions that
  are unavailable inside 213 itself.
- **For Paper 2:** gives a concrete, formally verified
  counterexample to any "R1–R4 force ℂ" claim.

## What would refute the suspicion

- The `ziLens` construction fails at R3 or R4 in Lean.
- A hidden consequence of R1–R4 (not visible in the paper's
  prose but provable in Lean) closes the ℂ → ℤ[i] gap.
- A 213-internal condition (not R5) singles out ℂ among
  quadratic extensions.

Each of these would strengthen Paper 1 and dissolve Paper 2.

## Next

Lean construction in `framework/E213/Research/ZI.lean` and
`ZILens.lean`. Writeup in `01_zi_counterexample.md`.
