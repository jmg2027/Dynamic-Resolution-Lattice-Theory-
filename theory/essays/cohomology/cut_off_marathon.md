# Cardinality cut-off, ten applications, one refactor, one open horizon

A cardinality cut-off principle is small as a theorem: any
DRLT-internal complexity class `H_k ⊆ ℕ` with explicit uniform bound
`M_k` eventually fails to capture an unboundedly-growing external
sequence `f : ℕ → ℕ` (`theory/meta/cardinality_cutoff_principle.md`
§1).  The mathematical content is pigeonhole.  The 213-native content
is **identification**: which `f`, which `H_k`, what coincidence slice
they share before the cut-off, what that slice says about `f` in
terms of Hunter atomic primitives `{NT, NS, d} = {2, 3, 5}`
(`catalogs/atomic-integers.md`).

## §7 — six directions, one body

The principle's §7 listed six instantiation slots.  Each became a
Lean file in `lean/E213/Lib/Math/Cohomology/Fractal/`:

Direction B — `AurifeuilleanLUnbounded.lean` (20 PURE) closes the
verbal premise "`L_m → ∞`" of `cardinality_cutoff_principle.md` §3
via a concrete chain `m ∈ {1, 3, 7}` computed externally by PARI/GP
`bnfisnorm` over `K = Q(√5)` and embedded as decide-checked norm
identities `L_m² − 5·M_m² = Φ_{10m²}(5)`.  Cap = `L_7 ≈ 5.27 × 10⁵⁸`.

Direction D — `HunterAtomicClosure.lean` (44 PURE) asks whether the
catalogue `{2, 3, 5, 7, 13, 521}` is closed under mod-p arithmetic.
The answer is: not closed under any of `+, *, ^`, but a 15-element
FLT sub-closure emerges — at every catalogue prime `p` and `a < p`
catalogue, `a^p ≡ a (mod p)`.

Direction A — `AurifeuilleanDepth2Cutoff.lean` (12 PURE) extends the
depth-1 Hunter universe (16 values, max 3125) to a restricted depth-2
universe (max 9 765 625, outer op ∈ {+, *}); `AurifeuilleanDepth2PowCutoff.lean`
(16 PURE) closes the unrestricted outer-pow case for 521 via
small-range decide + large-range monotonicity dispatch.

Direction C — `PellCutoff.lean` (35), `LucasCutoff.lean` (40),
`FibonacciCutoff.lean` (36), `TribonacciCutoff.lean` (28 PURE)
instantiate the principle for four non-Aurifeuillean external
sequences: Pell, Lucas, Fibonacci, Tribonacci.

Direction E — `HunterComplexity.lean` (32 PURE) defines
`hunterComplexity(v) := min {k : v ∈ H_k}` and proves the four-level
hierarchy for catalogue atoms: 2, 3, 5 at depth 0; 7 at depth 1; 13
at depth 2; 521 at depth 3 (unrestricted via the A-extension).

Direction F — `AltPrimitiveSet.lean` (28 PURE) drops `d = 5` from
the generator set, demonstrating that the principle's structural
content (locate / diagnose / refined-prove) is parametric in the
primitive set; only the cut-off slice moves with the choice.

Ten files, 291 PURE / 0 DIRTY, full `lake build` clean.  Every
theorem verified zero-axiom by `tools/scan_axioms.py`.

## Four cross-frame convergences

The methodology's "locate" step asks: at what slice does the external
`f(m)` meet `H_k`?  Across the four C-direction sequences and the
Aurifeuillean exemplar, the slice question gave four genuine
convergences.

`Pell P_5 = Lucas L_7 = Aurifeuillean L_1 = 29` (`LucasCutoff.Lucas_7_eq_Pell_5`).
Three a-priori-unrelated external sequences meet at the smallest
catalogue depth-2 atom.  29 carries three Hunter readings:
`NT^d − NS = d² + NT² = d² + d − 1` (= 32 − 3 = 25 + 4 = 25 + 5 − 1).
The convergence is the cut-off principle's "locate" step landing
simultaneously across three frames at one catalogue atom.

`Lucas L_13 = Φ_10(5) = 521`.  Lucas hits the Aurifeuillean
cyclotomic handle of `N_U + 1`.  Catalogue intersection count for
Lucas: five (`{2, 3, 5, 7, 13, 29, 521}` ∩ Lucas-image = `{2, 3, 7,
29, 521}` at indices `{0, 2, 4, 7, 13}`) — more than any other
sequence.

`(F_3, F_4, F_5) = (NT, NS, d) = (2, 3, 5)` (`FibonacciCutoff.Fib_3_4_5_are_Hunter_generators`).
Three consecutive Fibonacci values are exactly the three Hunter
generators.  Tightest possible coincidence between an external
sequence and the 213 atomic generator set.

`T_16 = 3136 = M_1 + 11` (`TribonacciCutoff.Trib_16_minus_M1_is_11`).
Tribonacci threads the depth-1 cut-off boundary `M_1 = 3125` by
just 11 — slower growth rate (tribonacci constant ψ ≈ 1.839 vs
golden ratio 1.618 vs Pell-silver 2.414).

These four are not pigeonhole consequences; they are the principle's
"locate" step instantiated across the family.  The principle says
*some* slice exists; the family says *which* slices, with what
arithmetic content.

## Why the atomic catalogue is `{2, 3, 5, 7, 13, 521}`

The catalogue contains exactly the integers with clean derivations from
`{NT, NS, d}` = `{2, 3, 5}`: the seeds `2, 3`; `d = NS + NT = 5`; the depth
closure `7, 13`; and `521 = Φ₁₀(5)` from the aurifeuillean bound.

Two superficially-atomic candidates are **not** members, and the distinction is
structural, not a rounding:
- `1/α_em = 137.035999…` is not the integer `137` — it is a measured physical
  constant, a physics input, not a 213-derived integer.
- `α_GUT⁻¹` is model-dependent (~24–26 in standard SUSY GUT, not `41`).

`ConfigCountModular.lean` §H.1 (mod 41 → 9 = NS²) and §H.5 (mod 137
→ 86 = NS²·NT² + d²·NT) carry their modular-congruence theorems as valid
arithmetic about those moduli, with no "catalogue atom" reading attached.
The closure counts in `HunterAtomicClosure`, `HunterComplexity`,
`AurifeuilleanDepth2PowCutoff`, `AltPrimitiveSet` are over the six-element
catalogue.

The refactor is itself the cut-off principle's "diagnose" step
applied at the meta-level: catalogue membership claims must derive
from generators (2, 3, 5) by arithmetic readings, not from
approximate identification with continuous physics constants.  The
literal-vs-refined distinction at the catalogue layer.

## L_11 — outside the container

The chain extension to `m = 11` (would push cap to ~10¹⁵⁰) was
attempted via five paths: PARI `bnfisnorm` (1-hour timeout, never
exited bnfisnorm step), sympy `factor(Φ_1210, extension=√5)` (2h+
killed, never exited factor step), trial division on primes
≡ 1 (mod 1210) (found 389621 only; 302-digit cofactor's prime
factors all > 10¹⁰), web fetches to known Aurifeuillean tables (all
404/403), and theoretical Stevens-Brent polynomial formula (same
complexity as sympy factor; no shortcut).  `Φ_{1210}(5)` is 308
digits; full factorization requires GNFS or precomputed tables,
neither accessible in this container.

The rust-engine binary `aurifeuillean-lm`
(`rust-engine/crates/app/src/bin/aurifeuillean_lm.rs`) catalogues
all five paths in its docstring and provides `phi`, `verify`,
`cornacchia`, `l7-check`, `l11-attempt` modes.  The L_7 round-trip
mode validates `Φ_490(5)` computation via num-bigint cyclotomic
recursion against the PARI-derived norm pair embedded in
`AurifeuilleanLUnbounded.lean`.

`L_11` remains an open computational frontier.  Lean-side, this is
without consequence: `L_7` already absorbs every Hunter depth-k
bound that is kernel-feasible to enumerate.

## Dual

The cut-off principle is the pigeonhole asymptotic structural-class
membership argument with redundant packaging removed.  Classical
statement: "every increasing sequence eventually leaves any finite
set."  213-native statement: identify `f`, identify `H_k`, locate
the coincidence slice, diagnose the literal-vs-refined gap, prove
the refined form.  The classical statement is the asymptotic.  The
213-native statement is the protocol that produces the asymptotic
together with the structural arithmetic content of the slice.  The
applications are the principle, not "applications of" the principle.

## Open frontier

`m = 11` (L_11 computation; requires GNFS or external tables).
Direction A unrestricted outer-pow for catalogue atoms other than
521 (small enumeration extends, mechanical).  Stevens-Brent
polynomial formula in rust (documented in `aurifeuillean_lm.rs`
"Algorithm landscape" section, not implemented).  Other external
sequences (Padovan, Fermat numbers, cyclotomic at bases ≠ 5).
Catalogue further audits (whether 7, 13 carry equally forced
framings — they appear generator-derivable: 7 = NS² − NT,
13 = NS² + NT², so likely OK).

## Self-check

The 41/137 refactor is the essay's own §8.4 retreat.  The
catalogue-atomicity claim was an import from physics-constant
numerics back into a structural framework; the marathon caught it
mid-pass and corrected.  The same retreat is documented in the
applications chapter §9 and in this branch's commit
`Catalogue refactor: remove 41 and 137 from Hunter atomic primes`.
The retreat is part of the marathon, not a separate cleanup.
