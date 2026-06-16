# The stabilization map (Finding I) — scoped, with an honest non-extension

**Origin:** multi-agent meta-analysis (the forward/convergence dual of the
descent schema, `general_theory_metaanalysis.md`).  **Status:** the genuine core
is **built ∅-axiom**; the hoped cross-domain reach is **rejected with a precise
reason** (a finding in itself, like the agent's R-A/R-B/R-C rejections).

## The map (213-native)

`StagedLimit C V` (`lean/E213/Meta/StagedLimit.lean`, PURE): a staged reading
`s : Nat → C → V` whose per-coordinate reading **settles past a per-coordinate
modulus** `N` has a limit `limit c := s (N c) c` that **equals every late stage**
(`limit_eq_late : N c ≤ i → limit c = s i c`).  The limit is *reached* — assembled
from genuinely-attained per-coordinate values — the **internal-reach** witness,
the positive complement to "reached by none" (`object1_not_surjective`).  It is
the forward (eventual-constancy) sibling of the descent schema
(`MonovariantFlow`): descent reaches a *normal form* by strict decrease,
stabilization reaches a *limit* by eventual constancy — both well-founded maps to
a fixed reading, one backward, one forward.

## What is genuine (built, PURE)

`StagedLimit` cleanly abstracts the **Real213 cut / modulus-limit**.  The
Cauchy-completeness limit is an instance, and its real theorem routes through the
abstract one:

- `Lib/Math/Analysis/StagedLimitCauchy.lean`: `cauchyToStagedLimit` casts
  `CauchyCutSeq` (coordinate `(m,k)`, value `Bool`, modulus `N m k`) as a
  `StagedLimit`; `cauchy_limit_eq_late` recovers `CauchyCutSeq.limit_eq_at` *via*
  `StagedLimit.limit_eq_late`.  This is the **generic-consumer** pass — the
  abstraction does real downstream work, not a vacuous container.

## What is rejected (the cross-domain claim) — and why

The initial hypothesis was that `StagedLimit` unifies the Real213 cut-limit with
the **p-adic diagonal** `Padic.Foundation.Zp.diagLimit` across the genuine
independence boundary (Padic ⊄ Real213).  **It does not.**

`Zp.diagLimit s := fun k => (s k).digits k` reads digit `k` off approximant `k`.
Its real content is `diagLimit_trunc_succ` — `(diagLimit s).trunc (n+1) =
(s n).trunc (n+1)` — proved by **assembling digits via `trunc`** under a
*trunc-level* one-step hypothesis `(s(n+1)).trunc(n+1) = (s n).trunc(n+1)`.  That
fold is **carrier-specific**: it does not reduce to the per-coordinate
`StagedLimit.limit_eq_late`.  The only way to cast `diagLimit` as a `StagedLimit`
is at the *digit* level — coordinate = digit index, `N k = k` — where
`limit_eq_late` would just be the per-digit stability *hypothesis* restated
(trivial), and the downstream consumers (`mul_invFull_correct`,
`teichmuller_pow_p_trunc`, …) go through `diagLimit_trunc_succ`, **not** through
the abstract map.

So by the shared-generator criterion (`theory/meta/boundary_discipline.md`):
`StagedLimit`'s genuine instances are the cut/Cauchy family (`CauchyCutSeq`,
`CauchyLensFounding` — one Real213 sub-tree), not Padic ⊥ Real213.  **Finding I is
the Real213 modulus-limit abstracted, not a cross-domain schema.**  This is the
same failure shape as R-B (the would-be cross-domain instances collapse into one
already-factored sub-tree) — recorded plainly rather than inflated.

## Residual value

- `StagedLimit` (`Meta/`) is a clean reusable form of "modulus-limit = read off
  the modulus stage = every late stage", the internal-reach forward map dual to
  descent — worth keeping for the cut/Cauchy family even though it is not the
  hoped cross-domain unifier.
- The descent ↔ stabilization duality (backward strict-decrease vs forward
  eventual-constancy, the two halves of the residue's convergence story) is the
  genuinely 213-native content; pairing them as one "well-founded map to a fixed
  reading" is a narrative resonance, not a single Lean generator (the proofs are
  dual, not shared).

## Open (low priority)

Whether a *non-trivial* p-adic stabilization can be stated at the trunc level so
that `diagLimit_trunc_succ` becomes an instance of a (different, trunc-aware)
generator — i.e. a `TruncStagedLimit` with an assembly law.  If it has its own
independent consumers beyond Padic, it would be a second schema; if not, leave
`diagLimit` as the carrier-specific fold it is.
