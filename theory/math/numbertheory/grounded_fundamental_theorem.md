# Grounded multiplicative discipline — the Fundamental Theorem of Arithmetic without borrowed `Nat` division

**Status**: Closed.

## Overview

The descent-leg programme asks that a classical discipline be *generated* — recursing on the
distinguishing's own descent — rather than *re-derived* over Lean's native `Nat` with its borrowed
well-founded division.  This chapter is the worked multiplicative case: the **Fundamental Theorem of
Arithmetic**, both existence and uniqueness, reconstructed so that **no theorem in the chain depends
on `Nat.div`, `Nat.mod`, `Nat.strongRecOn`, or `Nat.lt_wfRel`** — the kernel's non-structural
well-founded recursion is entirely absent from the closure.

Read 213-natively: divisibility is a *counting* relation, and the only descent permitted is the
structural one (repeated subtraction over an explicit fuel parameter, `Nat.rec`).  Every gear —
remainder, quotient, gcd, Bézout, Euclid's lemma, the `p`-adic valuation, its multiplicativity, and
the unique-factorisation count — is rebuilt on that single structural primitive.  The classical theory
borrows the kernel's `Nat.div`/`Nat.mod` (which internally invoke `WellFounded.fix` on `Nat.lt_wfRel`);
the grounded theory replaces them with `subMod`/`subDiv`, repeated subtraction over fuel.

## Lean source

- Files (∅-axiom, 0 DIRTY):
  - `lean/E213/Meta/Nat/SubMod213.lean` (153) — structural remainder/quotient `subMod`/`subDiv`.
  - `lean/E213/Meta/Nat/SubGcd213.lean` (106) — Euclidean gcd on `subMod` + prime coprimality.
  - `lean/E213/Meta/Nat/SubBezout213.lean` (134) — extended-Euclid Bézout, sign as a `Bool` flag.
  - `lean/E213/Meta/Nat/VpSub213.lean` (112) — `p`-adic valuation `vpSub` on `subMod`.
  - `lean/E213/Lib/Math/NumberTheory/EuclidLemmaGrounded.lean` (91) — `prime_dvd_mul`.
  - `lean/E213/Lib/Math/NumberTheory/VpMulGrounded.lean` (88) — `vpSub_mul`.
  - `lean/E213/Lib/Math/NumberTheory/FTAUniquenessGrounded.lean` (130) — `factorization_unique`.
  - `lean/E213/Lib/Math/NumberTheory/MulDescentGroundedNoDiv.lean` (176) — FTA existence (`minFac'`,
    `mul_factorization_exists_nodiv`).
  - `lean/E213/Lib/Math/NumberTheory/EuclidPrimesGrounded.lean` (85) — Euclid's infinitude of primes.
- ∅-axiom status: every headline theorem reports `#print axioms → "does not depend on any axioms"`,
  and a transitive kernel-closure walk over each finds **none** of
  `Nat.div`/`Nat.mod`/`Nat.lt_wfRel`/`Nat.strongRecOn`/`propext`/`Acc.rec`/`WellFounded.fix`/`gcd213`/
  `Valuation.vp`/`VpMul.vp_mul` (`factorization_unique`: 485-constant closure, zero forbidden hits).

## Narrative

### Why "grounded" is a stronger bar than ∅-axiom

A theorem can be `#print axioms`-clean yet still route its *computation* through the kernel's
well-founded recursion: `Nat.div`/`Nat.mod` carry no `propext`, but their definitions reduce via
`WellFounded.fix` on `Nat.lt_wfRel` — non-structural descent the kernel grants for free.  The
descent-leg criterion rejects that borrowing: the only legitimate recursion is **structural** (`Nat.rec`
on a fuel argument) or the distinguishing's own `Raw` descent (`Lambek.isPart_wf`).  The existence half
already used the latter (`MulDescentGroundedNoDiv` recurses via `measureInduction_grounded`, grounded in
`isPart_wf`); the uniqueness half built here uses structural fuel throughout.  Both avoid
`Nat.strongRecOn`/`Nat.lt_wfRel`.

### Division as repeated subtraction (`SubMod213`)

`subMod fuel a b` reduces `a` mod `b` by subtracting `b` while `a ≥ b`, bounded by `fuel`; `subDiv`
counts the subtractions.  `Nat.sub` is itself structural and clean, so this is division rebuilt from
the repo's own subtraction.  Two identities carry everything downstream:

- `subMod_eq` — `a = b·q + subMod fuel a b` for some `q` (`Nat.rec` on fuel).
- `subMod_zero_iff_dvd` — `subMod a a b = 0 ↔ b ∣ a` (`0 < b`): the `Nat.mod`-free divisibility test.
- `subDivMod_eq` — `b·subDiv + subMod = a`, the division algorithm.

The `subMod_eq` identity is the lever that makes every later lift cheap: where the `Nat.mod` proofs
grind out a mod-subtraction recursion, here `a = b·q + r` is in hand directly.

### gcd and coprimality (`SubGcd213`)

`gcdSub` is the Euclidean recursion `gcd(a,b) = gcd(b, a mod b)` with the remainder from `subMod`.
`gcdSub_dvd_both` (it divides both arguments) lifts through `subMod_eq` in two lines.  `gcdW a b :=
gcdSub (a+b) a b` discharges the fuel (`b ≤ a+b`).  `gcd_eq_one_of_prime_not_dvd` is the half of
Euclid's lemma that needs **no Bézout**: `gcdW p a ∣ p`, so it is `1` or `p`, and `p` is excluded
because `gcdW p a ∣ a` would force `p ∣ a`.

### Bézout without `Int` (`SubBezout213`)

The hard gear.  The extended Euclidean recursion `egcd` threads a coefficient quadruple `(g, x, y, s)`
where `s : Bool` is a **sign flag**, keeping the Bézout identity inside `Nat` — no signed integers:

| `s` | invariant |
|---|---|
| `true`  | `a·x = b·y + g` |
| `false` | `b·y = a·x + g` |

Writing the Euclidean step as `a = b·q + r` (`subDivMod_eq`, so no `Nat`-subtraction enters the
algebra) forces the uniform update `xₙ = y'`, `yₙ = x' + q·y'`, with `s` flipping — proved by
distribution and the induction hypothesis (`egcd_bezout`, `Nat.rec` on fuel).  `egcd_fst` ties the
`g`-component to `gcdSub`, and `bezout_one_of_coprime` reads off the one-sided form
`gcd(a,b)=1 → ∃ x y, a·x = b·y+1 ∨ b·y = a·x+1`.

### Euclid's lemma (`EuclidLemmaGrounded`)

`prime_dvd_mul`: `p` prime, `p ∣ a·b → p ∣ a ∨ p ∣ b`.  The repo's existing proof routes through a
`Nat.mod`-based gcd; this one uses the `subMod` Bézout.  One craft point is decisive for purity: the
proof cases on `gcd(p,a) ∈ {1, p}` (from primality and `gcdW_dvd_left`) **instead of** `by_cases
p ∣ a`.  The latter's `Decidable (p ∣ a)` instance computes via `Nat.mod` and would silently re-import
the very dirt being eliminated.  With `gcd(p,a)=1`, the Bézout identity times `b`, folded against
`p ∣ a·b`, yields `p·c₁ = p·c₂ + b`, whence `p ∣ b` (`dvd_of_pmul_eq`, a clean right-cancellation).

### Valuation and multiplicativity (`VpSub213`, `VpMulGrounded`)

`vpSub q n` is the largest `k` with `qᵏ ∣ n`, found by the same downward search as the classical `vp`
but deciding each step on `subMod n n (qᵏ) = 0` (bridged through `subMod_zero_iff_dvd`) rather than
`n % qᵏ = 0`.  Its four laws (`pow_vpSub_dvd`, `vpSub_ge`, `vpSub_not_dvd_succ`, `le_vpSub_iff`) mirror
the classical ones.  On top, `vpSub_mul` proves `vpSub p (a·b) = vpSub p a + vpSub p b` at a prime —
the same unit-part bookkeeping (`a = pᵅ·u`, `p ∤ u·v` by grounded Euclid) as the classical proof, now
on `vpSub` and the grounded `prime_dvd_mul`.  The prime-power valuation is a grounded homomorphism
`ℕ_{>0} → ℕ`.

### Uniqueness as valuation-count invariance (`FTAUniquenessGrounded`)

∅-axiom forbids the classical "lift to ℤ, use UFD" and the multiset-permutation argument; uniqueness
instead reads as **valuation-count invariance**.  `vpSub_self_pow` gives `vpSub q (qᵏ) = k`;
`vpSub_prime_single` gives `vpSub q p = (if p=q then 1 else 0)` for primes (with `q ∤ p` inlined from
`p`'s primality).  Inducting on `vpSub_mul`, `vpSub_prodL_eq_countOcc` shows that for a list `l` of
primes, `vpSub q (prodL l)` equals the number of occurrences of `q` in `l`.  Therefore two prime lists
with the same product have **equal occurrence count at every prime** (`factorization_unique`) — both
counts equal `vpSub q n`.  The prime multiset is *read off the product*; there is no abstract UFD and
no permutation bookkeeping.

## Key results

| Theorem | Lean module | Statement (informal) |
|---|---|---|
| `subMod_zero_iff_dvd` | `Meta/Nat/SubMod213` | `subMod a a b = 0 ↔ b ∣ a` — `Nat.mod`-free divisibility test |
| `gcdSub_dvd_both` | `Meta/Nat/SubGcd213` | structural gcd divides both arguments |
| `gcd_eq_one_of_prime_not_dvd` | `Meta/Nat/SubGcd213` | `p` prime, `p ∤ a ⟹ gcd(p,a)=1` (no Bézout) |
| `egcd_bezout` | `Meta/Nat/SubBezout213` | sign-flagged Bézout invariant, no `Int` |
| `bezout_one_of_coprime` | `Meta/Nat/SubBezout213` | `gcd(a,b)=1 ⟹ ∃ x y, a·x=b·y+1 ∨ b·y=a·x+1` |
| `prime_dvd_mul` | `Lib/.../EuclidLemmaGrounded` | Euclid's lemma, `subMod`-grounded |
| `vpSub_mul` | `Lib/.../VpMulGrounded` | `vₚ(a·b)=vₚa+vₚb` at a prime |
| `mul_factorization_exists_nodiv` | `Lib/.../MulDescentGroundedNoDiv` | FTA existence (factorisation into primes) |
| `factorization_unique` | `Lib/.../FTAUniquenessGrounded` | equal product ⟹ equal per-prime count (FTA uniqueness) |
| `infinitude_of_primes` | `Lib/.../EuclidPrimesGrounded` | no finite list holds every prime |

## Research-note provenance

- The descent-leg programme's multiplicative grounding marathon produced this chain.  Its conceptual
  frontier (generate `Nat₂₁₃`; forcing vs rival primitives) remains open; the multiplicative
  engineering is closed here.

## Open frontier

- **Leg 1 — generate ℕ from `Raw`.** This chain still grounds on the kernel's *structural* `Nat`
  (`Nat.rec`, fuel), not a distinguishing-generated `Nat₂₁₃`.  The descent-leg note's leg-1 target
  (promote the `RawRecurrence` spine into a naturals object) is independent of this multiplicative
  closure and remains open.
- **`vpSub`/`vp` bridge.** `vpSub` is a parallel grounded valuation; tying it definitionally to the
  classical `Valuation.vp` would re-import `Nat.mod` and is deliberately *not* done.

## How to verify

```bash
cd lean && lake build E213.Meta.Nat E213.Lib.Math.NumberTheory.FTAUniquenessGrounded
python3 tools/scan_axioms.py E213.Lib.Math.NumberTheory.FTAUniquenessGrounded
```
The grounded criterion (beyond ∅-axiom) is a transitive kernel-closure walk: confirm the closure of
`factorization_unique` contains no `Nat.div`/`Nat.mod`/`Nat.lt_wfRel`/`Nat.strongRecOn`.
