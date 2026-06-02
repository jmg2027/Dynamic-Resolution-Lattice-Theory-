# Session Handoff — 2026-06-02 (Markov uniqueness marathon)

## Branch
`claude/markov-uniqueness-0R0Ut` — pushed.  Working tree clean.  **`origin/main` merged in**
(101 commits: NewtonGregory/FiniteDepthAlgebra, StateMachine FSM, PolynomialDepth, `ring_nat`
tactic, ℤ-difference-Lens, …).  Full `lake build` clean.  Markov: `MarkovUniqueness` 47 PURE +
`ModArith/MarkovPrimeFactor` 28 PURE = 72, all ∅-axiom.  **Integration**: main's `ring_nat`
(∅-axiom `ℕ` ring, `Meta/Nat/PolyNatMTactic`) grafted into the Markov polynomial-identity lemmas
(`sq_expand`, `neg_one_sq_mod`, `neg_one_qr_of_inverse`'s `hsq`/`hkey`, `3bac=3abc`) — verbose
`rw` chains → one-line `ring_nat`, purity preserved.

## Goal
Marathon research on the **Markov uniqueness conjecture** (Frobenius 1913, classically open):
prove ∅-axiom neighbours, run agent discussion, build conjectures.

## What Was Done This Session

### New module `lean/E213/Lib/Math/Real213/MarkovUniqueness.lean` (44 PURE / 0 dirty)
The ∅-axiom **arithmetic spine** of the conjecture — none of this machinery existed in the repo.

- **§1–2 Neighbor congruence.** `markov_le_3mul` (every entry `≤ 3·`product of other two);
  `markov_neighbor_dvd` — **`c ∣ a²+b²`** with witness `a²+b² = c·(3ab−c)` (the lever of every
  partial result); `markov_neighbor_dvd_all` (3 symmetric), `markov_neighbor_residue` (`%c=0`).
- **§3 The `√(−1)` encoding.** `neg_one_qr_of_inverse` — if `b·b' = 1+c·j` (b invertible mod c)
  then **`c ∣ (a·b')²+1`**, i.e. `−1` is a QR mod `c`, witnessed by `u = a·b'`.  The exact form
  the prime-power theorems (Baragar/Button/Zhang) exploit.  Subtraction-free except one
  `dvd_sub_213`; additive inverse form `b·b'=1+c·j` keeps it clean.
- **§3b Toward coprimality.** `markov_common_dvd_sq` — `d∣b → d∣c → d∣a²` (descent-free, from
  `a²=3abc−(b²+c²)`); `markov_gcd_dvd_sq` — `gcd(b,c)∣a²`.  Foothold for pairwise coprimality.
- **§4 Encoding fires.** `neg_one_qr_mod_{5,29,433}` on triples `(1,2,5),(2,5,29),(5,29,433)`.
- **§5 Computational uniqueness.** `markov_max_unique_{5,13,29,34}` + `markovMaxUnique_{5,13,29}`
  — the conjecture verified decidably at small maxima.  (decide heartbeats out for `c≥169`.)
- **§8 Fibonacci spine via Cassini + recurrence.** `fib_spine_sqrt_neg_one` (`fib(2n+3) ∣
  fib(2n+2)²+1`, ∀n); `fib_spine_recurrence`/`pell_spine_recurrence` — the trace-`NS`(=3)/silver(=6)
  linear recurrences of the Markov spines (C-finite; the Vieta jump; Casoratian = Cassini = √(−1)).
- **§9 Cohn matrix.** `cohn_sq_neg_one_mod` — `C²≡−I mod c` for `tr=3c, det=1` (Cayley–Hamilton),
  pure ℕ: the order-4 generator `S` (Gaussian `i`) survives mod every Markov number.
- **§10 Pairwise coprimality (C2/C3).** `coprime_vieta_step` (Vieta step preserves `gcd`),
  `MarkovReachable` (inductive tree), `markov_reachable_coprime` (every tree triple pairwise
  coprime), `markov_reachable_is_triple` (sound: reachable ⟹ markovEq), `markov_reachable_gcd_bc`
  (the `gcd(b,c)=1` the encoding needs).  No descent / no Hurwitz — preservation + induction.
- **§11 Encoding from a modular inverse.** `neg_one_qr_of_mod`: `(b·b')%c = 1 ⟹ c ∣ (a·b')²+1`
  (residue form, via `AddMod213.div_add_mod`).
- **§6 `p≡3` obstruction.** `no_sqrt_neg_one_mod_{3,7,11,19}` (`−1` non-residue mod `p≡3(4)`)
  + `sqrt_neg_one_mod_5_and_13` contrast.
- **§7 The conjecture, formalised.** `MarkovMaxUnique c`, `SqrtNegOneTwoRoots c` (abbrev so
  `decide` sees it); reduction `SqrtNegOneTwoRoots c → MarkovMaxUnique c` documented as an
  **explicit OPEN target** (not claimed — red-team warned against vacuity).  Prime powers hold
  (`sqrtNegOneTwoRoots_{5,13,25,29}`); `not_sqrtNegOneTwoRoots_65` (c=65=5·13 has 4 roots
  {8,18,47,57}) pinpoints the composite-`c` onset of the open difficulty.

**Purity note**: all `decide` statements use the `%`-residue form (`(x*x+1)%c=0`), NOT `∣` —
the `Decidable (a∣b)` instance leaks `propext`; `Nat.decidableBallLT`+`%`+`decEq` are pure.

### Agents (the "discussion")
4 research agents: literature survey (Frobenius/Baragar/Button/Zhang/Aigner; Rabideau-Schiffler
& Lagisquet et al. for the now-proven monotonicity conjectures), repo-infra survey (found
`Gcd213.{dvd_sub_213,dvd_add_213}`, `AddMod213.*`, `ModBezout.modBezout`), and an adversarial
red-team (triviality/vacuity check on the encoding, graded conjecture slate, devil's-advocate +
rebuttal).  Synthesis recorded in `research-notes/G173`.

### Docs
- `research-notes/G173_markov_uniqueness.md` — conjecture slate C1–C8 (graded ∅-axiom
  tractability), literature, red-team discussion, 213-native angle.
- `research-notes/G174_markov_newton_synthesis.md` — **idea-level graft of merged `main`**: Markov
  spine = C-finite trace-`NS` recurrence (Newton/holonomicity layer); `√(−1)` residue = Casoratian
  (Cassini); uniqueness = Myhill–Nerode minimality of the tree coalgebra (StateMachine), localising
  the open C6 crux to "insufficient observable at composite `c`".
- `theory/math/analysis/markov_uniqueness.md` — promoted chapter mirroring the Lean.
- Wired into `theory/math/INDEX.md` + cross-link from `markov_spectrum.md`.
- `Real213.lean` umbrella imports `MarkovUniqueness`.

## Current Precision Results (0 free parameters)
**No physics constants changed** (pure math: Diophantine / number theory).  Precision table
unchanged — see `catalogs/physics-constants.md`, `catalogs/falsifiers.md`.

## Open Problems (Priority Order)

### 1. C2/C3 — pairwise coprimality — DONE along the tree (§10)
`markov_reachable_coprime` (every reachable triple pairwise coprime, via `coprime_vieta_step`
preservation + induction over `MarkovReachable`); `markov_reachable_gcd_bc` gives `gcd(b,c)=1`.
No descent / no Hurwitz needed.  **C2→C4 bridge now DONE** (`MarkovPrimeFactor.inverse_of_coprime`
via `xgcdAux_dvd_both`, the xgcd gcd-component divides both inputs under `fuel≥r₁+1`):
`markov_reachable_neg_one_qr` fires the encoding unconditionally on every reachable triple
(`1<c`).  (Gap to *all* Markov triples = "every triple reachable" = Markov's theorem, the
descent — separate.)

### 2. C5 `p≡3` no-root, GENERAL — DONE (`ModArith/MarkovPrimeFactor`, 16 PURE)
`no_sqrt_neg_one_4k3`: for `p=4k+3` with the prime-gcd hypothesis, `¬(p∣x²+1)`, via
`universal_flt_main` (`x^(p−1)=(x²)^(2k+1)≡(−1)^(2k+1)≡−1` vs Fermat `≡1`).  Helpers
`neg_one_sq_mod`, `neg_one_odd_pow_mod`, `pred_mod_of_dvd_succ`.  Concrete `no_sqrt_neg_one_mod_{7,11}`.
**Remaining C5**: the `p≡1(mod4)` *existence* branch (root of `x²≡−1 mod pᵏ`) — hard without
`Classical` (Wilson construction).

### 3. C6 — root-count reduction `SqrtNegOneTwoRoots c → MarkovMaxUnique c` — classically OPEN-ish
**Input now done for prime POWERS** (full Button/Zhang class): `two_roots_of_prime` (primes) and
`two_roots_of_prime_pow` (`SqrtNegOneTwoRoots (p^(k+1))`, odd prime `p`) — `p` divides ≤1 of
`x±y`, the coprime one cancels via `euclid_of_coprime` + `coprime_prime_pow`.  So the reduction's
hypothesis is discharged at every prime-power maximum; closing the residue-map injectivity (below)
would give prime-power-Markov uniqueness (C7).
The *implication* is classical; the crux is **injectivity of the residue map**
`triple ↦ a·b⁻¹ (mod c)`.  Keep as a single named open Lean target; attempt only the
injectivity lemma in isolation, guarding against vacuity.  Do NOT claim the full reduction.

### 4. C7 — prime-power Markov numbers unique (Baragar/Button/Zhang) = C5∘C6.  Aspirational capstone.

## 213-native conjecture (to sharpen)
The `√(−1)`-residue indexing a Markov number = the order-4 elliptic generator `S` (Gaussian `i`)
of `PSL(2,ℤ)=ℤ₂*ℤ₃` (`ModularElliptic`).  Conjecture: the Markov↦`√(−1)`-residue map is the
Stern-Brocot↦`PSL(2,ℤ)`-elliptic correspondence on the `c=2` `K_{3,2}` axis.

## Dead ends (don't repeat)
- `decide` on `c ∣ …` → `propext` DIRTY.  Use `% c = 0`.
- `decide` on `MarkovMaxUnique`/uniqueness for `c≥169` → heartbeat timeout (>200000) /
  max-recursion.  Cap in-kernel `decide` at `c≈34`; cite external enumeration for larger.
- `set` tactic = Mathlib, unavailable.  Use `obtain ⟨M,_⟩ : ∃ M, …`.
- A docstring may NOT be followed by `set_option … in` (parser rejects); order
  `set_option … in` *before* the docstring.
- `def` for a decidable Prop-shape hides the `Decidable` instance from `decide`; use `abbrev`,
  and put each bound `x < c` *immediately* after its binder (interleaved `∀ x y, x<c→y<c` breaks
  `Nat.decidableBallLT`).

## File Map
```
NEW Lean (∅-axiom):
  lean/E213/Lib/Math/Real213/MarkovUniqueness.lean       ← neighbor congruence + √(−1) encoding + coprimality (43 PURE)
  lean/E213/Lib/Math/ModArith/MarkovPrimeFactor.lean     ← p≡3 no-root (FLT), xgcd-correctness inverse, general Euclid, ≤2 roots mod p^(k+1) Button/Zhang (28 PURE)
NEW theory chapter:
  theory/math/analysis/markov_uniqueness.md
NEW research note:
  research-notes/G173_markov_uniqueness.md               ← conjecture slate C1–C8 + red-team
MODIFIED:
  lean/E213/Lib/Math/Real213.lean, ModArith.lean         ← umbrella imports
  theory/math/INDEX.md, theory/math/analysis/markov_spectrum.md  ← index + cross-link
```
