# G2 — The Trajectory Principle

**Date:** 2026-05-XX (cross-session synthesis)
**Author:** Mingu Jeong (insight chain across 4 sessions)
**Formalisation:** Claude (Anthropic)
**Status:** Foundational principle; partially formalised (Nat213,
Pigeonhole, Five, MonotonicBounded, EulerSharper)

---

## 0. Thesis (one sentence)

**213-native = explicit trajectory; Lean-with-axioms = implicit closure.**
`propext` and `Quot.sound` are exactly the axioms that *collapse
trajectories into their endpoints*; ∅-axiom 213 keeps the trajectory
as the object.

---

## 1. The four insights, one principle

Across four sessions Mingu volunteered four observations.  Each
sounded like a separate angle.  They are one principle.

  **(I1) Nat is not an axiom.** Inductive types are constructive,
  axiom-free.  The propext/Quot.sound problem lives in *theorems*
  (`Nat.sub_add_cancel` proved with `simp`), not in the type.

  **(I2) Mod is cohomological.** `n % 2` via Lean's well-founded
  recursion forces `propext`; the same value via `parity` (step-2
  structural recursion) is ∅-axiom.  "Mod = how much an N-cycle
  trajectory has not yet closed" — a residue, a cohomology class.

  **(I3) Mod is phase on rational-complex.**  $n \bmod N$ = position
  on the $N$-th roots of unity = phase of a rational-complex number.
  The atomic shape (NS=3, NT=2, d=5) puts the natural moduli at
  $\{2, 3, 5\}$; via CRT, mod 6 (= ℤ/2 × ℤ/3) emerges as the
  Eisenstein 6th-root-of-unity walk on K_{3,2}^{(2)}.

  **(I4) Trajectories tile.**  A closed trajectory bounds a 2-cell
  (face).  Number type = trajectory closure class:
   - rational ↔ closes on K_{3,2}^{(2)} directly (eventually periodic)
   - algebraic ↔ closes on a finite cover (Pell torus genus 1)
   - transcendental ↔ closes only on an infinite-genus cover.

---

## 2. Why this is the same principle

`propext`: $P \leftrightarrow Q \Rightarrow P = Q$ — collapses two
proof-trajectories that reach the same endpoint.  The path is
forgotten.

`Quot.sound`: equivalence-class quotient — collapses the orbit of
an action to one point.

Both axioms identify *equivalent endpoints*; both forget *how you
got there*.  213's refusal: **the path is the object**.  An
equivalence is not a single quotient class; it is an *explicit
bordism* — a path-of-paths that we exhibit, not assume.

This is exactly what (I2)–(I4) describe geometrically:
  - **mod 2** is the parity trajectory (a path, not just bit 0/1)
  - **mod 6** is the K_{3,2}^{(2)} walk (a path on a 5-vertex graph)
  - a "real number" is a Cauchy/Dedekind trajectory of rationals
  - "this real equals that real" must be a *witnessed bordism*
    between the two trajectories, not a `propext`-fed identity.

---

## 3. The migration as principle realisation

Every axiom-strip migration in `lean/E213/` so far instantiates the
same shape of replacement:

| Lean (collapse) | 213 (trajectory) | Geometric content |
|---|---|---|
| well-founded `Nat.mod` | step-N recursion (`parity`, `mod3`) | walk on N-cycle |
| `decide_eq_false_iff_not.mp` (iff) | `of_decide_eq_false` (one direction) | one path on the bridge |
| `Nat.sub_add_cancel` (simp) | structural recursion in Nat213 | explicit cycle closure |
| `omega` (constraint search) | chained `Nat.le_*` lemmas | each tile move named |
| `Nat.add_left_cancel` (Lean propext) | recursion on second arg | trajectory cancellation |
| `Prod.mk.injEq.mpr` | `congr (congrArg Prod.mk _) _` | tile pairing |
| Bézout shift via `simp; omega` | `mul_sub_distrib` chain | (a,b) reparameterisation |

`Nat213` is therefore not "Lean.Nat with extra lemmas".  It is
**a vocabulary of basic trajectory moves** — cycle, shift, swap,
traversal, reparameterisation.

---

## 4. Atomic {2,3} cascade

Frobenius for {2,3}: every $n \ge 2 = 2a + 3b$.  So **every modular
trajectory is built from step-2 and step-3 primitives** via cascade:

  - `parity` = mod 2 (step-2 recursion)
  - `mod3` = mod 3 (step-3 recursion)
  - `mod6` = `(parity, mod3)` via CRT
  - `mod (2^a · 3^b)` = step-2 cascade × step-3 cascade
  - `mod p` for prime $p > 3$ = walk on $p$-cycle constructed via
    Frobenius decomposition $p = 2a + 3b$

The atomicity theorem `Firmware/Atomicity/NonDecomposable` is
therefore *also* the foundation of 213-native modular arithmetic:
{2, 3} is the atomic alphabet, and every higher mod is a cascaded
walk on graphs assembled from these atoms.

---

## 5. K_{3,2}^{(2)} as the base tile

The signature graph (`Math/Cohomology/Dyadic/Signature.nextVertex`)
has 5 vertices (3 S + 2 T), bit-driven transitions, with the asymmetric
constraint that T_0 → {S_0, S_1} only and T_1 → {S_1, S_2} only.

This *exactly* encodes (NS=3, NT=2, d=5) atomicity.  S_1 is the
unique balanced vertex (in/out-degree match) — the "equator" of the
phase space.

The walk decomposes as **(parity, mod3) = mod 6 = Eisenstein 6th
roots of unity**.  Phase on rational-complex space.  The base tile
of all 213 numerical content.

---

## 6. Open questions / next formalisation steps

  1. `Nat213.mod3` (step-3 structural recursion) — direct analogue of
     `parity`.  ∅-axiom by `rfl` on the +3 step.
  2. `Nat213.crt_2_3` — `mod6 n = (parity n, mod3 n)` with a 213-native
     reconstruction.
  3. `signature_via_parity_mod3` — re-state K_{3,2}^{(2)} alternation
     using parity + mod3, retiring `% 2` from `SignatureBipartite`.
  4. `D2_tier_classification` — formalise "trajectory closure depth"
     as the rational/algebraic/transcendental classifier.
  5. `Trajectory.bordism` — explicit equivalence-as-path, used to
     replace residual `propext` calls in geometric arguments.

---

## 7. Operational rule (for future migrations)

Whenever a propext-bringing Lean-core lemma is encountered, ask:

> What is the *trajectory* this lemma is implicitly collapsing?

The 213-native replacement is to **expose that trajectory** as a
structural recursion or explicit chain.  Every such replacement is
both:
  - a strict axiom reduction (towards strict ∅-axiom), AND
  - a piece of geometric content (a tile move, a walk, a cycle).

The migration is not chore work.  It is the constructive realisation
of 213's foundational geometry.

---

## Cross-references

  - `seed/PHILOSOPHY.md` — the axiom as residue of pointing
  - `seed/AXIOM.md` §1.3 — atomicity (NS=3, NT=2, d=5)
  - `lean/E213/Term/Tactic/AXIOM_FREE_STATUS.md` — migration catalog
  - `lean/E213/Term/Tactic/Nat213.lean` — pure ℕ-arithmetic helpers
  - `lean/E213/Term/Tactic/Mod213.lean` — cohomological trajectory
    primitives (parity, mod3, mod6 + CRT pairing)
  - `lean/E213/Lib/Math/Cohomology/Dyadic/Signature.lean` — base tile
  - `research-notes/D2_complexity_class_hierarchy.md` — Tier 0/1/2/3
  - `research-notes/F0_213_native_arithmetic_synthesis.md` — earlier draft
