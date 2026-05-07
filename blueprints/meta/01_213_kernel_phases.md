# 213 Kernel — Detailed Phase Plan (KB → KH)

Each Phase = single Lean file (~80 lines); must finish with `#print axioms`
yielding an empty list for all theorems.

## Phase KB — Comparison primitives  (`Term/Compare.lean`)

Goal: add decidable comparisons of the form `Term → Term → Bool`.
  - `Term.le_b` : `a ≤ b` as Bool
  - `Term.lt_b` : `<`
  - Proof: `le_b a b = true ↔ eval a ≤ eval b` (Bool equality form)

Verification: `#print axioms` empty list.  ← `decide`/`Classical` not used.

## Phase KC — Pair / G-relation  (`Term/Pair.lean`)

Directly reflects CLAUDE.md axiom "things with pairwise relations":
  - Add `pair : Term → Term → Term` to `Term`
  - Semantics: G_ij = distinguishing weight of two entities (Bool/Nat)
  - `eval_pair (i j) := if equiv i j then 0 else 1`

This brings the *diagonal/off-diagonal* distinction into the kernel.

## Phase KD — Rational arithmetic  (`Term/Rat.lean`)

DRLT needs only ℕ + ℚ (CLAUDE.md "finite discrete lattice").
  - Add `frac : Term → Term → Term` to `Term` (numerator/denominator)
  - `eval_q : Term → ℚ` (Lean Rat = structure → 0 axiom)
  - comparison via cross-multiplication

Result: 213 ratios such as 6/10 and 137/100 become axiom-free.

## Phase KE — Decide procedure  (`Term/Decide.lean`)

Bypass the Lean `decide` tactic.  Finite enumeration is sufficient:
  - `Term.holds : Term → Bool`  (truth of a predicate Term)
  - `Term.allBelow : ℕ → (ℕ → Bool) → Bool`  (∀x<n, p x)

Once this is in place, propositions like "all pairs up to n" become axiom-free.

## Phase KF — Soundness bridge  (`Term/Sound.lean`)

Bridge between deep ↔ shallow:
  - `Sound_eq : equiv a b = true → eval a = eval b`
  - `Sound_le : le_b a b = true → eval a ≤ eval b`

Proof: structural induction + Nat arithmetic.  Uses only Lean Eq
(intensional), no propext.  `#print axioms` empty list maintained.

Once these theorems are closed, Bool results → Prop results *upgrade* is free.

## Phase KG — Core capstone porting  (`Term/Cap_*.lean`)

Ambitious milestone: encode 213's core integer results as Term:
  - Integer foundation of α_GUT (d², 6, 25)
  - magic numbers chain (2, 8, 20, 28, 50, 82, 126)
  - period closures (2 n_S², 2 n_S³, ...)

`#print axioms` is empty list for each capstone.

## Phase KH — Incremental porting tools (`tools/`) ✅ Complete

Automated assistance to port 800+ existing files → kernel encoding:
  - `audit_axioms.py`     parses `lake build` + `#print axioms`
  - `port_candidates.py`  auto-identifies short-proof candidates (85+ found)
  - `auto_port.py`        auto-converts bracket patterns (LO < N < HI)
  - `kernel_regress.sh`   automatically blocks axiom regressions (CI gate)

Hook automation (.claude/hooks/):
  - `purity-guard.sh`        Tier1 + Tier2 (Kernel-strict)
  - `kernel-axiom-check.sh`  PostToolUse regression check

**Achieved:** 7 capstone categories + 101 theorems all axiom-free
(exceeds the target of "5 or more").

---

## 5. Connections to Other Tracks

  - All track (math/physics) capstones are sequential porting targets after KG
  - Directly linked to blueprints/math/13_meta_213.md "Library Meta"
  - Synchronize with catalogs/ (add axiom-free closed column)

## 6. Open Problems

  Q1. How far is ℕ/ℚ alone sufficient?  Can the algebraic number
      φ=(1+√5)/2 be expressed as a Term via its minimal polynomial?
  Q2. Can "Lean's Eq itself" be absorbed into 213?
  Q3. Converting Iff to Eq anywhere triggers propext.  Full bypass?
  Q4. Higher-order relations (G_ij of G_ij) — next step.
