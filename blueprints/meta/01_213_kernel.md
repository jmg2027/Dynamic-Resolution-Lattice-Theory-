# 213 Kernel — Blueprint (Extreme Purity)

**Priority**: ★★★★ Top priority (redefines the floor of the entire theory)
**Status**: **Phase KA→KH complete** — all 101 theorems verified 0 axiom.
Next: KI+ (deep porting of Real213/Phase, expanding auto_port.py patterns).

---

## 1. Why This Domain

Historical setup (legacy text — kept for context): "0 external
axioms" was once read as *Lean kernel-relative*, with `propext`,
`Quot.sound`, and `Classical.choice` tolerated as given primitives.

**Current standard (post-Phase KH):** ∅-axiom is THE standard.
A theorem with *any* non-empty `#print axioms` output is
`sorry`-equivalent; `propext` and `Quot.sound` are now in the same
dirty bucket as `Classical.choice` and `Lean.ofReduceBool`.  The
prior tolerance is deprecated.

**Vision:** Raw/Lens is the *true floor*, Lean is the *syntactic host*.
Because 213 is a finite discrete lattice, infinite-type-theory axioms
such as `propext` and `Quot.sound` are not needed.  This is now
realized — the kernel marathon (KA→KH) closed every load-bearing
fact under ∅-axiom.

**Goal:** Ensure that *none* of the Lean kernel axioms are load-bearing
for the truth value of any 213 theorem — `#print axioms` yields a
*literally* empty list.  This goal is now THE standard, not the
asymptotic target.

Analogy: instead of building a "real program like C++" in Lean, we
borrow Lean to host a deep embedding of 213.  Lean serves only as a
type-checker; all meaning is determined by functions internal to 213.

## 2. 213-native Emergence — Deep Embedding Path

### 2.1 Data = Term

```
inductive Term : Type
  | zero | succ | add | mul | (... future extensions)
```

Pure inductive — neither propext nor quotient used.

### 2.2 Semantics = Total Function

```
def eval : Term → ℕ      -- structural recursion, total
def equiv : Term → Term → Bool   -- avoids Prop
```

Bool equality + Nat.beq → propositional extensionality unnecessary.

### 2.3 Theorem = rfl

`theorem T : equiv lhs rhs = true := rfl`
→ Lean performs only reduction; no axiom is cited.

### 2.4 Soundness Bridge (optional)

`theorem Sound : equiv a b = true → eval a = eval b`
→ Once proven, promotes Bool results to Prop results.  Uses only
Lean's Eq (intensional, 0 axiom).

## 3. Already-Laid Building Blocks (Phase KA complete)

  ✅ `lean/E213/Term/Term.lean`
     - `Term` inductive (zero, succ, add, mul)
     - `eval : Term → ℕ`
     - `equiv : Term → Term → Bool`
     - Standard constants: nS=3, nT=2, d=5, c=2

  ✅ `lean/E213/Term/Demo.lean` — 7 capstones, all 0 axiom:
     - `dim_law`     n_S + n_T ≡ d
     - `c_eq_nT`     c ≡ n_T
     - `d_sq_25`     d² ≡ 5·4 + 5
     - `eval_d_sq`   eval(d·d) = 25
     - `nSnT_sq_36`  ((n_S·n_T))² = 36
     - `two_nS_sq`   2·n_S² = 18  (Argon)
     - `two_nS_cube` 2·n_S³ = 54  (Xe)

  ✅ `lake build E213.Term.Demo` clean
  ✅ `#print axioms` output 7/7 all "does not depend on any axioms"

## 4. Phase Plan (KB → KH Marathon)

Each Phase = single Lean file (~80 lines); must finish with `#print axioms`
yielding an empty list for all theorems.
