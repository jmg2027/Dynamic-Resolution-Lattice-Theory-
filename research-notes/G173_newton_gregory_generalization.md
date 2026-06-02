# G173 — Newton–Gregory generalization (marathon scratchpad)

**Tier 1 (volatile).**  Goal: generalize the Newton–Gregory forward-difference
reconstruction so it actually closes ∅-axiom — unblocking the `polyDepth d ⟹
newton form` converse (HANDOFF Open Problem #4) and the `QuasiPolyCF ⟹
polynomially-bounded` bridge (T4).

## The blockage (HANDOFF #4, the honest obstruction)

`DepthPRecursiveInstances` proves the **forward** law cleanly over `ℕ`:

> `newton_polyDepth` : `polyDepth d (newton c d)` — every degree-`d` Newton-form
> polynomial `Σ_{i≤d} cᵢ·binom(·,i)` has divergence-depth `d`.

The **converse** (reconstruction) `polyDepth d s ⟹ s = newton (fun i => Δⁱs 0) d`
**FAILS over `ℕ`**.  Reason: the forward difference `diff s n = s(n+1) − s n` uses
**truncated** subtraction.  When an intermediate finite difference would be
negative, `ℕ` clamps it to `0`, and the information is gone.

### Witness of the obstruction (to be proven — G5)

`s n = (n−2)·(n−1)` over `ℕ` truncated: values `2, 0, 0, 2, 6, 12, …` (the
`(n-2)(n-1)` with `ℕ` cutoff at `n<2`).  Genuinely a degree-2 integer polynomial,
so its **faithful** 2nd difference is the constant `2`.  But the `ℕ`-truncated
`liftK 2 s` is *not* constant — the clamp at `n=0,1` corrupts the first
difference.  So **ℕ-`polyDepth 2 s` is FALSE** even though `s` is genuinely
degree 2.  Conclusion: ℕ-`polyDepth` ⊊ genuine-polynomiality; the gap is exactly
the non-monotone-difference sequences.

## The generalization: faithful finite-difference calculus over ℤ

The repo has full ∅-axiom `Int` ring arithmetic (`E213.Meta.Int213.Core`:
`add_comm/assoc`, `mul_comm/assoc`, `add_mul`, `mul_add`, `mul_sub`, `sub_mul`,
`add_neg_cancel`, …).  Over `ℤ` subtraction is faithful, so the whole obstruction
dissolves.  Define:

```
diffZ   (s : Nat → Int) : Nat → Int := fun n => s (n+1) - s n
liftKZ  : Nat → (Nat → Int) → (Nat → Int)            -- k-fold diffZ
polyDepthZ d s := isConstZ (liftKZ d s)              -- faithful depth
newtonZ (c : Nat → Int) : Nat → Nat → Int            -- Σ_{i≤d} cᵢ · binom(·,i)
```

(reusing the 213-native `binom : Nat → Nat → Nat`, cast to `Int`).

## The headline: the **universal** Newton–Gregory identity (operator form)

The forward shift `E s = s(·+1)` and difference `Δ = E − I` satisfy `E = I + Δ`,
hence (commuting operators) `Eⁿ = (I+Δ)ⁿ = Σ_{j=0}^n binom(n,j) Δʲ`.  Applied at a
base point `m`:

> **G1 (headline, UNCONDITIONAL)** for every `s : Nat → Int` and all `m, n`:
> `s(m+n) = Σ_{j=0}^{n} binom(n,j) · (liftKZ j s) m`.

This holds for **all** sequences (no polynomiality hypothesis) — it is the
faithful generalization of the broken ℕ formula.  At `m = 0`:
`s n = Σ_{j=0}^n binom(n,j) · (Δʲs)(0)`.

### Inductive core (single induction on `n`, generalized over `m`)

Base `n=0`: `s m = binom(0,0)·(Δ⁰s)(m) = s m`. ✓
Step: IH at base `m+1`, top `n`:
`s(m+n+1) = Σ_{j=0}^n binom(n,j)·(Δʲs)(m+1)`.  Expand
`(Δʲs)(m+1) = (Δʲs)(m) + (Δʲ⁺¹s)(m)`; the two sums Pascal-recombine
(`binom(n,j)+binom(n,j−1)=binom(n+1,j)`) to top `n+1`.  ∅-axiom over `Int213`.

**Sum lemma** (the Pascal recombination, the real work):
`Σ_{j=0}^{n+1} binom(n+1,j)·xⱼ = Σ_{j=0}^{n} binom(n,j)·xⱼ + Σ_{j=0}^{n} binom(n,j)·x_{j+1}`.

## Deliverables (marathon plan)

- **G1** universal forward Newton–Gregory over ℤ (headline).  [target]
- **G2 (inverse / involution)** the dual `Δⁿs(m) = Σ_{j=0}^n (−1)^{n−j} binom(n,j)
  s(m+j)`, and that G1 ⇄ G2 form an **inverse pair** (binomial transform is a
  sign-twisted involution).  The "generalization" in full: Newton–Gregory is one
  arrow of a self-inverse Lens.  [target]
- **G3 (reconstruction, unblocks #4)** `polyDepthZ d s ⟹ ∀ n, s n = newtonZ (fun
  i => liftKZ i s 0) d n` — the ℤ converse that ℕ blocked.  Corollary of G1 +
  vanishing of `Δʲs` for `j>d`.  [target]
- **G4 (bound, unblocks T4)** `polyDepthZ d s ⟹ ∃ C, ∀ n, |s n| ≤ C·(n+1)^d`.
  Via G3 + `binom n j ≤ (n+1)^j ≤ (n+1)^d` + triangle.  Then `QuasiPolyCF ⟹
  polynomially-bounded p.q.` (each residue section, lifted to ℤ).  [target]
- **G5 (obstruction)** the witness above: a genuine-degree-2 polynomial with
  non-constant ℕ-`liftK 2` but constant ℤ-`liftKZ 2`.  The honest "why ℤ".  [target]

## 213-native framing (to ground with red-team agent)

Newton–Gregory says: the whole sequence is reconstructible from its
**differences-at-a-point** `(Δʲs)(0)`.  Sequence and difference-data are two Lens
readings of one residue; G1⇄G2 is the involution relating them.  This is the
divergence-depth spiral coordinate read *as an interpolation basis*.  The ℤ-lift
is not an exterior import — `Int` here is the count-Lens reading with the *signed*
distinguishing kept (truncation = the count-Lens discarding a sign, the very
information the difference operator needs).

## Agent dispatches

- **A — literature** (web): Newton–Gregory forward/backward, umbral calculus, the
  binomial-transform involution, `Eⁿ=(I+Δ)ⁿ`, divided-difference & q-analogue
  generalizations, Nörlund–Rice, and any "Hurwitzian ⟹ poly-bounded p.q." route.
- **B — red-team / 213-framing**: is the ℤ-lift a legitimate 213-native move?
  Frame the involution in Lens terms; sanity-check the obstruction witness.

## Session log

- start: note created; baseline build clean; agents A+B dispatched.
