# G173 — Newton–Gregory generalization (marathon scratchpad)

**Tier 1 (volatile).**  Goal: generalize the Newton–Gregory forward-difference
reconstruction so it actually closes ∅-axiom — unblocking the `polyDepth d ⟹
newton form` converse (HANDOFF Open Problem #4) and the `QuasiPolyCF ⟹
polynomially-bounded` bridge (T4).

**STATUS (final): G1–G5 all closed ∅-axiom** in
`lean/E213/Lib/Math/Cauchy/NewtonGregory.lean` (41 PURE / 0 dirty).  See the
"Final results" + "Conjecture log" sections at the bottom.

## The blockage (HANDOFF #4, the honest obstruction)

`DepthPRecursiveInstances` proves the **forward** law cleanly over `ℕ`:

> `newton_polyDepth` : `polyDepth d (newton c d)` — every degree-`d` Newton-form
> polynomial `Σ_{i≤d} cᵢ·binom(·,i)` has divergence-depth `d`.

The **converse** (reconstruction) `polyDepth d s ⟹ s = newton (fun i => Δⁱs 0) d`
**FAILS over `ℕ`**.  Reason: the forward difference `diff s n = s(n+1) − s n` uses
**truncated** subtraction.  When an intermediate finite difference would be
negative, `ℕ` clamps it to `0`, and the information is gone.

### Witness of the obstruction (PROVEN — G5)

`s n = (n−2)·(n−1)`, genuine nonneg values `2, 0, 0, 2, 6, 12, …` (`vObs`).  The
**values are identical in ℕ and ℤ** (all ≥ 0, nothing clamps).  What differs is
the difference operator: the genuine first difference `s(1)−s(0) = −2` is faithful
over `ℤ` but **clamps to `0`** over `ℕ`'s truncated subtraction.  That single
clamp makes the ℕ second difference jump `0, 2, 2, …` (non-constant) while the ℤ
second difference is the constant `2`.  So **ℕ-`polyDepth 2 s` is FALSE** though
`s` is genuinely degree 2.

The honest lesson (red-team-corrected): ℕ-`diff` is **not a broken ℤ-`diff`** — it
is a *different Lens*, agreeing with ℤ-`diff` exactly on the monotone-difference
cone (where no clamp occurs).  ℤ is simply the **readout group in which `Δ` closes
under iteration**; there is no ℕ-vs-ℤ dichotomy and no "fixing" of ℕ.

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

## 213-native framing (red-team-grounded)

Newton–Gregory says: the whole sequence is reconstructible from its
**differences-at-a-point** `(Δʲs)(0)`.  Sequence and difference-data are **one
object read in two bases** (monomial ⇄ Pólya–Ostrowski/binomial); G1⇄G2 is the
invertible change of basis relating them — the anti-pluralism reading (one
Lens-arrow, two readings), *not* two objects.

On the ℤ-lift (red-team correction): do **not** say "ℤ keeps the signed
distinguishing" (that imports a sign-primitive into Raw — a Count-Lens-import-as-
Raw slip) and do **not** run an ℕ-vs-ℤ dichotomy.  The clean statement: **ℤ is the
readout group the difference-Lens `Δ` lands in.**  `Δ` is a count-Lens reading
that does not close under its own iteration unless its readout group is taken; that
group is `ℤ`.  No exterior, no comparison, no "fixing".  (`Int` is axiom-clean: a
definable inductive type with ∅-axiom ring laws in `Int213.Core`.)

On the involution (red-team correction): the binomial transform is
**fixed-point-RICH** (any ±1-eigen-sequence is fixed) — that is **Nat-style**
grounding (§5.2), the *opposite* of the Bool-style liar's fixed-point-free
oscillation.  Do **not** map "there is a minus sign and it squares to id" onto
Bool-style self-reference (stereotype-matching).  The right open question is the
transform's fixed-point eigenspace (Conjecture C5 below).

## Agent dispatches

- **A — literature** (web): Newton–Gregory forward/backward, umbral calculus, the
  binomial-transform involution, `Eⁿ=(I+Δ)ⁿ`, divided-difference & q-analogue
  generalizations, Nörlund–Rice, and any "Hurwitzian ⟹ poly-bounded p.q." route.
- **B — red-team / 213-framing**: is the ℤ-lift a legitimate 213-native move?
  Frame the involution in Lens terms; sanity-check the obstruction witness.

## Final results (all ∅-axiom, `Cauchy/NewtonGregory.lean`, 41 PURE / 0 dirty)

- **G1** `newton_gregory` — universal `s(m+n) = Σ_{j≤n} binom(n,j)·(Δʲs)(m)` for
  *every* `s : ℕ → ℤ` (operator `Eⁿ=(I+Δ)ⁿ`, no polynomiality hypothesis).
  `newton_gregory_zero` is the base-`0` form.
- **G2** `newton_gregory_inverse` — `(Δⁿs)(m) = Σ_{j≤n} (−1)^{n−j} binom(n,j)
  s(m+j)`; `binomial_transform_roundtrip` bundles `F∘G = id`.  Sign handled by
  reusing `bsum_pascal` (on `j≤n`, `(−1)^{n−j}=(−1)ⁿ(−1)ʲ`) — no second induction.
- **G3** `reconstruct` — `polyDepthZ d s ⟹ s n = Σ_{i≤d}(Δⁱs 0)·binom(n,i)`.
  **Closes HANDOFF Open Problem #4** (the ℤ converse ℕ could not state).
- **G4** `poly_bound` — `polyDepthZ d s ⟹ ∃C, |s n| ≤ C·(n+1)^d`,
  `C = Σ_{i≤d}|Δⁱs 0|`.  **Unblocks T4** (the ∅-axiom half of Hurwitzian ⟹
  poly-bounded p.q. ⟹ μ=2; μ step cited).  Reusable pure infra: `natAbs_add_le`
  (ℤ triangle), `natAbs_ofNat_mul`, `binom_le_pow` (`binom n i ≤ (n+1)ⁱ`).
- **G5** `obstruction_nat` / `obstruction_first_diff_clamp` /
  `obstruction_int_constant` — the witness `vObs=(n−2)(n−1)`: ℕ-`polyDepth 2`
  FALSE, ℤ-`polyDepthZ 2` constant `2`, the clamp pinned at the first difference.

**Literature anchors** (agent A): operator form Gregory c.1670 / Newton
*Methodus Differentialis* 1711; binomial-transform inverse pair = umbral inverse
(Rota–Kahaner–Odlyzko 1973, finite operator calculus, `Δ` a delta operator with
falling-factorial basic sequence); the `C(x,k)` ℤ-basis = Pólya 1915 / Ostrowski
1919 (Cahen–Chabert 1997); Hurwitzian numbers = integer-valued-polynomial p.q.
(Hurwitz 1896); the full Hurwitzian⟹μ=2 chain is a **novel synthesis** (each link
classical, no off-the-shelf theorem).  Out of ∅-axiom scope (analytic, cited only):
Nörlund–Rice integral, Newton-series convergence / Carlson's theorem.

## Conjecture log

- **C1 ✅ DONE** (`Cauchy/QuasiPolyBound.lean`, 14 PURE): `quasiPolyCFZ_poly_bounded`
  — `QuasiPolyCFZ p a ⟹ ∃ C D, ∀ n, a n ≤ C·(n+1)^D` (per-residue `poly_bound`
  reassembled via a pure finite max + the pure `div_add_mod` decomposition
  `n=p·⌊n/p⌋+n%p`).  Then (cited) `μ = 2`.  Witnesses: `periodic_partial_bounded`
  (quadratic irrationals, Lagrange, degree 0) and `e_partial_quotients_poly_bounded`
  (transcendental Hurwitzian, subsumes `ePQ_linear_bound`).  Note: had to use the
  ℤ-faithful `QuasiPolyCFZ` (polyDepthZ on lifted sections), NOT ℕ `QuasiPolyCF` —
  ℕ-`polyDepth` does not imply `polyDepthZ` (the `[3,2,1,0,0,…]` clamp gives a
  spurious ℕ depth-1).
- **C2 ✅ DONE** (`Cauchy/FiniteDepthAlgebra.lean`, 22 PURE): `polyDepthZ_mul`
  (`polyDepthZ d s → polyDepthZ e t → polyDepthZ (d+e) (s·t)`) via the discrete
  Leibniz rule `diffZ_mul` (`Δ(s·t)=(Es)(Δt)+(Δs)t`) + induction on the degree bound
  (`mul_vanish`, vanishing view `polyDepthZ d s ↔ Δ^{d+1}s≡0`).  Plus the module
  structure (`polyDepthZ_add`, `polyDepthZ_smul`, shift-invariance).  Turns the
  hand-counted "π depth 6 = 1+1+4" into a theorem.  Note: core `Int.zero_add` pulls
  propext (asymmetric vs `Int.add_zero`) — use `Int213.zero_add`; `funext` pulls
  `Quot.sound` — use the pointwise `liftKZ_congrZ`/`vanishZ_congr`.
- **C3 (combinatorial part ∅-axiom; transcendence part classically open)** the
  e/π depth separation (e depth 1, π Wallis-coeff depth 2) is a *structural*
  invariant.  Provable: their difference-orders differ.  **Do NOT** slide to "this
  explains the e–π separation" (metaphysical framing).
- **C4 (boundary marker, ∅-axiom-statable)** the Newton-reconstructible
  (finite-depth) sector and the periodic (Markov / quadratic-irrational) sector are
  disjoint: periodic non-constant sequences have *no* finite ℤ-difference-depth.
  A clean separation lemma; the Markov spectrum itself stays classically open.
- **C5 (∅-axiom-closable; the *right* home for the §5.2 self-reference question)**
  characterize the **fixed-point eigenspace** of the binomial transform
  `s = Σ (−1)^{n−j} binom(n,j) s(j)`.  This is a definable ℤ-subspace; computing it
  ∅-axiom would *earn* the "self-inverse Lens" narrative with an actual fixed-point
  set — and empirically settle Nat-style (fixed-point-rich, predicted) vs Bool-style
  (fixed-point-free).  Replaces the dropped liar-involution claim.

## Session log

- start: note created; baseline build clean; agents A (literature) + B (red-team)
  dispatched.
- A (literature): confirmed G1=Thread 1A, G2=Thread 2B, G4=Thread 4 (Pólya basis),
  Thread 5 (Hurwitzian⟹μ=2) a novel synthesis; analytic threads flagged out-of-scope.
- milestone: **G1 → G3 → G2 → G5 → G4** all closed ∅-axiom, committed incrementally
  (41 PURE).  Cauchy umbrella wired.
- B (red-team): three framing corrections folded in (readout-group not "signed
  distinguishing"; drop Bool-style involution → fixed-point eigenspace C5; obstruction
  prose — values don't truncate, first diff clamps).  Promote to theory pending.
