# G158 — `depth_floor_is_det_one`: scoping (read-only)

> **STATUS update**: the **forward direction is CLOSED** —
> `Lib/Math/Cauchy/DepthFloorDetOne.lean`,
> `convergent_crossdet_floor_is_one` (`reachesFloor W ∧ ∀ n, W n = 1`),
> 4 pure / 0 dirty.  The PURE Cassini used is
> `Real213.FibCassiniNat.fib_cassini_norm` (NOT `ConvergentDet.convergent_det`,
> which is axiom-dirty and lives in an orphaned-from-build subtree — see
> note below).  The **converse** (floor value 1 ⟹ autonomous P-step) is the
> remaining open work.

**Tier-1 scratch.**  Pre-implementation scoping of HANDOFF Target A
(`depth_floor_is_det_one`), produced read-only.  Conclusion up front: the
forward brick is **much closer than HANDOFF estimated** — the Int→Nat
subtraction obstacle HANDOFF flagged is already discharged, because both
Cassini identities are already PURE *Nat-additive* theorems.

## The two sides

**Abstract ladder floor** — `Lib/Math/Cauchy/DivergenceLadder.lean`:
  - `diff s n = s(n+1) − s n`, `liftK k` = `k`-fold diff,
    `isConst s := ∀ n, s n = s 0`,
    `reachesFloor s := ∃ k, isConst (liftK k s)` (least such `k` = divergence depth).
  - `const_reaches_floor (c) : reachesFloor (fun _ => c)` — a constant
    sequence is *already* at the floor (depth 0).  Docstring names this the
    algebraic base case: "constant cross-determinant (φ, √2: `Wₙ = ±1`)".

**Concrete P-orbit invariant** — `Lib/Math/Mobius213/Px/`:
  - `ConvergentDet.convergent_det (n)`:
    `(Q00 n + Q01 n) · Q00 n = Q01 n · (2·Q00 n + Q01 n) + 1`.
    This *is* the convergent cross-determinant `= 1` (det P = 1), in
    Nat-additive `A = B + 1` form.  PURE.
  - `CassiniUniversal.cassini_universal (n)`:
    `Lnat n · Lnat (n+2) = Lnat(n+1)·Lnat(n+1) + 5`  (Lucas Cassini `= d = 5`),
    Nat-additive, PURE.

## The bridge is shorter than HANDOFF thought

HANDOFF Target A worried: "`Wₙ` is Nat-abstract in DivergenceLadder, the
P-orbit is Int-valued ... bridge needs the sign-free Nat reading of
`Wₙ = ±1` matched to Cassini, via additive Int→Nat routing (no Int
subtraction)."  **That routing already exists**: `convergent_det` and
`cassini_universal` are the sign-free Nat-additive Cassini, already PURE.
No Int detour is needed.

### Forward direction — near-trivial, one sitting

Define the convergent cross-determinant **gap** as a `Nat → Nat`:

```
def W (n : Nat) : Nat := (Q00 n + Q01 n) * Q00 n - Q01 n * (2 * Q00 n + Q01 n)
```

By `convergent_det`, `(Q00 n + Q01 n)*Q00 n = [Q01 n*(2*Q00 n+Q01 n)] + 1`,
so in Nat `W n = (B n + 1) - B n = 1` for every `n` (pure: `(b+1) - b = 1`
via `NatHelper.succ_sub` / `add_sub_cancel`).  Hence:

  - `W_const : ∀ n, W n = 1`  (rewrite by `convergent_det`, then Nat subtraction).
  - `W_isConst : isConst W`   (`∀ n, W n = W 0`, both sides `= 1`).
  - **`depth_floor_is_det_one_forward : reachesFloor W`** — `⟨0, W_isConst⟩`,
    i.e. the convergent cross-det sequence is at the ladder floor (depth 0)
    with floor value 1.

This is the analysis-side ladder (`const_reaches_floor`) and the
atomic-side forcing (`convergent_det` = det P = 1) shown to be the *same*
floor.  Estimated: a short PURE proof, well under one session — the pieces
are all present and pure.

### Converse direction — sharpened: it is mostly assembly

The deeper half ("floor value 1 ⟹ the pair lies on the autonomous P-orbit")
turns out to need **no new machinery** — the key fact is already present:

  - `Real213.Mobius213PellInvariant.pellNormStep (a b : Nat)
    (h : a*a + 1 = a*b + b*b) : …` — the autonomous Pell/Cassini step.  Its
    **hypothesis `a*a + 1 = a*b + b*b` IS "floor value 1"** (the cross-det = 1
    Cassini relation, in the squared/normed form).
  - `Real213.FibCassiniNat.fib_cassini_norm n` has exactly that shape with
    `a = fib(2n+2)`, `b = fib(2n+1)` — and it is **PURE**.  So
    `pellNormStep (fib(2n+2)) (fib(2n+1)) (fib_cassini_norm n)` already feeds
    the floor-1 invariant into the autonomous step (FibCassiniNat line ~97
    does this inside its induction).

So the converse brick is: **floor value 1 (the Cassini relation) is precisely
`pellNormStep`'s premise; invoking it shows the pair advances by the P-orbit
recurrence, preserving the invariant.**  The theorem to state:

  - **`depth_floor_is_det_one_converse`**: `∀ n, W n = 1` (equivalently the
    Cassini relation `a*a + 1 = a*b + b*b` holds at each step) ⟹ the
    convergent pair obeys `pellNormStep` (the autonomous P-step), i.e. lies on
    a single P-orbit.  Proof: rewrite `W n = 1` back to the squared Cassini
    form (the inverse of the forward `succ_sub` step), then `exact
    pellNormStep _ _`.

The only real work is the **form bridge**: the forward brick used the *linear*
cross-det `a·b + b² − a²`-style gap (`fib_cassini_norm` rearranged); the
`pellNormStep` premise is the *squared* form `a² + 1 = a·b + b²`.  These are
the same identity; a one-step Nat-additive `rw` connects them (no Int, no
omega — same PURE toolbox as the forward brick).  Estimated: comparable to the
forward brick, well under a session.

(`OrbitForcing` then supplies the *uniqueness* layer — that `(NS,NT)=(3,2)`
forces this orbit specifically, via `pellLucasEq 3 1` canonical + the bounded
non-canonical-fail enumeration — if one wants the full "distance from
atomicity" statement rather than just "lies on *a* P-orbit".)

## Recommendation for the next active session

1. **DONE** — `convergent_crossdet_floor_is_one` in
   `Lib/Math/Cauchy/DepthFloorDetOne.lean` (4 pure / 0 dirty), via the PURE
   `Real213.FibCassiniNat.fib_cassini_norm` (the ungated `Mobius213/Px`
   Cassini was axiom-dirty, so routed around it).
2. **Converse — next**: add `depth_floor_is_det_one_converse` in the same
   file.  Bridge `W n = 1` back to the squared Cassini `a²+1 = a·b+b²` (one
   PURE Nat `rw`, inverse of the forward `succ_sub`), then `exact
   pellNormStep _ _ (fib_cassini_norm n)`.  Comparable cost to the forward
   brick — mostly assembly, no new machinery.
3. **Optional uniqueness layer**: wire `OrbitForcing` (`pellLucasEq 3 1`
   canonical + bounded non-canonical fails) to upgrade "lies on *a* P-orbit"
   to "lies on *the* (3,2)-forced orbit" — the full "distance from atomicity".

## Latent breakage found (separate issue)

`Lib/Math/Mobius213/Px/ConvergentDet.lean` does **not compile** and has
**no olean** — `farey_neighbour_fib` calls an undefined `convergent_det'`
(stray prime) and `convergent_det`'s own proof leaves goals unsolved.
`MobiusSelfForm.lean` likewise has no olean.  These sit in a subtree that
is **outside the `E213` root build closure**, so `lake build E213` reports
green without ever compiling them (broken since the G139 commit, unrelated
to this session).  Also: even the sibling `Mobius213/Px/FibCassini.lean`
that *does* build is **axiom-dirty** (`fib_cassini_norm` in `Real213` is
the PURE alternative used here).  Worth a dedicated Tier-A pass: integrate
the orphan subtree into the build (or prune it), fix `ConvergentDet`, audit
its purity.

## Pointers

  - Ladder: `Lib/Math/Cauchy/DivergenceLadder.lean`
    (`reachesFloor`, `const_reaches_floor`, `e_ratio_floor`, `infinite_depth`).
  - Cassini (Nat-additive, PURE): `Mobius213/Px/ConvergentDet.convergent_det`,
    `Mobius213/Px/CassiniUniversal.cassini_universal`.
  - Atomic forcing for the converse: `Theory/Atomicity/OrbitForcing`,
    `Mobius213/Px/PnFibonacciUniversal`.
  - Depth arc context: `theory/math/completeness_without_completeness.md`,
    HANDOFF "Next targets — A".
