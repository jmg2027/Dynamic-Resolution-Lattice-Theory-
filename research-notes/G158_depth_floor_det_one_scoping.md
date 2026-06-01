# G158 — `depth_floor_is_det_one`: scoping (read-only)

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

### Converse direction — the real remaining content

The deeper half ("depth measures distance from atomicity"):

  - **`depth_floor_is_det_one`** (HANDOFF brick): `reachesFloor` of the
    convergent cross-det *with floor value 1* ⟹ the convergents satisfy the
    autonomous Pell/Cassini step (lie on a P-orbit).
  - Obstacle here is **not** Int/Nat; it is a *recurrence-uniqueness*
    statement: "a depth-0 (constant) cross-det of value 1 forces the
    `Q00, Q01` to obey the P-step `Q(n+1) = P·Q(n)`."  That needs the
    autonomous-recurrence characterization (cf. `OrbitForcing`,
    `PnFibonacciUniversal`), not additive routing.

## Recommendation for the next active session

1. Land `depth_floor_is_det_one_forward` first (cheap, PURE, closes the
   "ladder floor = det 1" identification one direction).  Put it in a new
   `Lib/Math/Cauchy/DepthFloorDetOne.lean` importing `DivergenceLadder` +
   `Mobius213/Px/ConvergentDet`.
2. Then attack the converse via `OrbitForcing` / `PnFibonacciUniversal`
   recurrence-uniqueness; that is the genuine "distance from atomicity"
   theorem and the hinge between the analysis ladder and atomic forcing.

## Pointers

  - Ladder: `Lib/Math/Cauchy/DivergenceLadder.lean`
    (`reachesFloor`, `const_reaches_floor`, `e_ratio_floor`, `infinite_depth`).
  - Cassini (Nat-additive, PURE): `Mobius213/Px/ConvergentDet.convergent_det`,
    `Mobius213/Px/CassiniUniversal.cassini_universal`.
  - Atomic forcing for the converse: `Theory/Atomicity/OrbitForcing`,
    `Mobius213/Px/PnFibonacciUniversal`.
  - Depth arc context: `theory/math/completeness_without_completeness.md`,
    HANDOFF "Next targets — A".
