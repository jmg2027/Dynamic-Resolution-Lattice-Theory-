# G60: Tower ascent — meta-level fixed point at infinity

## Question

User (2026-05-09): "Tower를 계속 올라가면 어떻게 되는지 관찰해보자.
무한히 올라가는지, 어디서 멈추는지, 메타적으로 고정점이 있는지."
("Observe what happens as the tower keeps ascending.  Does it
ascend infinitely, stop somewhere, or have a meta-level fixed
point?")

## Three concurrent answers

The CD-doubling tower exhibits THREE different "fates" simultaneously
at distinct levels of structure:

### 1. Algebraic property loss (classical Hurwitz tower)

Properties degrade monotonically at fixed milestones:

| Layer | Algebra            | Lost property        |
|-------|--------------------|-----------------------|
| L0=ℝ  | comm, assoc, normed | total order (vs. Q)  |
| L1=ℂ  | comm, assoc, normed | none new              |
| L2=ℍ  | non-comm, assoc, normed | commutativity     |
| L3=𝕆 | non-assoc (alt), normed | full assoc → alt   |
| L4=𝕊 | non-alt (pow-assoc), zero divisors | alternativity, division |
| L5+   | progressively degenerate | norm-multiplicativity, ... |

This **stops at L4** in the classical sense: beyond L4 the structure
is "everything that breaks has broken", and further CD-doubling adds
new dimensions but no new property losses.

### 2. Order-4 monopoly (universal preservation)

The Order-4 mechanism `(0, u)² = (-conj(u)·u, 0)` survives at EVERY
layer (Theory/CDDouble/UniversalOrder4.lean — generic on
[StarRing213 α]).  So:

  ∀ n.  every "new im axis" generated at layer L_n+1 has order 4

This is **infinite ascent** — the mechanism never runs out.

### 3. Pointwise meta-fixed point: {±1}

**Lean ∅-axiom witness**:
`lean/E213/Lib/Math/CayleyDickson/TowerFixedPoint.lean`

Across measured layers L3 (Lipschitz / L4T), L4 (Cayley / L5T), L5
(Sedenion / L6T), the count of units NOT of order 4 is constant:

| Type | Layer | total units | non-order-4 count |
|------|-------|-------------|-------------------|
| A    | L3    | 8           | 2 (= ±1)          |
| A    | L4    | 16          | 2 (= ±1)          |
| A    | L5    | 32          | 2 (= ±1)          |
| B    | L4T   | 4           | 2 (= ±1)          |
| B    | L5T   | 8           | 2 (= ±1)          |
| B    | L6T   | 16          | 2 (= ±1)          |

The set `{+1, -1}` is the **pointwise fixed set** of CD doubling.
Every other unit gets absorbed into the order-4 column at the
next layer.

This is the **literal meta-fixed point**: the universal scalar
subring `ℤ ⊃ {±1}` is preserved unchanged at every layer.

## The asymptotic limit

As n → ∞:
  - count(units, order = 4) → ∞
  - count(units, order ≠ 4) = 2 (constant)
  - rat_4 = 1 - 2/|units_n| → 1

For Type A: |units_n| = 2^n, so rat_4(L_n) = 1 - 2/2^n = 1 - 1/2^(n-1).

The asymptotic limit is **rat_4 = 1.0** — every unit (in measure)
becomes order 4.  But never reaches 1 in finite n; ±1 always
contribute their 2 to the non-order-4 count.

## Synthesis

The tower has THREE concurrent "fates":

  1. **Stops at L4** (algebraic property loss)
  2. **Ascends infinitely** (Order-4 mechanism preserved)
  3. **Has a pointwise fixed point {±1}** (universal scalar subring)

These are not contradictory — they describe different aspects:
- (1) is about *which properties survive*, monotone-bounded
- (2) is about *what mechanism keeps firing*, unbounded
- (3) is about *which elements stay invariant*, pointwise

The user's three options ("infinite ascent / stops / meta fixed
point") are all **simultaneously true**, each at its own level.

## Why {±1} is the fixed point

±1 are the unique elements satisfying:
  - `u² = 1` (involutivity, order ≤ 2)
  - `u · u = 1` (= multiplicative inverse coincides with self)
  - `(0, u)² = (-conj(u)·u, 0) = (-1, 0)` BUT in CD-doubled algebra,
    elements that are scalars (`(s, 0)` with s ∈ {±1}) lift trivially:
    `(±1, 0)² = (1, 0)` (order 1 or 2, not 4)

So +1 lifts to L_{n+1}'s +1 (order 1).  -1 lifts to L_{n+1}'s -1
(order 2).  Both keep their orders forever.  Every OTHER element
either had order 4 already (preserved by the lift) or was an
"axis" element which, when doubled, generates a new order-4 axis.

## Connection to 213's residue

The fixed set {±1} is exactly the integer scalar subring
`ℤ ⊂ every CD layer`, which is the *most reductionist* form of
"scalar" in the tower.  It corresponds to:
- the `Raw.atom` count = 2 ⟶ projects to NS=2 (binary axis)
- the `±` distinction in 213's semantics
- the Möbius `[[2,1],[1,1]]` matrix's single "Pell direction"

So the meta-fixed-point of the algebra tower aligns with the
binary atom/anti-atom structure of Raw.  The CD-doubling tower
is, in a sense, "everything that grows away from {±1}".

## Lean witnesses

- `typeA_non_order4_fixed_at_2` (L3, L4, L5 each have 2 non-order-4)
- `typeB_non_order4_fixed_at_2` (L4T, L5T each have 2 non-order-4)
- `tower_fixed_point_summary` (combined ∅-axiom witness)

All in `lean/E213/Lib/Math/CayleyDickson/TowerFixedPoint.lean`,
verified ∅-axiom (does not depend on any axioms).

## See also

- `lean/E213/Theory/CDDouble/UniversalOrder4.lean` — generic Order-4
- `lean/E213/Lib/Math/CayleyDickson/UniversalOrderGrowth.lean` — growth law
- `lean/E213/Lib/Math/CayleyDickson/AlgebraTowerAsymptote.lean` — asymptote
- `research-notes/G58_algebra_tower_completion.md` — completion summary
- `research-notes/G59_generic_CDDouble_starring_lift.md` — type-level lift
