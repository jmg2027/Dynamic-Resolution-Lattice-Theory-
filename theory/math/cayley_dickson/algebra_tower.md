# Algebra Tower (Cayley-Dickson over 213)

**Status**: Closed at structural level — 4-row matrix (Types A/B/C/D)
each formalized with ∅-axiom Lean theorems through the first
past-Moufang layer.

## Overview

ℝ, ℂ, ℍ, 𝕆, ... Are **not** different mathematical worlds.  They
are *the same structural pair extension* on a common `Cut` substrate,
layered as a **Cayley-Dickson tower**:

```
Macro Universal CD Transient Law:
  rat_{n+3} = 14·rat_{n+2} − 56·rat_{n+1} + 64·rat_n + d_Type

  Char poly: (x−2)(x−4)(x−8), eigenvalues 2, 4, 8 (dyadic cube)
```

The tower's **asymptote** is governed by the Möbius signature
[[2,1],[1,1]] of 213 (trace 3 = NS, det 1, disc 5 = NS + NT):

```
Asymptote (Z[√5]):
  rate_n → 1 − 0.5 / φ^rank
  rank = ω(|G|) − 1 + non_abelian (computable)
```

where φ = (1 + √5)/2 is the golden ratio — appearing as the
**fixed point of 213**.

The 4-row matrix indexes algebra types by their base ring:

| Type | base | First past-Moufang layer (∅-axiom in Lean) |
|---|---|---|
| **A (ZI)** | Z_4 | L3 Q_8, L4 M_16, L5 Sedenion |
| **B (ZSqrt[D≥2])** | Z_2 | L4 Q_8, L5 M_16, L6 |
| **C (ZOmega)** | Z_6 | L3 Dic_3, L4 M_24, L5 ZOmegaOct |
| **D (Hurwitz)** | 2T | base level (binary tetrahedral) |

**Cross-reference — Type C unit count in Möbius P-orbit.**
The `|Z_6| = 6` base of Type C reappears in the Lucas-Pell trace
sequence as `L(3) = 18 = NS · 6`, linking the algebraic tower's
Eisenstein unit group to the mod-p period structure of the Möbius
213 matrix (see `theory/math/mobius213_p_orbit_closure.md`
§"Cross-reference — Cayley-Dickson Type C").  The mod-3 period
`4 = NT²` directly encodes the Z_6 / Z_2 index.

The single citable Lean theorem is `algebra_tower_capstone` ∈
`CayleyDickson/Tower/AlgebraTowerCapstone.lean`.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/CayleyDickson/` (50 files)
- **Tower core**: `CayleyDickson/Tower/` (12 files)
- **Master capstone**: `Tower/AlgebraTowerCapstone.lean`
- **∅-axiom status**: structural results PURE (some level-specific
  witnesses tolerate decidability)

### Sub-cluster organization

| Sub-cluster | Purpose |
|---|---|
| `Tower/` | Generic CD tower machinery: CDDouble functor, order-4 monopoly at L3-L6, asymptotic + fixed-point + universal-induction |
| `Levels/` | Cayley + Sedenion level concrete witnesses |
| `Lipschitz/` | Lipschitz-level (L1 → L2 transition where R2 commutativity drops) |
| `Integer/` | Concrete integer codomains (ZI, ZSqrt, ZOmega, Hurwitz) |
| `Misc/` | TypeE_Rejection witnesses |

### Structural drop pattern (per `CDTower.lean`)

| Layer | Axiom that DROPS here |
|-------|----------------------|
| 0 (ZI)        | — (baseline: all R-conditions hold) |
| 1 (Lipschitz) | R2 (commutativity)              |
| 2 (Cayley)    | associativity                   |
| 3 (Sedenion)  | R3 (no zero divisors)           |

Each layer the next CD-double drops one structural axiom.  This is
the standard CD progression but **expressed within 213's R-condition
framework** (per `seed/AXIOM/`).

## The narrative

### 1. CD-Double micro mechanism

The fundamental tool is `cdd_lift_squared`:

```
∀ α : StarRing213, ∀ u c,
  conj(u) · u = c  →  (⟨0, u⟩)² = ⟨−c, 0⟩
```

This is **why** Cayley-Dickson doubling produces the right algebraic
structure at each level — the imaginary unit squares to the negative
of the conjugate-product norm.  Pure structural, derivable in any
`StarRing213`.

### 2. Recurrence law (macro level)

The transient ratios `rat_n` (per `AlgebraTowerAsymptote.lean`) satisfy
a 3-term recurrence with characteristic polynomial `(x−2)(x−4)(x−8)`.

The eigenvalues `2, 4, 8` form a **dyadic cube** — three powers of 2
that govern the tower's growth.

Type-specific constants:
- `d_A = −10752 = −2⁹·3·7`
- `d_C = −124416 = −2⁹·3⁵`
- `d_D = +1188864 = +2¹⁰·3³·43`

These factor into `2^k · (small odd part)` — **everything in 213's
algebraic tower is dyadic up to a small rational correction**.

### 3. Asymptote → φ

The recurrence has dominant eigenvalue 8 with asymptotic rate:

```
rate_n → 1 − 0.5 / φ^rank
```

where φ = golden ratio.  This is the **algebraic-tower-side
appearance** of φ as the fixed point of 213's Möbius signature
[[2,1],[1,1]]:
- trace 3 = NS
- det 1
- discriminant 5 = NS + NT
- eigenvalues φ², 1/φ²
- fixed point φ = (1+√5)/2 = "residue"

### 4. 4-row matrix (Types A, B, C, D)

Each type formalizes its first past-Moufang layer:

**Type A (ZI base, Z_4 quaternion-like)**:
- L3 Q_8 (`LipschitzOrder4Monopoly`)
- L4 M_16 (`CayleyOrder4Monopoly`)
- L5 Sedenion past-Moufang (`SedenionOrder4Monopoly`)

**Type B (ZSqrt[D≥2] base, Z_2 with D-adjustment)**:
- L4-L6 monopoly (`Order4Monopoly_L4T/L5T/L6T`)
- ZSqrt[−2] L6 witness (`ZSqrtMinus2L6Witnesses`)

**Type C (ZOmega base, Z_6 Eisenstein-like)**:
- L3 Dic_3 (`ZOmegaDoubleOrderDist`)
- L4 M_24 (`ZOmegaQuadOrderDist`)
- L5 ZOmegaOct past-Moufang (`ZOmegaOctOrderDist`)

**Type D (Hurwitz, 2T binary tetrahedral)**:
- Base level (`Hurwitz213.lean`)

Other types (E) **rejected** with explicit witness
(`Misc/TypeE_Rejection.lean`): the 4-row matrix is complete.

### 5. Cross-domain consistency

The same φ appears in:
- **Algebra tower asymptote** (this chapter)
- **DRLT physics**: CKM δ = π/φ², Cabibbo A = φ/c, ν m₃/m₂
- **Raw atomicity**: NS + NT = 5, (2φ − 1)² = 5
- **Pell-Fib infrastructure** (`DyadicFSM/Fib`)
- **Theory/Raw/Mobius** (P_numerator/denominator)

This isn't coincidence — it's the algebraic-tower's fingerprint on
the rest of 213.

## Three concurrent fates of the tower

A natural question — does the tower stop, ascend forever, or have a
meta-fixed point? — admits **three simultaneously true answers**
at three distinct levels of structure.

### 1. Algebraic property loss — bounded at L4 (Hurwitz tower)

| Layer | Algebra      | Lost property            |
|-------|--------------|--------------------------|
| L0 = ℝ | comm, assoc, normed | total order        |
| L1 = ℂ | comm, assoc, normed | none new            |
| L2 = ℍ | non-comm, assoc, normed | commutativity   |
| L3 = 𝕆 | non-assoc (alt), normed | full assoc → alt |
| L4 = 𝕊 | non-alt (pow-assoc), zero divisors | alternativity, division |
| L5+   | progressively degenerate | norm-multiplicativity, … |

Property loss **terminates at L4**: beyond L4 every classical
algebraic property that can break has broken; further CD-doubling
adds new dimensions but no new losses.

### 2. Order-4 monopoly — universal preservation (infinite ascent)

The Order-4 mechanism `(0, u)² = (−conj(u)·u, 0)` survives at
every layer (generic on `[StarRing213 α]`):

  ∀ n.  every new im-axis generated at layer L_{n+1} has order 4.

Concrete monopoly witnesses appear at L3 (Q_8 / `LipschitzOrder4Monopoly`),
L4 (M_16 / `CayleyOrder4Monopoly`), L5 (Sedenion / `SedenionOrder4Monopoly`),
and the Type B parallel `Order4Monopoly_L4T/L5T/L6T`.  The mechanism
itself never runs out — **infinite ascent at the mechanism level**.

### 3. {±1} pointwise meta-fixed point

`Lib/Math/CayleyDickson/Tower/TowerFixedPoint.lean` measures the
count of units **not** of order 4 across the tower:

| Type | L3 | L4 | L5 | L6 | non-order-4 count |
|---|---|---|---|---|---|
| A | 8 units | 16 units | 32 units | —    | **2** (= ±1) |
| B | —      | 4 units  | 8 units  | 16 units | **2** (= ±1) |

The pair `{+1, −1}` is the **pointwise fixed set** of CD-doubling
across measured layers — the universal scalar subring `ℤ ⊃ {±1}`
preserved unchanged.  Asymptotically the order-4 fraction
`rat₄(L_n) = 1 − 2/|units_n| → 1`, but `{±1}` always contributes
its 2 to the non-order-4 count.

Witnesses: `typeA_non_order4_fixed_at_2`, `typeB_non_order4_fixed_at_2`,
`tower_fixed_point_summary` (all ∅-axiom).

The three readings are not in tension — they describe different
aspects (which properties survive / which mechanism keeps firing /
which elements stay invariant).  The fixed set `{±1}` aligns with
Raw's atom / anti-atom binary axis: the meta-fixed point of the
algebra tower IS the integer scalar subring at every layer.

## Generic-lift functor — type-level CD doubling

The first CD-doubling step is mechanical at the typeclass level:

```
[CommStarRing213 α]  →  StarRing213 (CDDouble α)
```

so a layer-2 demo like `cdd_lift_squared_at_layer2 : Ring213
(CDDouble (CDDouble α))` reduces to typeclass inference — no
per-layer ring / star-ring boilerplate.

Source: `Theory/Internal/Algebra213CDDoubleStar.lean` (generic
instance, ∅-axiom).  Demo: `Theory/CDDouble/GenericLiftDemo.lean`
(∅-axiom).

The chain breaks at the second step because `CDDouble α` of a
commutative base is non-commutative in general — `CDDouble (CDDouble α)`
inhabits `StarRing213` but not `CommStarRing213`, so the instance
cannot fire recursively.  This is intrinsic: a single typeclass
covering arbitrary `n` is impossible because Cayley-Dickson
strictly loses commutativity at each step.  What survives at every
layer is the generic Order-4 mechanism above plus the
concrete instances written for each named layer (Cayley, Sedenion,
L4T, L5T, L6T).

## Key results

| Theorem / Def | Module | Statement |
|---|---|---|
| `algebra_tower_capstone` | `Tower/AlgebraTowerCapstone` | Master: imports all type-specific layers |
| `cdd_lift_squared` | `Theory/CDDouble/UniversalOrder4` | (⟨0,u⟩)² = ⟨−c,0⟩ generic |
| `Z[√5]` integer pair recurrence | `Tower/AlgebraTowerAsymptote` | Char poly (x−2)(x−4)(x−8) |
| 4-row matrix Type A L3-L5 | `Levels/{Lipschitz,Cayley,Sedenion}` | First past-Moufang per type |
| Type B L4-L6 | `Tower/Order4Monopoly_L<n>T` | ZSqrt monopoly |
| Type C L3-L5 | `Integer/ZOmega{Double,Quad,Oct}OrderDist` | Eisenstein-like |
| Type D base | `Integer/Hurwitz213` | Binary tetrahedral 2T |
| Type E rejection | `Misc/TypeE_Rejection` | 4-row matrix complete |
| Möbius signature φ fixed point | `Theory/Raw/Mobius` (Pell-Fib bridge) | 213 = [[2,1],[1,1]] |

## Deeper layers — L7T closed (ZSqrtMinus2TowerL7.lean)

`Lib/Math/CayleyDickson/Integer/ZSqrtMinus2TowerL7.lean` (12 PURE
∅-axiom) extends the Type-B (ZSqrt[-2]) tower past L6T to **L7T**,
the next CD-doubling layer:

  · L7T structure (re : L6T, im : L6T) + DecidableEq + Repr.
  · Operations: mul, conj, normSq, Add, Neg, Sub, Zero, Mul.
  · `L7T_units` enumerated list, cardinality 64 = 2 × 32
    (`L7T_units_count`).
  · ★★★★ `L7T_deeper_layer_capstone` — cardinality + doubling
    relation `L7T_units.length = 2 * L6T_units.length`.

Order distribution `(1, 1, 62, 0)` at orders `(1, 2, 4, 0)` is
predicted by the L6T pattern + CD-doubling sign rule (`(0, u)² =
(-1, 0)` when u is a unit), but full `decide` verification at L7
exceeds practical heartbeat budget — the structural shell is the
deliverable.

## L8T / L9T (Type B deeper) — closed (TowerL8 + TowerL9, 18 PURE)

`Lib/Math/CayleyDickson/Integer/ZSqrtMinus2TowerL8.lean` extends
the ZSqrt[-2] tower past L7T to **L8T**: 128 = 2 × 64 units.
`ZSqrtMinus2TowerL9.lean` continues to **L9T**: 256 = 2 × 128
units.  `set_option maxRecDepth {1024, 2048}` for cardinality
`decide`.  Full CD-doubling pattern preserved at every step.

## Type D tower L1 + L2 — closed (HurwitzTowerL1 + L2, 22 PURE)

`Lib/Math/CayleyDickson/Integer/HurwitzTowerL1.lean` shows the
CD-doubling machinery applies to Type D (Hurwitz base):

  · `HurwitzL2 := Hurwitz × Hurwitz` with mul / conj / normSq /
    add / neg.
  · Local `hurAdd, hurNeg, hurSub` (base `Hurwitz` lacks Add/Sub
    instances).
  · `HurwitzL2_units` enumerated, cardinality 48 = 2 × 24.
  · `hurwitz_tower_L1_capstone` packages cardinality + doubling.
  · `HurwitzTowerL2.lean` (7 PURE) continues: `HurwitzL3 :=
    HurwitzL2 × HurwitzL2` with `hl2Add / hl2Neg / hl2Sub`
    componentwise; unit cardinality 96 = 2 × 48.
  · ★★★★ `hurwitz_tower_L2_capstone` packages L2 cardinality +
    doubling relation.

The 4-row matrix extends past base for all four types
(A/B/C/D); the framework is uniform.

## Open frontier

The 4-row matrix is **complete** at the first past-Moufang layer.
Open extensions:

1. ~~**Deeper layers** (L7+ for Type B/C)~~ — L7T (12 PURE) and
   L8T (11 PURE) above.  Pattern uniform; higher layers L9+
   follow CD-doubling.
2. ~~**Type D tower**~~ — L1 CLOSED via `HurwitzTowerL1.lean`
   (15 PURE).  CD-doubling works uniformly across all four types.

2. **Tower fixed-point at infinity**: `TowerFixedPoint.lean` gives
   the structural statement; the analytic fixed-point analysis at
   `L → 25 = d²` (the resolution-limit depth) ties into C5
   (fractal ζ_K convergence) but is structurally separate.

3. **Type D Hurwitz extension**: 2T binary tetrahedral is base
   level; whether a "Type D tower" exists in the same sense as
   Types A/B/C is open.  Type-E rejection rejection covered Type E
   (`ℤ`-base square matrices); a parallel Type D analysis is
   pending.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.CayleyDickson
python3 tools/scan_axioms.py Lib/Math/CayleyDickson
```

## Citation guidance

- ✅ `theory/math/cayley_dickson/algebra_tower.md` (primary narrative)
- ✅ archived G-notes for deep dives:
  `research-notes/archive/algebra_tower/G##_*.md`
