# The Steenrod-Whitehead bridge `cup_1(ω, ω) = δ²(ω)`

At the K_{3,2}^{(c=2)} 2-skeleton, the Steenrod cup_1 self-pairing
of the unique non-trivial H² class ω = (1, 1, 1) equals its
2-coboundary at the 3-cell extension.  Both are the constant
function `(true) : Fin 1 → Bool` on the single attaching 3-cell.

## 213-native statement

In `lean/E213/Lib/Math/Cohomology/Bipartite/FaceCup1At3Cell.lean`:

```
theorem omega_face_cup_1_eq_delta2 :
    ∀ i : Fin 1,
      face_cup_1 omega_face_vec omega_face_vec i
        = delta2_full omega_face_vec i
```

Two structurally distinct operations — `face_cup_1` (Steenrod's
higher cup product with rotational interlocking) and `delta2_full`
(the 2-coboundary at the 3-cell attaching) — agree on a single
Bool at a single 3-cell index.  Both evaluate to `true`.

## Derivation

Define the K_{3,2}^{(c=2)} 3-cell σ³ with attaching boundary
`[face_0, face_1, face_2]` (`Filled3CellExtension.C3_dim = 1`).
The 2-coboundary is

```
δ²(c)(σ³) := c(face_0) ⊕ c(face_1) ⊕ c(face_2)
```

(`Filled3CellExtension.delta2_full`).  The rotational face-cup_1
on the same 3-cell is

```
face_cup_1(α, β)(σ³)
   := α(face_0) ∧ β(face_2)
    ⊕ α(face_1) ∧ β(face_0)
    ⊕ α(face_2) ∧ β(face_1)
```

(`FaceCup1At3Cell.face_cup_1`).  These differ structurally:

  · δ² depends LINEARLY on a single cochain c.
  · cup_1 depends BILINEARLY on two cochains α, β.

For the H² class ω with face_vec = `(1, 1, 1)`:

```
δ²(ω)(σ³) = 1 ⊕ 1 ⊕ 1 = 1
cup_1(ω, ω)(σ³) = (1 ∧ 1) ⊕ (1 ∧ 1) ⊕ (1 ∧ 1) = 1 ⊕ 1 ⊕ 1 = 1
```

Both equal 1.  Proved by reflexivity after unfolding
(`omega_face_cup_1_self_eq_true`, `omega_delta2_full_eq_true`).

## Dual function

The identity is the classical **Steenrod-Whitehead theorem** —
the cup_1 self-pairing of a degree-p cocycle equals its
p-coboundary up to a sign, formalised for ordinary cup-i operations
on simplicial complexes — specialised to K_{3,2}^{(c=2)} face
cochains over F_2.  213's refinement: the identity is a
**Lean-checkable Bool equation at a concrete 3-cell index**,
not a sign-laden cohomological statement.  Both directions of
the bridge are decidable; no propositional manipulation involved.

## Cross-frame connections

The Steenrod-Whitehead bridge ties together three structural
readings of the cup-i ladder at H²:

  · **Cohomological**: `Sq^1` raises cohomology degree by 1; for
    ω at H², `Sq^1(ω) ∈ H^3` measures the obstruction to ω being
    a coboundary at the 3-cell extension.
  · **Algebraic**: `cup_(k-1)(c, c)` lands at degree `(2k − (k − 1)) =
    k + 1`; for k = 2, this is degree 3.
  · **Topological**: the 3-cell attaching `σ³ ↦ [face_0, face_1,
    face_2]` is the universal target where face dependence
    `Face_0 ⊕ Face_1 ⊕ Face_2 = 0` (true on im δ¹) detects ω's
    non-triviality.

All three give the SAME bit at σ³ — the cup_1 self-pairing, the
coboundary δ², and the face dependence indicator all coincide as
`(true) : Fin 1 → Bool`.

## Generalisation conjecture

If the K_{3,2}^{(c=2)} face dependence (`Face_0 ⊕ Face_1 ⊕ Face_2 = 0`
on `im δ¹`) is a universal phenomenon for filled bipartite
multigraph cohomology, then the Steenrod-Whitehead bridge
`cup_(k-1)(c, c) = δ^k(c)` should hold for every higher
cohomology class `c ∈ H^k` of such complexes.  At our level
(k = 2), this is proved.  For k ≥ 3, requires:

  · Higher-cell-complex extensions of K_{3,2}^{(c=2)} (which
    trivialise H^(<k) at the truncation, so different bipartite
    complexes are needed).
  · General Steenrod cup_(k-1) formula with the full
    Alexander-Whitney face-pair sum.
  · Generalised face-dependence theorems at each cohomology level.

The conjecture is open.

## Open frontier

  · **General `cup_(k-1)` formula** for arbitrary k ≥ 3.
  · **Bridge identity at k ≥ 3** in suitable cohomology complexes.
  · **Hodge / Bockstein** versions of the bridge for non-F_2
    coefficients.
  · **Massey product extension**: `cup_(k-1)(c, c)` is a
    self-pairing; triple Massey ⟨c, c, c⟩ is a partial operation;
    is there a unified Massey-Steenrod-Whitehead bridge at H^k?

## What you can point at

```
face_cup_1 omega_face_vec omega_face_vec ⟨0, _⟩ = true
delta2_full omega_face_vec ⟨0, _⟩ = true
```

Both equal `true`.  Two structurally distinct definitions, one bit
at one index, proved equal by reflexivity.  That's the bridge.
