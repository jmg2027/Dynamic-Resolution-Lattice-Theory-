# 4-Simplex Forcing: Formal Statement

Two parallel formalizations: **213 (Lean 4)** and **standard math**.
Goal: show that "every Reachable point has isomorphic local structure"
forces Aut-invariant Lens, and that atom decomposition forces 4-simplex.

Lean files (all building, 0 `sorry`):
- `E213/Atomicity.lean` — n = 5 theorem
- `E213/Homogeneity.lean` — swap automorphism, Aut-invariant Lens
- `E213/Simplex.lean` — 5-vertex partition, block-invariance

---

## Part I: Atomicity (d = 5 as a theorem)

### Standard math statement

**Theorem (Atomicity).** Let `Decomp(n) = {(a, b) ∈ ℕ² : n = 2a + 3b}`
and call `(a, b)` *alive* if both `a, b` are odd. Define
`n` to be **atomic** iff `Decomp(n)` has exactly one element and that
element is alive. Then `n` atomic ⟺ `n = 5`.

### Proof sketch

**Existence (n = 5).** `Decomp(5) = {(1, 1)}` (since `3b ≤ 5` forces
`b ≤ 1`; `b = 0` gives `2a = 5`, impossible; `b = 1` gives `a = 1`).
`(1, 1)` is alive (both odd). So `5` is atomic.

**Uniqueness.** Suppose `n` atomic with alive decomp `(a, b)`.
- **Bézout shift.** `(a±3, b∓2)` preserves `2a + 3b`: if either
  `(a-3, b+2)` or `(a+3, b-2)` is a valid (nonnegative) decomposition
  different from `(a, b)`, uniqueness fails.
- Hence `a < 3 ∧ b < 2` (else shift exists).
- Combined with `a, b` odd and ≥ 1, we get `a = b = 1`,
  so `n = 2 + 3 = 5`.  ∎

### Lean counterpart

```
theorem atomic_iff_five (n : Nat) : Atomic n ↔ n = 5
```

In `E213/Atomicity.lean`. Proof uses `rcases Nat.lt_or_ge` +
`omega` for the Bézout shift argument.

---

## Part II: Homogeneity on Reachable

### Standard math statement

Define `swap : Raw → Raw` by `swap(obj i) = obj(1 - i)`, extended
recursively through `rel`. Then:

1. **Involutive.** `swap ∘ swap = id`, hence `swap` is a bijection.
2. **Preserves Reachable.** `Reachable(x) ⟹ Reachable(swap(x))`.
3. **Local isomorphism.** At each Reachable point, swap identifies
   it with another Reachable point of identical "shape"
   (base ↔ base, rel ↔ rel with same tree structure up to base
   relabeling).

### Aut-invariant Lens forced

**Definition.** A Lens `L : Raw → α` is **swap-invariant** iff
`L.view(swap x) = L.view x` for all `x : Raw`.

**Theorem.** Swap-invariance forces `L.objValue(0) = L.objValue(1)`.

**Proof.** Apply swap-invariance to `x = obj 0`:
```
L.view(swap(obj 0)) = L.view(obj 1) = L.objValue 1
L.view(obj 0) = L.objValue 0
Swap-invariance ⟹ L.objValue 1 = L.objValue 0.   ∎
```

### Lean counterpart

```
theorem Reachable.swap {x : Raw} (h : Reachable x) :
    Reachable (Raw.swap x)

theorem Lens.swapInvariant_const_obj {α} {L : Lens α}
    (h : L.SwapInvariant) : L.objValue 0 = L.objValue 1
```

### Interpretation

"Every Reachable point has isomorphic local structure" = `swap` is a
structural automorphism respecting `Reachable`. A Lens that treats all
Reachable points uniformly (i.e. `swap`-invariant) cannot distinguish
the two base objects. Raw-level embodiment of "the universal measure
sees structure, not label."

---

## Part III: 4-Simplex from atomicity + Aut-invariance

### Standard math statement

From atomicity, `|V| = 5` with canonical partition `V = V_A ⊔ V_B`,
`|V_A| = 3, |V_B| = 2`. The atom-level automorphism group is
`Aut_atom = S_{V_A} × S_{V_B} ≅ S_3 × S_2` (order 12). Acting
diagonally on `V × V`, this partitions the 25 pairs into 6 orbits:

| Class  | Representative | Size |
|--------|---------------|------|
| AAdiag | `(0, 0)`      | 3    |
| AAoff  | `(0, 1)`      | 6    |
| AB     | `(0, 3)`      | 6    |
| BA     | `(3, 0)`      | 6    |
| BBdiag | `(3, 3)`      | 2    |
| BBoff  | `(3, 4)`      | 2    |

Total: `3 + 6 + 6 + 6 + 2 + 2 = 25 = d²`. ✓

**Theorem (Block invariance).** A weight `W : V × V → α` is
`Aut_atom`-invariant iff it factors through the `classify : V × V →
BlockPair` map.

### Lean counterpart (one direction proved)

```
theorem block_constant_implies_aut_invariant :
    BlockConstant W → AutInvariant W
```

In `E213/Simplex.lean`. The converse requires a transposition-
generator argument; stated but left for extension.

### Geometric consequence

5 vertices with an `Aut_atom`-invariant (hence block-constant) positive
Hermitian Gram matrix `G` embed into Euclidean space `ℝ^k` where
`k = rank(G) - 1 ≤ 4`. Generic rank is 4 (the 5 vectors mean-centered
lose one dimension), giving the standard 4-simplex `Δ^4 ⊂ ℝ^4`.

---

## Chain Summary

```
Atomicity             → |V| = 5, partition (3, 2)
                              ↓
Aut_atom invariance   → block-constant Gram G : V×V → ℂ
                              ↓
Positive Hermitian    → embedding V ↪ ℝ^4
                              ↓
Result                → weighted 4-simplex in ℝ^4
```

All three inputs on the left are **theorems** (given the single
axiom "relation exists between two objects" and the side axiom
"atoms are {2, 3}"), not independent postulates.

---

## Open formal items

1. **Converse of block-invariance** (hard direction of Part III
   theorem). Needs generating-transposition argument on `S_3 × S_2`.
   Tractable with explicit transpositions `(0 1), (1 2), (3 4)`.
2. **Atoms = {2, 3} derivation.** Justify atom set as the minimal
   coprime pair generating `ℕ_{≥2}` (Frobenius / Chicken McNugget).
3. **Link from Raw to 5-vertex structure.** Currently Raw's `Fin 2`
   base + atomicity → 5 is at the meta level (the "5" is the
   consequence of atom `{2, 3}` decomposition, not directly of Raw's
   `Fin 2`). A clean bridge theorem: "the minimal Aut-invariant
   closure of Raw under atom operations has 5 orbits."
