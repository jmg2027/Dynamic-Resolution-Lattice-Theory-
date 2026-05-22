# L1 4-sibling parametric methodology (TH-4)

How to consolidate a Cup-AW Leibniz lift 4-sibling group into 2
parametric helpers (one per side).  Companion to implicit-lemma extraction's structural
analysis and the L1 β/α-side commits.

## Surface pattern

A 4-sibling L1 family at degrees `(n, a, b)` consists of:
- 2 β-decomp lenses (typically `b = 2`, varies over `a ∈ {1, 2}`)
- 2 α-decomp lenses (typically `a = 2`, varies over `b ∈ {1, 2}`)

Each sibling's proof body is structurally identical (10-step bilinearity
expansion via `delta_cupAW_add_*` × 9 + `cupAW_add_*` × 9 +
`cupAW_delta_add_*` × 9 + `h_components ⟨i, _⟩` × 10 + `combine_10`).

The variable parts: the cochain dimensions and the index Fin type.

## β-side methodology (commit 0fabff84, Part 3)

Parameter: left-factor degree `a`.

```lean
theorem leibniz_via_β_decomp_general {a : Nat}
    (α : Cochain 5 a) (β : Cochain 5 2)
    (i : Fin (binom 5 (a + 2 - 1 + 1)))    -- LHS index, reduces for abstract a
    (h_components : ∀ p, ...) :
    delta (cupAW 5 a 2 α β) i = xor (...) (...)
```

The β-side index type `a + 2 - 1 + 1` reduces because the variable `a`
is on the LEFT of `Nat.add` and the constant `2` is on the RIGHT (Lean's
`Nat.add` recurses on its RHS argument).  After Lean's automatic
reduction, `a + 2 - 1 + 1 = a + 2`, which unifies with the RHS index
types `a + 1 + 2 - 1 = a + 2` and `a + (2+1) - 1 = a + 2` — all reduce
to the same canonical form.

Result: no casts needed; the parametric helper signature is clean.

## α-side methodology (commit a119b077, Part 5)

Parameter: right-factor degree `b`.

```lean
@[reducible] def castA (b : Nat) :
    Fin (binom 5 (2 + b - 1 + 1)) → Fin (binom 5 (3 + b - 1)) := ...
@[reducible] def castB (b : Nat) :
    Fin (binom 5 (2 + b - 1 + 1)) → Fin (binom 5 (2 + (b+1) - 1)) := ...

theorem leibniz_via_α_decomp_general {b : Nat}
    (α : Cochain 5 2) (β : Cochain 5 b)
    (i : Fin (binom 5 (2 + b - 1 + 1)))
    (h_components : ∀ p,
      delta (cupAW 5 2 b ...) i
        = xor (cupAW 5 3 b ... (castA b i))     -- RHS index 1: needs cast
              (cupAW 5 2 (b+1) ... (castB b i))) :  -- RHS index 2: needs cast
    ...
```

The α-side asymmetry: cup signature `cupAW 5 2 b` produces
`Cochain 5 (2 + b - 1)`, where `2 + b` is **stuck for abstract `b`**
(Nat.add doesn't reduce when the variable is on the RHS argument).  The
three index types appearing on LHS / RHS1 / RHS2 are propositionally
equal (all = `b + 2`) but not definitionally equal:
- LHS: `2 + b - 1 + 1`  (from `delta (cupAW 5 2 b)`)
- RHS1: `3 + b - 1`      (from `cupAW 5 3 b (delta α)`)
- RHS2: `2 + (b+1) - 1`  (from `cupAW 5 2 (b+1) α (delta β)`)

Solution: explicit `Fin.cast` plumbing in two helpers (`castA`, `castB`)
that bridge the LHS index to the RHS index spaces.  The casts use
`Nat.add_comm` to swap the variable to the LHS where Nat.add reduces.

The casts are `@[reducible]` so call-site `b ∈ {1, 2}` reduces them to
identity by `rfl` automatically.

## Caller pattern

For both sides, each concrete sibling becomes a 1-line corollary:

```lean
theorem leibniz_via_β_decomp_lens   -- (a=1, b=2)
    (α : Cochain 5 1) (β : Cochain 5 2) (i : Fin (binom 5 3))
    (h_components : ...) :
    delta (cupAW 5 1 2 α β) i = xor (...) (...) :=
  leibniz_via_β_decomp_general α β i h_components

theorem leibniz_via_α_decomp_21    -- (a=2, b=1)
    (α : Cochain 5 2) (β : Cochain 5 1) (i : Fin (binom 5 3))
    (h_components : ...) :
    delta (cupAW 5 2 1 α β) i = xor (...) (...) :=
  leibniz_via_α_decomp_general α β i h_components
```

The user's `h_components` (no cast) matches the generic helper's casted
`h_components` directly via `castA/castB` reducibility at concrete `b`.

## Mass reduction

| sibling | original | after corollary |
|---------|---------:|----------------:|
| β-decomp at (5, 1, 2) | 95 lines | 20 lines |
| β-decomp at (5, 2, 2) | 83 lines | 16 lines |
| α-decomp at (5, 2, 1) | 101 lines | 41 lines |
| α-decomp at (5, 2, 2) | 101 lines | 41 lines |
| β generic helper | (new) | 113 lines |
| α generic helper | (new) | 131 lines |

Net: 380 → 362 lines but ~170 lines of repeated 10-step body retired.

## Cross-references

- `LeibnizAlgLiftBeta.lean` (β-side generic, commit 0fabff84)
- `LeibnizAlgLiftAlpha.lean` (α-side generic, commit a119b077)
- `LeibnizAlgLift{21,22,21Alpha,22Alpha}.lean` (4 corollaries)
- The tactic-token + handshake-response + implicit-lemma extraction notes (deep dives on L1 structural analysis)
- `LESSONS_LEARNED.md` Pattern #11 (Cup-Leibniz dichotomy collapse)
- `seed/RAW_DERIVATION_SPEC.md` (Raw-derivation three levels)
