# Decomposition: parity (even/odd)

*213-decomposition of "even/odd", per `../README.md`.*

## The decomposition

- **Construction `C`** — `ℕ` = the iterated distinguishing (count): each `succ` is one more
  distinguishing-against the atom (`Lens/Number/Nat213/Generation.succ_is_distinguishing`).
- **Reading `L₂`** — `count ↦ count mod 2`: the finite reading that keeps only the *last bit* of the
  distinguishing-history and forgets the rest.
- **Residue** — infinitely many constructions collapse into exactly two classes; the residue is
  "everything the single bit forgets". (Generalizes: `L_n` = keep the count mod `n`.)

## Re-seeing the theorems

"even + odd = odd", "odd · odd = odd", … are **not** facts about numbers. They are the single fact that
`L₂` is a **homomorphism for the +-construction and the ×-construction**: the reading *respects the
way the construction was built*. Written in the calculus:

```
   even/odd  =  ⟨ ℕ (count) | L₂ = (· mod 2) ⟩
   "even+odd=odd"  =  L₂(a + b) = L₂(a) + L₂(b)        (L₂ is +-construction-preserving)
```

## Revelation (collapse)

The *same* shape — **"a finite reading `L_n` that respects the construction"** — is, verbatim:

- **modular arithmetic** — `L_n` on the +/× construction;
- **the sign of a permutation** — `L₂` read on inversion-count; this is **Zolotarev's lemma**, that
  the Legendre symbol *is* a permutation sign (`Lib/Math/NumberTheory/ModArith/Zolotarev.lean`:
  `psign_mulPerm_hom`, `psign_mulPerm_qr` — the multiplication-permutation's sign is the quadratic
  character, ∅-axiom);
- **`det = ±1` of a unimodular matrix** — `L₂` read on the Cassini/continuant construction
  (`CassiniUnimodular.det_step`).

So parity, congruence, permutation-sign, and the unimodular `±1` are **one** construction-preserving
finite reading, differing only in *which construction* `L₂`/`L_n` is laid over. Decomposing "even/odd"
— the most elementary object — immediately reveals four things conventionally taught in four separate
courses as one technique-instance. **Lean certifies the non-trivial leg** (Zolotarev: sign = Legendre)
so the collapse is proven, not asserted.

## Note for the technique

This decomposition argues the **shape-question** in the README — "should a construction-preserving
*finite reading* be a named first-class pattern in the calculus?" — *yes*: it is the single most
reused reading-shape so far. Candidate name: a **character** of a construction = a
construction-preserving reading into a finite cyclic readout.
