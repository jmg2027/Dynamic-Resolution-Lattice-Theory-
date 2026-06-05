# Synthesis — the COUNT substrate, after both named bounds closed

**Anchor.** Closing both named COUNT bounds — Sperner (`SpernerChains.sperner_theorem`)
and Erdős' `R(k,k) > N` (`RamseyNamedBound.ramsey_lower`) — built two reusable
substrates (the `perms` enumeration; the subset count `kLayer_card = C(N,k)`) and
exposed patterns worth harvesting.

## Patterns

- **Dual COUNT faces, one residue.**  The union bound (Ramsey, *deficit ⟹
  existence*) and the double count (Sperner, *per-column cap ⟹ row-sum bound*)
  are one `0/1` incidence matrix read by rows vs columns (`Sperner.sumOver_swap`
  = Fubini), and both consume the *same* subset count `C(N,k)`
  (`Sperner.layer_size` reads a Boolean-lattice layer; `RamseyNamedBound` reads
  the monochromatic-event list).  One Raw (the finite subset residue), two Lens
  readouts — the count-Lens essay's thesis, now load-bearing in two theorems.

- **"Engine + honest rung" closes once the enumeration infra exists.**  Both
  named bounds sat as "honest rungs" over built abstract engines (`erdos_schema`,
  `lym_double_count`) until the *enumeration* was built: `perms` (orderings, `n!`)
  for Sperner's chains, the `kLayer`/edge model for Ramsey.  The reusable lift:
  an abstract existence/counting engine's *named* instantiation is a
  finite-enumeration bridge, and the enumeration (`perms_length`/`layer_size`) is
  shared infrastructure, not per-problem.

- **`nodup`-of-`flatMap`-of-disjoint-fibres** is a recurring counting-injection
  idiom — `Permutations.perms_nodup` (insert-families disjoint via `eraseFirst`)
  and `SpernerChains.chain_low` (the `{σ++τ}` family nodup via append-injectivity)
  are the same shape: `nodup_flatMap213` over a nodup base with disjoint nodup
  fibres, then `nodup_length_le_of_subset` for the count bound.

- **The propext/Classical tax on core arithmetic recurs.**  Closing these needed
  clean replacements for core lemmas that carry `propext` — and one
  (`Nat.mul_lt_mul_right`) carries **`Classical.choice`**.  Swapped for
  `Binomial.add_mul_pure`, `NatHelper.{mul_assoc,mul_left_comm,add_sub_*}`,
  `List213.length_map`, and ad-hoc privates (`mul_lt_mul_right_clean`,
  `pow_add_clean`, `succ_sub_clean`).

## New questions

- **A clean strict-order + pow Meta suite.**  `Nat.mul_lt_mul_right`
  (Classical.choice!), `Nat.pow_add`, `Nat.succ_sub` are re-proven ad-hoc per
  file.  A small `Meta/Nat` campaign — canonical propext-free
  `mul_lt_mul_right` / `pow_add` / `succ_sub` / strict-mono — would dedup the
  privates scattered across `Sperner`, `RamseyNamedBound`, and likely elsewhere.

- **More COUNT-family named bounds on the same substrate.**  ✓ **The explicit
  LYM inequality `Σ_{A∈F} 1/C(n,|A|) ≤ 1` is now closed** —
  `LymInequality.lym_antichain` (division-free form `Σ |A|!(n−|A|)! ≤ n!`),
  with `lym_tight_layer` (sharpness) and `sperner_via_lym` (LYM ⟹ Sperner); it
  was the existing `lym_double_count` engine stopped one line before Sperner's
  `min`-collapse.

  ✓ **Bollobás' set-pair inequality `m ≤ C(a+b,a)` — the heart is closed** —
  `BollobasSetPair` (18/18 PURE).  The new content (the column cap: cross-
  intersection + per-pair disjointness ⟹ each ordering favours ≤ 1 pair, via
  `before_antisymm`) and the engine (`bollobas_sum` = `lym_double_count` on the
  favour-incidence) are done; the named bound `bollobas` holds **modulo the
  favour-count rung** `V·(a+b)! = n!·a!·b!`.

  **Open rung — the favour-count** `#{π : all A before all B} =
  C(n,a+b)·a!·b!·(n−a−b)!` (i.e. `V·(a+b)! = n!·a!·b!`).  The ordering-count
  analogue of `SpernerChains.chain_low`: build a duplicate-free injected family
  of orderings favouring `(A,B)` — choose the `a+b` positions hosting `A∪B`
  (`C(n,a+b)`), order `A` into the first `a` of them and `B` into the next `b`
  (`a!·b!`), order the rest (`(n−a−b)!`) — counted via `perms`/`perms_append_mem`.

  Still open and LYM-shaped on the same substrate: Dilworth/Mirsky
  (chain/antichain duality).

- **Leibniz determinant over `perms`.**  `Linalg213/Permutation` uses `LPerm`
  *equivalence* + inversion-sign but no enumeration; `perms` + `mem_perms_iff` +
  `perms_nodup` now supply the index set for an explicit
  `det = Σ_{σ ∈ perms} sign(σ)·Π M i σ(i)` — a bridge between the two permutation
  developments.

## Cross-references

`theory/essays/proof_isa/{counting_as_cardinality,sperner_double_counting,probabilistic_method}.md`;
`lean/E213/Lib/Math/Combinatorics/{Sperner,SpernerChains,Permutations,RamseyNamedBound,CountExistence,RamseyLowerBound}.lean`;
`lean/E213/Lib/Math/Algebra/Linalg213/Permutation.lean`; `seed/PROOF_ISA.md`.
