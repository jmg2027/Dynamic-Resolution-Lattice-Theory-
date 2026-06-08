# Determinant-closure synthesis — what the sign theory makes visible

**Anchor.** The permutation sign homomorphism `PermSign.psign_mul`
(`psign(σ∘τ) = psign σ · psign τ`, bubble-sort, ∅-axiom) closed and on it both
determinant capstones — `DetTranspose.det_transpose` (`det Mᵀ = det M`) and
`DetMul.det_matMul` (`det(A·B) = det A · det B`) — are now built strict ∅-axiom.

## Patterns

- **The pure `cnt`-decision sidesteps the membership instance.** The default
  `Decidable (a ∈ l)` carries `propext`/`Quot.sound`; every list-membership decision
  in the determinant stack instead routes through `cnt a l = 0` (decided by `Nat.decEq`,
  pure) — `DetMul.firstDup` (the pigeonhole scan) and `DetMul.funcs_filter_perms_lperm`
  (the partition predicate `0 < cnt f (perms n)`). This is the list-membership analogue
  of the `Meta/Nat` propext-free replacements: *when a PURE proof needs to decide
  membership, count, don't `∈`-decide.* Worth a named pattern (or a `Meta` lemma
  `decidableMem_via_cnt`).

- **A homomorphism to `{±1}` is a sorting invariant, not a pre-existing parity.**
  `psign_mul` is proved by reducing `τ` to `iota n` one adjacent swap at a time, each
  swap leaving `psign(σ∘τ)·psign τ` invariant (`Q_swap`) with base at the sorted list
  (`sorted_perm_eq_iota`). This is the same "invariant + adjacent-swap + sorted base"
  template as the bubble-sort/inversion counts elsewhere; the determinant's antisymmetry
  (equal rows ⟹ 0) is the *same* `psign_mul` read at the row-swap fixed point.

- **One keystone, multiple capstones.** `psign_mul` discharges `psign_inv` (a one-liner)
  ⟹ `det_transpose` (reindex by inverse) *and* the permutation-function assembly ⟹
  `det_matMul` (Cauchy–Binet). The "build the homomorphism once, harvest the corollaries"
  shape mirrors the c-counter / P-orbit closures (`theory/essays/synthesis/layer_multiplication_pattern.md`).

## New questions

- **`det(permMatrix σ) = psign σ`** — the missing bridge tying the two readings of a
  permutation (its value-list and its 0/1 matrix). With `det_matMul` + row-perm scaling
  (`leibDet_rowPerm`) in hand this should be a short corollary, and it would make `det`
  visibly a group homomorphism `GL_n(ℤ) → ℤˣ` restricted to permutation matrices.

- **General Laplace expansion along an arbitrary column.** `Laplace` has row expansion;
  with `det_transpose` now closed, column expansion is `det_transpose` + row expansion —
  is the general `det_cofactor_col` now a free corollary, removing the last asymmetry
  between rows and columns in the determinant API?

- **Relocate the constructive pigeonhole to `Meta`/`Combinatorics`.** `firstDup`,
  `mem_of_card_le`, `nodup_imp_perm`, `cnt_filter_le`, and the two `Nodup`-notion bridges
  (`listNodup_of_cntNodup`/`cntNodup_of_listNodup`) are domain-agnostic finite-injection
  ⟹ surjection plumbing currently living in `DetMul`. They are reusable for any
  finite-pigeonhole argument; an infra-relocation pass (org-audit Phase 6) should lift
  them out.

- **Transport `mem_perms_iff`/`perms_nodup` across `PermBridge`.** `permsOf_eq` makes the
  two permutation enumerations the *same list*, but the `Combinatorics` `LPerm`/`Nodup`
  (Pairwise) and the `PermClosure` `LPerm`/`Nodup` (cnt) are still distinct relations, so
  each side re-derives sound/complete/nodup. A relation-level bridge would let the
  determinant side reuse the Combinatorics characterisations directly. Low priority — both
  sides are complete; pure dedup.

## Cross-references

`lean/E213/Lib/Math/Algebra/Linalg213/{PermSign,PermGroup,DetTranspose,DetMul,Laplace}.lean`;
`theory/essays/algebra/{permutation_sign_as_homomorphism,determinant_as_quotient_characteristic,cayley_hamilton_self_characteristic}.md`;
`theory/essays/synthesis/layer_multiplication_pattern.md`.
